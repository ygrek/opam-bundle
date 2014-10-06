
open Printf
open OpamTypes

let match_package_atom nv (name,cstr) =
  OpamPackage.Name.compare (OpamPackage.name nv) name = 0 &&
  match cstr with
  | None -> true
  | Some (relop,version) -> OpamFormula.eval_relop relop (OpamPackage.version nv) version

let resolve_deps t atoms =
  let atoms = OpamSolution.sanitize_atom_list t ~permissive:true atoms in
  let action = Install (OpamPackage.Name.Set.of_list (List.map fst atoms)) in
  let universe = { (OpamState.universe t action) with u_installed = OpamPackage.Set.empty; } in
  let request = { wish_install = atoms; wish_remove = []; wish_upgrade = []; criteria = `Default; } in
  let requested = OpamPackage.Name.Set.of_list @@ List.map fst atoms in
  match OpamSolver.resolve ~verbose:true universe ~requested ~orphans:OpamPackage.Set.empty request with
  | Success solution ->
    (* return in order *)
    let l = OpamSolver.ActionGraph.Topological.fold (fun act acc -> match act with
        | To_change (_, p) -> p::acc
        | _ -> acc)
      solution.to_process []
    in
    List.rev l
  | Conflicts cs ->
    OpamGlobals.error_and_exit "Conflicts: %s"
      (OpamCudf.string_of_conflict (OpamState.unavailable_reason t) cs)

let bundle_compiler ~reuse ~dryrun (t:OpamState.state) archive =
  let open OpamFilename in
  let repo_name =
    Option.map_default
      (fun (r,_) -> OpamRepositoryName.to_string r.repo_name)
      "unknown repo"
      (OpamState.repository_and_prefix_of_compiler t t.compiler)
  in
  OpamGlobals.msg "Bundling compiler %s [%s]\n" (OpamCompiler.to_string t.compiler) repo_name;
  let comp_f = OpamPath.compiler_comp t.root t.compiler in
  match exists comp_f with
  | false -> OpamGlobals.error_and_exit "Cannot bundle compiler %s: no such file : %s"
      (OpamCompiler.to_string t.compiler)
      (to_string comp_f);
  | true ->
  let comp = OpamFile.Comp.read comp_f in
  match OpamFile.Comp.preinstalled comp with
  | true -> OpamGlobals.error_and_exit "Cannot bundle preinstalled compiler %s" (OpamCompiler.to_string t.compiler)
  | false ->
  match OpamFile.Comp.configure comp @ OpamFile.Comp.make comp <> [] with
  | true -> assert false (* old style comp file - not supported *)
  | false ->
  (* Install the compiler *)
  match OpamFile.Comp.src comp with
  | None -> OpamGlobals.error_and_exit "No source for compiler %s" (OpamCompiler.to_string t.compiler)
  | Some comp_src ->
  match dryrun with
  | true -> None
  | false ->
  let build_dir = OpamPath.Switch.build_ocaml t.root t.switch in
  let return = Some (basename_dir build_dir, comp) in
  match reuse && exists archive with
  | true -> OpamGlobals.msg "Reusing %s\n" (to_string archive); return
  | false ->
  let kind = OpamFile.Comp.kind comp in
  if kind = `local
  && Sys.file_exists (fst comp_src)
  && Sys.is_directory (fst comp_src) then
    OpamFilename.link_dir
      ~src:(OpamFilename.Dir.of_string (fst comp_src)) ~dst:build_dir
  else OpamFilename.with_tmp_dir (fun download_dir ->
      let result =
        OpamRepository.pull_url kind (OpamPackage.of_string "compiler.get")
          download_dir None [comp_src] in
      match result with
      | Not_available u -> OpamGlobals.error_and_exit "%s is not available." u
      | Up_to_date r
      | Result r        -> OpamFilename.extract_generic_file r build_dir
    );
  let patches = OpamFile.Comp.patches comp in
  let patches = List.map (fun f ->
      OpamFilename.download ~overwrite:true f build_dir
    ) patches in
  List.iter (fun f -> OpamFilename.patch f build_dir) patches;
  (exec (dirname_dir build_dir) [
    [ "tar"; "czf"; (to_string archive); Base.to_string (basename_dir build_dir) ]
  ]);
  return

let bundle ~reuse ~dryrun ~deps_only ~with_compiler bundle atoms =
  let open OpamFilename in
  (* OpamSystem.real_path is pure evil *)
  let bundle =
    if Filename.is_relative @@ OpamFilename.Dir.to_string bundle then
      OP.(OpamFilename.cwd () / OpamFilename.Dir.to_string bundle)
    else
      bundle
  in
  let archives = OP.(bundle / "archives") in
  if not dryrun && not reuse && exists_dir bundle then
    OpamGlobals.error_and_exit "Directory %s already exists" (Dir.to_string bundle);
  let t = OpamState.load_state "bundle" in
  let atoms = OpamSolution.sanitize_atom_list ~permissive:true t atoms in
  let packages = resolve_deps t atoms in
  let packages = match deps_only with
  | false -> packages
  | true -> List.filter (fun nv -> not (List.exists (match_package_atom nv) atoms)) packages
  in
  (* sync: variables and OpamPath.Switch directories *)
  let root_dirs = [ "lib"; "bin"; "sbin"; "man"; "doc"; "share"; "etc" ] in
  let variables =
    let vars1 = List.map (fun k -> OpamVariable.(of_string k, S (Filename.concat "$BUNDLE_PREFIX" k))) root_dirs in
    let vars2 = OpamVariable.([
      of_string "prefix", S "$BUNDLE_PREFIX";
      of_string "stublibs", S "$BUNDLE_PREFIX/lib/stublibs";
      of_string "preinstalled", B (not with_compiler);
      of_string "make", S "$MAKE";
    ]) in
    OpamVariable.Map.of_list (vars1 @ vars2)
  in
  let b = Buffer.create 10 in
  (* expecting quoted commands *)
  let shellout_build ?dir ~archive ~env commands =
    let archive_name = Filename.chop_suffix archive ".tar.gz" in
    let dir = Option.default archive_name dir in
    let pr fmt = ksprintf (fun s -> Buffer.add_string b (s ^ "\n")) fmt in
    pr "echo BUILD %s" archive_name;
    pr "(";
    pr "cd build";
    pr "rm -rf %s" dir;
    pr "tar -xzf ../archives/%s" archive;
    pr "cd %s" dir;
    List.iter (fun (k,v) -> pr "export %s=%s" k v) env;
    List.iter (fun args -> pr "%s" (String.concat " " args)) commands;
    pr ")"
  in
  List.iter (fun s -> Buffer.add_string b (s^"\n")) [
    "#! /bin/sh";
    "set -eu";
    ": ${BUNDLE_PREFIX=$(pwd)/local}";
    ": ${MAKE=make}";
    "mkdir -p build $BUNDLE_PREFIX " ^
      (String.concat " " (List.map (Filename.concat "$BUNDLE_PREFIX") root_dirs)) ^
      " $BUNDLE_PREFIX/lib/stublibs";
    "export PATH=$BUNDLE_PREFIX/bin:$PATH";
    "export CAML_LD_LIBRARY_PATH=$BUNDLE_PREFIX/lib/stublibs:${CAML_LD_LIBRARY_PATH:-}";
  ];
  if not dryrun then
    List.iter mkdir [bundle; archives];
  if with_compiler then
  begin
    let archive = "ocaml." ^ (OpamCompiler.to_string t.compiler) ^ ".tar.gz" in
    let archive_path = OP.(archives // archive) in
    match bundle_compiler ~reuse ~dryrun t archive_path with
    | None -> ()
    | Some (dir,comp) ->
      let env = OpamState.add_to_env t [] (OpamFile.Comp.env comp) variables in
      let commands = OpamState.filter_commands t variables (OpamFile.Comp.build comp) in
      let commands = List.map (fun l -> l @ [">>build.log 2>>build.log || (echo FAILED; tail build.log; exit 1)"]) commands in
      shellout_build ~dir:(Base.to_string dir) ~archive ~env commands
  end;
  List.iter begin fun nv ->
    try
      let repo_name =
        Option.map_default
          (fun r -> OpamRepositoryName.to_string r.OpamTypes.repo_name)
          "unknown repo"
          (OpamState.repository_of_package t nv)
      in
      OpamGlobals.msg "Bundling %s [%s]\n" (OpamPackage.to_string nv) repo_name;
      match dryrun with
      | true -> ()
      | false ->
      let archive = OP.(archives // (OpamPackage.to_string nv ^ ".tar.gz")) in
      if reuse && exists archive then
      begin
        OpamGlobals.msg "Reusing %s\n" (to_string archive)
      end
      else
      begin
        (* gets the source (from url, local path, git, etc) and applies patches and substitutions *)
        OpamAction.download_package t nv;
        OpamAction.extract_package t nv;
        let p_build = OpamPath.Switch.build t.root t.switch nv in
  (*
          OpamGlobals.msg "p_build: %s\n" (OpamFilename.Dir.to_string p_build);
          OpamGlobals.msg "archives: %s\n" (OpamFilename.Dir.to_string archives);
          OpamGlobals.msg "archive: %s\n" (OpamFilename.to_string archive);
  *)
        exec (dirname_dir p_build) [
          [ "tar"; "czf"; to_string archive; Base.to_string (basename_dir p_build) ]
        ];
      end;
      let archive = Base.to_string (basename archive) in
      let opam = OpamState.opam t nv in (* dev? *)
      let env = OpamState.add_to_env t ~opam [] (OpamFile.OPAM.build_env opam) variables in
      let install = OpamFile.Dot_install.safe_read (OpamPath.Switch.build_install t.root t.switch nv) in
      let commands = OpamState.filter_commands t ~opam variables (OpamFile.OPAM.build opam) in
      let commands = List.map (fun l -> l @ [">>build.log 2>>build.log || (echo FAILED; tail build.log; exit 1)"]) commands in
      let install_commands = ref [] in
      OpamAction.perform_dot_install (OpamPackage.name nv) install
          (`Shell (fun l -> install_commands := l :: !install_commands))
          (OpamSwitch.of_string "$BUNDLE_PREFIX");
      shellout_build ~archive ~env (commands @ List.rev !install_commands);
    with e ->
      OpamMisc.fatal e;
      OpamGlobals.error_and_exit "%s" (Printexc.to_string e);
  end packages;
  match dryrun with
  | true -> ()
  | false ->
  let install_sh = OP.(bundle // "install.sh") in
  write install_sh (Buffer.contents b);
  chmod install_sh 0o755;
  ()

let cmd =
  let open Cmdliner in
  let doc = "Generate a self-contained bundle of given packages with all dependencies." in
  let man = [
    `S "DESCRIPTION";
    `P "This command calculates the transitive dependencies of the given packages \
        and collects all the corresponding archives into a specified directory, \
        along with the shell script to unpack, build and install those packages \
        on any remote machine (even without OPAM installed).";
  ] in
  let outdir = 
    let doc = Arg.info ["o";"outdir"] ~docv:"DIR" ~doc:"Write bundle to the directory $(docv)." in
    Arg.(value & opt OpamArg.dirname (OpamFilename.Dir.of_string "bundle") & doc)
  in
  let deps_only =
    Arg.(value & flag & info ["deps-only"] ~doc:"Bundle only the dependencies, excluding the specified packages.")
  in
  let dryrun =
    Arg.(value & flag & info ["dry-run"] ~doc:"Do not actually create bundle, only show actions to be done.")
  in
  let with_compiler =
    Arg.(value & flag & info ["with-compiler"] ~doc:"Bundle the compiler too")
  in
  let reuse =
    let doc = "Allow reusing archives already bundled in the output directory (no checking performed, can be useful to \
    skip redownloading compiler sources)"
    in
    Arg.(value & flag & info ["reuse"] ~doc)
  in
  let bundle global_options deps_only dryrun with_compiler reuse outdir names =
    OpamArg.apply_global_options global_options;
    bundle ~dryrun ~deps_only ~with_compiler ~reuse outdir names
  in
  Term.(pure bundle $OpamArg.global_options $deps_only $dryrun $with_compiler $reuse $outdir $OpamArg.nonempty_atom_list),
  Term.info "opam-bundle" ~doc ~man

let () = match Cmdliner.Term.eval cmd with `Error _ -> exit 1 | _ -> exit 0
