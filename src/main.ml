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

let bundle ~dryrun ~deps_only bundle atoms =
  let open OpamFilename in
  (* OpamSystem.real_path is pure evil *)
  let bundle =
    if Filename.is_relative @@ OpamFilename.Dir.to_string bundle then
      OP.(OpamFilename.cwd () / OpamFilename.Dir.to_string bundle)
    else
      bundle
  in
  let archives = OP.(bundle / "archives") in
  if not dryrun && exists_dir bundle then
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
    let vars2 = OpamVariable.([of_string "prefix", S "$BUNDLE_PREFIX"; of_string "preinstalled", B true]) in
    OpamVariable.Map.of_list (vars1 @ vars2)
  in
  let b = Buffer.create 10 in
  (* expecting quoted commands *)
  let shellout_build ~archive ~env commands =
    let open Printf in
    let dir = Filename.chop_suffix archive ".tar.gz" in
    let pr fmt = ksprintf (fun s -> Buffer.add_string b (s ^ "\n")) fmt in
    pr "echo BUILD %s" dir;
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
    "mkdir -p build $BUNDLE_PREFIX " ^
      (String.concat " " (List.map (Filename.concat "$BUNDLE_PREFIX") root_dirs)) ^
      " $BUNDLE_PREFIX/lib/stublibs";
    "export PATH=$BUNDLE_PREFIX/bin:$PATH";
    "export CAML_LD_LIBRARY_PATH=$BUNDLE_PREFIX/lib/stublibs:${CAML_LD_LIBRARY_PATH:-}";
  ];
  if not dryrun then
    List.iter mkdir [bundle; archives];
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
      (* gets the source (from url, local path, git, etc) and applies patches and substitutions *)
      OpamAction.download_package t nv;
      OpamAction.extract_package t nv;
      let p_build = OpamPath.Switch.build t.root t.switch nv in
      let archive = OP.(archives // (OpamPackage.to_string nv ^ ".tar.gz")) in
(*
        OpamGlobals.msg "p_build: %s\n" (OpamFilename.Dir.to_string p_build);
        OpamGlobals.msg "archives: %s\n" (OpamFilename.Dir.to_string archives);
        OpamGlobals.msg "archive: %s\n" (OpamFilename.to_string archive);
*)
      exec (dirname_dir p_build) [
        [ "tar"; "czf"; to_string archive; Base.to_string (basename_dir p_build) ]
      ];
      let archive = Base.to_string (basename archive) in
      let opam = OpamState.opam t nv in (* dev? *)
      let env = OpamState.add_to_env t ~opam [] (OpamFile.OPAM.build_env opam) in
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
  let bundle global_options deps_only dryrun outdir names =
    OpamArg.apply_global_options global_options;
    bundle ~dryrun ~deps_only outdir names
  in
  Term.(pure bundle $OpamArg.global_options $deps_only $dryrun $outdir $OpamArg.nonempty_atom_list),
  Term.info "opam-bundle" ~doc ~man

let () = match Cmdliner.Term.eval cmd with `Error _ -> exit 1 | _ -> exit 0
