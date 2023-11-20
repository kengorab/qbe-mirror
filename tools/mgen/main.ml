open Cgen
open Match

let mgen ~verbose ~fuzz path input =
  let info ?(level = 1) fmt =
    if level <= verbose then
      Printf.eprintf fmt
    else
      Printf.ifprintf stdout fmt
  in

  let rules =
    match Sexp.(run_parser ppats) input with
    | `Error (ps, err, loc) ->
        Printf.eprintf "%s:%d:%d %s\n"
          path ps.Sexp.line ps.Sexp.coln err;
        Printf.eprintf "%s" loc;
        exit 1
    | `Ok rules -> rules
  in

  info "adding ac variants...%!";
  let nparsed =
    List.fold_left
      (fun npats (_, _, ps) ->
         npats + List.length ps)
      0 rules
  in
  let rules =
    List.concat_map (fun (name, vars, patterns) ->
        List.map
          (fun pattern -> {name; vars; pattern})
          (List.concat_map ac_equiv patterns)
      ) rules
  in
  info " %d -> %d patterns\n"
    nparsed (List.length rules);

  let rnames =
    List.map (fun r -> r.name) rules |> setify in

  info "generating match tables...%!";
  let sa, am, sm = generate_table rules in
  let numbr = make_numberer sa am sm in
  info " %d states, %d rules\n"
    (Array.length sa) (StateMap.cardinal sm);
  if verbose >= 2 then begin
    info "-------------\nstates:\n";
    Array.iteri (fun i s ->
        info ~level:2 "  state %d: %s\n"
          i (show_pattern s.seen)) sa;
    info "-------------\nstatemap:\n";
    Test.print_sm stderr sm;
    info "-------------\n";
  end;

  info "generating matchers...\n";
  let matchers =
    List.map (fun rname ->
        info "+ %s...%!" rname;
        let m = lr_matcher sm sa rules rname in
        info " %d nodes\n" (Action.size m);
        info ~level:2 "  -------------\n";
        info ~level:2 "  automaton:\n";
        info ~level:2 "%s\n"
          (Format.asprintf "    @[%a@]" Action.pp m);
        info ~level:2 "  ----------\n";
        (rname, m)
      ) rnames
  in

  if fuzz then begin
    info ~level:0 "fuzzing statemap...\n";
    let tp = Fuzz.fuzz_numberer rules numbr in
    info ~level:0 "testing %d patterns...\n"
      (List.length rules);
    Fuzz.test_matchers tp numbr rules
  end;

  info "emitting C...\n";
  flush stderr;

  let cgopts =
    { pfx = ""
    ; static = true
    ; oc = stdout }
  in
  emit_c cgopts numbr;
  (* emit_matchers cgopts *)

  ()

let read_all ic =
  let bufsz = 4096 in
  let buf = Bytes.create bufsz in
  let data = Buffer.create bufsz in
  while input ic buf 0 bufsz <> 0 do
    Buffer.add_bytes data buf;
  done;
  Buffer.contents data

let () =
  let usage_msg = "mgen [--fuzz] <file>" in
  let fuzz_arg = ref false in
  let verbose_arg = ref 0 in
  let input_paths = ref [] in

  let anon_fun filename =
    input_paths := filename :: !input_paths in

  let speclist =
    [ ("--fuzz", Arg.Set fuzz_arg, " fuzz tables and matchers")
    ; ("--verbose", Arg.Set_int verbose_arg, " ") ]
  in
  Arg.parse speclist anon_fun usage_msg;
  let input_paths = !input_paths in
  let verbose = !verbose_arg in
  let fuzz = !fuzz_arg in
  let input_path, input =
    match input_paths with
    | ["-"] -> ("-", read_all stdin)
    | [path] -> (path, read_all (open_in path))
    | _ -> Arg.usage speclist usage_msg; exit 1
  in

  mgen ~verbose ~fuzz input_path input;

  ()
