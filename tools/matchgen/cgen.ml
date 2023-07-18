open Match

type opts =
  { pfx: string
  ; static: bool }

type side = L | R

type id_pred =
  | InBitSet of Int64.t
  | Ge of int
  | Eq of int

and id_test =
  | Pred of (side * id_pred)
  | And of id_test * id_test

type case_code =
  | Table of ((int * int) * int) list
  | IfThen of
      { test: id_test
      ; cif: case_code
      ; cthen: case_code option }
  | Return of int

type case =
  { swap: bool
  ; code: case_code }

let cgen_case nstates map =
  let cgen_test ids =
    match ids with
    | [id] -> Eq id
    | _ ->
        let min_id =
          List.fold_left min max_int ids in
        if List.length ids = nstates - min_id
        then Ge min_id
        else begin
          assert (nstates <= 64);
          InBitSet
            (List.fold_left (fun bs id ->
                 Int64.logor bs
                   (Int64.shift_left 1L id))
                0L ids)
        end
  in
  let symmetric =
    let inverse ((l, r), x) = ((r, l), x) in
    setify map = setify (List.map inverse map) in
  let map =
    let ordered ((l, r), _) = r <= l in
    if symmetric then
      List.filter ordered map
    else map
  in
  let exception BailToTable in
  try
    let st =
      match setify (List.map snd map) with
      | [st] -> st
      | _ -> raise BailToTable
    in
    (* the operation considered can only
     * generate a single state *)
    let pairs = List.map fst map in
    let ls, rs = List.split pairs in
    let ls = setify ls and rs = setify rs in
    if List.length ls > 1 && List.length rs > 1 then
      raise BailToTable;
    { swap = symmetric
    ; code =
        let pl = Pred (L, cgen_test ls)
        and pr = Pred (R, cgen_test rs) in
        IfThen
          { test = And (pl, pr)
          ; cif = Return st
          ; cthen = Some (Return 0) } }
  with BailToTable ->
    { swap = symmetric
    ; code = Table map }

let show_op (_cls, op) =
  "O" ^ show_op_base op

let emit_swap oc i =
  let pf m = Printf.fprintf oc m in
  let indent n =
    pf "%s" (String.sub "\t\t\t\t" 0 n) in
  let pfi n m = indent n; pf m in
  pfi i "if (l < r) {\n";
  pfi (i+1) "t = l;\n";
  pfi (i+1) "l = r;\n";
  pfi (i+1) "r = t;\n";
  pfi i "}\n"

let gen_tables oc i pfx nstates (op, c) =
  let pf m = Printf.fprintf oc m in
  let indent n =
    pf "%s" (String.sub "\t\t\t\t" 0 n) in
  let pfi n m = indent n; pf m in
  let ntables = ref 0 in
  (* should mimic the order in which
   * we visit code in emit_case; or
   * else ntables is out of sync *)
  let base = pfx ^ show_op op in
  let swap = c.swap in
  let rec gen c =
    match c with
    | Table map ->
        let name =
          if !ntables = 0 then base else
          base ^ string_of_int !ntables
        in
        assert (nstates <= 256);
        if swap then
          let n = nstates * (nstates + 1) / 2 in
          pfi i "static uchar %s[%d] = {\n" name n
        else
          pfi i "static uchar %s[%d][%d] = {\n"
            name nstates nstates;
        for l = 0 to nstates - 1 do
          pfi (i+1) "";
          for r = 0 to nstates - 1 do
            if not swap || r <= l then
              begin
                pf "%02d"
                  (try List.assoc (l,r) map
                   with Not_found -> 0); (*FIXME*)
                pf ",";
              end
          done;
          pf "\n";
        done;
        pfi i "};\n"
    | IfThen {cif; cthen} ->
        gen cif;
        Option.iter gen cthen
    | Return _ -> ()
  in
  gen c.code

let emit_case oc pfx no_swap (op, c) =
  let fpf = Printf.fprintf in
  let pf m = fpf oc m in
  let indent n =
    pf "%s" (String.sub "\t\t\t\t" 0 n) in
  let pfi n m = indent n; pf m in
  let rec side oc = function
    | L -> fpf oc "l"
    | R -> fpf oc "r"
  in
  let pred oc (s, pred) =
    match pred with
    | InBitSet bs -> fpf oc "BIT(%a) & %#Lx" side s bs
    | Eq id -> fpf oc "%a == %d" side s id
    | Ge id -> fpf oc "%d <= %a" id side s
  in
  let swap = c.swap in
  let ntables = ref 0 in
  let rec code i c =
    match c with
    | Return id -> pfi i "return %d;\n" id
    | Table map ->
        let name =
          let base = pfx ^ show_op op in
          if !ntables = 0 then base else
          base ^ string_of_int !ntables
        in
        incr ntables;
        if swap then
          pfi i "return %s[(l + l*l)/2 + r];\n" name
        else pfi i "return %s[l][r];\n" name
    | IfThen ({test = And (And (t1, t2), t3)} as r) ->
        code i @@ IfThen
          {r with test = And (t1, And (t2, t3))}
    | IfThen {test = And (Pred p, t); cif; cthen} ->
        pfi i "if (%a)\n" pred p;
        code i (IfThen {test = t; cif; cthen})
    | IfThen {test = Pred p; cif; cthen} ->
        pfi i "if (%a) {\n" pred p;
        code (i+1) cif;
        pfi i "}\n";
        Option.iter (code i) cthen
  in
  pfi 1 "case %s:\n" (show_op op);
  if not no_swap && c.swap then
    emit_swap oc 2;
  code 2 c.code

let emit_numberer opts oc n =
  let pf m = Printf.fprintf oc m in
  let nst = Array.length n.states in
  let cases =
    StateMap.by_ops n.statemap |>
    List.map (fun (op, map) ->
        (op, cgen_case nst map))
  in
  let no_swap =
    List.for_all (fun (_, c) -> c.swap) cases in
  if opts.static then pf "static ";
  pf "int\n";
  pf "%sopn(int op, int l, int r)\n" opts.pfx;
  pf "{\n";
  cases |> List.iter (gen_tables oc 1 opts.pfx nst);
  if List.exists (fun (_, c) -> c.swap) cases
  then begin
    pf "\tint t;\n";
    pf "\n";
  end;
  if no_swap then emit_swap oc 1;
  pf "\tswitch (op) {\n";
  cases |> List.iter (emit_case oc opts.pfx no_swap);
  pf "\tdefault:\n";
  pf "\t\treturn 0;\n";
  pf "\t}\n";
  pf "}\n"
