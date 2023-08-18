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

let cgen_case tmp nstates map =
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
          ; cthen = Some (Return tmp) } }
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
  pfi i "if (l < r)\n";
  pfi (i+1) "t = l, l = r, r = t;\n"

let gen_tables oc tmp pfx nstates (op, c) =
  let i = 1 in
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
                   with Not_found -> tmp);
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
  let base = pfx ^ show_op op in
  let swap = c.swap in
  let ntables = ref 0 in
  let rec code i c =
    match c with
    | Return id -> pfi i "return %d;\n" id
    | Table map ->
        let name =
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
  let tmp = (atom_state n Tmp).id in
  let con = (atom_state n AnyCon).id in
  let nst = Array.length n.states in
  let cases =
    StateMap.by_ops n.statemap |>
    List.map (fun (op, map) ->
        (op, cgen_case tmp nst map))
  in
  let all_swap =
    List.for_all (fun (_, c) -> c.swap) cases in
  (* opn() *)
  if opts.static then pf "static ";
  pf "int\n";
  pf "%sopn(int op, int l, int r)\n" opts.pfx;
  pf "{\n";
  cases |> List.iter (gen_tables oc tmp opts.pfx nst);
  if List.exists (fun (_, c) -> c.swap) cases then
    pf "\tint t;\n\n";
  if all_swap then emit_swap oc 1;
  pf "\tswitch (op) {\n";
  cases |> List.iter (emit_case oc opts.pfx all_swap);
  pf "\tdefault:\n";
  pf "\t\treturn %d;\n" tmp;
  pf "\t}\n";
  pf "}\n\n";
  (* refn() *)
  if opts.static then pf "static ";
  pf "int\n";
  pf "%srefn(Ref r, TNum *tn, Con *con)\n" opts.pfx;
  pf "{\n";
  let cons =
    List.filter_map (function
        | (Con c, s) -> Some (c, s.id)
        | _ -> None)
      n.atoms
  in
  if cons <> [] then
    pf "\tint64_t n;\n\n";
  pf "\tswitch (rtype(r)) {\n";
  pf "\tcase RTmp:\n";
  if tmp <> 0 then begin
    assert 
      (List.exists (fun (_, s) ->
           s.id = 0
         ) n.atoms &&
       (* no temp should ever get state 0 *)
       List.for_all (fun (a, s) ->
           s.id <> 0 ||
           match a with
           | AnyCon | Con _ -> true
           | _ -> false
         ) n.atoms);
    pf "\t\tif (!tn[r.val].n)\n";
    pf "\t\t\ttn[r.val].n = %d;\n" tmp;
  end;
  pf "\t\treturn tn[r.val].n;\n";
  pf "\tcase RCon:\n";
  if cons <> [] then begin
    pf "\t\tif (con[r.val].type != CBits)\n";
    pf "\t\t\treturn %d;\n" con;
    pf "\t\tn = con[r.val].bits.i;\n";
    cons |> inverse |> group_by_fst
    |> List.iter (fun (id, cs) ->
        let wid = ref 20 in
        let fst = ref true in
        pf "\t\tif (";
        cs |> List.iter (fun c ->
            let w =
              (if !fst then 0 else 4) + 5 +
              (if c < 0L then 1 else 0) +
              (if c = 0L then 1 else
               Float.(
                 Int64.to_float c |> abs
                 |> log10 |> ceil |> to_int))
            in
            if !wid + w > 60 then begin
              pf "\n\t\t";
              wid := 15;
            end;
            if not !fst then begin
              if !wid <> 15 then pf " ";
              pf "|| ";
            end;
            pf "n == %Ld" c;
            wid := !wid + w;
            fst := false;
          );
        pf ")\n";
        pf "\t\t\treturn %d;\n" id
      );
  end;
  pf "\t\treturn %d;\n" con;
  pf "\tdefault:\n";
  pf "\t\tdie(\"constant or temporary expected\");\n";
  pf "\t}\n";
  pf "}\n"
