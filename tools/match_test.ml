(* #use "match.ml";; *)

open Match

(* unit tests *)

let test_pattern_match =
  let pm = pattern_match
  and nm = fun x y -> not (pattern_match x y) in
  begin
    assert (nm (Atm Tmp) (Atm (Con 42L)));
    assert (pm (Atm AnyCon) (Atm (Con 42L)));
    assert (nm (Atm (Con 42L)) (Atm AnyCon));
    assert (nm (Atm (Con 42L)) (Atm Tmp));
  end

let test_peel =
  let o = Kw, Oadd in
  let p = Bnr (o, Bnr (o, Atm Tmp, Atm Tmp),
                  Atm (Con 42L)) in
  let l = peel p () in
  let () = assert (List.length l = 3) in
  let atomic_p (p, _) =
    match p with Atm _ -> true | _ -> false in
  let () = assert (List.for_all atomic_p l) in
  let l = List.map (fun (p, c) -> fold_cursor c p) l in
  let () = assert (List.for_all ((=) p) l) in
  ()

let test_fold_pairs =
  let l = [1; 2; 3; 4; 5] in
  let p = fold_pairs l l [] (fun a b -> a :: b) in
  let () = assert (List.length p = 25) in
  let p = sort_uniq compare p in
  let () = assert (List.length p = 25) in
  ()

(* test pattern & state *)

let print_sm =
  StateMap.iter (fun k s' ->
    match k with
    | K (o, sl, sr) ->
        let top =
          List.fold_left (fun top c ->
            match c with
            | Top r -> top ^ " " ^ r
            | _ -> top) "" s'.point
        in
        Printf.printf
          "(%s %d %d) -> %d%s\n"
          (show_op o)
          sl.id sr.id s'.id top)

let rules =
  let oa = Kl, Oadd in
  let om = Kl, Omul in
  let va = Var ("a", Tmp)
  and vb = Var ("b", Tmp)
  and vc = Var ("c", Tmp)
  and vs = Var ("s", Tmp) in
  let rule name pattern =
    List.map
      (fun pattern -> {name; pattern})
      (ac_equiv pattern)
  in
  match `X64Addr with
  (* ------------------------------- *)
  | `X64Addr ->
    (* o + b *)
    (* rule "ob" (Bnr (oa, Atm Tmp, Atm AnyCon)) *) []
    @ (* b + s * i *)
    rule "bs" (Bnr (oa, vb, Bnr (om, Var ("m", AnyCon), vs)))
    @  (* b + s *)
    rule "bs1" (Bnr (oa, vb, vs))
    @ (* o + s * i *)
    (* rule "os" (Bnr (oa, Atm AnyCon, Bnr (om, Atm (Con 4L), Atm Tmp))) *) []
    @ (* b + o + s *)
    rule "bos1" (Bnr (oa, Bnr (oa, Var ("o", AnyCon), vb), vs))
    @ (* b + o + s * i *)
    rule "bos" (Bnr (oa, Bnr (oa, Var ("o", AnyCon), vb),
                         Bnr (om, Var ("m", AnyCon), vs)))
  (* ------------------------------- *)
  | `Add3 ->
    [ { name = "add"
      ; pattern = Bnr (oa, va, Bnr (oa, vb, vc)) } ] @
    [ { name = "add"
      ; pattern = Bnr (oa, Bnr (oa, va, vb), vc) } ]


let sa, sm = generate_table rules
let () =
  Array.iteri (fun i s ->
      Format.printf "@[state %d: %s@]@."
        i (show_pattern s.seen))
    sa
let () = print_sm sm; flush stdout

let matcher = lr_matcher sm sa rules "bos" (* XXX *)
let () = Format.printf "@[<v>%a@]@." Action.pp matcher
let () = Format.printf "@[matcher size: %d@]@." (Action.size matcher)

(* -------------------- *)

(* fuzz the tables and matchers generated *)

module Buffer: sig
  type 'a t
  val create: ?capacity:int -> unit -> 'a t
  val reset: 'a t -> unit
  val size: 'a t -> int
  val get: 'a t -> int -> 'a
  val set: 'a t -> int -> 'a -> unit
  val push: 'a t -> 'a -> unit
end = struct
  type 'a t =
    { mutable size: int
    ; mutable data: 'a array
    }
  let mk_array n = Array.make n (Obj.magic 0)
  let create ?(capacity = 10) () =
    if capacity < 0 then invalid_arg "Buffer.make";
    {size = 0; data = mk_array capacity}
  let reset b = b.size <- 0
  let size b = b.size
  let get b n =
    if n >= size b then invalid_arg "Buffer.get";
    b.data.(n)
  let set b n x =
    if n >= size b then invalid_arg "Buffer.set";
    b.data.(n) <- x
  let push b x =
    let cap = Array.length b.data in
    if size b = cap then begin
      let data = mk_array (2 * cap + 1) in
      Array.blit b.data 0 data 0 cap;
      b.data <- data
    end;
    let sz = size b in
    b.size <- sz + 1;
    set b sz x
end

type numberer =
  { atoms: (atomic_pattern * p state) list
  ; statemap: p state StateMap.t
  ; mutable ops: op list
    (* memoizes the list of possible operations
     * according to the statemap *)
  }

let atom_state n (atm: atomic_pattern): p state =
  List.assoc atm n.atoms

let binop_state n op s1 s2 =
  let key = K (op, s1, s2) in
  try StateMap.find key n.statemap
  with Not_found -> atom_state n Tmp

(* A term pool is a deduplicated set of term
 * that maintains nodes numbering using the
 * statemap passed at creation time *)
module TermPool = struct
  type id = int
  type term_data =
    | Binop of op * id * id
    | Leaf of atomic_pattern
  type term =
    { id: id
    ; data: term_data
    ; state: p state
    }

  type t =
    { terms: term Buffer.t
    ; hcons: (term_data, id) Hashtbl.t
    ; numbr: numberer
    }

  let create numbr =
    { terms = Buffer.create ()
    ; hcons = Hashtbl.create 100
    ; numbr
    }
  let reset tp =
    Buffer.reset tp.terms;
    Hashtbl.clear tp.hcons

  let size tp = Buffer.size tp.terms
  let term tp id = Buffer.get tp.terms id

  let mk_leaf tp atm =
    let data = Leaf atm in
    match Hashtbl.find tp.hcons data with
    | id -> term tp id
    | exception Not_found ->
        let id = Buffer.size tp.terms in
        let state = atom_state tp.numbr atm in
        Buffer.push tp.terms {id; data; state};
        Hashtbl.add tp.hcons data id;
        term tp id
  let mk_binop tp op t1 t2 =
    let data = Binop (op, t1.id, t2.id) in
    match Hashtbl.find tp.hcons data with
    | id -> term tp id
    | exception Not_found ->
        let id = Buffer.size tp.terms in
        let state =
          binop_state tp.numbr op t1.state t2.state
        in
        Buffer.push tp.terms {id; data; state};
        Hashtbl.add tp.hcons data id;
        term tp id

  let rec add_pattern tp = function
    | Bnr (op, p1, p2) ->
        let t1 = add_pattern tp p1 in
        let t2 = add_pattern tp p2 in
        mk_binop tp op t1 t2
    | Atm atm -> mk_leaf tp atm
    | Var (_, atm) -> add_pattern tp (Atm atm)
end

module R = Random

(* uniform pick in a list *)
let list_pick l =
  let rec aux n l x =
    match l with
    | [] -> x
    | y :: l ->
        if R.int (n + 1) = 0 then
          aux (n + 1) l y
        else
          aux (n + 1) l x
  in
  match l with
  | [] -> invalid_arg "list_pick"
  | x :: l -> aux 1 l x

let term_pick ~numbr =
  let ops =
    if numbr.ops = [] then
      numbr.ops <-
        (StateMap.fold (fun k _ ops ->
             match k with
             | K (op, _, _) -> op :: ops)
            numbr.statemap [] |> setify);
    numbr.ops
  in
  let rec gen depth =
    (* exponential probability for leaves to
     * avoid skewing towards shallow terms *)
    let atm_prob = Float.pow 0.7 (float_of_int depth) in
    if R.float 1.0 <= atm_prob || ops = [] then
      let atom, st = list_pick numbr.atoms in
      (st, Atm atom)
    else
      let op = list_pick ops in
      let s1, t1 = gen (depth - 1) in
      let s2, t2 = gen (depth - 1) in
      ( binop_state numbr op s1 s2
      , Bnr (op, t1, t2) )
  in
  fun ~depth -> gen depth

exception FuzzError

let rec pattern_depth = function
  | Bnr (_, p1, p2) ->
      1 + max (pattern_depth p1) (pattern_depth p2)
  | Atm _ -> 0
  | Var (_, atm) -> pattern_depth (Atm atm)

let fuzz_numberer rules numbr =
  (* pick twice the max pattern depth so we
   * have a chance to find non-trivial numbers
   * for the atomic patterns in the rules *)
  let depth =
    List.fold_left (fun depth r ->
        max depth (pattern_depth r.pattern))
      0 rules * 2
  in
  (* fuzz until the term pool we are constructing
   * is no longer growing fast enough; or we just
   * went through sufficiently many iterations *)
  let max_iter = 100_000_000 in
  let low_new_rate = 1e-2 in
  let tp = TermPool.create numbr in
  let rec loop new_stats i =
    let (_, _, new_rate) = new_stats in
    if new_rate <= low_new_rate then () else
    if i >= max_iter then () else
    (* periodically update stats *)
    let new_stats =
      let (num, cnt, rate) = new_stats in
      if num land 255 = 0 then
        let rate =
          0.5 *. (rate +. float_of_int cnt /. 255.)
        in
        let () =
          Format.printf "i:%d r:%.3g%%@."
            i (rate *. 1e2)
        in
        (num + 1, 0, rate)
      else new_stats
    in
    (* create a term and check that its number is
     * accurate wrt the rules *)
    let st, term = term_pick ~numbr ~depth in
    let state_matched =
      List.filter_map (fun cu ->
          match cu with
          | Top name -> Some name
          | _ -> None)
        st.point |> setify
    in
    let rule_matched =
      List.filter_map (fun r ->
          if pattern_match r.pattern term then
            Some r.name
          else None)
        rules |> setify
    in
    if state_matched <> rule_matched then begin
      let open Format in
      let pp_str_list =
        let pp_sep fmt () = fprintf fmt ",@ " in
        pp_print_list ~pp_sep pp_print_string
      in
      printf "@[<v2>fuzz error for %s"
        (show_pattern term);
      printf "@ state matched: %a"
        pp_str_list state_matched;
      printf "@ rule matched: %a"
        pp_str_list rule_matched;
      printf "@]@.";
      raise FuzzError;
    end;
    if state_matched = [] then
      loop new_stats (i + 1)
    else
      (* add to the term pool *)
      let old_size = TermPool.size tp in
      let _ = TermPool.add_pattern tp term in
      let new_stats =
        let (num, cnt, rate) = new_stats in
        if TermPool.size tp <> old_size then
          (num + 1, cnt + 1, rate)
        else
          (num + 1, cnt, rate)
      in
      loop new_stats (i + 1)
  in
  loop (1, 0, 1.0) 0;
  tp

(* -------------------- *)

let make_numberer sa sm =
  { atoms = Array.to_seq sa |>
            Seq.filter_map (fun s ->
                match atomic s.seen with
                | Some a -> Some (a, s)
                | None -> None) |>
            List.of_seq
  ; statemap = sm
  ; ops = []
  }

let _tp = fuzz_numberer rules (make_numberer sa sm)
