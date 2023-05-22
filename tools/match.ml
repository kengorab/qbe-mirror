type cls = Kw | Kl | Ks | Kd
type op_base =
  | Oadd
  | Osub
  | Omul
  | Oor
  | Oshl
  | Oshr
type op = cls * op_base

let commutative = function
  | (_, (Oadd | Omul | Oor)) -> true
  | (_, _) -> false

let associative = function
  | (_, (Oadd | Omul | Oor)) -> true
  | (_, _) -> false

type atomic_pattern =
  | Tmp
  | AnyCon
  | Con of int64

type pattern =
  | Bnr of op * pattern * pattern
  | Atm of atomic_pattern
  | Var of string * atomic_pattern

let is_atomic = function
  | (Atm _ | Var _) -> true
  | _ -> false

let show_op (k, o) =
  (match o with
   | Oadd -> "add"
   | Osub -> "sub"
   | Omul -> "mul"
   | Oor -> "or"
   | Oshl -> "shl"
   | Oshr -> "shr") ^
  (match k with
   | Kw -> "w"
   | Kl -> "l"
   | Ks -> "s"
   | Kd -> "d")

let rec show_pattern p =
  match p with
  | Atm Tmp -> "%"
  | Atm AnyCon -> "$"
  | Atm (Con n) -> Int64.to_string n
  | Var (v, p) ->
      show_pattern (Atm p) ^ "'" ^ v
  | Bnr (o, pl, pr) ->
      "(" ^ show_op o ^
      " " ^ show_pattern pl ^
      " " ^ show_pattern pr ^ ")"

let atomic p =
  match p with
  | (Atm a | Var (_, a)) -> Some a
  | _ -> None

let rec pattern_match p w =
  match p with
  | Var (_, p) ->
      pattern_match (Atm p) w
  | Atm Tmp ->
      begin match atomic w with
      | Some (Con _ | AnyCon) -> false
      | _ -> true
      end
  | Atm (Con _) -> w = p
  | Atm (AnyCon) ->
      not (pattern_match (Atm Tmp) w)
  | Bnr (o, pl, pr) ->
      begin match w with
      | Bnr (o', wl, wr) ->
          o' = o &&
          pattern_match pl wl &&
          pattern_match pr wr
      | _ -> false
      end

type +'a cursor = (* a position inside a pattern *)
  | Bnrl of op * 'a cursor * pattern
  | Bnrr of op * pattern * 'a cursor
  | Top of 'a

let rec fold_cursor c p =
  match c with
  | Bnrl (o, c', p') -> fold_cursor c' (Bnr (o, p, p'))
  | Bnrr (o, p', c') -> fold_cursor c' (Bnr (o, p', p))
  | Top _ -> p

let peel p x =
  let once out (p, c) =
    match p with
    | Var (_, p) -> (Atm p, c) :: out
    | Atm _ -> (p, c) :: out
    | Bnr (o, pl, pr) ->
        (pl, Bnrl (o, c, pr)) ::
        (pr, Bnrr (o, pl, c)) :: out
  in
  let rec go l =
    let l' = List.fold_left once [] l in
    if List.length l' = List.length l
    then l'
    else go l'
  in go [(p, Top x)]

let fold_pairs l1 l2 ini f =
  let rec go acc = function
    | [] -> acc
    | a :: l1' ->
        go (List.fold_left
          (fun acc b -> f (a, b) acc)
          acc l2) l1'
  in go ini l1

let iter_pairs l f =
  fold_pairs l l () (fun x () -> f x)

type 'a state =
  { id: int
  ; seen: pattern
  ; point: ('a cursor) list }

let rec binops side {point; _} =
  List.filter_map (fun c ->
      match c, side with
      | Bnrl (o, c, r), `L -> Some ((o, c), r)
      | Bnrr (o, l, c), `R -> Some ((o, c), l)
      | _ -> None)
    point

let group_by_fst l =
  List.fast_sort (fun (a, _) (b, _) ->
    compare a b) l |>
  List.fold_left (fun (oo, l, res) (o', c) ->
      match oo with
      | None -> (Some o', [c], [])
      | Some o when o = o' -> (oo, c :: l, res)
      | Some o -> (Some o', [c], (o, l) :: res))
    (None, [], []) |>
  (function
    | (None, _, _) -> []
    | (Some o, l, res) -> (o, l) :: res)

let sort_uniq cmp l =
  List.fast_sort cmp l |>
  List.fold_left (fun (eo, l) e' ->
      match eo with
      | None -> (Some e', l)
      | Some e when cmp e e' = 0 -> (eo, l)
      | Some e -> (Some e', e :: l))
    (None, []) |>
  (function
    | (None, _) -> []
    | (Some e, l) -> List.rev (e :: l))

let setify l =
  sort_uniq compare l

let normalize (point: ('a cursor) list) =
  setify point

let next_binary tmp s1 s2 =
  let pm w (_, p) = pattern_match p w in
  let o1 = binops `L s1 |>
           List.filter (pm s2.seen) |>
           List.map fst in
  let o2 = binops `R s2 |>
           List.filter (pm s1.seen) |>
           List.map fst in
  List.map (fun (o, l) ->
    o,
    { id = -1
    ; seen = Bnr (o, s1.seen, s2.seen)
    ; point = normalize (l @ tmp)
    }) (group_by_fst (o1 @ o2))

type p = string

module StateSet : sig
  type t
  val create: unit -> t
  val add: t -> p state ->
           [> `Added | `Found ] * p state
  val iter: t -> (p state -> unit) -> unit
  val elems: t -> (p state) list
end = struct
  open Hashtbl.Make(struct
    type t = p state
    let equal s1 s2 = s1.point = s2.point
    let hash s = Hashtbl.hash s.point
  end)
  type nonrec t =
    { h: int t
    ; mutable next_id: int }
  let create () =
    { h = create 500; next_id = 0 }
  let add set s =
    assert (s.point = normalize s.point);
    try
      let id = find set.h s in
      `Found, {s with id}
    with Not_found -> begin
      let id = set.next_id in
      set.next_id <- id + 1;
      add set.h s id;
      `Added, {s with id}
    end
  let iter set f =
    let f s id = f {s with id} in
    iter f set.h
  let elems set =
    let res = ref [] in
    iter set (fun s -> res := s :: !res);
    !res
end

type table_key =
  | K of op * p state * p state

module StateMap = struct
  include Map.Make(struct
      type t = table_key
      let compare ka kb =
        match ka, kb with
        | K (o, sl, sr), K (o', sl', sr') ->
            compare (o, sl.id, sr.id)
                    (o', sl'.id, sr'.id)
    end)
  let invert n sm =
    let rmap = Array.make n [] in
    iter (fun k {id; _} ->
        match k with
        | K (o, sl, sr) ->
            rmap.(id) <-
              (o, (sl.id, sr.id)) :: rmap.(id)
      ) sm;
    Array.map group_by_fst rmap
end

type rule =
  { name: string
  ; pattern: pattern
  }

let generate_table rl =
  let states = StateSet.create () in
  (* initialize states *)
  let ground =
    List.concat_map
      (fun r -> peel r.pattern r.name) rl |>
    group_by_fst
  in
  let find x d l =
    try List.assoc x l with Not_found -> d in
  let tmp = find (Atm Tmp) [] ground in
  let con = find (Atm AnyCon) [] ground in
  let () =
    List.iter (fun (seen, l) ->
      let point =
        if pattern_match (Atm Tmp) seen
        then normalize (tmp @ l)
        else normalize (con @ l)
      in
      let s = {id = -1; seen; point} in
      let flag, _ = StateSet.add states s in
      assert (flag = `Added)
    ) ground
  in
  (* setup loop state *)
  let map = ref StateMap.empty in
  let map_add k s' =
    map := StateMap.add k s' !map
  in
  let flag = ref `Added in
  let flagmerge = function
    | `Added -> flag := `Added
    | _ -> ()
  in
  (* iterate until fixpoint *)
  while !flag = `Added do
    flag := `Stop;
    let statel = StateSet.elems states in
    iter_pairs statel (fun (sl, sr) ->
      next_binary tmp sl sr |>
      List.iter (fun (o, s') ->
        let flag', s' =
          StateSet.add states s' in
        flagmerge flag';
        map_add (K (o, sl, sr)) s';
    ));
  done;
  let states =
    StateSet.elems states |>
    List.sort (fun s s' -> compare s.id s'.id) |>
    Array.of_list
  in
  (states, !map)

let intersperse x l =
  let rec go left right out =
    let out =
      (List.rev left @ [x] @ right) ::
      out in
    match right with
    | x :: right' ->
        go (x :: left) right' out
    | [] -> out
  in go [] l []

let rec permute = function
  | [] -> [[]]
  | x :: l ->
      List.concat (List.map
        (intersperse x) (permute l))

(* build all binary trees with ordered
 * leaves l *)
let rec bins build l =
  let rec go l r out =
    match r with
    | [] -> out
    | x :: r' ->
        go (l @ [x]) r'
          (fold_pairs
            (bins build l)
            (bins build r)
            out (fun (l, r) out ->
                   build l r :: out))
  in
  match l with
  | [] -> []
  | [x] -> [x]
  | x :: l -> go [x] l []

let products l ini f =
  let rec go acc la = function
    | [] -> f (List.rev la) acc
    | xs :: l ->
        List.fold_left (fun acc x ->
            go acc (x :: la) l)
          acc xs
  in go ini [] l

(* combinatorial nuke... *)
let rec ac_equiv =
  let rec alevel o = function
    | Bnr (o', l, r) when o' = o ->
        alevel o l @ alevel o r
    | x -> [x]
  in function
  | Bnr (o, _, _) as p
    when associative o ->
      products
        (List.map ac_equiv (alevel o p)) []
        (fun choice out ->
          List.concat_map
            (bins (fun l r -> Bnr (o, l, r)))
            (if commutative o
              then permute choice
              else [choice]) @ out)
  | Bnr (o, l, r)
    when commutative o ->
      fold_pairs
        (ac_equiv l) (ac_equiv r) []
        (fun (l, r) out ->
          Bnr (o, l, r) ::
          Bnr (o, r, l) :: out)
  | Bnr (o, l, r) ->
      fold_pairs
        (ac_equiv l) (ac_equiv r) []
        (fun (l, r) out ->
          Bnr (o, l, r) :: out)
  | x -> [x]

module Action: sig
  type node =
    | Switch of (int * t) list * t option
    | Push of bool * t
    | Pop of t
    | Set of string * t
    | Stop
  and t = private
    { id: int; node: node }
  val equal: t -> t -> bool
  val size: t -> int
  val stop: t
  val mk_push: sym:bool -> t -> t
  val mk_pop: t -> t
  val mk_set: string -> t -> t
  val mk_switch: ?default:t -> (int * t) list -> t
  val pp: Format.formatter -> t -> unit
end = struct
  type node =
    | Switch of (int * t) list * t option
    | Push of bool * t
    | Pop of t
    | Set of string * t
    | Stop
  and t =
    { id: int; node: node }

  let equal a a' = a.id = a'.id
  let size a =
    let seen = Hashtbl.create 10 in
    let rec node_size = function
      | Switch (l, d) ->
          List.fold_left
            (fun n (_, a) -> n + size a)
            (match d with
             | None -> 0
             | Some a -> size a)
            l
      | (Push (_, a) | Pop a | Set (_, a)) ->
          size a
      | Stop -> 0
    and size {id; node} =
      if Hashtbl.mem seen id
      then 0
      else begin
        Hashtbl.add seen id ();
        1 + node_size node
      end
    in
    size a

  let mk =
    let hcons = Hashtbl.create 100 in
    let fresh = ref 0 in
    fun node ->
      let id =
        try Hashtbl.find hcons node
        with Not_found ->
          let id = !fresh in
          Hashtbl.add hcons node id;
          fresh := id + 1;
          id
      in
      {id; node}
  let stop = mk Stop
  let mk_push ~sym a = mk (Push (sym, a))
  let mk_pop a =
    match a.node with
    | Stop -> a
    | _ -> mk (Pop a)
  let mk_set v a = mk (Set (v, a))
  let mk_switch ?default cases =
    mk (Switch (cases, default))

  open Format
  let rec pp_node fmt = function
    | Switch (l, d) ->
        fprintf fmt "@[<v>@[<v2>switch{";
        let pp_case pp_c (c, a) =
          fprintf fmt
            "@,@[<2>→%a:@ @[%a@]@]" pp_c c pp a
        in
        List.iter (pp_case pp_print_int) l;
        begin match d with
        | None -> ()
        | Some a -> pp_case pp_print_string ("?", a)
        end;
        fprintf fmt "@]@,}@]"
    | Push (true, a) -> fprintf fmt "pushsym@ %a" pp a
    | Push (false, a) -> fprintf fmt "push@ %a" pp a
    | Pop a -> fprintf fmt "pop@ %a" pp a
    | Set (v, a) -> fprintf fmt "set(%s)@ %a" v pp a
    | Stop -> fprintf fmt "•"
  and pp fmt a = pp_node fmt a.node
end

let count p l =
  let f n x = if p x then n + 1 else n in
  List.fold_left f 0 l

let mk_switch ids f =
  if ids = [] then
    failwith "empty switch";
  let (=$) = Action.equal in
  let cases = List.map f ids in
  let cnt, default =
    List.fold_left (fun (nd, d) c -> 
        let nc = count ((=$) c) cases in
        if nc > nd then (nc, c) else (nd, d))
      (0, Action.stop) cases
  in
  let cases = List.combine ids cases in
  if cnt = List.length cases then
    default
  else if cnt = 1 then
    Action.mk_switch cases
  else
    let cases =
      List.filter (fun (_, c) ->
          not (c =$ default)) cases
    in
    Action.mk_switch ~default cases

(* left-to-right matching of a set of patterns;
 * may raise if there is no lr matcher for the
 * input rule *)
let lr_matcher statemap states rules name =
  let rmap =
    let nstates = Array.length states in
    StateMap.invert nstates statemap
  in
  (* a state is commutative if (a op b) enters
   * it iff (b op a) enters it as well *)
  let symmetric id =
    List.for_all (fun (_, l) ->
        let l1, l2 =
          List.filter (fun (a, b) -> a <> b) l |>
          List.partition (fun (a, b) -> a < b)
        in
        let l2 = List.map (fun (a, b) -> (b, a)) l2 in
        setify l1 = setify l2)
      rmap.(id)
  in
  let exception Stuck in
  (* the list of ids represents a class of terms
   * whose root ends up being labelled with one
   * such id; the gen function generates a matcher
   * that will, given any such term, assign values
   * for the Var nodes of one pattern in pats *)
  let rec gen ids pats k =
    mk_switch ids (fun id ->
        let id_sym = symmetric id in
        let id_ops =
          let normalize (o, l) =
            (o, List.filter (fun (a, b) -> a <= b) l)
          in
          if id_sym then
            List.map normalize rmap.(id)
          else rmap.(id)
        in
        (* consider only the patterns that are
         * compatible with the current id *)
        let atm_pats, bin_pats =
          List.filter (function
            | (Bnr (o, _, _), _) ->
                List.exists (fun x -> fst x = o) id_ops
            | _ -> true) pats |>
          List.partition (fun (pat, _) -> is_atomic pat)
        in
        try
          if bin_pats = [] then raise Stuck else
          let lhs_pats =
            List.map (function
                | (Bnr (o, pl, pr), c) ->
                    (pl, Bnrl (o, c, pr))
                | _ -> assert false) bin_pats
          in
          let lhs_ids =
            List.concat_map snd id_ops |>
            List.map fst |> setify
          in
          Action.mk_push ~sym:id_sym
            (gen lhs_ids lhs_pats (fun lhs_id pats ->
              let rhs_ids =
                List.concat_map snd id_ops |>
                List.filter_map (fun (l, r) ->
                    if l = lhs_id then Some r else None) |>
                setify
              in
              let rhs_pats =
                List.map (function
                  | (pl, Bnrl (o, c, pr)) ->
                      (pr, Bnrr (o, pl, c))
                  | _ -> assert false) pats
              in
              Action.mk_pop
                (gen rhs_ids rhs_pats (fun _ pats ->
                  let id_pats =
                    List.map (function
                      | (pr, Bnrr (o, pl, c)) ->
                          (Bnr (o, pl, pr), c)
                      | _ -> assert false) pats
                  in
                  k id id_pats))))
        with Stuck ->
          let atm_pats =
            List.filter (fun (pat, _) ->
              pattern_match pat states.(id).seen) atm_pats
          in
          if atm_pats = [] then raise Stuck else
          let vars =
            List.filter_map (function
                | (Var (v, _), _) -> Some v
                | _ -> None) atm_pats |>
            setify
          in
          match vars with
          | [] -> k id atm_pats
          | [v] -> Action.mk_set v (k id atm_pats)
          | _ -> failwith "ambiguous var match")
  in
  (* generate a matcher for the rule *)
  let top_ids =
    Array.to_seq states |>
    Seq.filter_map (fun {id; point = p; _} ->
        if List.exists ((=) (Top name)) p then
          Some id
        else None) |>
    List.of_seq
  in
  let rec filter_dups pats =
    match pats with
    | p :: pats ->
        if List.exists (pattern_match p) pats
        then filter_dups pats
        else p :: filter_dups pats
    | [] -> []
  in
  let top_pats =
    List.filter_map (fun r ->
        if r.name = name then
          Some r.pattern
        else None) rules |>
    filter_dups |>
    List.map (fun p -> (p, Top ()))
  in
  gen top_ids top_pats (fun _ pats ->
      assert (pats <> []);
      let at_top (_, c) = c = Top () in
      assert (List.for_all at_top pats);
      Action.stop)
