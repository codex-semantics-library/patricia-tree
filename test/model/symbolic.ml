type 'a t =
  | Empty
  | Singleton of (int * 'a)
  | Add of (int * 'a * 'a t)
  | Remove of (int * 'a t)
  | Union of ((int -> 'a -> 'a -> 'a) * 'a t * 'a t)
  | Inter of ((int -> 'a -> 'a -> 'a) * 'a t * 'a t)
  | Merge of ((int -> 'a option -> 'a option -> 'a option) * 'a t * 'a t)

let rec print = function
  | Empty -> "Empty"
  | Singleton (i, c) ->
      "Singleton (" ^ Int.to_string i ^ ", " ^ Char.escaped c ^ ")"
  | Add (i, c, m) ->
      "Add (" ^ Int.to_string i ^ ", " ^ Char.escaped c ^ ", " ^ print m ^ ")"
  | Remove (i, m) -> "Remove (" ^ Int.to_string i ^ ", " ^ print m ^ ")"
  | Union (_, m0, m1) -> "Union (f, " ^ print m0 ^ ", " ^ print m1 ^ ")"
  | Inter (_, m0, m1) -> "Inter (f, " ^ print m0 ^ ", " ^ print m1 ^ ")"
  | Merge (_, m0, m1) -> "Merge (f, " ^ print m0 ^ ", " ^ print m1 ^ ")"

let singleton i a = Singleton (i, a)
let add i a m = Add (i, a, m)
let remove i m = Remove (i, m)
let union f m0 m1 = Union (f, m0, m1)
let inter f m0 m1 = Inter (f, m0, m1)
let merge f m0 m1 = Merge (f, m0, m1)

open QCheck.Gen

let key = small_signed_int
let elt = char_range 'a' 'z'

let gen_f =
  oneofl
    [
      (fun _ x _ -> x);
      (fun _ _ x -> x);
      (fun i x y -> if i mod 2 = 0 then x else y);
    ]

let gen_f_opt =
  oneofl
    [
      (fun _ _ _ -> None);
      (fun _ x _ -> x);
      (fun _ _ x -> x);
      (fun _ x y -> match x with None -> y | _ -> x);
      (fun _ x y -> match y with None -> x | _ -> y);
      (fun i x y -> if i mod 2 = 0 then x else y);
    ]

let gen g =
  sized @@ fix
  @@ fun self size ->
  match size with
  | 0 -> oneof [ return Empty; singleton <$> key <*> g ]
  | n ->
      frequency
        [
          (1, return Empty);
          (1, singleton <$> key <*> g);
          (2, add <$> key <*> g <*> self (n - 1));
          (2, remove <$> key <*> self (n - 1));
          (2, union <$> gen_f <*> self (n / 2) <*> self (n / 2));
          (2, inter <$> gen_f <*> self (n / 2) <*> self (n / 2));
          (2, merge <$> gen_f_opt <*> self (n / 2) <*> self (n / 2));
        ]

let shrink shrk =
  let open QCheck in
  let ( <+> ) = Iter.( <+> ) in
  let rec aux = function
    | Empty -> Iter.empty
    | Singleton (k, x) ->
        Iter.return Empty
        <+> Iter.map (fun k' -> Singleton (k', x)) (Shrink.int k)
        <+> Iter.map (fun x' -> Singleton (k, x')) (shrk x)
    | Add (k, x, t) ->
        Iter.of_list [ Empty; t; Singleton (k, x) ]
        <+> Iter.map (fun t' -> Add (k, x, t')) (aux t)
        <+> Iter.map (fun k' -> Add (k', x, t)) (Shrink.int k)
        <+> Iter.map (fun x' -> Add (k, x', t)) (shrk x)
    | Remove (i, t) ->
        Iter.of_list [ Empty; t ]
        <+> Iter.map (fun t' -> Remove (i, t')) (aux t)
        <+> Iter.map (fun i' -> Remove (i', t)) (Shrink.int i)
    | Union (f, t0, t1) ->
        Iter.of_list [ Empty; t0; t1 ]
        <+> Iter.map (fun t0' -> Union (f, t0', t1)) (aux t0)
        <+> Iter.map (fun t1' -> Union (f, t0, t1')) (aux t1)
    | Inter (f, t0, t1) ->
        Iter.of_list [ Empty; t0; t1 ]
        <+> Iter.map (fun t0' -> Inter (f, t0', t1)) (aux t0)
        <+> Iter.map (fun t1' -> Inter (f, t0, t1')) (aux t1)
    | Merge (f, t0, t1) ->
        Iter.of_list [ Empty; t0; t1 ]
        <+> Iter.map (fun t0' -> Merge (f, t0', t1)) (aux t0)
        <+> Iter.map (fun t1' -> Merge (f, t0, t1')) (aux t1)
  in
  aux

let tree = QCheck.make ~print ~shrink:(shrink QCheck.Shrink.char) (gen elt)

let two =
  let gen =
    frequency
      [
        (* Physically distinct trees. *)
        (4, pair (gen elt) (gen elt));
        (* Trees are identical. *)
        ( 1,
          let* t = gen elt in
          return (t, t) );
        (* Trees physically share an intersection. *)
        ( 5,
          let* a = gen elt and* b = gen elt and* c = gen elt in
          let union_left = union (fun _ l _ -> l) in
          return (union_left a b, union_left a c) );
      ]
  in
  let print (a, b) = print a ^ "\n" ^ print b in
  QCheck.make ~print gen
