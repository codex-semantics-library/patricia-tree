(** A naive model that we trust. Can be used both with QCheck (following Jan's
    paper) and Monolith *)

let uncurry f (a, b) = f a b
let second f (a, b) = (a, f b)
let second_opt f (a, b) = Option.map (fun x -> (a, x)) @@ f b
let secondi f (i, x) = (i, f i x)
let secondi_opt f (i, x) = Option.map (fun x -> (i, x)) @@ f i x
let with_uncurry comb = Fun.compose comb uncurry
let with_second comb = Fun.compose comb second
let with_second_opt comb = Fun.compose comb second_opt
let with_secondi comb = Fun.compose comb secondi
let with_secondi_opt comb = Fun.compose comb secondi_opt

(** Unsigned integer comparison. *)
let compare_keys k0 k1 = Int.compare (k0 - min_int) (k1 - min_int)

let cmp_keys a b = compare_keys (fst a) (fst b)
let keys m = List.(sort_uniq compare_keys @@ map fst m)

type 'a t = (int * 'a) list

let empty = []
let singleton i a = [ (i, a) ]

let compare cmp m0 m1 =
  let cmp' a b =
    let c = compare_keys (fst a) (fst b) in
    if c = 0 then cmp (snd a) (snd b) else c
  in
  let c = List.compare_lengths m0 m1 in
  if c = 0 then List.compare cmp' m0 m1 else c

let equal = List.equal
let is_empty = function [] -> true | _ -> false
let is_singleton = function [ x ] -> Some x | _ -> None
let size = List.length
let mem = List.mem_assoc
let find = List.assoc
let find_opt = List.assoc_opt

let add i a m =
  (* guarantee uniqueness of keys *)
  let m = List.remove_assoc i m in
  List.merge cmp_keys m [ (i, a) ]

let split k m =
  let l = List.filter (fun (k', _) -> compare_keys k' k < 0) m
  and o = List.assoc_opt k m
  and r = List.filter (fun (k', _) -> compare_keys k' k > 0) m in
  (l, o, r)

let remove = List.remove_assoc
let insert i f m = add i (f (List.assoc_opt i m)) m

let update i f m =
  match f (List.assoc_opt i m) with None -> remove i m | Some x -> add i x m

let fold f t acc = List.fold_left (fun acc (k, v) -> f k v acc) acc t
let iter f t = List.iter (fun (k, v) -> f k v) t
let map f = with_second List.map f
let mapi f = with_secondi List.map f
let filter f = with_uncurry List.filter f
let filter_map f = with_secondi_opt List.filter_map f
let for_all p = with_uncurry List.for_all p
let exists p = with_uncurry List.exists p

let union f m0 m1 =
  let keys = keys @@ List.append m0 m1 in
  let aux i =
    ( i,
      match (List.assoc_opt i m0, List.assoc_opt i m1) with
      | Some x, Some y -> f i x y
      | Some x, None -> x
      | None, Some y -> y
      | None, None -> assert false )
  in
  List.map aux keys

let interf f m0 m1 =
  let aux (i, x) =
    match List.assoc_opt i m1 with
    | Some y -> Option.map (fun r -> (i, r)) (f i x y)
    | None -> None
  in
  List.filter_map aux m0

let inter f m0 m1 = interf (fun i x y -> Some (f i x y)) m0 m1

let idempotent_inter_filter f m0 m1 =
  let aux (i, x) =
    match List.assoc_opt i m1 with
    | Some y when x == y -> Some (i, x)
    | Some y -> Option.map (fun r -> (i, r)) (f i x y)
    | None -> None
  in
  List.filter_map aux m0

let min_binding_inter m0 m1 =
  List.find_map
    (fun (i, v0) ->
      match List.assoc_opt i m1 with
      | Some v1 -> Some (i, v0, v1)
      | None -> None)
    m0

let max_binding_inter m0 m1 =
  List.find_map
    (fun (i, v0) ->
      match List.assoc_opt i m1 with
      | Some v1 -> Some (i, v0, v1)
      | None -> None)
    (List.rev m0)

let fold_on_nonequal_inter f m0 m1 acc =
  List.fold_left
    (fun acc (i, v0) ->
      match List.assoc_opt i m1 with
      | Some v1 when v0 != v1 -> f i v0 v1 acc
      | _ -> acc)
    acc m0

let fold_on_nonequal_union f m0 m1 acc =
  (* Compute the nonequal union *)
  let p x =
    match (List.assoc_opt x m0, List.assoc_opt x m1) with
    | Some v0, Some v1 -> v0 != v1
    | None, None -> false
    | _, _ -> true
  in
  let keys = List.filter p @@ keys @@ List.append m0 m1 in
  (* Run the fold *)
  let f acc k = f k (List.assoc_opt k m0) (List.assoc_opt k m1) acc in
  List.fold_left f acc keys

let nonidempotent_inter_no_share = inter

let diff f m0 m1 =
  let keys = keys @@ List.append m0 m1 in
  let aux i =
    match (List.assoc_opt i m0, List.assoc_opt i m1) with
    | Some x, Some y -> Option.map (fun a -> (i, a)) @@ f i x y
    | Some x, None -> Some (i, x)
    | _, _ -> None
  in
  List.filter_map aux keys

let rec subsetf phi s t =
  match (s, t) with
  | [], _ -> true
  | _, [] -> false
  | (x, a) :: xs, (y, b) :: ys ->
      let d = compare_keys x y in
      if d = 0 then phi x a b && subsetf phi xs ys
      else d > 0 && subsetf phi s ys

let subset = subsetf
let subsetk s t = subsetf (fun _i _x _y -> true) s t
let intersect m0 m1 = inter (fun _ _ _ -> ()) m0 m1 <> []

let intersectf f m0 m1 =
  let f i (a, b) = f i a b in
  exists f @@ inter (fun _ a b -> (a, b)) m0 m1

let merge f m0 m1 =
  let k0 = keys m0 and k1 = keys m1 in
  let keys = List.sort_uniq compare_keys @@ List.append k0 k1 in
  let aux i =
    let o0 = List.assoc_opt i m0 and o1 = List.assoc_opt i m1 in
    Option.map (fun x -> (i, x)) @@ f i o0 o1
  in
  List.filter_map aux keys

let of_list l = List.sort_uniq cmp_keys l
let of_seq s = List.sort_uniq cmp_keys (List.of_seq s)

(* Elements from [s] replace elements in [t] at the same key. *)
let add_seq s t = List.sort_uniq cmp_keys (List.of_seq s @ t)
let to_list t = t
let to_seq t = List.to_seq t
let to_rev_seq t = List.to_seq (List.rev t)
let unsigned_min_binding = function hd :: _ -> hd | [] -> raise Not_found

let unsigned_max_binding = function
  | hd :: tl -> List.fold_left (fun _ e -> e) hd tl
  | [] -> raise Not_found

let pop_unsigned_minimum = function
  | (i, v) :: tl -> Some (i, v, tl)
  | [] -> None

let pop_unsigned_maximum l =
  match List.rev l with (i, v) :: tl -> Some (i, v, List.rev tl) | [] -> None
