(** A naive model that we trust. Can be used both with QCheck (following Jan's
    paper) and Monolith *)

let uncurry f (a, b) = f a b
let second f (a, b) = (a, f b)
let second_opt f (a, b) = Option.map (fun x -> (a, x)) @@ f b
let secondi f (i, x) = (i, f i x)
let secondi_opt f (i, x) = Option.map (fun x -> (i, x)) @@ f i x

(** Unsigned integer comparison. *)
let compare_keys k0 k1 = Int.compare (k0 - min_int) (k1 - min_int)

let cmp_keys a b = compare_keys (fst a) (fst b)
let keys m = List.(sort_uniq compare_keys @@ map fst m)

type 'a t = (int * 'a) list

let empty = []
let singleton i a = [ (i, a) ]

(* This function doesn't model [reflexive_compare]. The output value is
   different and the total order as well. *)
let compare cmp m0 m1 =
  let cmp' a b =
    let c = compare_keys (fst a) (fst b) in
    if c = 0 then cmp (snd a) (snd b) else c
  in
  List.compare cmp' m0 m1

let disjoint m0 m1 =
  let keys0 = keys m0 and keys1 = keys m1 and p k m = not @@ List.mem m k in
  List.for_all (p keys1) keys0 && List.for_all (p keys0) keys1

let equal = List.equal
let is_empty = function [] -> true | _ -> false
let is_singleton = function [ x ] -> Some x | _ -> None
let size = List.length
let mem = List.mem_assoc
let find = List.assoc
let find_opt = List.assoc_opt

let add i a m =
  (* guarantee uniqueness of keys *)
  if List.mem_assoc i m then
    List.map (fun ((i', _) as old) -> if i' = i then (i, a) else old) m
  else List.merge cmp_keys m [ (i, a) ]

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
let map f = List.map (second f)
let mapi f = List.map (secondi f)
let filter f = List.filter (uncurry f)
let filter_map f = List.filter_map (secondi_opt f)
let for_all p = List.for_all (uncurry p)
let exists p = List.exists (uncurry p)

let idempotent_union f m0 m1 =
  let k0 = keys m0 and k1 = keys m1 in
  let keys = List.sort_uniq compare_keys @@ List.append k0 k1 in
  let aux i =
    ( i,
      match (List.assoc_opt i m0, List.assoc_opt i m1) with
      | Some x, Some y -> f i x y
      | Some x, None -> x
      | None, Some y -> y
      | None, None -> assert false )
  in
  List.map aux keys

let idempotent_inter_filter f m0 m1 =
  let aux (i, x) =
    match List.assoc_opt i m1 with
    | Some y when x == y -> Some (i, x)
    | Some y -> Option.map (fun r -> (i, r)) (f i x y)
    | None -> None
  in
  List.filter_map aux m0

let idempotent_inter f m0 m1 =
  idempotent_inter_filter (fun i x y -> Some (f i x y)) m0 m1

let nonidempotent_inter_no_share = idempotent_inter

let symmetric_difference f m0 m1 =
  let keys = List.sort_uniq compare_keys @@ List.append (keys m0) (keys m1)
  and aux k =
    match (List.assoc_opt k m0, List.assoc_opt k m1) with
    | Some v0, Some v1 -> Option.map (fun v -> (k, v)) @@ f k v0 v1
    | Some v, None | None, Some v -> Some (k, v)
    | None, None -> None
  in
  List.filter_map aux keys

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

let reflexive_same_domain_for_all2 p m0 m1 =
  let keys0 = keys m0
  and keys1 = keys m1
  and p k = p k (List.assoc k m0) (List.assoc k m1) in
  List.equal Int.equal keys0 keys1 && List.for_all p keys0

let nonreflexive_same_domain_for_all2 p m0 m1 =
  m0 <> [] && reflexive_same_domain_for_all2 p m0 m1

let difference f m0 m1 =
  let keys = keys @@ List.append m0 m1 in
  let aux i =
    match (List.assoc_opt i m0, List.assoc_opt i m1) with
    | Some x, Some y -> Option.map (fun a -> (i, a)) @@ f i x y
    | Some x, None -> Some (i, x)
    | _, _ -> None
  in
  List.filter_map aux keys

let rec reflexive_subset_domain_for_all2 phi s t =
  match (s, t) with
  | [], _ -> true
  | _, [] -> false
  | (x, a) :: xs, (y, b) :: ys ->
      let d = compare_keys x y in
      if d = 0 then phi x a b && reflexive_subset_domain_for_all2 phi xs ys
      else d > 0 && reflexive_subset_domain_for_all2 phi s ys

let intersect m0 m1 = idempotent_inter (fun _ l _ -> l) m0 m1 <> []

let slow_merge f m0 m1 =
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
