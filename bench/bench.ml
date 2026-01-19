open QCheck

module IntKey = struct
  type t = int

  let to_int = Fun.id
end

module Intmap = PatriciaTree.MakeMap (IntKey)
module IntSet = PatriciaTree.MakeSet(IntKey)

let intmap_add m (k, v) = Intmap.add k v m
let intset_add m k = IntSet.add k m

(** Pre-constructed test data. *)

let state = Random.get_state ()
let array_rand ar = ar.(Gen.int_bound (Array.length ar - 1) state)
let tree_size = 1000
let key_value_of_key k = (k, string_of_int k)

(* Number of trees in each dataset. *)
let trees_count = 20
let mk_tree = Array.fold_left intmap_add Intmap.empty
let mk_set x = Array.fold_left (fun m (k, _) -> IntSet.add k m) x
let mk_trees = Array.map mk_tree

let mk_key_values gen =
  Array.init trees_count (fun _ -> Array.init tree_size gen)

let random_key_values =
  mk_key_values (fun _ -> key_value_of_key (Gen.int state))

let similar_trees_key_values =
  let bound = tree_size * 2 in
  mk_key_values (fun _ -> key_value_of_key (Gen.int_bound bound state))

let ordered_low_key_values = mk_key_values key_value_of_key

let ordered_high_key_values =
  mk_key_values (fun i -> key_value_of_key (Int.max_int - i))

(* A set of trees with arbitrary keys. *)
let random_trees = mk_trees random_key_values

(* A set of trees with arbitrary keys and approx 50% of common bindings between
   them. Trees might be smaller than [tree_size]. *)
let similar_trees = mk_trees similar_trees_key_values

(* Random subset of trees in [similar_trees] with 50 elements or less. *)
let small_similar_trees =
  mk_trees
    (Array.map
       (fun kvs -> Array.init 50 (fun _ -> array_rand kvs))
       similar_trees_key_values)

(* A tree with continuous keys from 0 to [tree_size-1]. *)
let ordered_low_trees = mk_trees ordered_low_key_values
let ordered_high_trees = mk_trees ordered_high_key_values

let set_input_of_map_input x = Array.map fst x
(** Test definitions. *)

open Bechamel

let make_test name call = [ Test.make ~name (Staged.stage @@ call) ]

let make_indexed name ~fmt args call =
  let f arg = Staged.stage (call arg) in
  let mk_test (variation_name, dataset) =
    let name = Format.asprintf fmt name variation_name in
    Test.make ~name (f dataset)
  in
  List.map mk_test args

(** Construction from small positive ordered values. *)
let t_construct_pos_low_ordered =
  make_test "Map: constr: pos, ord, small" @@ fun () ->
  Array.fold_left intmap_add Intmap.empty (array_rand ordered_low_key_values)

let set_construct_pos_low_ordered =
  let array = array_rand ordered_low_key_values |> set_input_of_map_input in
  make_test "Set: constr: pos, ord, small" @@ fun () ->
  Array.fold_left intset_add IntSet.empty array

(** Construction from high positive ordered values. *)
let t_construct_pos_high_ordered =
  make_test "Map: constr: pos, ord, large" @@ fun () ->
  Array.fold_left intmap_add Intmap.empty (array_rand ordered_high_key_values)

let set_construct_pos_high_ordered =
  let array = array_rand ordered_high_key_values |> set_input_of_map_input in
  make_test "Set: constr: pos, ord, large" @@ fun () ->
  Array.fold_left intset_add IntSet.empty array

let mk_mixed ratio =
  mk_key_values (fun i ->
      let i = Option.value ~default:i Gen.(option ~ratio int state) in
      key_value_of_key i)

let data =
  [
    (0, ordered_low_key_values);
    (1, mk_mixed 0.01);
    (5, mk_mixed 0.05);
    (25, mk_mixed 0.25);
    (100, random_key_values);
  ]
let set_data = List.map (fun (i,x) -> (i,Array.map set_input_of_map_input x)) data

(** Construction from ordered keys with a part of random keys. *)
let t_construct_mixed =
  make_indexed "Map: constr" ~fmt:"%s: %d%% random" data @@ fun kvs () ->
  Array.fold_left intmap_add Intmap.empty (array_rand kvs)

let set_construct_mixed =
  make_indexed "Set: constr" ~fmt:"%s: %d%% random" set_data @@ fun kvs () ->
  Array.fold_left intset_add IntSet.empty (array_rand kvs)

(* Two equal trees except for one element *)
let equal_except_one_trees =
  Array.split
    (Array.map
        (fun kvs ->
          (mk_tree kvs, mk_tree (Array.sub kvs 0 (Array.length kvs - 1))))
        random_key_values)

let data =
  [
    ("random disjoint", (random_trees, random_trees));
    ("random 50% inter", (similar_trees, similar_trees));
    ("ordered disjoint", (ordered_low_trees, ordered_high_trees));
    ("large and small disjoint", (random_trees, small_similar_trees));
    ("equal except one element", equal_except_one_trees);
  ]


(** Test each map operation in several scenarios. *)
let make_map_op name f =
  make_indexed ("Map: " ^ name) ~fmt:"%s (%s)" data
  @@ fun (trees_l, trees_r) () ->
  ignore (f (array_rand trees_l) (array_rand trees_r))

let set_of_map m = Intmap.to_list m |> List.map fst |> IntSet.of_list

let set_data = List.map (fun (i,(l,r)) -> (i,(Array.map set_of_map l, Array.map set_of_map r))) data


(** Test each set operation in several scenarios. *)
let make_set_op name f =
  make_indexed ("Set: " ^ name) ~fmt:"%s (%s)" set_data
  @@ fun (trees_l, trees_r) () ->
  ignore (f (array_rand trees_l) (array_rand trees_r))

(* Left-biased *)
let t_idempotent_union =
  make_map_op "idempotent_union" (Intmap.idempotent_union (fun _ a _ -> a))

(* Left-biased *)
let t_slow_merge =
  make_map_op "slow_merge"
    (Intmap.slow_merge (fun _ a b -> if Option.is_none a then b else a))

(* Left-biased *)
let t_idempotent_inter =
  make_map_op "idempotent_inter" (Intmap.idempotent_inter (fun _ a _ -> a))

let t_nonidempotent_inter_no_share =
  make_map_op "nonidempotent_inter_no_share"
    (Intmap.nonidempotent_inter_no_share (fun _ a _ -> a))

let t_symmetric_difference =
  make_map_op "symmetric_difference"
    (Intmap.symmetric_difference (fun _ _ _ -> None))

let t_difference =
  make_map_op "difference" (Intmap.difference (fun _ _ _ -> None))

let t_reflexive_same_domain_for_all2 =
  make_map_op "reflexive_same_domain_for_all2"
    (Intmap.reflexive_same_domain_for_all2 (fun _ a b -> a = b))

let t_nonreflexive_same_domain_for_all2 =
  make_map_op "nonreflexive_same_domain_for_all2"
    (Intmap.nonreflexive_same_domain_for_all2 (fun _ a b -> a = b))

let t_reflexive_subset_domain_for_all2 =
  make_map_op "reflexive_subset_domain_for_all2"
    (Intmap.reflexive_subset_domain_for_all2 (fun _ a b -> a = b))

let set_union = make_set_op "union" IntSet.union
let set_inter = make_set_op "inter" IntSet.inter
let set_diff = make_set_op "diff" IntSet.diff

let tests =
  List.concat
    [
      (* Map tests *)
      t_construct_pos_low_ordered;
      t_construct_pos_high_ordered;
      t_construct_mixed;
      t_idempotent_union;
      t_slow_merge;
      t_idempotent_inter;
      t_nonidempotent_inter_no_share;
      t_symmetric_difference;
      t_difference;
      t_reflexive_same_domain_for_all2;
      t_nonreflexive_same_domain_for_all2;
      t_reflexive_subset_domain_for_all2;
      (* Set tests *)
      set_construct_pos_low_ordered;
      set_construct_pos_high_ordered;
      set_construct_mixed;
      set_union;
      set_inter;
      set_diff;
    ]
