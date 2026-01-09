open Signatures



module MutexProtectHeterogeneousMap
  (Map: HETEROGENEOUS_MAP)
  (Mutex: MUTEX)
= struct
  (* cannot inline, otherwise flambda might move code around. *)
  let[@inline never] protect f arg =
    Mutex.lock ();
    match f arg with
    | x -> Mutex.unlock (); x
    | exception e -> Mutex.unlock (); raise e

  (* We could include Map to get all types here, but this forces us to redefine,
     and thus protect, all functions. *)
  type 'k key = 'k Map.key
  type ('k, 'm) value = ('k, 'm) Map.value
  type 'm t = 'm Map.t
  type 'm view = 'm Map.view = private
    | Empty : 'map view
    | Branch : { prefix : Ints.intkey; branching_bit : Ints.mask; tree0 : 'map t; tree1 : 'map t; } -> 'map view
    | Leaf : { key : 'key key; value : ('key, 'map) value; } -> 'map view
  type 'm key_value_pair = 'm Map.key_value_pair = KeyValue : 'a key * ('a, 'map) value -> 'map key_value_pair
  type 'm polyiter = 'm Map.polyiter = { f : 'a. 'a key -> ('a, 'm) value -> unit; } [@@unboxed]
  type ('acc, 'map) polyfold = ('acc, 'map) Map.polyfold = { f : 'a. 'a key -> ('a, 'map) value -> 'acc -> 'acc; } [@@unboxed]
  type ('acc, 'map) polyfold2 = ('acc, 'map) Map.polyfold2 = { f : 'a. 'a key -> ('a, 'map) value -> ('a, 'map) value -> 'acc -> 'acc; } [@@unboxed]
  type ('acc, 'map) polyfold2_union = ('acc, 'map) Map.polyfold2_union = { f : 'a. 'a key -> ('a, 'map) value option -> ('a, 'map) value option -> 'acc -> 'acc; } [@@unboxed]
  type 'map polypredicate = 'map Map.polypredicate = { f : 'a. 'a key -> ('a, 'map) value -> bool; } [@@unboxed]
  type ('map1, 'map2) polymap = ('map1, 'map2) Map.polymap = { f : 'a. ('a, 'map1) value -> ('a, 'map2) value; } [@@unboxed]
  type ('map1, 'map2) polymapi = ('map1, 'map2) Map.polymapi = { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value; } [@@unboxed]
  type ('map1, 'map2) polyfilter_map = ('map1, 'map2) Map.polyfilter_map = { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value option; } [@@unboxed]
  type 'map polypretty = 'map Map.polypretty = { f : 'a. Format.formatter -> 'a key -> ('a, 'map) value -> unit; } [@@unboxed]
  type ('map1, 'map2) polysame_domain_for_all2 = ('map1, 'map2) Map.polysame_domain_for_all2 = { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value -> bool; } [@@unboxed]
  type 'map polycompare = 'map Map.polycompare = { f : 'a. 'a key -> ('a, 'map) value -> ('a, 'map) value -> int; } [@@unboxed]
  type ('map1, 'map2, 'map3) polyunion = ('map1, 'map2, 'map3) Map.polyunion = { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value -> ('a, 'map3) value; } [@@unboxed]
  type ('map1, 'map2, 'map3) polyinter = ('map1, 'map2, 'map3) Map.polyinter = { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value -> ('a, 'map3) value; } [@@unboxed]
  type ('map1, 'map2, 'map3) polyinterfilter = ('map1, 'map2, 'map3) Map.polyinterfilter = { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value -> ('a, 'map3) value option; } [@@unboxed]
  type ('map1, 'map2, 'map3) polymerge = ('map1, 'map2, 'map3) Map.polymerge = { f : 'a. 'a key -> ('a, 'map1) value option -> ('a, 'map2) value option -> ('a, 'map3) value option; } [@@unboxed]
  type ('a, 'b) polydifference = ('a, 'b, 'a) polyinterfilter
  type ('a, 'b) key_value_value = ('a, 'b) Map.key_value_value =
      KeyValueValue : 'k key * ('k, 'a) value *
        ('k, 'b) value -> ('a, 'b) key_value_value
  let empty = Map.empty
  let leaf k = protect (Map.leaf k)
  let branch ~prefix ~branching_bit ~tree0 ~tree1 = protect (fun () -> Map.branch ~prefix ~branching_bit ~tree0 ~tree1) ()
  let is_empty t = protect Map.is_empty t
  let view t = protect Map.view t
  let find k = protect (Map.find k)
  let find_opt k = protect (Map.find_opt k)
  let unsigned_min_binding t = protect Map.unsigned_min_binding t
  let unsigned_max_binding t = protect Map.unsigned_max_binding t
  let singleton k = protect (Map.singleton k)
  let cardinal t = protect Map.cardinal t
  let is_singleton t = protect Map.is_singleton t
  let mem k = protect (Map.mem k)
  let remove k = protect (Map.remove k)
  let pop_unsigned_maximum t = protect Map.pop_unsigned_maximum t
  let pop_unsigned_minimum t = protect Map.pop_unsigned_minimum t
  let insert k f = protect (Map.insert k f)
  let update k f = protect (Map.update k f)
  let add k v = protect (Map.add k v)
  let split k = protect (Map.split k)
  let iter f = protect (Map.iter f)
  let fold f t = protect (Map.fold f t)
  let fold_on_nonequal_inter f t1 t2 = protect (Map.fold_on_nonequal_inter f t1 t2)
  let fold_on_nonequal_union f t1 t2 = protect (Map.fold_on_nonequal_union f t1 t2)
  let filter f = protect (Map.filter f)
  let for_all f = protect (Map.for_all f)
  let map f = protect (Map.map f)
  let map_no_share f = protect (Map.map_no_share f)
  let mapi f = protect (Map.mapi f)
  let mapi_no_share f = protect (Map.mapi_no_share f)
  let filter_map f = protect (Map.filter_map f)
  let filter_map_no_share f = protect (Map.filter_map_no_share f)
  let pretty ?pp_sep f fmt = protect (Map.pretty ?pp_sep f fmt)
  let reflexive_same_domain_for_all2 f t1 = protect (Map.reflexive_same_domain_for_all2 f t1)
  let nonreflexive_same_domain_for_all2 f t1 = protect (Map.nonreflexive_same_domain_for_all2 f t1)
  let reflexive_subset_domain_for_all2 f t1 = protect (Map.reflexive_subset_domain_for_all2 f t1)
  let reflexive_compare f t1 = protect (Map.reflexive_compare f t1)
  let disjoint t1 = protect (Map.disjoint t1)
  let idempotent_union f t1 = protect (Map.idempotent_union f t1)
  let idempotent_inter f t1 = protect (Map.idempotent_inter f t1)
  let nonidempotent_inter_no_share f t1 = protect (Map.nonidempotent_inter_no_share f t1)
  let idempotent_inter_filter f t1 = protect (Map.idempotent_inter_filter f t1)
  let slow_merge f t1 = protect (Map.slow_merge f t1)
  let difference f t1 = protect (Map.difference f t1)
  let symmetric_difference f t1 = protect (Map.symmetric_difference f t1)
  let min_binding_inter t = protect (Map.min_binding_inter t)
  let max_binding_inter t = protect (Map.max_binding_inter t)
  let to_seq t = protect Map.to_seq t
  let to_rev_seq t = protect Map.to_rev_seq t
  let add_seq s = protect (Map.add_seq s)
  let of_seq s = protect Map.of_seq s
  let of_list l = protect Map.of_list l
  let to_list t = protect Map.to_list t

  module WithForeign(Map2:NODE_WITH_FIND with type 'a key = 'a key) = struct
    module WF = Map.WithForeign(Map2)

    type ('map1, 'map2) polyinter_foreign = ('map1, 'map2) WF.polyinter_foreign = { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) Map2.value -> ('a, 'map1) value; } [@@unboxed]
    type ('map2, 'map1) polyfilter_map = ('map2, 'map1) WF.polyfilter_map = { f : 'a. 'a key -> ('a, 'map2) Map2.value -> ('a, 'map1) value option; } [@@unboxed]
    type ('map1, 'map2) polyupdate_multiple = ('map1, 'map2) WF.polyupdate_multiple = { f : 'a. 'a key -> ('a, 'map1) value option -> ('a, 'map2) Map2.value -> ('a, 'map1) value option; } [@@unboxed]
    type ('map1, 'map2, 'map3) polyupdate_multiple_inter = ('map1, 'map2, 'map3) WF.polyupdate_multiple_inter = { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) Map2.value -> ('a, 'map3) value option; } [@@unboxed]
    type ('map1, 'map2) polydifference = ('map1, 'map2, 'map1) polyupdate_multiple_inter

    type ('a, 'b) key_value_value = ('a, 'b) WF.key_value_value =
      | KeyValueValue : 'k key * ('k, 'a) value * ('k, 'b) Map2.value -> ('a, 'b) key_value_value

    let nonidempotent_inter f t = protect (WF.nonidempotent_inter f t)
    let filter_map_no_share f = protect (WF.filter_map_no_share f)
    let update_multiple_from_foreign a f = protect (WF.update_multiple_from_foreign a f)
    let update_multiple_from_inter_with_foreign a f = protect (WF.update_multiple_from_inter_with_foreign a f)
    let min_binding_inter t = protect (WF.min_binding_inter t)
    let max_binding_inter t = protect (WF.max_binding_inter t)
    let difference f t1 = protect (WF.difference f t1)
  end
end
