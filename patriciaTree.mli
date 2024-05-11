(**************************************************************************)
(*  This file is part of the Codex semantics library                      *)
(*    (patricia-tree sub-component).                                      *)
(*                                                                        *)
(*  Copyright (C) 2024                                                    *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  You can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file LICENSE).                      *)
(**************************************************************************)

(** Association maps from key to values, and sets, implemented with
    Patricia Trees, allowing fast merge operations by making use of
    physical equality between subtrees; and custom implementation of
    tree nodes (allowing normal maps, hash-consed maps, weak key or
    value maps, sets, custom maps, etc.)

    This is similar to OCaml's Map, except that:

    {ul
    {- The required signature for keys is different, in that we require
      each key to be mapped to a unique integer identifier.}

    {- The implementation uses Patricia Tree, as described in Oksasaki
      and Gill's 1998 paper
      {{: https://www.semanticscholar.org/paper/Fast-Mergeable-Integer-Maps-Okasaki-Gill/23003be706e5f586f23dd7fa5b2a410cc91b659d}{i Fast mergeable integer maps}},
      i.e. it is a space-efficient prefix trie over the big-endian representation of
      the key's integer identifier.

      Example 5-bit patricia tree containing five numbers: 0 [0b0000], 1 [0b0001],
      5 [0b0101] and 7 [0b0111] and -8 [0b1111]:
      {v
                              Branch
                          (prefix=0b?___)
                          /             \
                    Branch               Leaf(-8)
                (prefix=0b0?__)          0b1111
                /             \
           Branch             Branch
       (prefix=0b000?)     (prefix=0b01?_)
         |        |          |       |
      Leaf(0)  Leaf(1)    Leaf(5)  Leaf(7)
      0b0000   0b0001     0b0101   0b0111
      v}


      The main benefit of Patricia Tree is that their representation
      is stable (contrary to maps, inserting nodes in any order will
      return the same shape), which allows different versions of a map
      to share more subtrees in memory, and the operations over two
      maps to benefit from this sharing. The functions in this library
      attempt to maximally preserve sharing and benefit from sharing,
      allowing very important improvements in complexity and running
      time when combining maps or sets is a frequent operation.}

    {- Finally, the implementation is more customizable, allowing
      notably (key,value) pairs or different types to be in the same map,
      or to choose the memory representation of the nodes of the tree.}

    {- Some operations like {{!BASE_MAP.pop_unsigned_minimum}[pop_unsigned_minimum]} and
     {{!BASE_MAP.pop_unsigned_maximum}[pop_unsigned_maximum]} make our Set
     suitable as priority queue (but remember that each element in the
     queue must map to a distinct integer, and that using the {{!unsigned_lt}unsigned order}
     means elements with negative priority are seen as greater than elements with
     positive ones).}
    } *)

(** Note on complexity: in the following, n represents the size of the
    map when there is one (and [|map1|] is the number of elements in
    [map1]).  The term log(n) correspond to the maximum height of the
    tree, which is log(n) if we assume an even distribution of numbers
    in the map (e.g. random distribution, or integers chosen
    contiguously using a counter). The worst-case height is
    O(min(n,64)) which is actually constant, but not really
    informative; log(n) corresponds to the real complexity in usual
    distributions. *)

val unsigned_lt : int -> int -> bool
(** All integers comparisons in this library are done according to their
    {b unsigned representation}. This is the same as signed comparison for same
    sign integers, but all negative integers are greater than the positives.
    This means [-1] is the greatest possible number, and [0] is the smallest.
    {[
    # unsigned_lt 2 (-1);;
    - bool : true
    # unsigned_lt max_int min_int;;
    - bool : true
    # unsigned_lt 3 2;;
    - bool : false
    # unsigned_lt 2 3;;
    - bool : true
    # unsigned_lt (-2) (-3);;
    - bool : false
    # unsigned_lt (-4) (-3);;
    - bool : true
    # unsigned_lt 0 0;;
    - bool : false
    ]}

    Using this unsigned order helps avoid a bug described in
    {{: https://www.cs.tufts.edu/comp/150FP/archive/jan-midtgaard/qc-patricia.pdf}{i QuickChecking Patricia Trees}}
    by Jan Mitgaard.

    @since 0.10.0 *)


type intkey = private int
(** Private type used to represent prefix stored in nodes.
    These are integers with all bits after branching bit (included) set to zero *)

type mask = private int
(** Private type: integers with a single bit set. *)

(**/**)

val highest_bit : int -> (int[@untagged])
(** [highest_bit x] is an integer with a single bit set: the highest set bit of [x].
    exported for test purposes only.

    @since 0.10.0 *)

(**/**)

(** {1 Nodes} *)

(** This module explains how a node is stored in memory, with
    functions to create and view nodes. *)
module type NODE = sig
  (** We use a uniform type ['map view] to pattern match on maps and sets
      The actual types ['map t] can be a bit different from ['map view]
      to allow for more efficient representations, but {!val:view} should be a
      constant time operation for quick conversions. *)

  (** {2 Types} *)

  type 'key key
  (** The type of keys. *)

  type ('key, 'map) value
  (** The type of value, which depends on the type of the key and the type of the map. *)

  type 'map t
  (** The type of the map, which is parameterized by a type. *)

  (** {2 Constructors: build values} *)

  val empty : 'map t
  (** The empty map *)

  val leaf : 'key key -> ('key, 'map) value -> 'map t
  (** A singleton leaf, similar to {!BASE_MAP.singleton} *)

  val branch :
    prefix:intkey ->
    branching_bit:mask -> tree0:'map t -> tree1:'map t -> 'map t
  (** A branch node.
      {b This shouldn't be called externally unless you know what you're doing!}
      Doing so could easily break the data structure's invariants.

      When called, it assumes that:
      - Neither [tree0] nor [tree1] should be empty.
      - [branching_bit] should have a single bit set
      - [prefix] should be normalized (bits below [branching_bit] set to zero)
      - All elements of [tree0] should have their [to_int] start by
        [prefix] followed by 0 at position [branching_bit]).
      - All elements of [tree1] should have their [to_int] start by
        [prefix] followed by 0 at position [branching_bit]). *)

  (** {2 Destructors: access the value} *)

  (** This makes the map nodes accessible to the pattern matching
      algorithm; this corresponds 1:1 to the {!SimpleNode}
      implementation. This just needs to be copy-and-pasted for every
      node type. *)
  type 'map view = private
    | Empty : 'map view
    (** Can happen only at the toplevel: there is no empty interior node. *)
    | Branch : { prefix : intkey; branching_bit : mask;
                 tree0 : 'map t; tree1 : 'map t; } -> 'map view
    (** Same constraints as {!branch}:
        - [branching_bit] contains only one bit set; the corresponding mask is (branching_bit - 1).
        - [prefix] is normalized: the bits below the [branching_bit] are set to zero
          (i.e. [prefix & (branching_bit - 1) = 0]).
        - All elements of [tree0] should have their [to_int] start by
          [prefix] followed by 0 at position [branching_bit]).
        - All elements of [tree1] should have their [to_int] start by
          [prefix] followed by 0 at position [branching_bit]). *)
    | Leaf : { key : 'key key; value : ('key, 'map) value; } -> 'map view
    (** A key -> value mapping. *)

  val is_empty: 'map t -> bool
  (** Check if the map is empty. Should be constant time. *)

  val view: 'a t -> 'a view
  (** Convert the map to a view. Should be constant time. *)
end

(** Associate a unique number to each node, so they can be used as keys in sets or maps. *)
module type NODE_WITH_ID = sig
  include NODE (** @closed *)

  val get_id: 'a t -> int
  (** Unique number for each node.

      This is not {{!hash_consed}hash-consing}.
      Equal nodes created separately will have different
      identifiers. On the flip side, nodes with equal identifiers will always be
      physically equal. *)
end

(** Hash-consed nodes also associate a unique number to each node,
    Unlike {!NODE_WITH_ID}, they also check before instanciating the node whether
    a similar node already exists. This results in slightly slower constructors
    (they perform an extra hash-table lookup), but allows for constant time
    equality and comparison.

    See {!hash_consed} for a details on strengths and limits of hash-consing.

    @since v0.10.0 *)
module type HASH_CONSED_NODE = sig
  include NODE (** @closed *)

  val get_id : 'a t -> int
  (** Returns the {{!hash_consed}hash-consed} id of the map.
      Unlike {!NODE_WITH_ID.get_id}, hash-consing ensures that maps
      which contain the same keys (compared by {!KEY.to_int}) and values (compared
      by {!HASHED_VALUE.polyeq}) will always be physically equal
      and have the same identifier.

      Note that when using physical equality as {!HASHED_VALUE.polyeq}, some
      maps of different types [a t] and [b t] may be given the same identifier.
      See the end of the documentation of {!HASHED_VALUE.polyeq} for details. *)

  val equal : 'a t -> 'a t -> bool
  (** Constant time equality using the {{!hash_consed}hash-consed} nodes identifiers.
      This is equivalent to physical equality.
      Two nodes are equal if their trees contain the same bindings,
      where keys are compare by {!KEY.to_int} and values are compared by
      {!HASHED_VALUE.polyeq}. *)

  val compare : 'a t -> 'a t -> int
  (** Constant time comparison using the {{!hash_consed}hash-consed} node identifiers.
      This order is fully arbitrary, but it is total and can be used to sort nodes.
      It is based on node ids which depend on the order in which the nodes where created
      (older nodes having smaller ids).

      One useful property of this order is that
      child nodes will always have a smaller identifier than their parents. *)
end

(** {1 Map signatures} *)

(** {2 Base map} *)

(** Base map signature: a generic ['b map] storing bindings
    of ['a key] to [('a,'b) values].
    All maps and set are a variation of this type,
    sometimes with a simplified interface.
    - {!HETEROGENEOUS_MAP} is just a {!BASE_MAP} with a functor {!HETEROGENEOUS_MAP.WithForeign}
      for building operations that operate on two maps of different base types;
    - {!MAP} specializes the interface for non-generic keys ([key] instead of ['a key]);
    - {!HETEROGENEOUS_SET} specializes {!BASE_MAP} for sets ([('a,'b) value = unit]) and
      removes the value argument from most operations;
    - {!SET} specializes {!HETEROGENEOUS_SET} further by making elements (keys)
      non-generic ([elt] instead of ['a elt]).  *)
module type BASE_MAP = sig
  include NODE

  (** Existential wrapper for the ['a] parameter in a ['a key], [('a,'map) value] pair *)
  type 'map key_value_pair =
      KeyValue : 'a key * ('a, 'map) value -> 'map key_value_pair

  (** {3 Basic functions} *)

  val unsigned_min_binding : 'a t -> 'a key_value_pair
  (** [unsigned_min_binding m] is minimal binding [KeyValue(k,v)] of the map,
      using the {{!unsigned_lt}unsigned order} on {!KEY.to_int}.
      @raises Not_found if the map is empty *)

  val unsigned_max_binding : 'a t -> 'a key_value_pair
  (** [unsigned_max_binding m] is maximal binding [KeyValue(k,v)] of the map,
      using the {{!unsigned_lt}unsigned order} on {!KEY.to_int}.
      @raises Not_found if the map is empty *)

  val singleton : 'a key -> ('a, 'b) value -> 'b t
  (** Create a map with a single binding. *)

  val cardinal : 'a t -> int
  (** The size of the map, O(n) complexity *)

  val is_singleton : 'a t -> 'a key_value_pair option
  (** [is_singleton m] returns [Some(KeyValue(k,v))] if and only if
      [m] contains a unique binding [k->v]. *)

  val find : 'key key -> 'map t -> ('key, 'map) value
  (** [find key map] returns the value associated with [key] in [map] if present.
      @raises Not_found if [key] is absent from map *)

  val find_opt : 'key key -> 'map t -> ('key, 'map) value option
  (** Same as {!find}, but returns [None] for Not_found *)

  val mem : 'key key -> 'map t -> bool
  (** [mem key map] returns [true] iff [key] is bound in [map], O(log(n)) complexity. *)

  val remove : 'key key -> 'map t -> 'map t
  (** Returns a map with the element removed, O(log(n)) complexity.
      Returns a physically equal map if the element is absent. *)

  val pop_unsigned_minimum: 'map t -> ('map key_value_pair * 'map t) option
  (** [pop_unsigned_minimum m] returns [None] if [is_empty m], or [Some(key,value,m')] where
      [(key,value) = unsigned_min_binding m] and [m' = remove m key].
      Uses the {{!unsigned_lt}unsigned order} on {!KEY.to_int}.
      O(log(n)) complexity. *)

  val pop_unsigned_maximum: 'map t -> ('map key_value_pair * 'map t) option
  (** [pop_unsigned_maximum m] returns [None] if [is_empty m], or [Some(key,value,m')] where
      [(key,value) = unsigned_max_binding m] and [m' = remove m key].
      Uses the {{!unsigned_lt}unsigned order} on {!KEY.to_int}.
      O(log(n)) complexity. *)

  val insert: 'a key -> (('a,'map) value option -> ('a,'map) value) -> 'map t -> 'map t
  (** [insert key f map] modifies or insert an element of the map; [f]
      takes [None] if the value was not previously bound, and [Some old]
      where [old] is the previously bound value otherwise. The function
      preserves physical equality when possible. O(log(n))
      complexity.
      Preserves physical equality if the new value is physically equal to the old. *)

  val update: 'a key -> (('a,'map) value option -> ('a,'map) value option) -> 'map t -> 'map t
  (** [update key f map] modifies, insert, or remove an element from
      the map; [f] takes [None] if the value was not previously bound, and
      [Some old] where [old] is the previously bound value otherwise. The
      function preserves physical equality when possible. It returns
      None if the element should be removed O(log(n)) complexity.
      Preserves physical equality if the new value is physically equal to the old. *)

  val add : 'key key -> ('key, 'map) value -> 'map t -> 'map t
  (** Unconditionally adds a value in the map (independently from
      whether the old value existed). O(log(n)) complexity.
      Preserves physical equality if the new value is physically equal to the old. *)

  (** {3 Iterators} *)

  val split : 'key key -> 'map t -> 'map t * ('key, 'map) value option * 'map t
  (** [split key map] splits the map into:
      - submap of [map] whose keys are smaller than [key]
      - value associated to [key] (if present)
      - submap of [map] whose keys are bigger than [key]

      Where the order is given by the {{!unsigned_lt}unsigned order} on {!KEY.to_int}. *)

  type 'map polyiter = { f : 'a. 'a key -> ('a, 'map) value -> unit; } [@@unboxed]
  val iter : 'map polyiter -> 'map t -> unit
  (** [iter f m] calls [f.f] on all bindings of [m],
      in the {{!unsigned_lt}unsigned order} on {!KEY.to_int} *)

  type ('acc,'map) polyfold = { f: 'a. 'a key -> ('a,'map) value -> 'acc -> 'acc } [@@unboxed]
  val fold : ('acc,'map) polyfold -> 'map t -> 'acc -> 'acc
  (** [fold f m acc] returns [f.f key_n value_n (... (f.f key_1 value_1 acc))]
      where [(key_1, value_1) ... (key_n, value_n)] are the bindings of [m], in
      the {{!unsigned_lt}unsigned order} on {!KEY.to_int}. *)

  type ('acc,'map) polyfold2 = { f: 'a. 'a key -> ('a,'map) value -> ('a,'map) value -> 'acc -> 'acc } [@@unboxed]
  val fold_on_nonequal_inter : ('acc,'map) polyfold2 -> 'map t -> 'map t -> 'acc -> 'acc
  (** [fold_on_nonequal_inter f m1 m2 acc] returns
      [f.f key_n value1_n value2n (... (f.f key_1 value1_1 value2_1 acc))] where
      [(key_1, value1_1, value2_1) ... (key_n, value1_n, value2_n)] are the
      bindings that exist in both maps ([m1 ∩ m2]) whose values are physically different.
      Calls to [f.f] are performed in the {{!unsigned_lt}unsigned order} of [Key.to_int]. *)


  type ('acc,'map) polyfold2_union = { f: 'a. 'a key -> ('a,'map) value option -> ('a,'map) value option -> 'acc -> 'acc } [@@unboxed]
  val fold_on_nonequal_union : ('acc,'map) polyfold2_union -> 'map t -> 'map t -> 'acc -> 'acc
  (** [fold_on_nonequal_union f m1 m2 acc] returns
      [f.f key_n value1_n value2n (... (f.f key_1 value1_1 value2_1 acc))] where
      [(key_1, value1_1, value2_1) ... (key_n, value1_n, value2_n)] are the
      bindings that exists in either map ([m1 ∪ m2]) whose values are physically
      different.
      Calls to [f.f] are performed in the {{!unsigned_lt}unsigned order} of [Key.to_int]. *)

  type 'map polypredicate = { f: 'a. 'a key -> ('a,'map) value -> bool; } [@@unboxed]
  val filter : 'map polypredicate -> 'map t -> 'map t
  (** [filter f m] returns the submap of [m] containing the bindings [k->v]
      such that [f.f k v = true].
      [f.f] is called in the {{!unsigned_lt}unsigned order} of {!KEY.to_int} *)

  val for_all : 'map polypredicate -> 'map t -> bool
  (** [for_all f m] checks that [f] holds on all bindings of [m].
      Short-circuiting. *)

  (** In the following, the *no_share function allows taking arguments
      of different types (but cannot share subtrees of the map), while
      the default functions attempt to preserve and benefit from
      sharing the subtrees (using physical equality to detect
      sharing). *)

  type ('map1,'map2) polymap = { f : 'a. ('a, 'map1) value -> ('a, 'map2) value; } [@@unboxed]
  val map : ('map,'map) polymap -> 'map t -> 'map t
  val map_no_share : ('map1,'map2) polymap -> 'map1 t -> 'map2 t
  (** [map f m] and [map_no_share f m] replace all bindings [(k,v)] by [(k, f.f v)].
      Bindings are examined in the {{!unsigned_lt}unsigned order} of {!KEY.to_int}. *)

  type ('map1,'map2) polymapi =
    { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value; } [@@unboxed]
  val mapi : ('map,'map) polymapi -> 'map t -> 'map t
  val mapi_no_share : ('map1,'map2) polymapi -> 'map1 t -> 'map2 t
  (** [mapi f m] and [mapi_no_share f m] replace all bindings [(k,v)] by [(k, f.f k v)].
      Bindings are examined in the {{!unsigned_lt}unsigned order} of {!KEY.to_int}. *)

  type ('map1,'map2) polyfilter_map =
    { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value option; } [@@unboxed]
  val filter_map : ('map,'map) polyfilter_map -> 'map t -> 'map t
  val filter_map_no_share : ('map1,'map2) polyfilter_map -> 'map1 t -> 'map2 t
  (** [filter_map m f] and [filter_map_no_share m f] remove the bindings
      [(k,v)] for which [f.f k v] is [None], and replaces the bindings [(k,v)]
      for which [f.f k v] is [Some v'] by [(k,v')].
      Bindings are examined in the {{!unsigned_lt}unsigned order} of {!KEY.to_int}. *)

  type 'map polypretty = { f: 'a. Format.formatter -> 'a key -> ('a, 'map) value -> unit } [@@unboxed]
  val pretty :
    ?pp_sep:(Format.formatter -> unit -> unit) -> 'map polypretty ->
    Format.formatter -> 'map t -> unit
  (** Pretty-prints a map using the given formatter.
      [pp_sep] is called once between each binding,
      it defaults to {{: https://v2.ocaml.org/api/Format.html#VALpp_print_cut}[Format.pp_print_cut]}.
      Bindings are printed in the {{!unsigned_lt}unsigned order} of {!KEY.to_int} *)

  (** {3 Functions on pairs of maps} *)

  type ('map1,'map2) polysame_domain_for_all2 =
    { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value -> bool; } [@@unboxed]

  val reflexive_same_domain_for_all2 :
    ('map,'map) polysame_domain_for_all2 -> 'map t -> 'map t -> bool
  (** [reflexive_same_domain_for_all2 f m1 m2] is true if and only if
      - [m1] and [m2] have the same domain (set of keys)
      - for all bindings [(k, v1)] in [m1] and [(k, v2)] in [m2], [f.f k v1 v2] holds

      {b Assumes} [f.f] is reflexive, i.e. [f.f k v v = true] to skip calls to equal subtrees.
      Calls [f.f] in ascending {{!unsigned_lt}unsigned order} of {!KEY.to_int}.
      Exits early if the domains mismatch or if [f.f] returns false.

      It is useful to implement equality on maps:
      {[
        let equal m1 m2 = reflexive_same_domain_for_all2
          { f = fun _ v1 v2 -> Value.equal v1 v2}
          m1 m2
      ]}
      *)

  val nonreflexive_same_domain_for_all2:
    ('map1,'map2) polysame_domain_for_all2 -> 'map1 t -> 'map2 t -> bool
  (** [nonreflexive_same_domain_for_all2 f m1 m2] is the same as
      {!reflexive_same_domain_for_all2}, but doesn't assume [f.f] is reflexive.
      It thus calls [f.f] on every binding, in ascending {{!unsigned_lt}unsigned order} of {!KEY.to_int}.
      Exits early if the domains mismatch or if [f.f] returns false. *)

  val reflexive_subset_domain_for_all2 :
    ('map,'map) polysame_domain_for_all2 -> 'map t -> 'map t -> bool
  (** [reflexive_subset_domain_for_all2 f m1 m2] is true if and only if
      - [m1]'s domain is a subset of [m2]'s. (all keys defined in [m1] are also defined in [m2])
      - for all bindings [(k, v1)] in [m1] and [(k, v2)] in [m2], [f.f k v1 v2] holds

      {b Assumes} [f.f] is reflexive, i.e. [f.f k v v = true] to skip calls to equal subtrees.
      Calls [f.f] in ascending {{!unsigned_lt}unsigned order} of {!KEY.to_int}.
      Exits early if the domains mismatch. *)

  type ('map1, 'map2, 'map3) polyunion = {
    f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value -> ('a, 'map3) value; } [@@unboxed]
  val idempotent_union : ('a, 'a, 'a) polyunion -> 'a t -> 'a t -> 'a t
  (** [idempotent_union f map1 map2] returns a map whose keys is the
      union of the keys of [map1] and [map2]. [f.f] is used to combine
      the values of keys mapped in both maps.

      {b Assumes} [f.f] idempotent (i.e. [f key value value == value])
      [f.f] is called in the {{!unsigned_lt}unsigned order} of {!KEY.to_int}.
      [f.f] is never called on physically equal values.
      Preserves physical equality as much as possible.
      Complexity is O(log(n)*Delta) where Delta is the number of
      different keys between [map1] and [map2]. *)

  type ('map1, 'map2, 'map3) polyinter = {
    f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value -> ('a, 'map3) value;
  } [@@unboxed]
  val idempotent_inter : ('a, 'a, 'a) polyinter -> 'a t -> 'a t -> 'a t
  (** [idempotent_inter f map1 map2] returns a map whose keys is the
      intersection of the keys of [map1] and [map2]. [f.f] is used to combine
      the values a key is mapped in both maps.

      {b Assumes} [f.f] idempotent (i.e. [f key value value == value])
      [f.f] is called in the {{!unsigned_lt}unsigned order} of {!KEY.to_int}.
      [f.f] is never called on physically equal values.
      Preserves physical equality as much as possible.
      Complexity is O(log(n)*Delta) where Delta is the number of
      different keys between [map1] and [map2]. *)

  val nonidempotent_inter_no_share :('a, 'b, 'c) polyinter -> 'a t -> 'b t -> 'c t
  (** [nonidempotent_inter_no_share f map1 map2] is the same as {!idempotent_inter}
      but doesn't preverse physical equality, doesn't assume [f.f] is idempotent,
      and can change the type of values. [f.f] is called on every shared binding.
      [f.f] is called in increasing {{!unsigned_lt}unsigned order} of keys.
      O(n) complexity *)


  type ('map1, 'map2, 'map3) polyinterfilter = { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value -> ('a, 'map3) value option; } [@@unboxed]
  val idempotent_inter_filter : ('a, 'a, 'a) polyinterfilter -> 'a t -> 'a t -> 'a t
  (** [idempotent_inter_filter f map1 map2] is the same as {!idempotent_inter}
      but [f.f] can return [None] to remove a binding from the resutling map. *)

  type ('map1, 'map2, 'map3) polymerge = {
    f : 'a. 'a key -> ('a, 'map1) value option -> ('a, 'map2) value option -> ('a, 'map3) value  option; } [@@unboxed]
  val slow_merge : ('map1, 'map2, 'map3) polymerge -> 'map1 t -> 'map2 t -> 'map3 t
  (** This is the same as {{: https://ocaml.org/api/Map.S.html#VALmerge}Stdlib.Map.S.merge} *)

  val disjoint : 'a t -> 'a t -> bool
  (** [disjoint m1 m2] is [true] iff [m1] and [m2] have disjoint domains *)

  (** {3 Conversion functions} *)

  val to_seq : 'a t -> 'a key_value_pair Seq.t
  (** [to_seq m] iterates the whole map, in increasing {{!unsigned_lt}unsigned order} of {!KEY.to_int} *)

  val to_rev_seq : 'a t -> 'a key_value_pair Seq.t
  (** [to_rev_seq m] iterates the whole map, in decreasing {{!unsigned_lt}unsigned order} of {!KEY.to_int} *)

  val add_seq : 'a key_value_pair Seq.t -> 'a t -> 'a t
  (** [add_seq s m] adds all bindings of the sequence [s] to [m] in order. *)

  val of_seq : 'a key_value_pair Seq.t -> 'a t
  (** [of_seq s] creates a new map from the bindings of [s].
      If a key is bound multiple times in [s], the latest binding is kept *)

  val of_list : 'a key_value_pair list -> 'a t
  (** [of_list l] creates a new map from the bindings of [l].
      If a key is bound multiple times in [l], the latest binding is kept *)

  val to_list : 'a t -> 'a key_value_pair list
  (** [to_list m] returns the bindings of [m] as a list, in increasing {{!unsigned_lt}unsigned order} of {!KEY.to_int} *)
end

(** {2 Heterogeneous maps and sets} *)
(** Maps and sets with generic keys ['a key] and values [('a,'b) value]  *)

module type HETEROGENEOUS_MAP = sig
  (** This is the same as {!MAP}, but with simple type [key] being replaced by type
      constructor ['a key] and ['b value] being replaced by [('a,'b) value].

      The main changes from {!MAP} are:
      - The type of {!key} is replaced by a type constructor ['k key].
        Because of that, most higher-order arguments require higher-ranking
        polymorphism, and we provide records that allows to
        pass them as arguments (e.g. {!polyiter}, {!polymap}, {!polyunion}, etc.)
      - The type of the map ({!type:t}) is still parameterized by an argument (['m t])
      - The type of {!type:value} depend on both the type of the key and the
        type of the map, hence the type [('k,'m) value].
      - The type of some return values, like key-value pairs, must be
        concealed existentially, hence the {!KeyValue} constructor. *)

  include BASE_MAP (** @closed *)

  (** Operation with maps/set of different types.
      [Map2] must use the same {!KEY.to_int} function. *)
  module WithForeign(Map2:BASE_MAP with type 'a key = 'a key):sig
    type ('map1,'map2) polyinter_foreign = { f: 'a. 'a key -> ('a,'map1) value -> ('a,'map2) Map2.value -> ('a,'map1) value } [@@unboxed]

    val nonidempotent_inter : ('a,'b) polyinter_foreign -> 'a t -> 'b Map2.t -> 'a t
    (** Like {!BASE_MAP.idempotent_inter}. Tries to preserve physical equality on the first argument when possible. *)

    type ('map2,'map1) polyfilter_map_foreign =
      { f : 'a. 'a key -> ('a, 'map2) Map2.value -> ('a, 'map1) value option; } [@@unboxed]
    val filter_map_no_share : ('map2,'map1) polyfilter_map_foreign -> 'map2 Map2.t -> 'map1 t
    (** Like {!BASE_MAP.filter_map_no_share}, but allows to transform a foreigh map into the current one. *)

    type ('map1,'map2) polyupdate_multiple = { f: 'a. 'a key -> ('a,'map1) value option -> ('a,'map2) Map2.value -> ('a,'map1) value option } [@@unboxed]
    val update_multiple_from_foreign : 'b Map2.t -> ('a,'b) polyupdate_multiple -> 'a t -> 'a t
    (** This is equivalent to multiple calls to {!update}, but more efficient.
        [update_multiple_from_foreign m_from f m_to] is the same as calling
        [update k {f=fun v_to -> f.f k v_to v_from} m_to]
        on all bindings [(k, v_from)] of [m_from],
        i.e. [update_multiple_from_foreign m_from f m_to] calls [f.f] on every
        key of [m_from], says if the corresponding value also exists in [m_to],
        and adds or remove the element in [m_to] depending on the value of [f.f].
        [f.f] is called in the {{!unsigned_lt}unsigned order} of {!KEY.to_int}.
        O(size(m_from) + size(m_to)) complexity. *)

    type ('map1,'map2) polyupdate_multiple_inter = { f: 'a. 'a key -> ('a,'map1) value -> ('a,'map2) Map2.value -> ('a,'map1) value option } [@@unboxed]
    val update_multiple_from_inter_with_foreign : 'b Map2.t -> ('a,'b) polyupdate_multiple_inter -> 'a t ->'a t
    (** [update_multiple_from_inter_with_foreign m_from f m_to] is the same as
        {!update_multiple_from_foreign}, except that instead of updating for all
        keys in [m_from], it only updates for keys that are both in [m_from] and
        [m_to]. *)
  end
end

module type HETEROGENEOUS_SET = sig
  (** A set containing different keys, very similar to
      {!SET}, but with simple type [elt] being replaced by type
      constructor ['a elt]. *)
  (** The main changes from {!SET} are:
      - The type of {!elt} is replaced by a type constructor ['k elt].
        Because of that, most higher-order arguments require higher-ranking
        polymorphism, and we provide records that allows to
        pass them as arguments (e.g. {!polyfold}, {!polypretty}, etc.)
      - The type of some return values, must be concealed existentially,
        hence the {!Any} constructor. *)

  type 'a elt
  (** Elements of the set *)

  (** Underlying basemap, for cross map/set operations *)
  module BaseMap : HETEROGENEOUS_MAP
    with type 'a key = 'a elt
     and type (_,_) value = unit

  type t = unit BaseMap.t
  (** The type of our set *)

  type 'a key = 'a elt
  (** Alias for elements, for compatibility with other PatriciaTrees *)

  (** Existential wrapper for set elements. *)
  type any_elt = Any : 'a elt -> any_elt

  (** {3 Basic functions} *)

  val empty: t
  (** The empty set *)

  val is_empty: t -> bool
  (** [is_empty st] is [true] if [st] contains no elements, [false] otherwise *)

  val mem: 'a elt -> t -> bool
  (** [mem elt set] is [true] if [elt] is contained in [set], O(log(n)) complexity. *)

  val add: 'a elt -> t -> t
  (** [add elt set] adds element [elt] to the [set].
      Preserves physical equality if [elt] was already present.
      O(log(n)) complexity. *)

  val singleton: 'a elt -> t
  (** [singleton elt] returns a set containing a single element: [elt] *)

  val cardinal: t -> int
  (** the size of the set (number of elements), O(n) complexity. *)

  val is_singleton: t -> any_elt option
  (** [is_singleton set] is [Some (Any elt)] if [set] is [singleton elt] and [None] otherwise. *)

  val remove: 'a elt -> t -> t
  (** [remove elt set] returns a set containing all elements of [set] except [elt].
      Returns a value physically equal to [set] if [elt] is not present. *)

  val unsigned_min_elt: t -> any_elt
  (** The minimal element if non empty, according to the
      {{!unsigned_lt}unsigned order} on elements.
      @raises Not_found *)

  val unsigned_max_elt: t -> any_elt
  (** The maximal element if non empty, according to the
      {{!unsigned_lt}unsigned order} on elements.
      @raises Not_found *)

  val pop_unsigned_minimum: t -> (any_elt * t) option
  (** [pop_unsigned_minimum s] is [Some (elt, s')] where [elt = unsigned_min_elt s] and [s' = remove elt s]
      if [s] is non empty.
      Uses the {{!unsigned_lt}unsigned order} on elements. *)

  val pop_unsigned_maximum: t -> (any_elt * t) option
  (** [pop_unsigned_maximum s] is [Some (elt, s')] where [elt = unsigned_max_elt s] and [s' = remove elt s]
      if [s] is non empty.
      Uses the {{!unsigned_lt}unsigned order} on elements. *)

  (** {3 Functions on pairs of sets} *)

  val union: t -> t -> t
  (** [union a b] is the set union of [a] and [b], i.e. the set containing all
      elements that are either in [a] or [b]. *)

  val inter: t -> t -> t
  (** [inter a b] is the set intersection of [a] and [b], i.e. the set containing all
      elements that are in both [a] or [b]. *)

  val disjoint: t -> t -> bool
  (** [disjoint a b] is [true] if [a] and [b] have no elements in common. *)

  val equal : t -> t -> bool
  (** [equal a b] is [true] if [a] and [b] contain the same elements. *)

  val subset : t -> t -> bool
  (** [subset a b] is [true] if all elements of [a] are also in [b]. *)

  val split: 'a elt -> t -> t * bool * t
  (** [split elt set] returns [s_lt, present, s_gt] where
      [s_lt] contains all elements of [set] smaller than [elt], [s_gt]
      all those greater than [elt], and [present] is [true] if [elt] is in [set].
      Uses the {{!unsigned_lt}unsigned order} on elements. *)

  (** {3 Iterators} *)

  type polyiter = { f: 'a. 'a elt -> unit; } [@@unboxed]
  val iter: polyiter -> t -> unit
  (** [iter f set] calls [f.f] on all elements of [set], in the {{!unsigned_lt}unsigned order} of {!KEY.to_int}. *)

  type polypredicate = { f: 'a. 'a elt -> bool; } [@@unboxed]
  val filter: polypredicate -> t -> t
  (** [filter f set] is the subset of [set] that only contains the elements that
      satisfy [f.f]. [f.f] is called in the {{!unsigned_lt}unsigned order} of {!KEY.to_int}. *)

  val for_all: polypredicate -> t -> bool
  (** [for_all f set] is [true] if [f.f] is [true] on all elements of [set].
      Short-circuits on first [false]. [f.f] is called in the {{!unsigned_lt}unsigned order} of {!KEY.to_int}. *)

  type 'acc polyfold = { f: 'a. 'a elt -> 'acc -> 'acc } [@@unboxed]
  val fold: 'acc polyfold -> t -> 'acc -> 'acc
  (** [fold f set acc] returns [f.f elt_n (... (f.f elt_1 acc) ...)], where
      [elt_1, ..., elt_n] are the elements of [set], in increasing {{!unsigned_lt}unsigned order} of
      {!KEY.to_int} *)

  type polypretty = { f: 'a. Format.formatter -> 'a elt -> unit; } [@@unboxed]
  val pretty :
    ?pp_sep:(Format.formatter -> unit -> unit) -> polypretty -> Format.formatter -> t -> unit
  (** Pretty prints the set, [pp_sep] is called once between each element,
      it defaults to {{: https://v2.ocaml.org/api/Format.html#VALpp_print_cut}[Format.pp_print_cut]} *)

  (** {3 Conversion functions} *)

  val to_seq : t -> any_elt Seq.t
  (** [to_seq st] iterates the whole set, in increasing {{!unsigned_lt}unsigned order} of {!KEY.to_int} *)

  val to_rev_seq : t -> any_elt Seq.t
  (** [to_rev_seq st] iterates the whole set, in decreasing {{!unsigned_lt}unsigned order} of {!KEY.to_int} *)

  val add_seq : any_elt Seq.t -> t -> t
  (** [add_seq s st] adds all elements of the sequence [s] to [st] in order. *)

  val of_seq : any_elt Seq.t -> t
    (** [of_seq s] creates a new set from the elements of [s]. *)

  val of_list : any_elt list -> t
  (** [of_list l] creates a new set from the elements of [l]. *)

  val to_list : t -> any_elt list
  (** [to_list s] returns the elements of [s] as a list, in increasing {{!unsigned_lt}unsigned order} of {!KEY.to_int} *)
end


(** {2 Homogeneous maps and sets}                             *)
(** Same as above, but simple interfaces for non-generic keys. These
    are also close to the standard library's interface for sets and maps. *)

(** Signature for sets implemented using Patricia trees.
    Most of this interface should be shared with {{: https://ocaml.org/api/Set.S.html}[Stdlib.Set.S]}. *)
module type SET = sig
  type elt
  (** The type of elements of the set *)

  type key = elt
  (** Alias for the type of elements, for cross-compatibility with maps *)

  (** Underlying basemap, for cross map/set operations *)
  module BaseMap : HETEROGENEOUS_MAP
    with type _ key = elt
     and type (_,_) value = unit

  type t = unit BaseMap.t
  (** The set type *)

  (** {3 Basic functions}                         *)

  val empty: t
  (** The empty set *)

  val is_empty: t -> bool
  (** [is_empty st] is [true] if [st] contains no elements, [false] otherwise *)

  val mem: elt -> t -> bool
  (** [mem elt set] is [true] if [elt] is contained in [set], O(log(n)) complexity. *)

  val add: elt -> t -> t
  (** [add elt set] adds element [elt] to the [set].
      Preserves physical equality if [elt] was already present.
      O(log(n)) complexity. *)

  val singleton: elt -> t
  (** [singleton elt] returns a set containing a single element: [elt] *)

  val cardinal: t -> int
  (** [cardinal set] is the size of the set (number of elements), O(n) complexity. *)

  val is_singleton: t -> elt option
  (** [is_singleton set] is [Some (Any elt)] if [set] is [singleton elt] and [None] otherwise. *)

  val remove: elt -> t -> t
  (** [remove elt set] returns a set containing all elements of [set] except [elt].
      Returns a value physically equal to [set] if [elt] is not present. *)

  val unsigned_min_elt: t -> elt
  (** The minimal element (according to the {{!unsigned_lt}unsigned order} on {!KEY.to_int}) if non empty.
      @raises Not_found *)

  val unsigned_max_elt: t -> elt
  (** The maximal element (according to the {{!unsigned_lt}unsigned order} on {!KEY.to_int}) if non empty.
      @raises Not_found *)

  val pop_unsigned_minimum: t -> (elt * t) option
  (** [pop_unsigned_minimum s] is [Some (elt, s')] where [elt = unsigned_min_elt s] and [s' = remove elt s]
      if [s] is non empty.
      Uses the {{!unsigned_lt}unsigned order} on {!KEY.to_int}. *)

  val pop_unsigned_maximum: t -> (elt * t) option
  (** [pop_unsigned_maximum s] is [Some (elt, s')] where [elt = unsigned_max_elt s] and [s' = remove elt s]
      if [s] is non empty.
      Uses the {{!unsigned_lt}unsigned order} on {!KEY.to_int}. *)

  (** {3 Iterators} *)

  val iter: (elt -> unit) -> t -> unit
  (** [iter f set] calls [f] on all elements of [set], in the {{!unsigned_lt}unsigned order} of {!KEY.to_int}. *)

  val filter: (elt -> bool) -> t -> t
  (** [filter f set] is the subset of [set] that only contains the elements that
      satisfy [f]. [f] is called in the {{!unsigned_lt}unsigned order} of {!KEY.to_int}. *)

  val for_all: (elt -> bool) -> t -> bool
  (** [for_all f set] is [true] if [f] is [true] on all elements of [set].
      Short-circuits on first [false]. [f] is called in the {{!unsigned_lt}unsigned order} of {!KEY.to_int}. *)

  val fold: (elt -> 'acc -> 'acc) -> t -> 'acc -> 'acc
  (** [fold f set acc] returns [f elt_n (... (f elt_1 acc) ...)], where
      [elt_1, ..., elt_n] are the elements of [set], in increasing {{!unsigned_lt}unsigned order} of
      {!KEY.to_int} *)

  val split: elt -> t -> t * bool * t
  (** [split elt set] returns [s_lt, present, s_gt] where
      [s_lt] contains all elements of [set] smaller than [elt], [s_gt]
      all those greater than [elt], and [present] is [true] if [elt] is in [set].
      Uses the {{!unsigned_lt}unsigned order} on {!KEY.to_int}.*)

  val pretty :
    ?pp_sep:(Format.formatter -> unit -> unit) ->
    (Format.formatter -> elt -> unit) -> Format.formatter -> t -> unit
  (** Pretty prints the set, [pp_sep] is called once between each element,
      it defaults to {{: https://v2.ocaml.org/api/Format.html#VALpp_print_cut}[Format.pp_print_cut]} *)

  (** {3 Functions on pairs of sets} *)

  val union: t -> t -> t
  (** [union a b] is the set union of [a] and [b], i.e. the set containing all
      elements that are either in [a] or [b]. *)

  val inter: t -> t -> t
  (** [inter a b] is the set intersection of [a] and [b], i.e. the set containing all
      elements that are in both [a] or [b]. *)

  val disjoint: t -> t -> bool
  (** [disjoint a b] is [true] if [a] and [b] have no elements in common. *)

  val equal : t -> t -> bool
  (** [equal a b] is [true] if [a] and [b] contain the same elements. *)

  val subset : t -> t -> bool
  (** [subset a b] is [true] if all elements of [a] are also in [b]. *)

  (** {3 Conversion functions} *)

  val to_seq : t -> elt Seq.t
  (** [to_seq st] iterates the whole set, in increasing {{!unsigned_lt}unsigned order} of {!KEY.to_int} *)

  val to_rev_seq : t -> elt Seq.t
  (** [to_rev_seq st] iterates the whole set, in decreasing {{!unsigned_lt}unsigned order} of {!KEY.to_int} *)

  val add_seq : elt Seq.t -> t -> t
  (** [add_seq s st] adds all elements of the sequence [s] to [st] in order. *)

  val of_seq : elt Seq.t -> t
    (** [of_seq s] creates a new set from the elements of [s]. *)

  val of_list : elt list -> t
  (** [of_list l] creates a new set from the elements of [l]. *)

  val to_list : t -> elt list
  (** [to_list s] returns the elements of [s] as a list, in increasing {{!unsigned_lt}unsigned order} of {!KEY.to_int} *)
end

(** The typechecker struggles with forall quantification on values if they
    don't depend on the first parameter, this wrapping allows our code to pass
    typechecking by forbidding overly eager simplification.
    Since the type is unboxed, it doesn't introduce any performance overhead.

    This is due to a bug in the typechecker, more info on
    {{: https://discuss.ocaml.org/t/weird-behaviors-with-first-order-polymorphism/13783} the OCaml discourse post}. *)
type (_, 'b) snd = Snd of 'b [@@unboxed]


(** The signature for maps with a single type for keys and values,
    a ['a map] binds [key] to ['a value].
    This is slightly more generic than {!MAP}, which just binds to ['a].
    It is used for maps that need to restrict their value type, namely {!hash_consed}. *)
module type MAP_WITH_VALUE = sig
  type key
  (** The type of keys. *)

  type 'a t
  (** A map from [key] to values of type ['a value].  *)

  type 'a value
  (** Type for values, this is a divergence from Stdlib's [Map],
      but becomes equivalent to it when using {!MAP},
      which is just [MAP_WITH_VALUE with type 'a value = 'a].
      On the other hand, it allows defining maps with fixed values, which is useful
      for hash-consing.

      @since v0.10.0 *)

  (** Underlying basemap, for cross map/set operations *)
  module BaseMap : HETEROGENEOUS_MAP
    with type 'a t = 'a t
    and type _ key = key
    and type ('a,'b) value = ('a,'b value) snd

  (** {3 Basic functions} *)

  val empty : 'a t
  (** The empty map. *)

  val is_empty : 'a t -> bool
  (** Test if a map is empty; O(1) complexity. *)

  val unsigned_min_binding : 'a t -> (key * 'a value)
  (** Returns the (key,value) where [Key.to_int key] is minimal (in the
      {{!unsigned_lt}unsigned representation} of integers); O(log n) complexity.
      @raises Not_found if the map is empty *)

  val unsigned_max_binding : 'a t -> (key * 'a value)
  (** Returns the (key,value) where [Key.to_int key] is maximal (in the
      {{!unsigned_lt}unsigned representation} of integers); O(log n) complexity.
      @raises Not_found if the map is empty *)

  val singleton : key -> 'a value -> 'a t
  (** [singleton key value] creates a map with a single binding, O(1) complexity.  *)

  val cardinal : 'a t -> int
  (** The size of the map. O(n) complexity *)

  val is_singleton : 'a t -> (key * 'a value) option
  (** [is_singleton m] is [Some (k,v)] iff [m] is [singleton k v] *)

  val find : key -> 'a t -> 'a value
  (** Return an element in the map, or raise [Not_found], O(log(n)) complexity. *)

  val find_opt : key -> 'a t -> 'a value option
  (** Return an element in the map, or [None], O(log(n)) complexity. *)

  val mem : key -> 'a t -> bool
  (** [mem key map] returns [true] iff [key] is bound in [map], O(log(n)) complexity. *)

  val remove : key -> 'a t -> 'a t
  (** Returns a map with the element removed, O(log(n)) complexity.
      Returns a physically equal map if the element is absent. *)

  val pop_unsigned_minimum : 'a t -> (key * 'a value * 'a t) option
  (** [pop_unsigned_minimum m] returns [None] if [is_empty m], or [Some(key,value,m')] where
      [(key,value) = unsigned_min_binding m] and [m' = remove m key]. O(log(n)) complexity.
      Uses the {{!unsigned_lt}unsigned order} on {!KEY.to_int}. *)

  val pop_unsigned_maximum : 'a t -> (key * 'a value * 'a t) option
  (** [pop_unsigned_maximum m] returns [None] if [is_empty m], or [Some(key,value,m')] where
      [(key,value) = unsigned_max_binding m] and [m' = remove m key]. O(log(n)) complexity.
      Uses the {{!unsigned_lt}unsigned order} on {!KEY.to_int}. *)

  val insert : key -> ('a value option -> 'a value) -> 'a t -> 'a t
  (** [insert key f map] modifies or insert an element of the map; [f]
      takes [None] if the value was not previously bound, and [Some old]
      where [old] is the previously bound value otherwise. The function
      preserves physical equality when possible. O(log(n))
      complexity.
      Preserves physical equality if the new value is physically equal to the old. *)

  val update : key -> ('a value option -> 'a value option) -> 'a t -> 'a t
  (** [update key f map] modifies, insert, or remove an element from
      the map; [f] takes [None] if the value was not previously bound, and
      [Some old] where [old] is the previously bound value otherwise. The
      function preserves physical equality when possible. It returns
      None if the element should be removed O(log(n)) complexity.
      Preserves physical equality if the new value is physically equal to the old. *)

  val add : key -> 'a value -> 'a t -> 'a t
  (** Unconditionally adds a value in the map (independently from
      whether the old value existed). O(log(n)) complexity.
      Preserves physical equality if the new value is physically equal to the old. *)

  (** {3 Iterators} *)

  val split : key -> 'a t -> 'a t * 'a value option * 'a t
  (** [split key map] splits the map into:
      - submap of [map] whose keys are smaller than [key]
      - value associated to [key] (if present)
      - submap of [map] whose keys are bigger than [key]
      Using the {{!unsigned_lt}unsigned order} is given by {!KEY.to_int}. *)

  val iter : (key -> 'a value -> unit) -> 'a t -> unit
  (** Iterate on each (key,value) pair of the map, in increasing {{!unsigned_lt}unsigned order} of keys. *)

  val fold : (key -> 'a value -> 'acc -> 'acc) ->  'a t -> 'acc -> 'acc
  (** Fold on each (key,value) pair of the map, in increasing {{!unsigned_lt}unsigned order} of keys. *)

  val fold_on_nonequal_inter : (key -> 'a value -> 'a value -> 'acc -> 'acc) ->
    'a t -> 'a t -> 'acc -> 'acc
  (** [fold_on_nonequal_inter f m1 m2 acc] returns
      [f key_n value1_n value2n (... (f key_1 value1_1 value2_1 acc))] where
      [(key_1, value1_1, value2_1) ... (key_n, value1_n, value2_n)] are the
      bindings that exist in both maps ([m1 ∩ m2]) whose values are physically different.
      Calls to [f] are performed in the {{!unsigned_lt}unsigned order} of [Key.to_int]. *)

  val fold_on_nonequal_union: (key -> 'a value option -> 'a value option -> 'acc -> 'acc) ->
    'a t -> 'a t -> 'acc -> 'acc
  (** [fold_on_nonequal_union f m1 m2 acc] returns
      [f key_n value1_n value2n (... (f key_1 value1_1 value2_1 acc))] where
      [(key_1, value1_1, value2_1) ... (key_n, value1_n, value2_n)] are the
      bindings that exists in either map ([m1 ∪ m2]) whose values are physically
      different.
      Calls to [f.f] are performed in the {{!unsigned_lt}unsigned order} of [Key.to_int]. *)

  val filter : (key -> 'a value -> bool) -> 'a t -> 'a t
  (** Returns the submap containing only the key->value pairs satisfying the
      given predicate. [f] is called in increasing {{!unsigned_lt}unsigned order} of keys. *)

  val for_all : (key -> 'a value -> bool) -> 'a t -> bool
  (** Returns true if the predicate holds on all map bindings. Short-circuiting.
      [f] is called in increasing {{!unsigned_lt}unsigned order} of keys. *)

  (** In the following, the *no_share function allows taking arguments
      of different types (but cannot share subtrees of the map), while
      the default functions attempt to preserve and benefit from
      sharing the subtrees (using physical equality to detect
      sharing). *)

  val map : ('a value -> 'a value) -> 'a t -> 'a t
  (** [map f m] returns a map where the [value] bound to each [key] is
      replaced by [f value]. The subtrees for which the returned
      value is physically the same (i.e. [f key value == value] for
      all the keys in the subtree) are guaranteed to be physically
      equal to the original subtree. O(n) complexity.
      [f] is called in increasing {{!unsigned_lt}unsigned order} of keys. *)

  val map_no_share : ('a value -> 'b value) -> 'a t -> 'b t
  (** [map_no_share f m] returns a map where the [value] bound to each
      [key] is replaced by [f value]. O(n) complexity.
      [f] is called in increasing {{!unsigned_lt}unsigned order} of keys. *)

  val mapi : (key -> 'a value -> 'a value) -> 'a t -> 'a t
  (** [mapi f m] returns a map where the [value] bound to each [key] is
      replaced by [f key value]. The subtrees for which the returned
      value is physically the same (i.e. [f key value == value] for
      all the keys in the subtree) are guaranteed to be physically
      equal to the original subtree. O(n) complexity.
      [f] is called in increasing {{!unsigned_lt}unsigned order} of keys. *)

  val mapi_no_share : (key -> 'a value -> 'b value) -> 'a t -> 'b t
  (** [mapi_no_share f m] returns a map where the [value] bound to each
      [key] is replaced by [f key value]. O(n) complexity.
      [f] is called in increasing {{!unsigned_lt}unsigned order} of keys. *)

  val filter_map : (key -> 'a value -> 'a value option) -> 'a t -> 'a t
  (** [filter_map m f] returns a map where the [value] bound to each
      [key] is removed (if [f key value] returns [None]), or is
      replaced by [v] ((if [f key value] returns [Some v]). The
      subtrees for which the returned value is physically the same
      (i.e. [f key value = Some v] with [value == v] for all the keys
      in the subtree) are guaranteed to be physically equal to the
      original subtree. O(n) complexity.
      [f] is called in increasing {{!unsigned_lt}unsigned order} of keys. *)

  val filter_map_no_share : (key -> 'a value -> 'b value option) -> 'a t -> 'b t
  (** [filter_map m f] returns a map where the [value] bound to each
      [key] is removed (if [f key value] returns [None]), or is
      replaced by [v] ((if [f key value] returns [Some v]). O(n)
      complexity.
      [f] is called in increasing {{!unsigned_lt}unsigned order} of keys. *)


  (** {3 Operations on pairs of maps} *)
  (** The following functions combine two maps. It is key for the
      performance, when we have large maps who share common subtrees,
      not to visit the nodes in these subtrees. Hence, we have
      specialized versions of these functions that assume properties
      of the function parameter (reflexive relation, idempotent
      operation, etc.)

      When we cannot enjoy these properties, our functions explicitly
      say so (with a nonreflexive or nonidempotent prefix). The names
      are a bit long, but having these names avoids using an
      ineffective code by default, by forcing to know and choose
      between the fast and slow version.

      It is also important to not visit a subtree when there merging
      this subtree with Empty; hence we provide union and inter
      operations. *)

  val reflexive_same_domain_for_all2 : (key -> 'a value -> 'a value -> bool) -> 'a t -> 'a t ->  bool
  (** [reflexive_same_domain_for_all2 f map1 map2] returns true if
      [map1] and [map2] have the same keys, and [f key value1 value2]
      returns true for each mapping pair of keys. We assume that [f]
      is reflexive (i.e. [f key value value] returns true) to avoid
      visiting physically equal subtrees of [map1] and [map2]. The
      complexity is O(log(n)*Delta) where Delta is the number of
      different keys between [map1] and [map2]. *)

  val nonreflexive_same_domain_for_all2 : (key -> 'a value -> 'b value -> bool) -> 'a t -> 'b t -> bool
  (** [nonreflexive_same_domain_for_all2 f map1 map2] returns true if
      map1 and map2 have the same keys, and [f key value1 value2]
      returns true for each mapping pair of keys. The complexity is
      O(min(|map1|,|map2|)). *)

  val reflexive_subset_domain_for_all2 : (key -> 'a value -> 'a value -> bool) -> 'a t -> 'a t -> bool
  (** [reflexive_subset_domain_for_all2 f map1 map2] returns true if
      all the keys of [map1] also are in [map2], and [f key (find map1
      key) (find map2 key)] returns [true] when both keys are present
      in the map. We assume that [f] is reflexive (i.e. [f key value
      value] returns true) to avoid visiting physically equal subtrees
      of [map1] and [map2]. The complexity is O(log(n)*Delta) where
      Delta is the number of different keys between [map1] and
      [map2]. *)

  val idempotent_union : (key -> 'a value -> 'a value -> 'a value) -> 'a t -> 'a t -> 'a t
  (** [idempotent_union f map1 map2] returns a map whose keys is the
      union of the keys of [map1] and [map2]. [f] is used to combine
      the values a key is mapped in both maps. We assume that [f] is
      idempotent (i.e. [f key value value == value]) to avoid visiting
      physically equal subtrees of [map1] and [map2], and also to
      preserve physical equality of the subtreess in that case.  The
      complexity is O(log(n)*Delta) where Delta is the number of
      different keys between [map1] and [map2].
      [f] is called in increasing {{!unsigned_lt}unsigned order} of keys.
      [f] is never called on physically equal values. *)

  val idempotent_inter : (key -> 'a value -> 'a value -> 'a value) -> 'a t -> 'a t -> 'a t
  (** [idempotent_inter f map1 map2] returns a map whose keys is the
      intersection of the keys of [map1] and [map2]. [f] is used to combine
      the values a key is mapped in both maps. We assume that [f] is
      idempotent (i.e. [f key value value == value]) to avoid visiting
      physically equal subtrees of [map1] and [map2], and also to
      preserve physical equality of the subtrees in that case.  The
      complexity is O(log(n)*Delta) where Delta is the number of
      different keys between [map1] and [map2].
      [f] is called in increasing {{!unsigned_lt}unsigned order} of keys.
      [f] is never called on physically equal values. *)

  val nonidempotent_inter_no_share : (key -> 'a value -> 'b value -> 'c value) -> 'a t -> 'b t -> 'c t
  (** [nonidempotent_inter_no_share f map1 map2] returns a map whose keys is
      the intersection of the keys of [map1] and [map2]. [f] is used
      to combine the values a key is mapped in both maps. [f] does not
      need to be idempotent, which imply that we have to visit
      physically equal subtrees of [map1] and [map2].  The complexity
      is O(log(n)*min(|map1|,|map2|)).
      [f] is called in increasing {{!unsigned_lt}unsigned order} of keys.
      [f] is called on every shared binding. *)

  val idempotent_inter_filter : (key -> 'a value -> 'a value -> 'a value option) -> 'a t -> 'a t -> 'a t
  (** [idempotent_inter_filter f m1 m2] is like {!idempotent_inter}
      (assuming idempotence, using and preserving physically
      equal subtrees), but it also removes the key->value bindings for
      which [f] returns [None]. *)

  val slow_merge : (key -> 'a value option -> 'b value option -> 'c value option) -> 'a t -> 'b t -> 'c t
  (** [slow_merge f m1 m2] returns a map whose keys are a subset of the
      keys of [m1] and [m2].  The [f] function is used to combine
      keys, similarly to the [Map.merge] function.  This funcion has
      to traverse all the bindings in [m1] and [m2]; its complexity is
      O(|m1|+|m2|). Use one of faster functions above if you can. *)

  val disjoint : 'a t -> 'a t -> bool

  (** Combination with other kinds of maps.
      [Map2] must use the same {!KEY.to_int} function. *)
  module WithForeign(Map2 : BASE_MAP with type _ key = key):sig

    type ('b,'c) polyfilter_map_foreign = { f: 'a. key -> ('a,'b) Map2.value -> 'c value option } [@@unboxed]
    val filter_map_no_share : ('b, 'c) polyfilter_map_foreign -> 'b Map2.t ->  'c t
    (** Like [filter_map_no_share], but takes another map. *)

    type ('value,'map2) polyinter_foreign =
      { f: 'a. 'a Map2.key -> 'value value-> ('a, 'map2) Map2.value -> 'value value } [@@unboxed]
    val nonidempotent_inter : ('a, 'b) polyinter_foreign -> 'a t -> 'b Map2.t -> 'a t
    (** Like [nonidempotent_inter], but takes another map as an argument. *)


    type ('map1,'map2) polyupdate_multiple = { f: 'a. key -> 'map1 value option -> ('a,'map2) Map2.value -> 'map1 value option } [@@unboxed]
    val update_multiple_from_foreign : 'b Map2.t -> ('a,'b) polyupdate_multiple -> 'a t -> 'a t
    (** This is equivalent to multiple calls to {!update} (but more efficient)
        [update_multiple_from_foreign m_from f m_to] is the same as calling
        [update k {f=fun v_to -> f.f k v_to v_from} m_to]
        on all bindings [(k, v_from)] of [m_from],
        i.e. [update_multiple_from_foreign m_from f m_to] calls [f.f] on every
        key of [m_from], says if the corresponding value also exists in [m_to],
        and adds or remove the element in [m_to] depending on the value of [f.f].
        [f.f] is called in the {{!unsigned_lt}unsigned order} of {!KEY.to_int}.
        O(size(m_from) + size(m_to)) complexity. *)


    type ('map1,'map2) polyupdate_multiple_inter = { f: 'a. key -> 'map1 value -> ('a,'map2) Map2.value -> 'map1 value option } [@@unboxed]
    val update_multiple_from_inter_with_foreign: 'b Map2.t -> ('a,'b) polyupdate_multiple_inter -> 'a t -> 'a t
    (** [update_multiple_from_inter_with_foreign m_from f m_to] is the same as
        {!update_multiple_from_foreign}, except that instead of updating for all
        keys in [m_from], it only updates for keys that are both in [m_from] and
        [m_to]. *)
  end

  val pretty :
    ?pp_sep:(Format.formatter -> unit -> unit) ->
    (Format.formatter -> key -> 'a value -> unit) ->
    Format.formatter -> 'a t -> unit
  (** Pretty prints all bindings of the map.
      [pp_sep] is called once between each binding pair and defaults to {{: https://v2.ocaml.org/api/Format.html#VALpp_print_cut}[Format.pp_print_cut]}. *)

  (** {3 Conversion functions} *)

  val to_seq : 'a t -> (key * 'a value) Seq.t
  (** [to_seq m] iterates the whole map, in increasing {{!unsigned_lt}unsigned order} of {!KEY.to_int} *)

  val to_rev_seq : 'a t -> (key * 'a value) Seq.t
  (** [to_rev_seq m] iterates the whole map, in decreasing {{!unsigned_lt}unsigned order} of {!KEY.to_int} *)

  val add_seq : (key * 'a value) Seq.t -> 'a t -> 'a t
  (** [add_seq s m] adds all bindings of the sequence [s] to [m] in order. *)

  val of_seq : (key * 'a value) Seq.t -> 'a t
  (** [of_seq s] creates a new map from the bindings of [s].
      If a key is bound multiple times in [s], the latest binding is kept *)

  val of_list : (key * 'a value) list -> 'a t
  (** [of_list l] creates a new map from the bindings of [l].
      If a key is bound multiple times in [l], the latest binding is kept *)

  val to_list : 'a t -> (key * 'a value) list
  (** [to_list m] returns the bindings of [m] as a list,
      in increasing {{!unsigned_lt}unsigned order} of {!KEY.to_int} *)
end

(** The signature for maps with a single type for keys and values,
    a ['a map] binds [key] to ['a].
    Most of this interface should be shared with {{: https://ocaml.org/api/Map.S.html}[Stdlib.Map.S]}. *)
module type MAP = MAP_WITH_VALUE with type 'a value = 'a

(** {1 Keys} *)
(** Keys are the functor arguments used to build the maps. *)

(** The signature of homogeneous keys (non-generic, unparameterized keys).  *)
module type KEY = sig
  type t
  (** The type of keys.

      {b It is recommended to use immutable keys.}
      If keys are mutable,
      any mutations to keys must preserve {!to_int}. Failing to do so will
      break the patricia trees' invariants. *)

  (** A unique identifier for values of the type. Usually, we use a
      fresh counter that is increased to give a unique id to each
      object. Correctness of the operations requires that different
      values in a tree correspond to different integers.

      {b Must be injective, and ideally fast.}
      {{: https://en.wikipedia.org/wiki/Hash_consing}hash-consing} keys is a good way to
      generate such unique identifiers.

      Note that since Patricia Trees use {{!unsigned_lt}unsigned order}, negative
      keys are seen as bigger than positive keys.
      Be wary of this when using negative keys combined with functions like
      {{!BASE_MAP.unsigned_max_binding}[unsigned_max_binding]} and {{!BASE_MAP.pop_unsigned_maximum}[pop_unsigned_maximum]}. *)
  val to_int: t -> int
end

(** To have heterogeneous keys, we must define a polymorphic equality
    function.  Like in the homogeneous case, it should have the
    requirement that [(to_int a) = (to_int b) ==> polyeq a b = Eq]. *)
type (_, _) cmp = Eq : ('a, 'a) cmp | Diff : ('a, 'b) cmp

(** The signature of heterogeneous keys.  *)
module type HETEROGENEOUS_KEY = sig
  type 'key t
  (** The type of generic/heterogeneous keys.

      {b It is recommended to use immutable keys.}
      If keys are mutable,
      any mutations to keys must preserve {!to_int}. Failing to do so will
      break the patricia trees' invariants. *)


  val to_int : 'key t -> int
  (** A unique identifier for values of the type. Usually, we use a
      fresh counter that is increased to give a unique id to each
      object. Correctness of the operations requires that different
      values in a tree correspond to different integers.

      {b Must be injective, and ideally fast.}
      {{: https://en.wikipedia.org/wiki/Hash_consing}hash-consing} keys is a good way to
      generate such unique identifiers.

      Note that since Patricia Trees use {{!unsigned_lt}unsigned order}, negative
      keys are seen as bigger than positive keys.
      Be wary of this when using negative keys combined with functions like
      {{!BASE_MAP.unsigned_max_binding}[unsigned_max_binding]} and {{!BASE_MAP.pop_unsigned_maximum}[pop_unsigned_maximum]}. *)

  val polyeq : 'a t -> 'b t -> ('a, 'b) cmp
  (** Polymorphic equality function used to compare our keys.
      It should satisfy [(to_int a) = (to_int b) ==> polyeq a b = Eq], and be
      fast. *)
end

(** {1 Values} *)

(** Module type used for specifying custom homogeneous value types in {!MakeCustomMap}.
    For most purposes, use the provided {!Value} implementation.
    It sets ['a t = 'a], which is the desired effect (maps can map to any value).
    This is the case in {!MakeMap}.
    However, for maps like {!hash_consed}, it can be useful to restrict the type
    of values in order to implement [hash] and [polyeq] functions on values.
    See the {!HASHED_VALUE} module type for more details.

    @since 0.10.0 *)
module type VALUE = sig
    type 'a t
    (** The type of values. A ['map map] maps [key] to ['map value].
    Can be mutable if desired, unless it is being used in {!hash_consed}. *)
end

(** Default implementation of {!VALUE}, used in {!MakeMap}.
    @since 0.10.0 *)
module Value : VALUE with type 'a t = 'a

(** The module type of values, which can be heterogeneous.
    This can be used to specify how the type of the value depends on that of the key.
    If the value doesn't depend on the key type, you can use the provided default
    implementations {!HomogeneousValue} and {!WrappedHomogeneousValue}. *)
module type HETEROGENEOUS_VALUE = sig
    type ('key, 'map) t
    (** The type of values. A ['map map] maps ['key key] to [('key, 'map) value].
    Can be mutable if desired, unless it is being used in {!hash_consed}. *)
end

(** Default implementation of {!HETEROGENEOUS_VALUE}, to use when the type of the
    value in a heterogeneous map does not depend on the type of the key, only on
    the type of the map. *)
module HomogeneousValue : HETEROGENEOUS_VALUE with type ('a,'map) t = 'map

(** Same as {!HomogeneousValue}, but uses a wrapper (unboxed) type instead of direct
    equality. This avoids a problem in the typechecker with overly eager simplification of aliases.
    More info on
    {{: https://discuss.ocaml.org/t/weird-behaviors-with-first-order-polymorphism/13783} the OCaml discourse post}. *)
module WrappedHomogeneousValue : HETEROGENEOUS_VALUE with type ('a,'map) t = ('a,'map) snd

(** {!VALUE} parameter for {!hash_consed}, as hash-consing requires hashing and comparing values.

    This is the parameter type for homogeneous maps, used in {!MakeHashconsedMap}.
    A default implementation is provided in {!HashedValue}, using
    {{: https://ocaml.org/api/Hashtbl.html#VALhash}[Hashtbl.hash]}
    as [hash] function and physical equality as [polyeq].

    @since 0.10.0 *)
module type HASHED_VALUE = sig
  type 'a t
  (** The type of values for a hash-consed maps.

      Unlike {!VALUE.t}, {b hash-consed values should be immutable}.
      Or, if they do mutate, they must not change their {!hash} value, and
      still be equal to the same values via {!polyeq} *)

  val hash : 'map t -> int
  (** [hash v] should return an integer hash for the value [v].
      It is used for {{!hash_consed}hash-consing}.

      Hashing should be fast, avoid mapping too many values to the same integer
      and compatible with {!polyeq} (equal values must have the same hash:
      [polyeq v1 v2 = true ==> hash v1 = hash v2]). *)

  val polyeq : 'a t -> 'b t -> bool
  (** Polymorphic equality on values.

     {b WARNING: if [polyeq a b] is true, then casting [b] to the type of [a]
        (and [a] to the type of [b]) must be type-safe.} Eg. if [a : t1 t] and [b : t2 t]
     yield [polyeq a b = true], then [let a' : t2 t = Obj.magic a] and
     [let b' : t1 t = Obj.magic b] must be safe.

     Examples of safe implementations include:
     {ul
     {li Having a type ['a t] which doesn't depend on ['a], in which case casting
         form ['a t] to ['b t] is always safe:
         {[
          type _ t = foo
          let cast : type a b. a t -> b t = fun x -> x
          let polyeq : type a b. a t -> b t -> bool = fun x y -> x = y
         ]}}
     {li Using a GADT type and examining its constructors to only return [true]
         when the constructors are equal:
         {[
            type _ t =
                | T_Int : int -> int t
                | T_Bool : bool -> bool t
            let polyeq : type a b. a t -> b t -> bool = fun x y ->
                match x, y with
                | T_Int i, T_Int j -> i = j (* Here type a = b = int, we can return true *)
                | T_Bool i, T_Bool j -> i && j (* same here, but with a = b = bool *)
                | _ -> false (* never return true on heterogeneous cases. *)
         ]}}
     {li Using physical equality:
         {[
            let polyeq a b = a == Obj.magic b
         ]}
         While this contains an [Obj.magic], it is still type safe (OCaml just compares
         the immediate values) and we can safely cast values from one type to the
         other if they satisfy this (since they are already physically equal).

         This is the implementation used in {!HashedValue}. Note however that
         using this function can lead to {b identifiers no longer being unique across
         types}. They will still be unique and behave as expected within a certain type,
         but since some values of different types can physically equal, we may have
         identifer clashes:
         {[
            let _ = 97 == Obj.magic 'a' (* This is true *)

            module HMap = MakeHashconsedMap(Int)(HashedValue)

            let m1 = HMap.singleton 5 97 (* int HMap.t *)
            let m2 = HMap.singleton 5 'a' (* char HMap.t *)
            let _ = HMap.get_id m1 = HMap.get_id m2 (* This is also true. *)
         ]}
         This can cause problems if you wish to use identifiers of different map
         types together:
         {[
            module MapOfMaps = MakeMap(struct
              type t = Any : 'a HMap.t -> t
              let to_int (Any x) = Node.get_id x
            end)

           let m3 = MapOfMaps.of_list [ (m1, "foo"); (m2, "bar") ]
           (* m3 has cardinal 1, the m1->foo binding has been overwritten. *)
         ]}
         This issue does not happen with the two previous variants, since they
         both only return true on the same types.}} *)
end

(** In order to build {!hash_consed}, we need to be able to hash and compare values.

    This is the heterogeneous version of {!HASHED_VALUE}, used to specify a value
    for heterogeneous maps (in {!MakeHashconsedHeterogeneousMap}).
    A default implementation is provided in {!HeterogeneousHashedValue}, using
    {{: https://ocaml.org/api/Hashtbl.html#VALhash}[Hashtbl.hash]}
    as [hash] function and physical equality as [polyeq].

    @since 0.10.0 *)
module type HETEROGENEOUS_HASHED_VALUE = sig
    type ('key, 'map) t
    (** The type of values for a hash-consed maps.

        Unlike {!HETEROGENEOUS_VALUE.t}, {b hash-consed values should be immutable}.
        Or, if they do mutate, they must not change their {!hash} value, and
        still be equal to the same values via {!polyeq} *)

    val hash : ('key, 'map) t -> int
    (** [hash v] should return an integer hash for the value [v].
        It is used for {{!hash_consed}hash-consing}.

        Hashing should be fast, avoid mapping too many values to the same integer
        and compatible with {!polyeq} (equal values must have the same hash:
        [polyeq v1 v2 = true ==> hash v1 = hash v2]). *)

    val polyeq : ('key, 'map_a) t -> ('key, 'map_b) t -> bool
    (** Polymorphic equality on values.

       {b WARNING: if [polyeq a b] is true, then casting [b] to the type of [a]
          (and [a] to the type of [b]) must be type-safe.} Eg. if [a : (k, t1) t] and [b : (k, t2) t]
       yield [polyeq a b = true], then [let a' : (k,t2) t = Obj.magic a] and
       [let b' : (k,t1) t = Obj.magic b] must be safe.

       Examples of safe implementations include:
       {ul
       {li Having a type [('key, 'map) t] which doesn't depend on ['map] (i can depend on ['key]), in which case casting
           form [('key, 'a) t] to [('key, 'b) t] is always safe:
           {[
            type ('k, _) t = 'k list
            let cast : type a b. ('k, a) t -> ('k, b) t = fun x -> x
            let polyeq : type a b. ('k, a) t -> ('k, b) t -> bool = fun x y -> x = y
           ]}}
       {li Using a GADT type and examining its constructors to only return [true]
           when the constructors are equal:
           {[
              type (_, _) t =
                  | T_Int : int -> (unit, int) t
                  | T_Bool : bool -> (unit, bool) t
              let polyeq : type k a b. (k, a) t -> (k, b) t -> bool = fun x y ->
                  match x, y with
                  | T_Int i, T_Int j -> i = j (* Here type a = b = int, we can return true *)
                  | T_Bool i, T_Bool j -> i && j (* same here, but with a = b = bool *)
                  | _ -> false (* never return true on heterogeneous cases. *)
           ]}}
       {li Using physical equality:
           {[
              let polyeq a b = a == Obj.magic b
           ]}
           While this contains an [Obj.magic], it is still type safe (OCaml just compares
           the immediate values) and we can safely cast values from one type to the
           other if they satisfy this (since they are already physically equal).

           This is the implementation used in {!HeterogeneousHashedValue}. Note however that
           using this function can lead to {b identifiers no longer being unique across
           types}. See {!HASHED_VALUE.polyeq} for more information on this.}} *)
end

module HashedValue : HASHED_VALUE with type 'a t = 'a
(** Generic implementation of {!HASHED_VALUE}.
    Uses {{: https://ocaml.org/api/Hashtbl.html#VALhash}[Hashtbl.hash]} for hashing
    and physical equality for equality.
    Note that this may lead to maps of different types having the same identifier
    ({!MakeHashconsedMap.get_id}), see the documentation of {!HASHED_VALUE.polyeq}
    for details on this. *)

module HeterogeneousHashedValue : HETEROGENEOUS_HASHED_VALUE with type ('k, 'm) t = 'm
(** Generic implementation of {!HETEROGENEOUS_HASHED_VALUE}.
    Uses {{: https://ocaml.org/api/Hashtbl.html#VALhash}[Hashtbl.hash]} for hashing
    and physical equality for equality.
    Note that this may lead to maps of different types having the same identifier
    ({!MakeHashconsedHeterogeneousMap.get_id}), see the documentation of
    {!HASHED_VALUE.polyeq} for details on this. *)


(** {1 Functors} *)
(** This section presents the functors which can be used to build patricia tree
    maps and sets. *)

(** {2 Homogeneous maps and sets} *)
(** These are homogeneous maps and set, their keys/elements are a single
    non-generic type, just like the standard library's [Map] and [Set] modules. *)

module MakeMap(Key: KEY) : MAP with type key = Key.t
module MakeSet(Key: KEY) : SET with type elt = Key.t

(** {2 Heterogeneous maps and sets} *)
(** Heterogeneous maps are ['map map], which store bindings of ['key key]
    to [('key, 'map) value], where ['key key] is a GADT, as we must be able
    to compare keys of different types together.

    Similarly, heterogeneous sets store sets of ['key key]. *)

module MakeHeterogeneousSet(Key: HETEROGENEOUS_KEY) : HETEROGENEOUS_SET
  with type 'a elt = 'a Key.t
module MakeHeterogeneousMap(Key: HETEROGENEOUS_KEY)(Value: HETEROGENEOUS_VALUE) : HETEROGENEOUS_MAP
  with type 'a key = 'a Key.t
   and type ('k,'m) value = ('k,'m) Value.t


(** {2 Maps and sets with custom nodes} *)
(** We can also customize the representation and creation of nodes, to
    gain space or time.

    Possibitities include having weak key and/or values, hash-consing,
    giving unique number to nodes or keeping them in sync with the
    disk, lazy evaluation and/or caching, adding size information for
    constant time [cardinal] functions, etc.

    See {!node_impl} for the provided implementations of {!NODE}, or create your own. *)

(** Create a homogeneous map with a custom {!NODE}. Also allows
    customizing the map values *)
module MakeCustomMap
    (Key: KEY)
    (Value: VALUE)
    (Node: NODE with type 'a key = Key.t and type ('key,'map) value = ('key, 'map Value.t) snd)
  : MAP_WITH_VALUE
    with type key = Key.t
     and type 'm value = 'm Value.t
     and type 'm t = 'm Node.t


(** Create a homogeneous set with a custom {!NODE}.
    @since v0.10.0 *)
module MakeCustomSet
    (Key: KEY)
    (Node: NODE with type 'a key = Key.t and type ('key,'map) value = unit)
  : SET
    with type elt = Key.t
     and type 'a BaseMap.t = 'a Node.t

(** Create an heterogeneous map with a custom {!NODE}. *)
module MakeCustomHeterogeneousMap
    (Key: HETEROGENEOUS_KEY)
    (Value: HETEROGENEOUS_VALUE)
    (Node: NODE with type 'a key = 'a Key.t and type ('key,'map) value = ('key,'map) Value.t)
  : HETEROGENEOUS_MAP
    with type 'a key = 'a Key.t
     and type ('k,'m) value = ('k,'m) Value.t
     and type 'm t = 'm Node.t

(** Create an heterogeneous set with a custom {!NODE}.
    @since v0.10.0 *)
module MakeCustomHeterogeneousSet
    (Key: HETEROGENEOUS_KEY)
    (NODE: NODE with type 'a key = 'a Key.t and type ('key,'map) value = unit)
  : HETEROGENEOUS_SET
    with type 'a elt = 'a Key.t
     and type 'a BaseMap.t = 'a NODE.t

(** {2:hash_consed Hash-consed maps and sets} *)
(** Hash-consed maps and sets uniquely number each of their nodes.
    Upon creation, they check whether a similar node has been created before,
    if so they return it, else they return a new node with a new number.
    With this unique numbering:
    - [equal] and [compare] become constant time operations;
    - two maps with the same bindings (where keys compared by {!KEY.to_int} and
      values by {!HASHED_VALUE.polyeq}) will always be physically equal;
    - functions that benefit from sharing, like {!BASE_MAP.idempotent_union} and
      {!BASE_MAP.idempotent_inter} will see improved performance;
    - constructors are slightly slower, as they now require a hash-table lookup;
    - memory usage is increased: nodes store their tags inside themselves, and
      a global hash-table of all built nodes must be maintained;
    - hash-consed maps assume their values are immutable;
    - {b WARNING:} when using physical equality as {!HASHED_VALUE.polyeq}, some
      {b maps of different types may be given the same identifier}. See the end of
      the documentation of {!HASHED_VALUE.polyeq} for details.
      Note that this is the case in the default implementations {!HashedValue}
      and {!HeterogeneousHashedValue}.

    All hash-consing functors are {b generative}, since each functor call will
    create a new hashtable to store the created nodes. Calling a functor
    twice with same arguments will lead to two numbering systems for identifiers,
    and thus the types should not be considered compatible.  *)

(** Hash-consed version of {!MAP}. See {!hash_consed} for the differences between
    hash-consed and non hash-consed maps.

    @since v0.10.0 *)
module MakeHashconsedMap(Key: KEY)(Value: HASHED_VALUE)() : sig
  include MAP_WITH_VALUE with type key = Key.t and type 'a value = 'a Value.t (** @closed *)

  val get_id : 'a t -> int
  (** Returns the {{!hash_consed}hash-consed} id of the map.
      Unlike {!NODE_WITH_ID.get_id}, hash-consing ensures that maps
      which contain the same keys (compared by {!KEY.to_int}) and values (compared
      by {!HASHED_VALUE.polyeq}) will always be physically equal
      and have the same identifier.

      Note that when using physical equality as {!HASHED_VALUE.polyeq}, some
      maps of different types [a t] and [b t] may be given the same identifier.
      See the end of the documentation of {!HASHED_VALUE.polyeq} for details. *)

  val equal : 'a t -> 'a t -> bool
  (** Constant time equality using the {{!hash_consed}hash-consed} nodes identifiers.
      This is equivalent to physical equality.
      Two nodes are equal if their trees contain the same bindings,
      where keys are compare by {!KEY.to_int} and values are compared by
      {!HASHED_VALUE.polyeq}. *)

  val compare : 'a t -> 'a t -> int
  (** Constant time comparison using the {{!hash_consed}hash-consed} node identifiers.
      This order is fully arbitrary, but it is total and can be used to sort nodes.
      It is based on node ids which depend on the order in which the nodes where created
      (older nodes having smaller ids).

      One useful property of this order is that
      child nodes will always have a smaller identifier than their parents. *)
end

(** Hash-consed version of {!SET}. See {!hash_consed} for the differences between
    hash-consed and non hash-consed sets.

    @since v0.10.0 *)
module MakeHashconsedSet(Key: KEY)() : sig
  include SET with type elt = Key.t (** @closed *)

  val get_id : t -> int
  (** Returns the {{!hash_consed}hash-consed} id of the map.
      Unlike {!NODE_WITH_ID.get_id}, hash-consing ensures that maps
      which contain the same keys (compared by {!KEY.to_int}) and values (compared
      by {!HASHED_VALUE.polyeq}) will always be physically equal
      and have the same identifier.

      Note that when using physical equality as {!HASHED_VALUE.polyeq}, some
      maps of different types [a t] and [b t] may be given the same identifier.
      See the end of the documentation of {!HASHED_VALUE.polyeq} for details. *)

  val equal : t -> t -> bool
  (** Constant time equality using the {{!hash_consed}hash-consed} nodes identifiers.
      This is equivalent to physical equality.
      Two nodes are equal if their trees contain the same bindings,
      where keys are compare by {!KEY.to_int} and values are compared by
      {!HASHED_VALUE.polyeq}. *)

  val compare : t -> t -> int
  (** Constant time comparison using the {{!hash_consed}hash-consed} node identifiers.
      This order is fully arbitrary, but it is total and can be used to sort nodes.
      It is based on node ids which depend on the order in which the nodes where created
      (older nodes having smaller ids).

      One useful property of this order is that
      child nodes will always have a smaller identifier than their parents. *)
end

(** Hash-consed version of {!HETEROGENEOUS_SET}.  See {!hash_consed} for the differences between
    hash-consed and non hash-consed sets.

    @since v0.10.0 *)
module MakeHashconsedHeterogeneousSet(Key: HETEROGENEOUS_KEY)() : sig
  include HETEROGENEOUS_SET with type 'a elt = 'a Key.t (** @closed *)

  val get_id : t -> int
  (** Returns the {{!hash_consed}hash-consed} id of the map.
      Unlike {!NODE_WITH_ID.get_id}, hash-consing ensures that maps
      which contain the same keys (compared by {!KEY.to_int}) and values (compared
      by {!HASHED_VALUE.polyeq}) will always be physically equal
      and have the same identifier.

      Note that when using physical equality as {!HASHED_VALUE.polyeq}, some
      maps of different types [a t] and [b t] may be given the same identifier.
      See the end of the documentation of {!HASHED_VALUE.polyeq} for details. *)

  val equal : t -> t -> bool
  (** Constant time equality using the {{!hash_consed}hash-consed} nodes identifiers.
      This is equivalent to physical equality.
      Two nodes are equal if their trees contain the same bindings,
      where keys are compare by {!KEY.to_int} and values are compared by
      {!HASHED_VALUE.polyeq}. *)

  val compare : t -> t -> int
  (** Constant time comparison using the {{!hash_consed}hash-consed} node identifiers.
      This order is fully arbitrary, but it is total and can be used to sort nodes.
      It is based on node ids which depend on the order in which the nodes where created
      (older nodes having smaller ids).

      One useful property of this order is that
      child nodes will always have a smaller identifier than their parents. *)
end

(** Hash-consed version of {!HETEROGENEOUS_MAP}.  See {!hash_consed} for the differences between
    hash-consed and non hash-consed maps.

    @since v0.10.0 *)
module MakeHashconsedHeterogeneousMap(Key: HETEROGENEOUS_KEY)(Value: HETEROGENEOUS_HASHED_VALUE)() : sig
  include HETEROGENEOUS_MAP
      with type 'a key = 'a Key.t
      and type ('k,'m) value = ('k, 'm) Value.t (** @closed *)

  val get_id : 'a t -> int
  (** Returns the {{!hash_consed}hash-consed} id of the map.
      Unlike {!NODE_WITH_ID.get_id}, hash-consing ensures that maps
      which contain the same keys (compared by {!KEY.to_int}) and values (compared
      by {!HASHED_VALUE.polyeq}) will always be physically equal
      and have the same identifier.

      Note that when using physical equality as {!HASHED_VALUE.polyeq}, some
      maps of different types [a t] and [b t] may be given the same identifier.
      See the end of the documentation of {!HASHED_VALUE.polyeq} for details. *)

  val equal : 'a t -> 'a t -> bool
  (** Constant time equality using the {{!hash_consed}hash-consed} nodes identifiers.
      This is equivalent to physical equality.
      Two nodes are equal if their trees contain the same bindings,
      where keys are compare by {!KEY.to_int} and values are compared by
      {!HASHED_VALUE.polyeq}. *)

  val compare : 'a t -> 'a t -> int
  (** Constant time comparison using the {{!hash_consed}hash-consed} node identifiers.
      This order is fully arbitrary, but it is total and can be used to sort nodes.
      It is based on node ids which depend on the order in which the nodes where created
      (older nodes having smaller ids).

      One useful property of this order is that
      child nodes will always have a smaller identifier than their parents. *)
end


(** {1:node_impl Some implementations of NODE} *)
(** We provide a few different implementations of {!NODE}, they can be used with
    the {!MakeCustomMap}, {!MakeCustomSet}, {!MakeCustomHeterogeneousMap} and
    {!MakeCustomHeterogeneousSet} functors. *)

(** {2 Basic nodes} *)

(** This module is such that ['map t = 'map view].
    This is the node used in {!MakeHeterogeneousMap} and {!MakeMap}. *)
module SimpleNode(Key: sig type 'k t end)(Value: HETEROGENEOUS_VALUE) : NODE
  with type 'a key = 'a Key.t
   and type ('key,'map) value = ('key,'map) Value.t

(** Here, nodes also contain a unique id, e.g. so that they can be
    used as keys of maps or hashtables. *)
module NodeWithId(Key: sig type 'k t end)(Value: HETEROGENEOUS_VALUE) : NODE_WITH_ID
  with type 'a key = 'a Key.t
   and type ('key,'map) value = ('key,'map) Value.t


(* Maybe: we can make variations around NodeWithId; e.g. a version
    that does HashConsing, or a version that replicates the node to a
    key-value store on disk, etc. *)

(** An optimized representation for sets, i.e. maps to unit: we do not
    store a reference to unit (note that you can further optimize when
    you know the representation of the key).
    This is the node used in {!MakeHeterogeneousSet} and {!MakeSet}. *)
module SetNode(Key: sig type 'k t end) : NODE
  with type 'a key = 'a Key.t
   and type ('key,'map) value = unit

(** {2 Weak nodes} *)

(** NODE used to implement weak key hashes (the key-binding pair is an
    Ephemeron, the reference to the key is weak, and if the key is
    garbage collected, the binding disappears from the map *)
module WeakNode(Key: sig type 'k t end)(Value: HETEROGENEOUS_VALUE) : NODE
  with type 'a key = 'a Key.t
   and type ('key,'map) value = ('key,'map) Value.t

(** Both a {!WeakNode} and a {!SetNode}, useful to implement Weak sets.  *)
module WeakSetNode(Key: sig type 'k t end) : NODE
  with type 'a key = 'a Key.t
   and type ('key,'map) value = unit


(** {2 Hashconsed nodes} *)

(** Gives a unique number to each node like {!NodeWithId},
    but also performs hash-consing. So two maps with the same bindings will
    always be physically equal. See {!hash_consed} for more details on this.

    Using these nodes with multiple {!MakeCustomMap} functors will result in
    all those maps being hash-consed (stored in the same hash table, same numbering system).

    @since v0.10.0 *)
module HashconsedNode(Key: HETEROGENEOUS_KEY)(Value: HETEROGENEOUS_HASHED_VALUE)() : HASH_CONSED_NODE
  with type 'a key = 'a Key.t
   and type ('key,'map) value = ('key, 'map) Value.t

(** Both a {!HashconsedNode} and a {!SetNode}.
    @since v0.10.0 *)
module HashconsedSetNode(Key: HETEROGENEOUS_KEY)() : HASH_CONSED_NODE
  with type 'a key = 'a Key.t
   and type ('key,'map) value = unit

(* TODO: Functor to make sets from maps. *)
(* TODO: A possibility of customizing the fixpoint in the recursive
   calls, so that we can cache operations or make lazy some of the
   operations. *)
