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

(** {1 Signatures} *)

(** The integer associated with a key *)
type intkey = int

(** A mask is an integer with a single bit set (i.e. a power of 2). *)
type mask = int

module type NODE = sig
  type 'key key
  type ('key, 'map) value
  type 'map t

  val empty : 'map t
  val leaf : 'key key -> ('key, 'map) value -> 'map t
  val branch :
    prefix:intkey ->
    branching_bit:mask -> tree0:'map t -> tree1:'map t -> 'map t

  type 'map view = private
    | Empty : 'map view
    | Branch : { prefix : intkey; branching_bit : mask;
                 tree0 : 'map t; tree1 : 'map t; } -> 'map view
    | Leaf : { key : 'key key; value : ('key, 'map) value; } -> 'map view

  val is_empty: 'map t -> bool
  val view: 'a t -> 'a view
end

module type NODE_WITH_ID = sig
  include NODE
  val get_id: 'a t -> int
end

module type BASE_MAP = sig
  include NODE

  type 'map key_value_pair =
      KeyValue : 'a key * ('a, 'map) value -> 'map key_value_pair
  val unsigned_min_binding : 'a t -> 'a key_value_pair
  val unsigned_max_binding : 'a t -> 'a key_value_pair
  val singleton : 'a key -> ('a, 'b) value -> 'b t
  val cardinal : 'a t -> int
  val is_singleton : 'a t -> 'a key_value_pair option
  val find : 'key key -> 'map t -> ('key, 'map) value
  val find_opt : 'key key -> 'map t -> ('key, 'map) value option
  val mem : 'key key -> 'map t -> bool
  val remove : 'key key -> 'map t -> 'map t
  val pop_unsigned_minimum: 'map t -> ('map key_value_pair * 'map t) option
  val pop_unsigned_maximum: 'map t -> ('map key_value_pair * 'map t) option

  val insert: 'a key -> (('a,'map) value option -> ('a,'map) value) -> 'map t -> 'map t
  val update: 'a key -> (('a,'map) value option -> ('a,'map) value option) -> 'map t -> 'map t
  val add : 'key key -> ('key, 'map) value -> 'map t -> 'map t
  val split : 'key key -> 'map t -> 'map t * ('key, 'map) value option * 'map t

  type 'map polyiter = { f : 'a. 'a key -> ('a, 'map) value -> unit; } [@@unboxed]
  val iter : 'map polyiter -> 'map t -> unit

  type ('acc,'map) polyfold = { f: 'a. 'a key -> ('a,'map) value -> 'acc -> 'acc } [@@unboxed]
  val fold : ('acc,'map) polyfold -> 'map t -> 'acc -> 'acc

  type ('acc,'map) polyfold2 = { f: 'a. 'a key -> ('a,'map) value -> ('a,'map) value -> 'acc -> 'acc } [@@unboxed]
  val fold_on_nonequal_inter : ('acc,'map) polyfold2 -> 'map t -> 'map t -> 'acc -> 'acc

  type ('acc,'map) polyfold2_union = { f: 'a. 'a key -> ('a,'map) value option -> ('a,'map) value option -> 'acc -> 'acc } [@@unboxed]
  val fold_on_nonequal_union : ('acc,'map) polyfold2_union -> 'map t -> 'map t -> 'acc -> 'acc

  type 'map polypredicate = { f: 'a. 'a key -> ('a,'map) value -> bool; } [@@unboxed]
  val filter : 'map polypredicate -> 'map t -> 'map t
  val for_all : 'map polypredicate -> 'map t -> bool

  type ('map1,'map2) polymap = { f : 'a. ('a, 'map1) value -> ('a, 'map2) value; } [@@unboxed]
  val map : ('map,'map) polymap -> 'map t -> 'map t
  val map_no_share : ('map1,'map2) polymap -> 'map1 t -> 'map2 t

  type ('map1,'map2) polymapi =
    { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value; } [@@unboxed]
  val mapi : ('map,'map) polymapi -> 'map t -> 'map t
  val mapi_no_share : ('map1,'map2) polymapi -> 'map1 t -> 'map2 t

  type ('map1,'map2) polyfilter_map =
    { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value option; } [@@unboxed]
  val filter_map : ('map,'map) polyfilter_map -> 'map t -> 'map t
  val filter_map_no_share : ('map1,'map2) polyfilter_map -> 'map1 t -> 'map2 t

  type 'map polypretty = { f: 'a. Format.formatter -> 'a key -> ('a, 'map) value -> unit } [@@unboxed]
  val pretty :
    ?pp_sep:(Format.formatter -> unit -> unit) -> 'map polypretty ->
    Format.formatter -> 'map t -> unit

  type ('map1,'map2) polysame_domain_for_all2 =
    { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value -> bool; } [@@unboxed]
  val reflexive_same_domain_for_all2 :
    ('map,'map) polysame_domain_for_all2 -> 'map t -> 'map t -> bool
  val nonreflexive_same_domain_for_all2:
    ('map1,'map2) polysame_domain_for_all2 -> 'map1 t -> 'map2 t -> bool
  val reflexive_subset_domain_for_all2 :
    ('map,'map) polysame_domain_for_all2 -> 'map t -> 'map t -> bool

  type ('map1, 'map2, 'map3) polyunion = {
    f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value -> ('a, 'map3) value; } [@@unboxed]
  val idempotent_union : ('a, 'a, 'a) polyunion -> 'a t -> 'a t -> 'a t


  type ('map1, 'map2, 'map3) polyinter = {
    f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value -> ('a, 'map3) value;
  } [@@unboxed]
  val idempotent_inter : ('a, 'a, 'a) polyinter -> 'a t -> 'a t -> 'a t
  val nonidempotent_inter_no_share :('a, 'b, 'c) polyinter -> 'a t -> 'b t -> 'c t


  type ('map1, 'map2, 'map3) polyinterfilter = { f : 'a. 'a key -> ('a, 'map1) value -> ('a, 'map2) value -> ('a, 'map3) value option; } [@@unboxed]
  val idempotent_inter_filter : ('a, 'a, 'a) polyinterfilter -> 'a t -> 'a t -> 'a t

  type ('map1, 'map2, 'map3) polymerge = {
    f : 'a. 'a key -> ('a, 'map1) value option -> ('a, 'map2) value option -> ('a, 'map3) value  option; } [@@unboxed]
  val slow_merge : ('map1, 'map2, 'map3) polymerge -> 'map1 t -> 'map2 t -> 'map3 t
  val disjoint : 'a t -> 'a t -> bool

  val to_seq : 'a t -> 'a key_value_pair Seq.t
  val to_rev_seq : 'a t -> 'a key_value_pair Seq.t
  val add_seq : 'a key_value_pair Seq.t -> 'a t -> 'a t
  val of_seq : 'a key_value_pair Seq.t -> 'a t

  val of_list : 'a key_value_pair list -> 'a t
  val to_list : 'a t -> 'a key_value_pair list
end

(** {2 Heterogeneous maps and sets} *)

module type HETEROGENEOUS_MAP = sig
  include BASE_MAP

  module WithForeign(Map2:BASE_MAP with type 'a key = 'a key):sig
    type ('map1,'map2) polyinter_foreign = { f: 'a. 'a key -> ('a,'map1) value -> ('a,'map2) Map2.value -> ('a,'map1) value } [@@unboxed]

    val nonidempotent_inter : ('a,'b) polyinter_foreign -> 'a t -> 'b Map2.t -> 'a t

    type ('map2,'map1) polyfilter_map_foreign =
      { f : 'a. 'a key -> ('a, 'map2) Map2.value -> ('a, 'map1) value option; } [@@unboxed]
    val filter_map_no_share : ('map2,'map1) polyfilter_map_foreign -> 'map2 Map2.t -> 'map1 t
    (** Like {!BASE_MAP.filter_map_no_share}, but allows to transform a foreigh map into the current one. *)

    type ('map1,'map2) polyupdate_multiple = { f: 'a. 'a key -> ('a,'map1) value option -> ('a,'map2) Map2.value -> ('a,'map1) value option } [@@unboxed]
    val update_multiple_from_foreign : 'b Map2.t -> ('a,'b) polyupdate_multiple -> 'a t -> 'a t

    type ('map1,'map2) polyupdate_multiple_inter = { f: 'a. 'a key -> ('a,'map1) value -> ('a,'map2) Map2.value -> ('a,'map1) value option } [@@unboxed]
    val update_multiple_from_inter_with_foreign : 'b Map2.t -> ('a,'b) polyupdate_multiple_inter -> 'a t -> 'a t
  end
end


module type HETEROGENEOUS_SET = sig
  type 'a elt

  module BaseMap : HETEROGENEOUS_MAP
    with type 'a key = 'a elt
     and type (_,_) value = unit

  type t = unit BaseMap.t
  type 'a key = 'a elt

  type any_elt = Any : 'a elt -> any_elt

  val empty: t
  val is_empty: t -> bool
  val mem: 'a elt -> t -> bool
  val add: 'a elt -> t -> t
  val singleton: 'a elt -> t
  val cardinal: t -> int
  val is_singleton: t -> any_elt option
  val remove: 'a elt -> t -> t
  val unsigned_min_elt: t -> any_elt
  val unsigned_max_elt: t -> any_elt
  val pop_unsigned_minimum: t -> (any_elt * t) option
  val pop_unsigned_maximum: t -> (any_elt * t) option
  val union: t -> t -> t
  val inter: t -> t -> t
  val disjoint: t -> t -> bool
  val equal : t -> t -> bool
  val subset : t -> t -> bool
  val split: 'a elt -> t -> t * bool * t
  type polyiter = { f: 'a. 'a elt -> unit; } [@@unboxed]
  val iter: polyiter -> t -> unit

  type polypredicate = { f: 'a. 'a elt -> bool; } [@@unboxed]
  val filter: polypredicate -> t -> t
  val for_all: polypredicate -> t -> bool

  type 'acc polyfold = { f: 'a. 'a elt -> 'acc -> 'acc } [@@unboxed]
  val fold: 'acc polyfold -> t -> 'acc -> 'acc

  type polypretty = { f: 'a. Format.formatter -> 'a elt -> unit; } [@@unboxed]
  val pretty :
    ?pp_sep:(Format.formatter -> unit -> unit) -> polypretty -> Format.formatter -> t -> unit

  val to_seq : t -> any_elt Seq.t
  val to_rev_seq : t -> any_elt Seq.t
  val add_seq : any_elt Seq.t -> t -> t
  val of_seq : any_elt Seq.t -> t

  val of_list : any_elt list -> t
  val to_list : t -> any_elt list
end


(** {2 Homogeneous maps and sets} *)

(** Signature for sets implemented using Patricia trees. *)
module type SET = sig
  type elt

  module BaseMap : HETEROGENEOUS_MAP
    with type _ key = elt
     and type (_,_) value = unit

  type key = elt
  type t = unit BaseMap.t

  val empty: t
  val is_empty: t -> bool
  val mem: elt -> t -> bool
  val add: elt -> t -> t
  val singleton: elt -> t
  val cardinal: t -> int
  val is_singleton: t -> elt option
  val remove: elt -> t -> t
  val unsigned_min_elt: t -> elt
  val unsigned_max_elt: t -> elt
  val pop_unsigned_minimum: t -> (elt * t) option
  val pop_unsigned_maximum: t -> (elt * t) option
  val iter: (elt -> unit) -> t -> unit
  val filter: (elt -> bool) -> t -> t
  val for_all: (elt -> bool) -> t -> bool
  val fold: (elt -> 'b -> 'b) -> t -> 'b -> 'b
  val split: elt -> t -> t * bool * t
  val pretty :
    ?pp_sep:(Format.formatter -> unit -> unit) ->
    (Format.formatter -> elt -> unit) ->
    Format.formatter -> t -> unit
  val union: t -> t -> t
  val inter: t -> t -> t
  val disjoint: t -> t -> bool
  val equal : t -> t -> bool
  val subset : t -> t -> bool
  val to_seq : t -> elt Seq.t
  val to_rev_seq : t -> elt Seq.t
  val add_seq : elt Seq.t -> t -> t
  val of_seq : elt Seq.t -> t

  val of_list : elt list -> t
  val to_list : t -> elt list
end

type (_, 'b) snd = Snd of 'b [@@unboxed]

(** The signature for maps with a single type for keys and values. *)
module type MAP = sig
  type key
  type 'a t

  module BaseMap : HETEROGENEOUS_MAP
   with type 'a t = 'a t
    and type _ key = key
    and type ('a,'b) value = ('a,'b) snd

  val empty : 'a t
  val is_empty : 'a t -> bool
  val unsigned_min_binding : 'a t -> (key * 'a)
  val unsigned_max_binding : 'a t -> (key * 'a)
  val singleton : key -> 'a -> 'a t
  val cardinal : 'a t -> int
  val is_singleton : 'a t -> (key * 'a) option
  val find : key -> 'a t -> 'a
  val find_opt : key -> 'a t -> 'a option
  val mem : key -> 'a t -> bool
  val remove : key -> 'a t -> 'a t
  val pop_unsigned_minimum : 'a t -> (key * 'a * 'a t) option
  val pop_unsigned_maximum : 'a t -> (key * 'a * 'a t) option
  val insert : key -> ('a option -> 'a) -> 'a t -> 'a t
  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val split : key -> 'a t -> 'a t * 'a option * 'a t
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val fold : (key -> 'a -> 'acc -> 'acc) ->  'a t -> 'acc -> 'acc
  val fold_on_nonequal_inter : (key -> 'a -> 'a -> 'acc -> 'acc) ->
    'a t -> 'a t -> 'acc -> 'acc
  val fold_on_nonequal_union :
    (key -> 'a option -> 'a option -> 'acc -> 'acc) ->
    'a t -> 'a t -> 'acc -> 'acc
  val filter : (key -> 'a -> bool) -> 'a t -> 'a t
  val for_all : (key -> 'a -> bool) -> 'a t -> bool
  val map : ('a -> 'a) -> 'a t -> 'a t
  val map_no_share : ('a -> 'b) -> 'a t -> 'b t
  val mapi : (key -> 'a -> 'a) -> 'a t -> 'a t
  val mapi_no_share : (key -> 'a -> 'b) -> 'a t -> 'b t
  val filter_map : (key -> 'a -> 'a option) -> 'a t -> 'a t
  val filter_map_no_share : (key -> 'a -> 'b option) -> 'a t -> 'b t
  val reflexive_same_domain_for_all2 : (key -> 'a -> 'a -> bool) -> 'a t -> 'a t ->  bool
  val nonreflexive_same_domain_for_all2 : (key -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool
  val reflexive_subset_domain_for_all2 : (key -> 'a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val idempotent_union : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
  val idempotent_inter : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
  val nonidempotent_inter_no_share : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val idempotent_inter_filter : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
  val slow_merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
  val disjoint : 'a t -> 'a t -> bool

  module WithForeign(Map2 : BASE_MAP with type _ key = key):sig
    type ('b,'c) polyfilter_map_foreign = { f: 'a. key -> ('a,'b) Map2.value -> 'c option } [@@unboxed]
    val filter_map_no_share : ('b, 'c) polyfilter_map_foreign -> 'b Map2.t ->  'c t

    type ('value,'map2) polyinter_foreign =
      { f: 'a. 'a Map2.key -> 'value -> ('a, 'map2) Map2.value -> 'value  } [@@unboxed]
    val nonidempotent_inter : ('a, 'b) polyinter_foreign -> 'a t -> 'b Map2.t -> 'a t

    type ('map1,'map2) polyupdate_multiple = { f: 'a. key -> 'map1 option -> ('a,'map2) Map2.value -> 'map1 option } [@@unboxed]
    val update_multiple_from_foreign : 'b Map2.t -> ('a,'b) polyupdate_multiple -> 'a t -> 'a t

    type ('map1,'map2) polyupdate_multiple_inter = { f: 'a. key -> 'map1 -> ('a,'map2) Map2.value -> 'map1 option } [@@unboxed]
    val update_multiple_from_inter_with_foreign : 'b Map2.t -> ('a,'b) polyupdate_multiple_inter -> 'a t -> 'a t
  end

  val pretty :
    ?pp_sep:(Format.formatter -> unit -> unit) ->
    (Format.formatter -> key -> 'a -> unit) ->
    Format.formatter -> 'a t -> unit

  val to_seq : 'a t -> (key * 'a) Seq.t
  val to_rev_seq : 'a t -> (key * 'a) Seq.t
  val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t
  val of_seq : (key * 'a) Seq.t -> 'a t

  val of_list : (key * 'a) list -> 'a t
  val to_list : 'a t -> (key * 'a) list
end


(** {2 Keys and Value} *)

module type KEY = sig
  type t
  val to_int: t -> int
end

type (_,_) cmp = Eq: ('a,'a) cmp | Diff: ('a,'b) cmp

module type HETEROGENEOUS_KEY = sig
  type 'key t
  val to_int: ('key) t -> int
  val polyeq: 'a t -> 'b t -> ('a,'b) cmp
end

module type VALUE = sig
  type ('key,'map) t
end

(** {1 Utility functions} *)

(** Fast highest bit computation in c, using GCC's __builtin_clz
    which compile to efficient instruction (bsr) when possible. *)
external highest_bit: int -> (int[@untagged]) =
  "caml_int_builtin_highest_bit_byte" "caml_int_builtin_highest_bit" [@@noalloc]

let unsigned_lt x y = x - min_int < y - min_int
  (* if x >= 0 && y >= 0
  then x < y
  else if x >= 0
    then (* pos < neg *) true
    else if y >= 0 then false
    else x < y *)

(** Note: in the original version, okasaki give the masks as arguments
    to optimize the computation of highest_bit. *)
let branching_bit a b = highest_bit (a lxor b)

let mask i m = i land (lnot (2*m-1))

(** {1 Nodes} *)

(** Simple node, with no hash consing. *)
module [@inline] SimpleNode(Key:sig type 'a t end)(Value:VALUE) = struct
  type 'a key = 'a Key.t
  type ('key,'map) value = ('key,'map) Value.t

  type 'map view =
    | Empty: 'map view
    | Branch: {prefix:intkey;branching_bit:mask;tree0:'map t;tree1:'map t} -> 'map view
    | Leaf: {key:'key key; value:('key,'map) value} -> 'map view
  and 'map t = 'map view
  let view x = x

  let empty = Empty
  let is_empty x = x == Empty
  let leaf key value  = Leaf {key;value}
  let branch ~prefix ~branching_bit ~tree0 ~tree1 =
    match tree0,tree1 with
    | Empty, x -> x
    | x, Empty -> x
    | _ -> Branch{prefix;branching_bit;tree0;tree1}
end

module WeakNode(Key:sig type 'a t end)(Value:VALUE)(* :NODE *) = struct
  type 'a key = 'a Key.t
  type ('key,'map) value = ('key,'map) Value.t

  type 'map view =
    | Empty: 'map view
    | Branch: {prefix:intkey;branching_bit:mask;tree0:'map t;tree1:'map t} -> 'map view
    | Leaf: {key:'key key; value:('key,'map) value} -> 'map view
  and 'a t =
    | TEmpty: 'map t
    | TBranch: {prefix:intkey;branching_bit:mask;tree0:'map t;tree1:'map t} -> 'map t
    (* Additional hidden case: leaf, which is an Ephemeron.K1, whose
       tag is 251, so it can be discriminated against the other
       cases. This avoids an indirection. *)

  let empty = TEmpty
  let is_empty x = x == TEmpty
  let leaf key value = Obj.magic (Ephemeron.K1.make key value)
  let branch ~prefix ~branching_bit ~tree0 ~tree1 =
    match tree0,tree1 with
    | TEmpty, x -> x
    | x, TEmpty -> x
    | _ -> TBranch{prefix;branching_bit;tree0;tree1}

  let view (type k) (type map) (t:map t) =
    let obj = Obj.repr t in
    if Obj.is_block obj && Obj.tag obj != 0 then
      (* Ephemeron.K1.get_(key|value) are no longer available in 5.0,
         so we do that instead. *)
      let ephe:Obj.Ephemeron.t = Obj.magic obj in
      let key:k key option = Obj.magic @@ Obj.Ephemeron.get_key ephe 0 in
      let data:(k,map) Value.t option = Obj.magic @@ Obj.Ephemeron.get_data ephe in
      match key,data with
      | Some key, Some value -> Leaf{key;value}
      | _ -> Empty
    else match t with
    | TEmpty -> Empty
    | TBranch{prefix;branching_bit;tree0;tree1} -> Branch{prefix;branching_bit;tree0;tree1}

end


(** Add a unique id to nodes, e.g. so that they can be used as keys in maps or sets.  *)
module NodeWithId(Key:sig type 'a t end)(Value:VALUE):NODE_WITH_ID
  with type 'key key = 'key Key.t
   and type ('key,'map) value = ('key,'map) Value.t
= struct

  type 'a key = 'a Key.t
  type ('key,'map) value = ('key,'map) Value.t

  type 'map view =
    | Empty: 'map view
    | Branch: {prefix:intkey;branching_bit:mask;tree0:'map t;tree1:'map t} -> 'map view
    | Leaf: {key:'key key; value:('key,'map) value} -> 'map view
  and 'map t =
    | NEmpty: 'map t
    | NBranch: {prefix:intkey;branching_bit:mask;tree0:'map t;tree1:'map t;id:int} -> 'map t
    | NLeaf: {key:'key key;value:('key,'map) value;id:int} -> 'map t

  let view = function
    | NEmpty -> Empty
    | NBranch{prefix;branching_bit;tree0;tree1;_} -> Branch{prefix;branching_bit;tree0;tree1}
    | NLeaf{key;value;_} -> Leaf{key;value}

  let get_id = function
    | NEmpty -> 0
    | NBranch{id;_} -> id
    | NLeaf{id;_} -> id

  let count = ref 0;;

  let empty = NEmpty
  let is_empty x = x == NEmpty
  let leaf key value = incr count; NLeaf {key;value;id=(!count)}
  let branch ~prefix ~branching_bit ~tree0 ~tree1 =
    match tree0,tree1 with
    | NEmpty, x -> x
    | x, NEmpty -> x
    | _ -> incr count; NBranch{prefix;branching_bit;tree0;tree1;id=(!count)}

end


(** NODE for sets, i.e. when there is no associated values.  *)
module SetNode(Key:sig type 'a t end):NODE
  with type 'key key = 'key Key.t
   and type ('key,'map) value = unit
= struct

  type 'a key = 'a Key.t
  type ('key,'map) value = unit

  type 'map view =
    | Empty: 'map view
    | Branch: {prefix:intkey;branching_bit:mask;tree0:'map t;tree1:'map t} -> 'map view
    | Leaf: {key:'key key; value:('key,'map) value} -> 'map view
  and 'map t =
    | NEmpty: 'map t
    | NBranch: {prefix:intkey;branching_bit:mask;tree0:'map t;tree1:'map t} -> 'map t
    | NLeaf: {key:'key key} -> 'map t


  let view = function
    | NEmpty -> Empty
    | NBranch{prefix;branching_bit;tree0;tree1} -> Branch{prefix;branching_bit;tree0;tree1}
    | NLeaf{key} -> Leaf{key;value=()}

  let empty = NEmpty
  let is_empty x = x == NEmpty
  let leaf key _value = NLeaf {key}
  let branch ~prefix ~branching_bit ~tree0 ~tree1 =
    match tree0,tree1 with
    | NEmpty, x -> x
    | x, NEmpty -> x
    | _ -> NBranch{prefix;branching_bit;tree0;tree1}

end

module WeakSetNode(Key:sig type 'a t end)(* :NODE *) = struct
  type 'a key = 'a Key.t
  type ('key,'map) value = unit

  type 'map view =
    | Empty: 'map view
    | Branch: {prefix:intkey;branching_bit:mask;tree0:'map t;tree1:'map t} -> 'map view
    | Leaf: {key:'key key; value:('key,'map) value} -> 'map view
  and 'a t =
    | TEmpty: 'map t
    | TBranch: {prefix:intkey;branching_bit:mask;tree0:'map t;tree1:'map t} -> 'map t
    (* Additional hidden case: leaf, which is a Weak array, whose tag
       is 251, so it can be discriminated against the other
       cases. This avoids an indirection. *)

  let empty = TEmpty
  let is_empty x = x == TEmpty
  let leaf key () = Obj.magic (let a = Weak.create 1 in Weak.set a 0 (Some key))
  let branch ~prefix ~branching_bit ~tree0 ~tree1 =
    match tree0,tree1 with
    | TEmpty, x -> x
    | x, TEmpty -> x
    | _ -> TBranch{prefix;branching_bit;tree0;tree1}

  let view t =
    let obj = Obj.repr t in
    if Obj.is_block obj && Obj.tag obj != 0 then
      let weak = Obj.magic obj in
      let key = Weak.get weak 0 in
      match key with
      | Some key -> Leaf{key;value=()}
      | _ -> Empty
    else  match t with          (* Identity in memory. *)
    | TEmpty -> Empty
    | TBranch{prefix;branching_bit;tree0;tree1} -> Branch{prefix;branching_bit;tree0;tree1}

end

module MakeCustomHeterogeneous
    (Key:HETEROGENEOUS_KEY)
    (Value:VALUE)
    (NODE:NODE with type 'a key = 'a Key.t and type ('key,'map) value = ('key,'map) Value.t) :
  HETEROGENEOUS_MAP with type 'a key = 'a Key.t
                       and type ('key,'map) value = ('key,'map) Value.t
                       and type 'a t = 'a NODE.t
= struct

  (* We provide two versions: with or without hash-consing. Hash-consing
     allows faster implementations for the fold_on_diff* operations.
     Benchmarks seems to indicate that hashconsing and the more complex
     fold_on_diff are not very useful in practice (perhaps they would on
     huge structures?) *)

  (* With hash-consing of interior nodes: slower node construction, but
     faster comparison with fold_on_diff. *)

  (* module NODE = TNoHashCons;; *)
  include NODE

  type 'map key_value_pair = KeyValue: 'a Key.t * ('a,'map) value -> 'map key_value_pair
  let rec unsigned_min_binding x = match NODE.view x with
    | Empty -> raise Not_found
    | Leaf{key;value} -> KeyValue(key,value)
    | Branch{tree0;_} -> unsigned_min_binding tree0
  let rec unsigned_max_binding x = match NODE.view x with
    | Empty -> raise Not_found
    | Leaf{key;value} -> KeyValue(key,value)
    | Branch{tree1;_} -> unsigned_max_binding tree1


  (* Merge trees whose prefix disagree. *)
  let join pa treea pb treeb =
    (* Printf.printf "join %d %d\n" pa pb; *)
    let m = branching_bit pa pb in
    let p = mask pa (* for instance *) m in
    if (pa land m) = 0 then
      branch ~prefix:p ~branching_bit:m ~tree0:treea ~tree1:treeb
    else
      branch ~prefix:p ~branching_bit:m ~tree0:treeb ~tree1:treea


  (** [match_prefix k p m] returns [true] if and only if the key [k] has prefix [p] up to bit [m]. *)
  let match_prefix k p m = mask k m = p

  let singleton = leaf

  let rec cardinal m =
    match NODE.view m with
    | Empty -> 0
    | Leaf _ -> 1
    | Branch{tree0; tree1; _ } -> cardinal tree0 + cardinal tree1

  let is_singleton m =
    match NODE.view m with
    | Leaf{key;value} -> Some (KeyValue(key,value))
    | _ -> None

  let rec findint: type a map. a Key.t -> int -> map t -> (a,map) value =
    fun witness searched m -> match NODE.view m with
      | Leaf{key;value} -> begin
          match Key.polyeq key witness with
          | Eq -> value
          | Diff -> raise Not_found
        end
      | Branch{branching_bit;tree0;tree1;_} ->
        (* Optional if not (match_prefix searched prefix branching_bit) then raise Not_found
           else *) if (branching_bit land searched == 0)
        then findint witness searched tree0
        else findint witness searched tree1
      | Empty -> raise Not_found
  let find searched m = findint searched (Key.to_int searched) m

  let rec split: type a map. a key -> int -> map t -> map t * ((a,map) value) option * map t =
    fun split_key split_key_int m -> match NODE.view m with
      | Leaf{key;value} -> begin
          match Key.polyeq key split_key with
          | Eq -> NODE.empty, Some value, NODE.empty
          | Diff ->
            if unsigned_lt (Key.to_int key) split_key_int then
              m, None, NODE.empty else NODE.empty, None, m
        end
      | Branch{prefix;branching_bit;tree0;tree1} ->
          if not (match_prefix split_key_int prefix branching_bit) then
            if unsigned_lt prefix split_key_int
            then m, None, NODE.empty
            else NODE.empty, None, m
          else if (branching_bit land split_key_int == 0) then
            let left, found, right = split split_key split_key_int tree0 in
            left, found, NODE.branch ~prefix ~branching_bit ~tree0:right ~tree1
          else
            let left, found, right = split split_key split_key_int tree1 in
            NODE.branch ~prefix ~branching_bit ~tree0 ~tree1:left, found, right
      | Empty -> NODE.empty, None, NODE.empty

  let split k m = split k (Key.to_int k) m

  let find_opt searched m = match find searched m with
    | x -> Some x
    | exception Not_found -> None

  let mem searched m =
    match findint searched (Key.to_int searched) m with
    | exception Not_found -> false
    | _ -> true

  type ('map1,'map2) polymapi = { f: 'a. 'a Key.t -> ('a,'map1) Value.t -> ('a,'map2) Value.t } [@@unboxed]
  let rec mapi (f:('map1,'map1) polymapi) m = match NODE.view m with
    | Empty -> empty
    | Leaf{key;value} ->
      let newval = (f.f key value) in
      if newval == value
      then m
      else leaf key newval
    | Branch{prefix;branching_bit;tree0;tree1} ->
      let newtree0 = mapi f tree0 in
      let newtree1 = mapi f tree1 in
      if tree0 == newtree0 && tree1 == newtree1 then m
      else branch ~prefix ~branching_bit ~tree0:newtree0 ~tree1:newtree1


  (* MAYBE: A map (and map_filter) homogeneous, that try to preserve physical equality. *)
  let rec mapi_no_share (f:('map1,'map2) polymapi) m = match NODE.view m with
    | Empty -> empty
    | Leaf{key;value} -> leaf key (f.f key value)
    | Branch{prefix;branching_bit;tree0;tree1} ->
        let tree0 = mapi_no_share f tree0 in
        let tree1 = mapi_no_share f tree1 in
        branch ~prefix ~branching_bit ~tree0 ~tree1

  type ('map1,'map2) polymap = { f: 'a. ('a,'map1) Value.t -> ('a,'map2) Value.t } [@@unboxed]
  let map (f:('map1,'map1) polymap) m = mapi { f=fun _ v -> f.f v } m
  let map_no_share (f:('map1,'map2) polymap) m = mapi_no_share { f=fun _ v -> f.f v } m

  type ('map1,'map2) polyfilter_map = { f: 'a. 'a Key.t -> ('a,'map1) Value.t -> ('a,'map2) Value.t option } [@@unboxed]
  let rec filter_map (f:('map1,'map1) polyfilter_map) m = match NODE.view m with
    | Empty -> empty
    | Leaf{key;value} ->
      (match f.f key value with
       | None -> empty
       | Some newval -> if newval == value then m else leaf key newval)
    | Branch{prefix;branching_bit;tree0;tree1} ->
      let newtree0 = filter_map f tree0 in
      let newtree1 = filter_map f tree1 in
      if tree0 == newtree0 && tree1 == newtree1 then m
      else branch ~prefix ~branching_bit ~tree0:newtree0 ~tree1:newtree1

  let rec filter_map_no_share (f:('b,'c) polyfilter_map) m = match NODE.view m with
    | Empty -> empty
    | Leaf{key;value} -> (match (f.f key value) with Some v -> leaf key v | None -> empty)
    | Branch{prefix;branching_bit;tree0;tree1} ->
        let tree0 = filter_map_no_share f tree0 in
        let tree1 = filter_map_no_share f tree1 in
        branch ~prefix ~branching_bit ~tree0 ~tree1

  type 'map polypretty = { f: 'a. Format.formatter -> 'a Key.t -> ('a, 'map) Value.t -> unit } [@@unboxed]
  let rec pretty ?(pp_sep=Format.pp_print_cut) (f : 'map polypretty) fmt m =
    match NODE.view m with
    | Empty -> ()
    | Leaf{key;value} -> (f.f fmt key value)
    | Branch{tree0; tree1; _} ->
        pretty f ~pp_sep fmt tree0;
        pp_sep fmt ();
        pretty f ~pp_sep fmt tree1

  let rec removeint to_remove m = match NODE.view m with
    | Leaf{key;_} when (Key.to_int key) == to_remove -> empty
    | (Empty | Leaf _) -> m
    | Branch{prefix;branching_bit;tree0;tree1} ->
      if (branching_bit land to_remove) == 0
      then begin
        let tree0' = removeint to_remove tree0 in
        if tree0' == empty then tree1
        else if tree0' == tree0 then m
        else branch ~prefix ~branching_bit ~tree0:tree0' ~tree1
      end
      else begin
        let tree1' = removeint to_remove tree1 in
        if tree1' == empty then tree0
        else if tree1' == tree1 then m
        else branch ~prefix ~branching_bit ~tree0 ~tree1:tree1'
      end

  let remove to_remove m = removeint (Key.to_int to_remove) m

  let rec pop_unsigned_minimum m = match NODE.view m with
    | Empty -> None
    | Leaf{key;value} -> Some (KeyValue(key,value),empty)
    | Branch{prefix;branching_bit;tree0;tree1} ->
      match pop_unsigned_minimum tree0 with
      | None -> pop_unsigned_minimum tree1
      | Some(res,tree0') ->
          let restree =
            if is_empty tree0' then tree1
            else branch ~prefix ~branching_bit ~tree0:tree0' ~tree1
          in Some(res,restree)

  let rec pop_unsigned_maximum m = match NODE.view m with
    | Empty -> None
    | Leaf{key;value} -> Some (KeyValue(key,value),empty)
    | Branch{prefix;branching_bit;tree0;tree1} ->
      match pop_unsigned_maximum tree1 with
      | None -> pop_unsigned_maximum tree0
      | Some(res,tree1') ->
          let restree =
            if is_empty tree1' then tree0
            else branch ~prefix ~branching_bit ~tree0 ~tree1:tree1'
          in Some(res,restree)

  let insert: type a map. a Key.t -> ((a,map) Value.t option -> (a,map) Value.t) -> map t -> map t =
    fun thekey f t ->
    let thekeyint = Key.to_int thekey in
    (* Preserve physical equality whenever possible. *)
    let exception Unmodified in
    try
      let rec loop t = match NODE.view t with
        | Empty -> leaf thekey (f None)
        | Leaf{key;value=old} ->
          begin match Key.polyeq key thekey with
            | Eq ->
              let newv = f (Some old) in
              if newv == old then raise Unmodified
              else leaf key newv
            | Diff ->
              let keyint = (Key.to_int key) in
              join thekeyint (leaf thekey (f None)) keyint t
          end
        | Branch{prefix;branching_bit;tree0;tree1} ->
          if match_prefix thekeyint prefix branching_bit then
            if (thekeyint land branching_bit) == 0
            then branch ~prefix ~branching_bit ~tree0:(loop tree0) ~tree1
            else branch ~prefix ~branching_bit ~tree0 ~tree1:(loop tree1)
          else join thekeyint (leaf thekey (f None)) prefix t
      in loop t
    with Unmodified -> t

  (* XXXX: This is a better update, that can also remove element, depending on how the join between the old and new values goes.
     Can be useful (e.g. when join is top), I should export that, maybe replace insert with it. *)
  (* TODO: Test. *)
  let update: type a map. a Key.t -> ((a,map) Value.t option -> (a,map) Value.t option) -> map t -> map t =
    fun thekey f t ->
    let thekeyint = Key.to_int thekey in
    (* Preserve physical equality whenever possible. *)
    let exception Unmodified in
    try
      let rec loop t = match NODE.view t with
        | Empty -> begin
            match (f None) with
            | None -> raise Unmodified
            | Some v -> leaf thekey v
          end
        | Leaf{key;value=old} ->
          begin match Key.polyeq key thekey with
            | Eq ->
              let newv = f (Some old) in
              begin match newv with
                | None -> empty
                | Some newv when newv == old -> raise Unmodified
                | Some newv -> leaf key newv end
            | Diff ->
              let keyint = (Key.to_int key) in
              begin match f None with
                | None -> raise Unmodified
                | Some value -> join thekeyint (leaf thekey value) keyint t
              end
          end
        | Branch{prefix;branching_bit;tree0;tree1} ->
          if match_prefix thekeyint prefix branching_bit then
            if (thekeyint land branching_bit) == 0
            then branch ~prefix ~branching_bit ~tree0:(loop tree0) ~tree1
            else branch ~prefix ~branching_bit ~tree0 ~tree1:(loop tree1)
          else begin match f None with
            | None -> raise Unmodified
            | Some value -> join thekeyint (leaf thekey value) prefix t
          end
      in loop t
    with Unmodified -> t

  (* Note: Insert is a bit weird, I am not sure it should be exported. *)
  type 'map polyinsert = { f: 'a . key:'a Key.t -> old:('a,'map) Value.t -> value:('a,'map) Value.t -> ('a,'map) Value.t } [@@unboxed]
  let insert_for_union: type a map. map polyinsert -> a Key.t -> (a,map) Value.t -> map t -> map t =
    fun f thekey value t ->
    let thekeyint = Key.to_int thekey in
    (* Preserve physical equality whenever possible. *)
    let exception Unmodified in
    try
      let rec loop t = match NODE.view t with
        | Empty -> leaf thekey value
        | Leaf{key;value=old} ->
          begin match Key.polyeq key thekey with
            | Eq ->
              if value == old then raise Unmodified else
              let newv = f.f ~key ~old ~value in
              if newv == old then raise Unmodified
              else leaf key newv
            | Diff ->
              let keyint = (Key.to_int key) in
              join thekeyint (leaf thekey value) keyint t
          end
        | Branch{prefix;branching_bit;tree0;tree1} ->
          if match_prefix thekeyint prefix branching_bit then
            if (thekeyint land branching_bit) == 0
            then branch ~prefix ~branching_bit ~tree0:(loop tree0) ~tree1
            else branch ~prefix ~branching_bit ~tree0 ~tree1:(loop tree1)
          else join thekeyint (leaf thekey value) prefix t
      in loop t
    with Unmodified -> t

  let add key value t = insert key (fun _ -> value) t

  type ('map1,'map2) polysame_domain_for_all2 = { f: 'a 'b. 'a Key.t -> ('a,'map1) Value.t -> ('a,'map2) Value.t -> bool } [@@unboxed]
  (* Fast equality test between two maps. *)
  let rec reflexive_same_domain_for_all2 f ta tb = match (NODE.view ta),(NODE.view tb) with
    | _ when ta == tb -> true (* Skip same subtrees thanks to reflexivity. *)
    | Empty, _ | _, Empty -> false
    | Leaf _, Branch _ | Branch _, Leaf _ -> false
    | Leaf{key=keya;value=valuea}, Leaf{key=keyb;value=valueb} ->
      begin match Key.polyeq keya keyb with
        | Diff -> false
        | Eq -> f.f keya valuea valueb
      end
    | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
      Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
      pa == pb && ma == mb &&
      reflexive_same_domain_for_all2 f ta0 tb0 &&
      reflexive_same_domain_for_all2 f ta1 tb1

  let rec nonreflexive_same_domain_for_all2 f ta tb = match (NODE.view ta),(NODE.view tb) with
    | Empty, _ | _, Empty -> false
    | Leaf _, Branch _ | Branch _, Leaf _ -> false
    | Leaf{key=keya;value=valuea}, Leaf{key=keyb;value=valueb} ->
      begin match Key.polyeq keya keyb with
        | Diff -> false
        | Eq -> f.f keya valuea valueb
      end
    | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
      Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
      pa == pb && ma == mb &&
      nonreflexive_same_domain_for_all2 f ta0 tb0 &&
      nonreflexive_same_domain_for_all2 f ta1 tb1

  let rec reflexive_subset_domain_for_all2 f ta tb = match (NODE.view ta),(NODE.view tb) with
    | _ when ta == tb -> true   (* Skip same subtrees thanks to reflexivity. *)
    | Empty, _ -> true
    | _, Empty -> false
    | Branch _, Leaf _ -> false
    | Leaf {key=keya;value=valuea}, viewb ->
      (* Reimplement find locally, mostly because of typing issues
         (which could be solved if we had a version of find that
         returns a (key,value) pair. *)
      let searched = Key.to_int keya in
      let rec search = function
        | Leaf{key=keyb;value=valueb} ->
          begin match Key.polyeq keya keyb with
            | Diff -> false
            | Eq -> f.f keya valuea valueb
          end
        | Branch{branching_bit;tree0;tree1;_} ->
          if (branching_bit land searched == 0)
          then search (NODE.view tree0)
          else search (NODE.view tree1)
        | Empty -> assert false (* We already saw that tb is not empty. *)
      in search viewb
    | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
      Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
      if ma == mb && pa == pb
      (* Same prefix: divide the search. *)
      then
        (reflexive_subset_domain_for_all2 f ta0 tb0) &&
        (reflexive_subset_domain_for_all2 f ta1 tb1)
        (* Case where ta have to be included in one of tb0 or tb1. *)
      else if unsigned_lt ma mb && match_prefix pa pb mb
      then if mb land pa == 0
        then reflexive_subset_domain_for_all2 f ta tb0
        else reflexive_subset_domain_for_all2 f ta tb1
        (* Any other case: there are elements in ta that are unmatched in tb. *)
      else false

  let rec disjoint ta tb =
    if ta == tb then is_empty ta
    else match NODE.view ta,NODE.view tb with
      | Empty, _ | _, Empty -> true
      | Leaf{key;_},_ -> not (mem key tb)
      | _,Leaf{key;_} -> not (mem key ta)
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: check both subtrees *)
        then disjoint ta0 tb0 && disjoint ta1 tb1
        else if unsigned_lt mb ma && match_prefix pb pa ma (* tb included in ta0 or ta1 *)
        then if ma land pb == 0
          then disjoint ta0 tb
          else disjoint ta1 tb
        else if unsigned_lt ma mb && match_prefix pa pb mb (* ta included in tb0 or tb1 *)
        then if mb land pa == 0
          then disjoint ta tb0
          else disjoint ta tb1
        else true (* Different prefixes => no intersection *)

  type ('map1,'map2,'map3) polyunion = { f: 'a. 'a Key.t -> ('a,'map1) Value.t -> ('a,'map2) Value.t -> ('a,'map3) Value.t } [@@unboxed]
  let rec idempotent_union f ta tb =
    if ta == tb then ta
    else
      match NODE.view ta,NODE.view tb with
      | Empty, _ -> tb
      | _, Empty -> ta
      | Leaf{key;value},_ -> insert_for_union ({f=fun ~key ~old ~value -> f.f key value old}) key value tb
      | _,Leaf{key;value} -> insert_for_union ({f=fun ~key ~old ~value -> f.f key old value}) key value ta
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: merge the subtrees *)
        then
          (* MAYBE: if ta0 == tb0 and ta1 == tb1, we can return ta (or
             tb). Probably not useful. *)
          let tree0 = idempotent_union f ta0 tb0 in
          let tree1 = idempotent_union f ta1 tb1 in
          branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
        else if unsigned_lt mb ma && match_prefix pb pa ma
        then if ma land pb == 0
          then branch ~prefix:pa ~branching_bit:ma ~tree0:(idempotent_union f ta0 tb) ~tree1:ta1
          else branch ~prefix:pa ~branching_bit:ma ~tree0:ta0 ~tree1:(idempotent_union f ta1 tb)
        else if unsigned_lt ma mb && match_prefix pa pb mb
        then if mb land pa == 0
          then branch ~prefix:pb ~branching_bit:mb ~tree0:(idempotent_union f ta tb0) ~tree1:tb1
          else branch ~prefix:pb ~branching_bit:mb ~tree0:tb0 ~tree1:(idempotent_union f ta tb1)
        else join pa ta pb tb

  type ('map1,'map2,'map3) polyinter = { f: 'a. 'a Key.t -> ('a,'map1) Value.t -> ('a,'map2) Value.t -> ('a,'map3) Value.t } [@@unboxed]
  let rec idempotent_inter f ta tb =
    if ta == tb then ta
    else match NODE.view ta,NODE.view tb with
      | Empty, _ | _, Empty -> empty
      | Leaf{key;value},_ ->
        (try let res = find key tb in
            if res == value then ta else
            let newval = f.f key value res in
            if newval == value then ta else
            leaf key newval
         with Not_found -> empty)
      | _,Leaf{key;value} ->
        (try let res = find key ta in
            if res == value then tb else
            let newval = f.f key res value in
            if newval == value then tb else
            leaf key newval
         with Not_found -> empty)
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: merge the subtrees *)
        then
          let tree0 = idempotent_inter f ta0 tb0 in
          let tree1 = idempotent_inter f ta1 tb1 in
          branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
        else if unsigned_lt mb ma && match_prefix pb pa ma
        then if ma land pb == 0
          then idempotent_inter f ta0 tb
          else idempotent_inter f ta1 tb
        else if unsigned_lt ma mb && match_prefix pa pb mb
        then if mb land pa == 0
          then idempotent_inter f ta tb0
          else idempotent_inter f ta tb1
        else empty

  (* Same as above, without the same subtree optimisation. *)
  let rec nonidempotent_inter_no_share f ta tb =
    match NODE.view ta,NODE.view tb with
    | Empty, _ | _, Empty -> empty
    | Leaf{key;value},_ ->
      (try let res = find key tb in
         leaf key (f.f key value res)
       with Not_found -> empty)
    | _,Leaf{key;value} ->
      (try let res = find key ta in
         leaf key (f.f key res value)
       with Not_found -> empty)
    | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
      Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
      if ma == mb && pa == pb
      (* Same prefix: merge the subtrees *)
      then
        let tree0 = nonidempotent_inter_no_share f ta0 tb0 in
        let tree1 = nonidempotent_inter_no_share f ta1 tb1 in
        branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
      else if unsigned_lt mb ma && match_prefix pb pa ma
      then if ma land pb == 0
        then nonidempotent_inter_no_share f ta0 tb
        else nonidempotent_inter_no_share f ta1 tb
      else if unsigned_lt ma mb && match_prefix pa pb mb
      then if mb land pa == 0
        then nonidempotent_inter_no_share f ta tb0
        else nonidempotent_inter_no_share f ta tb1
      else empty

  type ('map1,'map2,'map3) polyinterfilter = { f: 'a. 'a Key.t -> ('a,'map1) Value.t -> ('a,'map2) Value.t -> ('a,'map3) Value.t option } [@@unboxed]
  let rec idempotent_inter_filter f ta tb =
    if ta == tb then ta
    else match NODE.view ta,NODE.view tb with
      | Empty, _ | _, Empty -> empty
      | Leaf{key;value},_ ->
        (try let res = find key tb in
           if res == value then ta else
           match (f.f key value res) with
           | Some v when v == value -> ta
           | Some v -> leaf key v
           | None -> empty
         with Not_found -> empty)
      | _,Leaf{key;value} ->
        (try let res = find key ta in
           if res == value then tb else
           match f.f key res value with
           | Some v when v == value -> tb
           | Some v -> leaf key v
           | None -> empty
         with Not_found -> empty)
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: merge the subtrees *)
        then
          let tree0 = idempotent_inter_filter f ta0 tb0 in
          let tree1 = idempotent_inter_filter f ta1 tb1 in
          branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
        else if unsigned_lt mb ma && match_prefix pb pa ma
        then if ma land pb == 0
          then idempotent_inter_filter f ta0 tb
          else idempotent_inter_filter f ta1 tb
        else if unsigned_lt ma mb && match_prefix pa pb mb
        then if mb land pa == 0
          then idempotent_inter_filter f ta tb0
          else idempotent_inter_filter f ta tb1
        else empty

  type ('map1,'map2,'map3) polymerge = { f: 'a. 'a Key.t -> ('a,'map1) Value.t option -> ('a,'map2) Value.t option -> ('a,'map3) Value.t option } [@@unboxed]
  let rec slow_merge: type mapa mapb mapc. (mapa,mapb,mapc) polymerge -> mapa NODE.t -> mapb NODE.t -> mapc NODE. t=
    fun f ta tb ->
    let upd_ta ta = filter_map_no_share {f=fun key value -> f.f key (Some value) None} ta in
    let upd_tb tb = filter_map_no_share {f=fun key value -> f.f key None (Some value)} tb in
    let oldf = f in
    match NODE.view ta,NODE.view tb with
    | Empty, _ -> upd_tb tb
    | _, Empty -> upd_ta ta
    | Leaf{key;value},_ ->
      let found = ref false in
      let f: type a. a Key.t -> (a,mapb) Value.t -> (a,mapc) Value.t option = fun curkey curvalue ->
        match Key.polyeq curkey key with
        | Eq -> found:= true; f.f key (Some value) (Some curvalue)
        | Diff -> f.f curkey None (Some curvalue) in
      let res = filter_map_no_share {f} tb in
      (* If the key of the leaf is not present, add it back.  Note
         that it breaks the assumption that merge is done in ascending
         number of keys; if we wanted that, we would need a
         "filter_map_no_share_add_key" function.  *)
      if !found then res
      else begin
        match oldf.f key (Some value) None with
        | None -> res
        | Some value -> add key value res
      end
    | _, Leaf{key;value} ->
      let found = ref false in
      let f: type a. a Key.t -> (a,mapa) Value.t -> (a,mapc) Value.t option = fun curkey curvalue ->
        match Key.polyeq curkey key with
        | Eq -> found := true; f.f key (Some curvalue) (Some value)
        | Diff -> f.f curkey (Some curvalue) None in
      let res = filter_map_no_share {f} ta in
      if !found then res
      else begin
        match oldf.f key None (Some value) with
        | None -> res
        | Some value -> add key value res
      end
    | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
      Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
      if ma == mb && pa == pb
      (* Same prefix: merge the subtrees *)
      then
        branch ~prefix:pa ~branching_bit:ma ~tree0:(slow_merge f ta0 tb0) ~tree1:(slow_merge f ta1 tb1)
      else if unsigned_lt mb ma && match_prefix pb pa ma
      then if ma land pb == 0
        then branch ~prefix:pa ~branching_bit:ma ~tree0:(slow_merge f ta0 tb) ~tree1:(upd_ta ta1)
        else branch ~prefix:pa ~branching_bit:ma ~tree0:(upd_ta ta0) ~tree1:(slow_merge f ta1 tb)
      else if unsigned_lt ma mb && match_prefix pa pb mb
      then if mb land pa == 0
        then branch ~prefix:pb ~branching_bit:mb ~tree0:(slow_merge f ta tb0) ~tree1:(upd_tb tb1)
        else branch ~prefix:pb ~branching_bit:mb ~tree0:(upd_tb tb0) ~tree1:(slow_merge f ta tb1)
      else join pa (upd_ta ta) pb (upd_tb tb)

  type 'map polyiter = { f: 'a. 'a Key.t -> ('a,'map) Value.t -> unit } [@@unboxed]
  let rec iter f x = match NODE.view x with
    | Empty -> ()
    | Leaf{key;value} -> f.f key value
    | Branch{tree0;tree1;_} -> iter f tree0; iter f tree1

  type ('acc,'map) polyfold = { f: 'a. 'a Key.t -> ('a,'map) Value.t -> 'acc -> 'acc } [@@unboxed]
  let rec fold f m acc = match NODE.view m with
    | Empty -> acc
    | Leaf{key;value} -> f.f key value acc
    | Branch{tree0;tree1;_} ->
      let acc = fold f tree0 acc in
      fold f tree1 acc


  type ('acc,'map) polyfold2 = { f: 'a. 'a key -> ('a,'map) value -> ('a,'map) value -> 'acc -> 'acc } [@@unboxed]
  let rec fold_on_nonequal_inter f ta tb acc =
    if ta == tb then acc
    else match NODE.view ta,NODE.view tb with
      | Empty, _ | _, Empty -> acc
      | Leaf{key;value},_ ->
        (try let valueb = find key tb in
           if valueb == value then acc else
             f.f key value valueb acc
         with Not_found -> acc)
      | _,Leaf{key;value} ->
        (try let valuea = find key ta in
           if valuea == value then acc else
             f.f key valuea value acc
         with Not_found -> acc)
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: fold on each subtrees *)
        then
          let acc = fold_on_nonequal_inter f ta0 tb0 acc in
          let acc = fold_on_nonequal_inter f ta1 tb1 acc in
          acc
        else if unsigned_lt mb ma && match_prefix pb pa ma
        then if ma land pb == 0
          then fold_on_nonequal_inter f ta0 tb acc
          else fold_on_nonequal_inter f ta1 tb acc
        else if unsigned_lt ma mb && match_prefix pa pb mb
        then if mb land pa == 0
          then fold_on_nonequal_inter f ta tb0 acc
          else fold_on_nonequal_inter f ta tb1 acc
        else acc


  type ('acc,'map) polyfold2_union =
    { f: 'a. 'a key -> ('a,'map) value option -> ('a,'map) value option ->
        'acc -> 'acc } [@@unboxed]
  let rec fold_on_nonequal_union:
    'm 'acc. ('acc,'m) polyfold2_union -> 'm t -> 'm t -> 'acc -> 'acc =
    fun (type m) f (ta:m t) (tb:m t) acc ->
    if ta == tb then acc
    else
      let fleft:(_,_) polyfold =
        {f=fun key value acc -> f.f key (Some value) None acc} in
      let fright:(_,_)polyfold =
        {f=fun key value acc -> f.f key None (Some value) acc} in
      match NODE.view ta,NODE.view tb with
      | Empty, _ -> fold fright tb acc
      | _, Empty -> fold fleft ta acc
      | Leaf{key;value},_ ->
        let ida = Key.to_int key in
        (* Fold on the rest, knowing that ida may or may not be in b. So we fold and use
           did_a to remember if we already did the call to a. *)
        (* We need to pass keya and valuea to the function to specify their types. *)
        let g (type a) (type b) (keya: a key) (keyb:b key)
            (valuea:(a,m) value) (valueb:(b,m) value) (acc,did_a) =
          let default() = (f.f keyb None (Some valueb) acc,did_a) in
          if did_a then default()
          else
            let idb = Key.to_int keyb in
            if unsigned_lt idb ida then default()
            else if unsigned_lt ida idb then
              let acc = f.f keya (Some valuea) None acc in
              let acc = f.f keyb None (Some valueb) acc in
              (acc,true)
            else match Key.polyeq keya keyb with
              | Eq ->
                if valuea == valueb then (acc,true)
                else (f.f keya (Some valuea) (Some valueb) acc,true)
              | Diff -> assert false (* Same id should be equal. *)
        in
        let (acc,found) = fold{f=fun keyb valueb acc -> g key keyb value valueb acc} tb (acc,false) in
        if found then acc
        else f.f key (Some value) None acc
      | _,Leaf{key;value} ->
        let idb = Key.to_int key in
        let g (type a) (type b) (keya: a key) (keyb:b key)
            (valuea:(a,m) value) (valueb:(b,m) value) (acc,did_b) =
          let default() = (f.f keya (Some valuea) None acc,did_b) in
          if did_b then default()
          else
            let ida = Key.to_int keya in
            if unsigned_lt ida idb then default()
            else if unsigned_lt idb ida then
              let acc = f.f keyb None (Some valueb) acc in
              let acc = f.f keya (Some valuea) None acc in
              (acc,true)
            else match Key.polyeq keya keyb with
              | Eq ->
                if valuea == valueb then (acc,true)
                else (f.f keya (Some valuea) (Some valueb) acc,true)
              | Diff -> assert false
        in
        let (acc,found) = fold{f=fun keya valuea acc -> g keya key valuea value acc} ta (acc,false) in
        if found then acc
        else f.f key None (Some value) acc
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: merge the subtrees *)
        then
          let acc = fold_on_nonequal_union f ta0 tb0 acc in
          let acc = fold_on_nonequal_union f ta1 tb1 acc in
          acc
        else if unsigned_lt mb ma && match_prefix pb pa ma
        then if ma land pb == 0
          then
            let acc = fold_on_nonequal_union f ta0 tb acc in
            let acc = fold fleft ta1 acc in
            acc
          else
            let acc = fold fleft ta0 acc in
            let acc = fold_on_nonequal_union f ta1 tb acc in
            acc
        else if unsigned_lt ma mb && match_prefix pa pb mb
        then if mb land pa == 0
          then
            let acc = fold_on_nonequal_union f ta tb0 acc in
            let acc = fold fright tb1 acc in
            acc
          else
            let acc = fold fright tb0 acc in
            let acc = fold_on_nonequal_union f ta tb1 acc in
            acc
        else
        (* Distinct subtrees: process them in increasing order of keys. *)
        if unsigned_lt pa pb then
          let acc = fold fleft ta acc in
          let acc = fold fright tb acc in
          acc
        else
          let acc = fold fright tb acc in
          let acc = fold fleft ta acc in
          acc
  ;;



  type 'map polypredicate = { f: 'a. 'a key -> ('a,'map) value -> bool; } [@@unboxed]
  let filter f m = filter_map {f = fun k v -> if f.f k v then Some v else None } m
  let rec for_all f m = match NODE.view m with
    | Empty -> true
    | Leaf{key;value} -> f.f key value
    | Branch{tree0; tree1; _ } -> for_all f tree0 && for_all f tree1

  module WithForeign(Map2:BASE_MAP with type 'a key = 'a key) = struct

    (* Intersects the first map with the values of the second map,
       trying to preserve physical equality of the first map whenever
       possible. *)
    type ('map1,'map2) polyinter_foreign = { f: 'a. 'a key -> ('a,'map1) value -> ('a,'map2) Map2.value -> ('a,'map1) value } [@@unboxed]
    let rec nonidempotent_inter f ta tb =
      match NODE.view ta,Map2.view tb with
      | Empty, _ | _, Empty -> NODE.empty
      | Leaf{key;value},_ ->
        (try let res = Map2.find key tb in
           let newval = (f.f key value res) in
           if newval == value then ta
           else NODE.leaf key newval
         with Not_found -> NODE.empty)
      | _,Leaf{key;value} ->
        (try let res = find key ta in
           NODE.leaf key (f.f key res value)
         with Not_found -> NODE.empty)
      | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
        Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
        if ma == mb && pa == pb
        (* Same prefix: merge the subtrees *)
        then
          let tree0 = (nonidempotent_inter f ta0 tb0) in
          let tree1 = (nonidempotent_inter f ta1 tb1) in
          if(ta0 == tree0 && ta1 == tree1)
          then ta
          else NODE.branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
        else if unsigned_lt mb ma && match_prefix pb pa ma
        then if ma land pb == 0
          then nonidempotent_inter f ta0 tb
          else nonidempotent_inter f ta1 tb
        else if unsigned_lt ma mb && match_prefix pa pb mb
        then if mb land pa == 0
          then nonidempotent_inter f ta tb0
          else nonidempotent_inter f ta tb1
        else NODE.empty

  type ('map2,'map1) polyfilter_map_foreign = { f: 'a. 'a Key.t -> ('a,'map2) Map2.value -> ('a,'map1) value option } [@@unboxed]
  let rec filter_map_no_share (f:('b,'c) polyfilter_map_foreign) m = match Map2.view m with
    | Empty -> empty
    | Leaf{key;value} -> (match (f.f key value) with Some v -> leaf key v | None -> empty)
    | Branch{prefix;branching_bit;tree0;tree1} ->
        let tree0 = filter_map_no_share f tree0 in
        let tree1 = filter_map_no_share f tree1 in
        branch ~prefix ~branching_bit ~tree0 ~tree1

  (** Add all the bindings in tb to ta (after transformation).  *)
  type ('map1,'map2) polyupdate_multiple = { f: 'a. 'a Key.t -> ('a,'map1) value option -> ('a,'map2) Map2.value -> ('a,'map1) value option } [@@unboxed]
  let rec update_multiple_from_foreign (tb:'map2 Map2.t) f (ta:'map1 t) =
    let upd_tb tb = filter_map_no_share {f=fun key value -> f.f key None value} tb in
    match NODE.view ta,Map2.view tb with
    | Empty, _ -> upd_tb tb
    | _, Empty -> ta
    | _,Leaf{key;value} -> update key (fun maybeval -> f.f key maybeval value) ta
    | Leaf{key;value},_ ->
      let found = ref false in
      let f: type a. a key -> (a,'map2) Map2.value -> (a,'map1) value option =
        fun curkey curvalue ->
          match Key.polyeq key curkey with
          | Eq -> found := true; f.f curkey (Some value) curvalue
          | Diff -> f.f curkey None curvalue
      in
      let res = filter_map_no_share {f} tb in
      if !found then res
      else add key value res
    | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
      Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
      if ma == mb && pa == pb
      (* Same prefix: merge the subtrees *)
      then
        let tree0 = update_multiple_from_foreign tb0 f ta0 in
        let tree1 = update_multiple_from_foreign tb1 f ta1 in
        if tree0 == ta0 && tree1 == ta1 then ta
        else branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
      else if unsigned_lt mb ma && match_prefix pb pa ma
      then if ma land pb == 0
        then
          let ta0' = update_multiple_from_foreign tb f ta0 in
          if ta0' == ta0 then ta
          else branch ~prefix:pa ~branching_bit:ma ~tree0:ta0' ~tree1:ta1
        else
          let ta1' = update_multiple_from_foreign tb f ta1 in
          if ta1' == ta1 then ta
          else branch ~prefix:pa ~branching_bit:ma ~tree0:ta0 ~tree1:ta1'
      else if unsigned_lt ma mb && match_prefix pa pb mb
      then if mb land pa == 0
        then
          let tree0 = update_multiple_from_foreign tb0 f ta in
          let tree1 = upd_tb tb1 in
          branch ~prefix:pb ~branching_bit:mb ~tree0 ~tree1
        else
          let tree0 = upd_tb tb0 in
          let tree1 = update_multiple_from_foreign tb1 f ta in
          branch ~prefix:pb ~branching_bit:mb ~tree0 ~tree1
      else join pa ta pb (upd_tb tb)


  (* Map difference: (possibly) remove from ta elements that are in tb, the other are preserved, no element is added. *)
  type ('map1,'map2) polyupdate_multiple_inter = { f: 'a. 'a Key.t -> ('a,'map1) value -> ('a,'map2) Map2.value -> ('a,'map1) value option } [@@unboxed]
  let rec update_multiple_from_inter_with_foreign tb f ta =
    match NODE.view ta, Map2.view tb with
    | Empty, _ -> ta
    | _, Empty -> ta
    | Leaf{key;value},_ ->
      begin match Map2.find key tb with
      | exception Not_found -> ta
      | foundv -> begin
          match f.f key value foundv with
          | None -> empty
          | Some v when v == value -> ta
          | Some v -> leaf key v
        end
      end
    | _,Leaf{key;value} ->
      update key (fun v -> match v with None -> None | Some v -> f.f key v value) ta
    | Branch{prefix=pa;branching_bit=ma;tree0=ta0;tree1=ta1},
      Branch{prefix=pb;branching_bit=mb;tree0=tb0;tree1=tb1} ->
      if ma == mb && pa == pb
      (* Same prefix: merge the subtrees *)
      then
        let tree0 = update_multiple_from_inter_with_foreign tb0 f ta0 in
        let tree1 = update_multiple_from_inter_with_foreign tb1 f ta1 in
        if tree0 == ta0 && tree1 == ta1 then ta
        else branch ~prefix:pa ~branching_bit:ma ~tree0 ~tree1
      else if unsigned_lt mb ma && match_prefix pb pa ma
      then if ma land pb == 0
        then
          let ta0' = update_multiple_from_inter_with_foreign tb f ta0 in
          if ta0' == ta0 then ta
          else branch ~prefix:pa ~branching_bit:ma ~tree0:ta0' ~tree1:ta1
        else
          let ta1' = update_multiple_from_inter_with_foreign tb f ta1 in
          if ta1' == ta1 then ta
          else branch ~prefix:pa ~branching_bit:ma ~tree0:ta0 ~tree1:ta1'
      else if unsigned_lt ma mb && match_prefix pa pb mb
      then if mb land pa == 0
        then update_multiple_from_inter_with_foreign tb0 f ta
        else update_multiple_from_inter_with_foreign tb1 f ta
      else ta
  end

  let rec to_seq m () = match NODE.view m with
    | Empty -> Seq.Nil
    | Leaf{key; value} -> Seq.Cons (KeyValue(key,value), Seq.empty)
    | Branch{tree0; tree1; _} -> Seq.append (to_seq tree0) (to_seq tree1) ()

  let rec to_rev_seq m () = match NODE.view m with
    | Empty -> Seq.Nil
    | Leaf{key; value} -> Seq.Cons (KeyValue(key,value), Seq.empty)
    | Branch{tree0; tree1; _} -> Seq.append (to_rev_seq tree1) (to_rev_seq tree0) ()

  let rec add_seq: type a. a key_value_pair Seq.t -> a t -> a t =
    fun s m -> match s () with
    | Seq.Nil -> m
    | Seq.Cons(KeyValue(key,value), s) -> add_seq s (add key value m)

  let of_seq s = add_seq s empty
  let of_list l = of_seq (List.to_seq l)
  let to_list m = List.of_seq (to_seq m)
end


(* TODO: We should make it a functor, so that we can simplify the
   interface for set independently from how it is constructed. *)
module MakeHeterogeneousSet(Key:HETEROGENEOUS_KEY) : HETEROGENEOUS_SET
  with type 'a elt = 'a Key.t = struct
  module NODE = SetNode(Key)
  module BaseMap = MakeCustomHeterogeneous(Key)(struct type ('a,'b) t = unit end)(NODE)

  (* No need to differentiate the values. *)
  include BaseMap

  type t = unit BaseMap.t
  type 'a elt = 'a key

  type any_elt = Any : 'a elt -> any_elt

  (* Note: as add is simpler, without any insertion function needed,
     maybe it is worth reimplementing it. *)
  let [@specialised] add key map = BaseMap.add key () map
  let singleton elt = singleton elt ()
  let is_singleton set = match BaseMap.is_singleton set with
    | None -> None
    | Some(KeyValue(k,())) -> Some(Any(k))

  (* Likewise with union and inter: we do not have to worry about
     reconciling the values here, so we could reimplement if the
     compiler is not smart enough. *)
  let [@specialised] union =
    let f:(unit,unit,unit) BaseMap.polyunion = {f=fun _ () () -> ()} in
    fun sa sb -> BaseMap.idempotent_union f sa sb

  let [@specialised] inter =
    let f:(unit,unit,unit) BaseMap.polyinter = {f=fun _ () () -> ()} in
    fun sa sb -> (BaseMap.idempotent_inter (* [@specialised] *)) f sa sb

  type polyiter = { f: 'a. 'a elt -> unit; } [@@unboxed]
  let iter f set = BaseMap.iter {f=fun k () -> f.f k} set

  (* TODO: A real implementation of fold would be faster. *)
  type 'acc polyfold = { f: 'a. 'a key -> 'acc -> 'acc } [@@unboxed]
  let fold f set acc =
    let f: type a. a key -> unit -> 'acc -> 'acc = fun k () acc -> f.f k acc in
    BaseMap.fold { f } set acc

  let unsigned_min_elt t = let KeyValue(m, ()) = BaseMap.unsigned_min_binding t in Any m
  let unsigned_max_elt t = let KeyValue(m, ()) = BaseMap.unsigned_max_binding t in Any m

  let pop_unsigned_maximum t = Option.map (fun (KeyValue(m,()),t) -> Any m,t) (BaseMap.pop_unsigned_maximum t)
  let pop_unsigned_minimum t = Option.map (fun (KeyValue(m,()),t) -> Any m,t) (BaseMap.pop_unsigned_minimum t)

  type polypretty = { f: 'a. Format.formatter -> 'a key -> unit; } [@@unboxed]
  let pretty ?pp_sep f fmt s = BaseMap.pretty ?pp_sep { f = fun fmt k () -> f.f fmt k} fmt s

  let equal t1 t2 = BaseMap.reflexive_same_domain_for_all2 {f=fun _ _ _ -> true} t1 t2
  let subset t1 t2 = BaseMap.reflexive_subset_domain_for_all2 {f=fun _ _ _ -> true} t1 t2

  let split k m = let (l, present, r) = BaseMap.split k m in
    (l, Option.is_some present, r)

  type polypredicate = { f: 'a. 'a key -> bool; } [@@unboxed]
  let filter f s = BaseMap.filter {f = fun k () -> f.f k } s
  let for_all f s = BaseMap.for_all {f = fun k () -> f.f k} s

  let to_seq m = Seq.map (fun (KeyValue(elt,())) -> Any elt) (BaseMap.to_seq m)
  let to_rev_seq m = Seq.map (fun (KeyValue(elt,())) -> Any elt) (BaseMap.to_rev_seq m)
  let add_seq s m = BaseMap.add_seq (Seq.map (fun (Any elt) -> KeyValue(elt,())) s) m

  let of_seq s = add_seq s empty
  let of_list l = of_seq (List.to_seq l)
  let to_list s = List.of_seq (to_seq s)
end

module MakeHeterogeneousMap(Key:HETEROGENEOUS_KEY)(Value:VALUE) =
  MakeCustomHeterogeneous(Key)(Value)(SimpleNode(Key)(Value))



module HomogeneousValue = struct
  type ('a,'map) t = 'map
end

module WrappedHomogeneousValue = struct
  type ('a, 'map) t = ('a, 'map) snd
end

module HeterogeneousKeyFromKey(Key:KEY):(HETEROGENEOUS_KEY with type 'a t = Key.t)  = struct
  type 'a t = Key.t

  (** The type-safe way to do it would be to define this type, to
      guarantee that 'a is always bound to the same type, and Eq is
      safe. But this requires a lot of conversion code, and identity
      functions that may not be well detected. [polyeq] is unsafe in
      that it allows arbitrary conversion of t1 by t2 in t1 t, but
      this unsafety is not exported, and I don't think we can do
      something wrong using it. *)
  (* type 'a t = K: Key.t -> unit t [@@unboxed] *)
  let polyeq: type a b. a t -> b t -> (a,b) cmp =
    fun a b -> match a,b with
      | a, b when (Key.to_int a) == (Key.to_int b) -> Obj.magic Eq
      | _ -> Diff
  let to_int = Key.to_int
end

module MakeCustom
    (Key:KEY)
    (NODE:NODE with type 'a key = Key.t and type ('key,'map) value = ('key,'map) snd)
= struct

  module NewKey(* :Key *) = HeterogeneousKeyFromKey(Key)

  module BaseMap = MakeCustomHeterogeneous(NewKey)(WrappedHomogeneousValue)(NODE)
  include BaseMap
  type key = Key.t

  let snd_opt = function
    | None -> None
    | Some x -> Some (Snd x)
  let opt_snd = function
    | None -> None
    | Some (Snd x) -> Some x
  let singleton k v = singleton k (Snd v)
  let find k m = let Snd x = find k m in x
  let find_opt k m = opt_snd (find_opt k m)
  let insert k f m = insert k (fun v -> Snd (f (opt_snd v))) m
  let update k f m = update k (fun v -> snd_opt (f (opt_snd v))) m
  let add k v m = add k (Snd v) m
  let split x m = let (l,m,r) = split x m in (l, opt_snd m, r)
  let unsigned_min_binding m = let KeyValue(key,Snd value) = BaseMap.unsigned_min_binding m in key,value
  let unsigned_max_binding m = let KeyValue(key,Snd value) = BaseMap.unsigned_max_binding m in key,value
  (* let singleton k v = BaseMap.singleton (PolyKey.K k) v *)
  let pop_unsigned_minimum m =
    match BaseMap.pop_unsigned_minimum m with
    | None -> None
    | Some(KeyValue(key,Snd value),m) -> Some(key,value,m)

  let pop_unsigned_maximum m =
    match BaseMap.pop_unsigned_maximum m with
    | None -> None
    | Some(KeyValue(key,Snd value),m) -> Some(key,value,m)

  let is_singleton m = match BaseMap.is_singleton m with
    | None -> None
    | Some(KeyValue(k,Snd v)) -> Some(k,v)

  let filter (f: key -> 'a -> bool) m = BaseMap.filter {f = fun k (Snd v) -> f k v} m
  let map f a = BaseMap.map {f = fun (Snd v) -> Snd (f v)} a
  let map_no_share f a = BaseMap.map_no_share {f = fun (Snd v) -> Snd (f v)} a
  let mapi (f : key -> 'a -> 'a) a = BaseMap.mapi {f = fun k (Snd v) -> Snd (f k v)} a
  let mapi_no_share (f : key -> 'a -> 'b) a = BaseMap.mapi_no_share {f = fun k (Snd v) -> Snd (f k v)} a
  let filter_map (f: key -> 'a -> 'a option) a =
    BaseMap.filter_map {f=fun k (Snd v) -> snd_opt (f k v) } a
  let filter_map_no_share (f: key -> 'a -> 'b option) a =
    BaseMap.filter_map_no_share {f=fun k (Snd v) -> snd_opt (f k v) } a
  let idempotent_union (f: key -> 'a -> 'a -> 'a) a b =
    BaseMap.idempotent_union {f=fun k (Snd v1) (Snd v2) -> Snd (f k v1 v2)} a b
  let idempotent_inter (f: key -> 'a -> 'a -> 'a) a b =
    BaseMap.idempotent_inter {f=fun k (Snd v1) (Snd v2) -> Snd (f k v1 v2)} a b
  let nonidempotent_inter_no_share (f: key -> 'a -> 'b -> 'c) a b =
    BaseMap.nonidempotent_inter_no_share {f=fun k (Snd v1) (Snd v2) -> Snd (f k v1 v2)} a b
  let idempotent_inter_filter (f: key -> 'a -> 'a -> 'a option) a b =
    BaseMap.idempotent_inter_filter {f=fun k (Snd v1) (Snd v2) -> snd_opt (f k v1 v2)} a b
  let reflexive_same_domain_for_all2 (f: key -> 'a -> 'a -> bool) a b =
    BaseMap.reflexive_same_domain_for_all2 {f=fun k (Snd v1) (Snd v2) -> f k v1 v2} a b
  let nonreflexive_same_domain_for_all2 (f: key -> 'a -> 'b -> bool) a b =
    BaseMap.nonreflexive_same_domain_for_all2 {f=fun k (Snd v1) (Snd v2) -> f k v1 v2} a b
  let reflexive_subset_domain_for_all2 (f: key -> 'a -> 'a -> bool) a b =
    BaseMap.reflexive_subset_domain_for_all2 {f=fun k (Snd v1) (Snd v2) -> f k v1 v2} a b
  let slow_merge (f : key -> 'a option -> 'b option -> 'c option) a b = BaseMap.slow_merge {f=fun k v1 v2 -> snd_opt (f k (opt_snd v1) (opt_snd v2))} a b
  let iter (f: key -> 'a -> unit) a = BaseMap.iter {f=fun k (Snd v) -> f k v} a
  let fold (f: key -> 'a -> 'acc) m acc = BaseMap.fold {f=fun k (Snd v) acc -> f k v acc} m acc
  let fold_on_nonequal_inter (f: key -> 'a -> 'b -> 'acc) ma mb acc =
    let f k (Snd va) (Snd vb) acc = f k va vb acc in
    BaseMap.fold_on_nonequal_inter {f} ma mb acc
  let fold_on_nonequal_union
      (f: key -> 'a option -> 'b option -> 'acc) ma mb acc =
    let f k va vb acc =
      let va = Option.map (fun (Snd v) -> v) va in
      let vb = Option.map (fun (Snd v) -> v) vb in
      f k va vb acc in
    BaseMap.fold_on_nonequal_union {f} ma mb acc

  let pretty ?pp_sep (f: Format.formatter -> key -> 'a -> unit) fmt m =
    BaseMap.pretty ?pp_sep {f=fun fmt k (Snd v) -> f fmt k v} fmt m

  let for_all (f : key -> 'a -> bool) m = BaseMap.for_all {f = fun k (Snd v) -> f k v} m

  module WithForeign(Map2 : BASE_MAP with type _ key = key) = struct
    module BaseForeign = BaseMap.WithForeign(Map2)
    type ('b,'c) polyfilter_map_foreign = { f: 'a. key -> ('a,'b) Map2.value -> 'c option } [@@unboxed]
    let filter_map_no_share f m2 =
      BaseForeign.filter_map_no_share { f=fun k v-> snd_opt (f.f k v)} m2


  type ('value,'map2) polyinter_foreign =
    { f: 'a. 'a Map2.key -> 'value -> ('a, 'map2) Map2.value -> 'value  } [@@unboxed]
  let nonidempotent_inter f m1 m2 =
    BaseForeign.nonidempotent_inter {f = fun k (Snd v) v2 -> Snd (f.f k v v2)} m1 m2

  type ('map1,'map2) polyupdate_multiple = { f: 'a. key -> 'map1 option -> ('a,'map2) Map2.value -> 'map1 option } [@@unboxed]
  let update_multiple_from_foreign m2 f m =
    BaseForeign.update_multiple_from_foreign m2 {f = fun k v1 v2 -> snd_opt (f.f k (opt_snd v1) v2)} m

  type ('map1,'map2) polyupdate_multiple_inter = { f: 'a. key -> 'map1 -> ('a,'map2) Map2.value -> 'map1 option } [@@unboxed]
  let update_multiple_from_inter_with_foreign m2 f m =
    BaseForeign.update_multiple_from_inter_with_foreign m2 {f = fun k (Snd v1) v2 -> snd_opt (f.f k v1 v2)} m
  end

  let to_seq m = Seq.map (fun (KeyValue(key,Snd value)) -> (key,value)) (BaseMap.to_seq m)
  let to_rev_seq m = Seq.map (fun (KeyValue(key,Snd value)) -> (key,value)) (BaseMap.to_rev_seq m)
  let add_seq s m = BaseMap.add_seq (Seq.map (fun (key,value) -> KeyValue(key,Snd value)) s) m

  let of_seq s = add_seq s empty
  let of_list l = of_seq (List.to_seq l)
  let to_list s = List.of_seq (to_seq s)
end

module MakeMap(Key: KEY) = struct
  module NKey = struct type 'a t = Key.t end
  module NODE = SimpleNode(NKey)(WrappedHomogeneousValue)
  include MakeCustom(Key)(NODE)
end

module MakeSet(Key: KEY) : SET with type elt = Key.t = struct
  module HKey = HeterogeneousKeyFromKey(Key)
  module S = MakeHeterogeneousSet(HKey)
  include S
  type key = Key.t
  type elt = key

  let iter (f: elt -> unit) set = S.iter {f} set
  let fold (f: key -> 'acc -> 'acc) set acc = S.fold {f} set acc
  let filter (f: key -> bool) set = S.filter {f} set
  let for_all (f: key -> bool) set = S.for_all {f} set

  let pretty ?pp_sep (f : Format.formatter -> key -> unit) fmt s =
    S.pretty ?pp_sep {f} fmt s

  let is_singleton m = match BaseMap.is_singleton m with
    | None -> None
    | Some(KeyValue(k,())) -> Some k

  let unsigned_min_elt t = let Any x = unsigned_min_elt t in x
  let unsigned_max_elt t = let Any x = unsigned_max_elt t in x
  let pop_unsigned_minimum t = Option.map (fun (Any x, t) -> (x,t)) (pop_unsigned_minimum t)
  let pop_unsigned_maximum t = Option.map (fun (Any x, t) -> (x,t)) (pop_unsigned_maximum t)

  let to_seq m = Seq.map (fun (BaseMap.KeyValue(elt,())) -> elt) (BaseMap.to_seq m)
  let to_rev_seq m = Seq.map (fun (BaseMap.KeyValue(elt,())) -> elt) (BaseMap.to_rev_seq m)
  let add_seq s m = BaseMap.add_seq (Seq.map (fun (elt) -> BaseMap.KeyValue(elt,())) s) m

  let of_seq s = add_seq s empty
  let of_list l = of_seq (List.to_seq l)
  let to_list s = List.of_seq (to_seq s)
end
