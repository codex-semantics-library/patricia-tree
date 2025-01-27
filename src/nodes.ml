(**************************************************************************)
(*  This file is part of the Codex semantics library                      *)
(*    (patricia-tree sub-component).                                      *)
(*                                                                        *)
(*  Copyright (C) 2024-2025                                               *)
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

open Ints
open Signatures

let sdbm x y = y + (x lsl 16) + (x lsl 6) - x
(** Combine two numbers into a new hash *)

(** Simple node, with no hash consing. *)
module [@inline] SimpleNode(Key:sig type 'a t end)(Value:HETEROGENEOUS_VALUE) = struct
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

module WeakNode(Key:sig type 'a t end)(Value:HETEROGENEOUS_VALUE)(* :NODE *) = struct
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
module NodeWithId(Key:sig type 'a t end)(Value:HETEROGENEOUS_VALUE):NODE_WITH_ID
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

  let to_int = function
    | NEmpty -> 0
    | NBranch{id;_} -> id
    | NLeaf{id;_} -> id

  let count = ref 0

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

module HashconsedNode(Key:HETEROGENEOUS_KEY)(Value:HETEROGENEOUS_HASHED_VALUE)()
(* : HASH_CONSED_NODE
  with type 'key key = 'key Key.t
   and type ('key, 'map) value = ('key, 'map) Value.t *)
= struct

  type 'a key = 'a Key.t
  type ('key, 'map) value = ('key, 'map) Value.t

  type 'map view =
    | Empty: 'map view
    | Branch: { prefix:intkey; branching_bit:mask; tree0:'map t; tree1:'map t } -> 'map view
    | Leaf: { key:'key key; value:('key,'map) value } -> 'map view
  and 'map t =
    | NEmpty: 'map t
    | NBranch: { prefix:intkey; branching_bit:mask; tree0:'map t; tree1:'map t; id:int } -> 'map t
    | NLeaf: { key:'key key; value:('key, 'map) Value.t; id:int } -> 'map t

  let view = function
    | NEmpty -> Empty
    | NBranch{prefix;branching_bit;tree0;tree1;_} -> Branch{prefix;branching_bit;tree0;tree1}
    | NLeaf{key;value;_} -> Leaf{key;value}

  let to_int = function
    | NEmpty -> 0
    | NBranch{ id; _ } -> id
    | NLeaf{ id; _ } -> id

  let count = ref 1 (** Start at 1 as we increment in post *)

  type any_map = AnyMap : 'a t -> any_map [@@unboxed]

  module HashArg = struct
    type t = any_map
    let equal (AnyMap a) (AnyMap b) = match a, b with
      | NEmpty, NEmpty -> true
      | NLeaf{key=key1;value=value1;_}, NLeaf{key=key2;value=value2;_} ->
        begin match Key.polyeq key1 key2 with
        | Eq -> Value.polyeq value1 value2
        | Diff -> false
        end
      | NBranch{prefix=prefixa;branching_bit=branching_bita;tree0=tree0a;tree1=tree1a;_},
        NBranch{prefix=prefixb;branching_bit=branching_bitb;tree0=tree0b;tree1=tree1b;_} ->
        prefixa == prefixb && branching_bita == branching_bitb &&
        to_int tree0a = to_int tree0b && to_int tree1a = to_int tree1b
      | _ -> false

    let hash (AnyMap x) = match x with
      | NEmpty -> 0
      | NLeaf{key; value; _} ->
          let hash = sdbm (Key.to_int key) (Value.hash value) in
          (hash lsl 1) lor 1
          (* All leaf hashes are odd *)
      | NBranch{prefix; branching_bit; tree0; tree1; _} -> (* All branch hashes are even *)
        (sdbm ((prefix :> int) lor (branching_bit :> int)) @@ sdbm (to_int tree0) (to_int tree1)) lsl 1
  end

  module WeakHash = Weak.Make(HashArg)

  let weakh = WeakHash.create 120

  let empty = NEmpty
  let is_empty x = x == NEmpty

  let try_find (tentative : 'a t) =
    let AnyMap x = WeakHash.merge weakh (AnyMap tentative) in
    let x : 'a t = Obj.magic x in
    if x == tentative then incr count;
    x

  let leaf key value = try_find (NLeaf{key;value;id= !count})

  let branch ~prefix ~branching_bit ~tree0 ~tree1 =
    match tree0,tree1 with
    | NEmpty, x -> x
    | x, NEmpty -> x
    | _ -> try_find (NBranch{prefix;branching_bit;tree0;tree1;id=(!count)})

  let equal x y = x == y
  let compare x y = Int.compare (to_int x) (to_int y)
end

module HashconsedSetNode(Key:HETEROGENEOUS_KEY)(): HASH_CONSED_NODE
  with type 'key key = 'key Key.t
   and type ('key,'map) value = unit
= struct

  type 'a key = 'a Key.t
  type ('key,'map) value = unit

  type map =
    | NEmpty: map
    | NBranch: { prefix:intkey; branching_bit:mask; tree0:map; tree1:map; id:int } -> map
    | NLeaf: { key:'key key; id:int } -> map
  type 'map view =
    | Empty: 'map view
    | Branch: { prefix:intkey; branching_bit:mask; tree0:'map t; tree1:'map t } -> 'map view
    | Leaf: { key:'key key; value:unit } -> 'map view
  and _ t = map

  let view = function
    | NEmpty -> Empty
    | NBranch{prefix;branching_bit;tree0;tree1;_} -> Branch{prefix;branching_bit;tree0;tree1}
    | NLeaf{ key; _ } -> Leaf{ key; value=() }

  let to_int = function
    | NEmpty -> 0
    | NBranch{ id; _ } -> id
    | NLeaf{ id; _ } -> id

  let count = ref 1 (** Start at 1 as we increment in post *)

  module HashArg = struct
    type t = map
    let equal a b = match a, b with
      | NEmpty, NEmpty -> true
      | NLeaf{key=key1;_}, NLeaf{key=key2;_} ->
        begin match Key.polyeq key1 key2 with
        | Eq -> true
        | Diff -> false
        end
      | NBranch{prefix=prefixa;branching_bit=branching_bita;tree0=tree0a;tree1=tree1a;_},
        NBranch{prefix=prefixb;branching_bit=branching_bitb;tree0=tree0b;tree1=tree1b;_} ->
        prefixa == prefixb && branching_bita == branching_bitb &&
        tree0a == tree0b && tree1a == tree1b
      | _ -> false

    let hash a = match a with
      | NEmpty -> 0
      | NLeaf{key; _} -> ((Key.to_int key) lsl 1) lor 1 (* All leaf hashes are odd *)
      | NBranch{prefix; branching_bit; tree0; tree1; _} -> (* All branch hashes are even *)
        (sdbm ((prefix :> int) lor (branching_bit :> int)) @@ sdbm (to_int tree0) (to_int tree1)) lsl 1
  end

  module WeakHash = Weak.Make(HashArg)

  let weakh = WeakHash.create 120

  let empty = NEmpty
  let is_empty x = x == NEmpty

  let try_find tentative =
    let x = WeakHash.merge weakh tentative in
    if x == tentative then incr count;
    x

  let leaf key () = try_find (NLeaf{ key; id = !count })

  let branch ~prefix ~branching_bit ~tree0 ~tree1 =
    match tree0,tree1 with
    | NEmpty, x -> x
    | x, NEmpty -> x
    | _ -> try_find (NBranch{prefix;branching_bit;tree0;tree1;id=(!count)})

  let equal x y = x == y
  let compare x y = Int.compare (to_int x) (to_int y)
end
