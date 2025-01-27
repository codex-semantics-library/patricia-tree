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

open Signatures

(** This section presents the functors which can be used to build patricia tree
    maps and sets. *)

(** {1 Homogeneous maps and sets} *)
(** These are homogeneous maps and set, their keys/elements are a single
    non-generic type, just like the standard library's [Map] and [Set] modules. *)

(** Create a Patricia tree based map, analogous to the standard library's
    {{: https://ocaml.org/api/Map.Make.html}[Map.Make]} *)
module MakeMap(Key: KEY) : MAP with type key = Key.t

(** Create a Patricia tree based set, analogous to the standard library's
    {{: https://ocaml.org/api/Set.Make.html}[Set.Make]}  *)
module MakeSet(Key: KEY) : SET with type elt = Key.t

(** {1 Heterogeneous maps and sets} *)
(** Heterogeneous maps are ['map map], which store bindings of ['key key]
    to [('key, 'map) value]. Note that ['key] is quantified existentially,
    so ['key key] should be a GADT, as we must be able
    to compare keys of different types together.

    Similarly, heterogeneous sets store sets of ['key key]. *)

(** Create a Patricia tree based heterogeneous set, analogous to the standard library's
  {{: https://ocaml.org/api/Set.Make.html}[Set.Make]}, but with an extra type
  parameter: a set stores elements of type ['a elt]. *)
module MakeHeterogeneousSet(Key: HETEROGENEOUS_KEY) : HETEROGENEOUS_SET
  with type 'a elt = 'a Key.t

(** Create a Patricia tree based heterogeneous map, analogous to the standard library's
    {{: https://ocaml.org/api/Map.Make.html}[Map.Make]}, but with an extra type
    parameter: a ['map map] stores bindings of ['key key] to [('key, 'map) value]. *)
module MakeHeterogeneousMap(Key: HETEROGENEOUS_KEY)(Value: HETEROGENEOUS_VALUE) : HETEROGENEOUS_MAP
  with type 'a key = 'a Key.t
    and type ('k,'m) value = ('k,'m) Value.t


(** {1 Maps and sets with custom nodes} *)
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

(** {1:hash_consed Hash-consed maps and sets} *)
(** Hash-consed maps and sets uniquely number each of their nodes.
    Upon creation, they check whether a similar node has been created before,
    if so they return it, else they return a new node with a new number.
    With this unique numbering:
    - [equal] and [compare] become constant time operations;
    - two maps with the same bindings (where keys are compared by {!KEY.to_int} and
      values by {!HASHED_VALUE.polyeq}) will always be physically equal;
    - functions that benefit from sharing, like {!BASE_MAP.idempotent_union} and
      {!BASE_MAP.idempotent_inter} will see improved performance;
    - constructors are slightly slower, as they now require a hash-table lookup;
    - memory usage is increased: nodes store their tags inside themselves, and
      a global hash-table of all built nodes must be maintained.
      This is quickly amortized if multiple identical nodes are built,
      as only one will be kept in memory.
    - hash-consed maps assume their keys and values are immutable, where regular
      maps can mutate values freely;
    - {b WARNING:} when using physical equality as {!HASHED_VALUE.polyeq}, some
      {b maps of different types may be given the same identifier}. See the end of
      the documentation of {!HASHED_VALUE.polyeq} for details.
      Note that this is the case in the default implementations {!HashedValue}
      and {!HeterogeneousHashedValue}.

    All hash-consing functors are {b generative}, since each functor call will
    create a new hash-table to store the created nodes. Calling a functor
    twice with same arguments will lead to two numbering systems for identifiers,
    and thus the types should not be considered compatible.  *)

(** Hash-consed version of {!MAP}. See {!hash_consed} for the differences between
    hash-consed and non hash-consed maps.

    This is a generative functor, as calling it creates a new hash-table to store
    the created nodes, and a reference to store the next unallocated identifier.
    Maps/sets from different hash-consing functors (even if these functors have
    the same arguments) will have different (incompatible) numbering systems and
    be stored in different hash-tables (thus they will never be physically equal).

    @since v0.10.0 *)
module MakeHashconsedMap(Key: KEY)(Value: HASHED_VALUE)() : sig
  include MAP_WITH_VALUE with type key = Key.t and type 'a value = 'a Value.t (** @closed *)

  include HASH_CONSED_OPERATIONS with type 'a t := 'a t (** @inline *)
end

(** Hash-consed version of {!SET}. See {!hash_consed} for the differences between
    hash-consed and non hash-consed sets.

    This is a generative functor, as calling it creates a new hash-table to store
    the created nodes, and a reference to store the next unallocated identifier.
    Maps/sets from different hash-consing functors (even if these functors have
    the same arguments) will have different (incompatible) numbering systems and
    be stored in different hash-tables (thus they will never be physically equal).

    @since v0.10.0 *)
module MakeHashconsedSet(Key: KEY)() : sig
  include SET with type elt = Key.t (** @closed *)

  include HASH_CONSED_OPERATIONS with type 'a t := t (** @inline *)
end

(** Hash-consed version of {!HETEROGENEOUS_SET}.  See {!hash_consed} for the differences between
    hash-consed and non hash-consed sets.

    This is a generative functor, as calling it creates a new hash-table to store
    the created nodes, and a reference to store the next unallocated identifier.
    Maps/sets from different hash-consing functors (even if these functors have
    the same arguments) will have different (incompatible) numbering systems and
    be stored in different hash-tables (thus they will never be physically equal).

    @since v0.10.0 *)
module MakeHashconsedHeterogeneousSet(Key: HETEROGENEOUS_KEY)() : sig
  include HETEROGENEOUS_SET with type 'a elt = 'a Key.t (** @closed *)

  include HASH_CONSED_OPERATIONS with type 'a t := t (** @inline *)
end

(** Hash-consed version of {!HETEROGENEOUS_MAP}.  See {!hash_consed} for the differences between
    hash-consed and non hash-consed maps.

    This is a generative functor, as calling it creates a new hash-table to store
    the created nodes, and a reference to store the next unallocated identifier.
    Maps/sets from different hash-consing functors (even if these functors have
    the same arguments) will have different (incompatible) numbering systems and
    be stored in different hash-tables (thus they will never be physically equal).

    @since v0.10.0 *)
module MakeHashconsedHeterogeneousMap(Key: HETEROGENEOUS_KEY)(Value: HETEROGENEOUS_HASHED_VALUE)() : sig
  include HETEROGENEOUS_MAP
      with type 'a key = 'a Key.t
      and type ('k,'m) value = ('k, 'm) Value.t (** @closed *)

  include HASH_CONSED_OPERATIONS with type 'a t := 'a t (** @inline *)
end
