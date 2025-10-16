(**************************************************************************)
(*  This file is part of the Codex semantics library                      *)
(*    (patricia-tree sub-component).                                      *)
(*                                                                        *)
(*                                                                        *)
(*  Copyright (C) 2013-2025                                               *)
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
(*                                                                        *)
(**************************************************************************)

open Signatures

(** {1 Basic nodes} *)

(** This module is such that ['map t = 'map view].
    This is the node used in {!MakeHeterogeneousMap} and {!MakeMap}. *)
    module SimpleNode(Key: sig type 'k t end)(Value: HETEROGENEOUS_VALUE) : NODE
  with type 'a key = 'a Key.t
   and type ('key,'map) value = ('key,'map) Value.t

(** Here, nodes also contain a unique id, e.g. so that they can be
    used as keys of maps or hash-tables. *)
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

(** {1 Weak nodes} *)

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


(** {1 Hashconsed nodes} *)

(** Gives a unique number to each node like {!NodeWithId},
    but also performs hash-consing. So two maps with the same bindings will
    always be physically equal. See {!hash_consed} for more details on this.

    This is a generative functor, as calling it creates a new hash-table to store
    the created nodes, and a reference to store the next unallocated identifier.
    Maps/sets from different hash-consing functors (even if these functors have
    the same arguments) will have different (incompatible) numbering systems and
    be stored in different hash-tables (thus they will never be physically equal).

    Using a single {!HashconsedNode} in multiple {!MakeCustomMap} functors will result in
    all those maps being hash-consed together (stored in the same hash-table,
    same numbering system).

    @since v0.10.0 *)
module HashconsedNode(Key: HETEROGENEOUS_KEY)(Value: HETEROGENEOUS_HASHED_VALUE)() : HASH_CONSED_NODE
  with type 'a key = 'a Key.t
   and type ('key,'map) value = ('key, 'map) Value.t

(** Both a {!HashconsedNode} and a {!SetNode}.
    @since v0.10.0 *)
module HashconsedSetNode(Key: HETEROGENEOUS_KEY)() : HASH_CONSED_NODE
  with type 'a key = 'a Key.t
   and type ('key,'map) value = unit
