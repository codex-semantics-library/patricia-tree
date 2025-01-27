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

open Signatures

module Value : VALUE with type 'a t = 'a
(** Default implementation of {!VALUE}, used in {!MakeMap}.
    @since v0.10.0 *)

module HomogeneousValue : HETEROGENEOUS_VALUE with type ('a,'map) t = 'map
(** Default implementation of {!HETEROGENEOUS_VALUE}, to use when the type of the
    value in a heterogeneous map does not depend on the type of the key, only on
    the type of the map. *)

module WrappedHomogeneousValue : HETEROGENEOUS_VALUE with type ('a,'map) t = ('a,'map) snd
(** Same as {!HomogeneousValue}, but uses a wrapper (unboxed) type instead of direct
    equality. This avoids a problem in the typechecker with overly eager simplification of aliases.
    More info on
    {{: https://discuss.ocaml.org/t/weird-behaviors-with-first-order-polymorphism/13783} the OCaml discourse post}
    and {{: https://github.com/ocaml/ocaml/issues/13292}the github issue}. *)

module HashedValue : HASHED_VALUE with type 'a t = 'a
(** Generic implementation of {!HASHED_VALUE}.
    Uses {{: https://ocaml.org/api/Hashtbl.html#VALhash}[Hashtbl.hash]} for hashing
    and physical equality for equality.
    Note that this may lead to maps of different types having the same identifier
    ({!MakeHashconsedMap.to_int}), see the documentation of {!HASHED_VALUE.polyeq}
    for details on this. *)

module HeterogeneousHashedValue : HETEROGENEOUS_HASHED_VALUE with type ('k, 'm) t = 'm
(** Generic implementation of {!HETEROGENEOUS_HASHED_VALUE}.
    Uses {{: https://ocaml.org/api/Hashtbl.html#VALhash}[Hashtbl.hash]} for hashing
    and physical equality for equality.
    Note that this may lead to maps of different types having the same identifier
    ({!MakeHashconsedHeterogeneousMap.to_int}), see the documentation of
    {!HASHED_VALUE.polyeq} for details on this. *)


(**/**)
(** For local library use only *)

module HeterogeneousKeyFromKey(Key: KEY): HETEROGENEOUS_KEY with type 'a t = Key.t
(** Create a {!HETEROGENEOUS_KEY} from a non-polymorphic {!KEY} *)

module HeterogeneousHashedValueFromHashedValue(Value: HASHED_VALUE)
  : HETEROGENEOUS_HASHED_VALUE with type ('a, 'map) t = ('a, 'map Value.t) snd
(** Create a {!HETEROGENEOUS_HASHED_VALUE} from a {!HASHED_VALUE} *)

(**/**)
