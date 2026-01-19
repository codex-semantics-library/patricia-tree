(**************************************************************************)
(*  This file is part of the Codex semantics library                      *)
(*    (patricia-tree sub-component).                                      *)
(*                                                                        *)
(*                                                                        *)
(*  Copyright (C) 2013-2026                                               *)
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

(** {1 Keys and values} *)

module HomogeneousValue = struct
  type ('a,'map) t = 'map
end

module WrappedHomogeneousValue = struct
  type ('a, 'map) t = ('a, 'map) snd
end

module HeterogeneousKeyFromKey(Key: KEY): HETEROGENEOUS_KEY with type 'a t = Key.t =
struct
  type _ t = Key.t

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


module Value : VALUE with type 'a t = 'a = struct type 'a t = 'a end

module HashedValue : HASHED_VALUE with type 'a t = 'a = struct
  include Value
  let hash x = Hashtbl.hash x
  let polyeq: type a b. a -> b -> bool = fun a b -> a == Obj.magic b
end
module HeterogeneousHashedValue : HETEROGENEOUS_HASHED_VALUE with type ('k, 'm) t = 'm =
struct
  include HomogeneousValue
  let hash x = Hashtbl.hash x
  let polyeq: type a b. a -> b -> bool = fun a b -> a == Obj.magic b
end

module HeterogeneousHashedValueFromHashedValue(Value: HASHED_VALUE)
  : HETEROGENEOUS_HASHED_VALUE with type ('a, 'map) t = ('a, 'map Value.t) snd =
struct
  type ('a, 'map) t = ('a, 'map Value.t) snd
  let hash (Snd x) = Value.hash x
  let polyeq (Snd a) (Snd b) = Value.polyeq a b
end
