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

(** File run by MDX before running all others, sets up some stuff so the
    comments don't have to *)

open PatriciaTree
open Sigs

type foo

module IntKey = struct
    type 'a t = int
    let to_int x = x
    let polyeq : type a b. a t -> b t -> (a, b) cmp = fun a b ->
        if a == Obj.magic b then Obj.magic Eq else Diff
end
module MyValue = Int
module MyMap = MakeHeterogeneousMap(IntKey)(struct type ('a,'b) t = int end)
