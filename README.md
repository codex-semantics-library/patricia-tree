# Patricia Tree

![Static Badge](https://img.shields.io/badge/version-0.9.0-yellow)
[![OCaml Version](https://img.shields.io/badge/OCaml-4.14_--_5.x-blue?logo=ocaml&logoColor=white)](https://github.com/codex-semantics-library/patricia-tree/blob/main/dune-project)
[![GitHub License](https://img.shields.io/github/license/codex-semantics-library/patricia-tree)](https://github.com/codex-semantics-library/patricia-tree/blob/main/LICENSE)
[![GitHub Actions Workflow Status](https://img.shields.io/github/actions/workflow/status/codex-semantics-library/patricia-tree/ocaml.yml)](https://github.com/codex-semantics-library/patricia-tree/actions/workflows/ocaml.yml)


This is an [OCaml](https://ocaml.org/) library that implements sets and maps as
Patricia Trees, as described in Oksasaki and Gill's 1998 paper [*Fast mergeable integer maps*](https://www.semanticscholar.org/paper/Fast-Mergeable-Integer-Maps-Okasaki-Gill/23003be706e5f586f23dd7fa5b2a410cc91b659d).
It is a space-efficient prefix trie over the big-endian representation of the key's integer identifier.

**Table of Contents:**
<!-- TOC -->
- [Installation](#installation)
- [Features](#features)
- [Quick overview](#quick-overview)
- [Examples](#examples)
  - [Non-generic map (homogeneous)](#non-generic-map-homogeneous)
  - [Generic map (heterogeneous)](#generic-map-heterogeneous)
- [Release status](#release-status)
- [Known issues](#known-issues)
- [Comparison to other OCaml libraries](#comparison-to-other-ocaml-libraries)
- [Contributions and bug reports](#contributions-and-bug-reports)
<!-- /TOC -->

## Installation

This library can be installed with:
```bash
opam install patricia-tree
```
Alternatively, you can clone the source repository and install with dune:
```bash
git clone git@github.com:codex-semantics-library/patricia-tree.git
cd patricia-tree
dune build
dune install
```

## Features

- Similar to OCaml's `Map` and `Set`, using the same function names when possible
  and the same convention for order of arguments. This should allow switching to
  and from Patricia Tree with minimal effort.
- The functor parameters (`KEY` module) requires an injective `to_int : t -> int`
  function instead of a `compare` function. `to_int` should be fast and injective,
  this works well with [hash-consed](https://en.wikipedia.org/wiki/Hash_consing) types.
- The Patricia Tree representation is stable, contrary to maps, inserting nodes
  in any order will return the same shape.
  This allows different versions of a map to share more subtrees in memory, and
  the operations over two maps to benefit from this sharing. The functions in
  this library attempt to **maximally preserve sharing and benefit from sharing**,
  allowing very important improvements in complexity and running time when
  combining maps or sets is a frequent operation.

  To do so, these functions often have extra requirements on their argument
  (e.g. `inter f m1 m2` can be optimized by not inspecting common subtrees when
  `f` is idempotent). To avoid accidental errors, they are renamed (e.g. to
  `idempotent_inter` for the efficient version and `nonidempotent_inter_no_share`
  for the general one)

- Since our Patricia Tree use big-endian order on keys, the maps and sets are
  sorted in increasing order of keys.
- Supports generic maps and sets: a `'m map` that maps `'k key` to `('k, 'm) value`.
  This is especially useful when using [GADTs](https://v2.ocaml.org/manual/gadts-tutorial.html) for the type of keys.
- Allows easy and fast operations across different types of maps and set (e.g.
  an intersection between a map and a set), since all sets and maps, no matter their key type, are really integer sets or maps.
- Multiple choices for internal representation (`NODE`), which allows for efficient
  storage (no need to store a value for sets), or using weak nodes only (values removed from the tree if no other pointer to it exists). This system can also
  be extended to store size information in nodes if needed.
- Exposes a common interface (`view`) to allow users to write their own pattern
  matching on the tree structure without depending on the `NODE` being used.

## Quick overview

<!-- TODO: links to documentation -->

This library contains a single module, `PatriciaTree`.
The main functor used to build our maps and sets are the following:
```ocaml
(** {2 Homogeneous maps and sets} *)

module MakeMap(Key: KEY) : MAP with type key = Key.t
module MakeSet(Key: KEY) : SET with type elt = Key.t

(** {2 Heterogeneous maps and sets} *)

module MakeHeterogeneousSet(Key: HETEROGENEOUS_KEY) : HETEROGENEOUS_SET
  with type 'a elt = 'a Key.t
module MakeHeterogeneousMap(Key: HETEROGENEOUS_KEY)(Value: VALUE) : HETEROGENEOUS_MAP
  with type 'a key = 'a Key.t
   and type ('k,'m) value = ('k,'m) Value.t
```

Here is a brief overview of the various module types of our library:
- `BASE_MAP`: the underlying module type of all our trees (maps end sets). It
  represents a `'b map` binding `'a key` to `('a,'b) value`, as well as all functions needed to manipulate them.

  It can be accessed from any of the more specific maps types, thus providing a
  unified representation, useful for cross map operations. However, for practical
  purposes, it is often best to use the more specific interfaces:
  - `HETEROGENEOUS_MAP` for heterogeneous maps (this is just `BASE_MAP` with a
    `WithForeign` functor).
  - `MAP` for homogeneous maps, this interface is close to [`Stdlib.Map.S`](https://ocaml.org/api/Map.S.html).
  - `HETEROGENEOUS_SET` for heterogeneous sets (sets of `'a elt`). These are just
    maps to unit, but with a custom node representation to avoid storing unit in
    nodes.
  - `SET` for homogeneous sets, this interface is close to [`Stdlib.Set.S`](https://ocaml.org/api/Set.S.html).
- The parameter of our functor are either `KEY` or `HETEROGENEOUS_KEY`.
  These just consist of a type, a (polymorphic) equality function, and an
  injective `to_int` coercion.

  The heterogeneous map functor also has a `VALUE` parameter to specify the
  `('a, 'b) value` type
- The internal representations of our tree can be customized to use different
  internal `NODE`. Each node come with its own private constructors and destructors,
  as well as a cast to a uniform `view` type used for pattern matching.

  A number of implementations are provided `SimpleNode` (exactly the `view` type),
  `WeakNode` (node which only store weak pointer to its elements), `NodeWithId`
  (node which contain a unique identifier), `SetNode` (node optimized for set,
  doesn't store the `unit` value) and `WeakSetNode`.

  Use the functors `MakeCustomHeterogeneous` and `MakeCustom` to build
  maps using these nodes, or any other custom nodes.

## Examples

### Non-generic map (homogeneous)

Here is a small example of a non-generic map:

```ocaml
(** Create a key struct *)
module Int (*: PatriciaTree.KEY*) = struct
  type t = int
  let to_int x = x
end

(** Call the map and/or set functors *)
module IMap = PatriciaTree.MakeMap(Int)
module ISet = PatriciaTree.MakeSet(Int)

(** Use all the usual map operations *)
let map =
  IMap.empty |>
  IMap.add 1 "hello" |>
  IMap.add 2 "world" |>
  IMap.add 3 "how do you do?"
  (* Also has an [of_list] and [of_seq] operation for initialization *)

let _ = IMap.find 1 map (* "hello" *)
let _ = IMap.cardinal map (* 3 *)

(** The strength of Patricia Tree is the speedup of operation on multiple maps
    with common subtrees. *)
let map2 =
  IMap.idempotent_inter_filter (fun _key _l _r -> None)
  (IMap.add 4 "something" map) (IMap.add 5 "something else" map)
let _ = map == map2 (* true *)
(* physical equality is preserved as much as possible, although some intersections
   may need to build new nodes and won't be fully physically equal, they will
   still share subtrees if possible. *)

(** Many operations preserve physical equality whenever possible *)
let _ = (IMap.add 1 "hello" map) == map (* true: already present *)

(** Example of cross map/set operation: only keep the bindings of [map]
    whose keys are in a given set *)
let set = ISet.of_list [1; 3]
module CrossOperations = IMap.WithForeign(ISet.BaseMap)
let restricted_map = CrossOperations.nonidempotent_inter
  {f=fun _key value () -> value } map set
```

### Generic map (heterogeneous)

```ocaml
(** Very small typed expression language *)
type 'a expr =
  | G_Const_Int : int -> int expr
  | G_Const_Bool : bool -> bool expr
  | G_Addition : int expr * int expr -> int expr
  | G_Equal : 'a expr * 'a expr -> bool expr

module Expr : PatriciaTree.HETEROGENEOUS_KEY with type 'a t = 'a expr = struct
  type 'a t = 'a expr

  (** Injective, so long as expression are small enough
      (encodes the constructor discriminant in two lowest bits).
      Ideally, use a hash-consed type, to_int needs to be fast *)
  let rec to_int : type a. a expr -> int = function
    | G_Const_Int i ->   0 + 4*i
    | G_Const_Bool b ->  1 + 4*(if b then 1 else 0)
    | G_Addition(l,r) -> 2 + 4*(to_int l mod 10000 + 10000*(to_int r))
    | G_Equal(l,r) ->    3 + 4*(to_int l mod 10000 + 10000*(to_int r))

  (** Full polymorphic equality *)
  let rec polyeq : type a b. a expr -> b expr -> (a, b) PatriciaTree.cmp =
    fun l r -> match l, r with
    | G_Const_Int l, G_Const_Int r -> if l = r then Eq else Diff
    | G_Const_Bool l, G_Const_Bool r -> if l = r then Eq else Diff
    | G_Addition(ll, lr), G_Addition(rl, rr) -> (
        match polyeq ll rl with
        | Eq -> polyeq lr rr
        | Diff -> Diff)
    | G_Equal(ll, lr), G_Equal(rl, rr) ->    (
        match polyeq ll rl with
        | Eq -> (match polyeq lr rr with Eq -> Eq | Diff -> Diff) (* Match required by typechecker *)
        | Diff -> Diff)
    | _ -> Diff
end

(** Map from expression to their values: here the value only depends on the type
    of the key, not that of the map *)
module EMap = PatriciaTree.MakeHeterogeneousMap(Expr)(struct type ('a, _) t = 'a end)

(** You can use all the usual map operations *)
let map : unit EMap.t =
  EMap.empty |>
  EMap.add (G_Const_Bool false) false |>
  EMap.add (G_Const_Int 5) 5 |>
  EMap.add (G_Addition (G_Const_Int 3, G_Const_Int 6)) 9 |>
  EMap.add (G_Equal (G_Const_Bool false, G_Equal (G_Const_Int 5, G_Const_Int 7))) true

let _ = EMap.find (G_Const_Bool false) map (* false *)
let _ = EMap.cardinal map (* 4 *)

(** Fast operations on multiple maps with common subtrees. *)
let map2 =
  EMap.idempotent_inter_filter
    { f = fun _key _l _r -> None } (* polymorphic 1rst order functions are wrapped in records *)
    (EMap.add (G_Const_Int 0) 8 map)
    (EMap.add (G_Const_Int 0) 9 map)
```

## Release status

This should be close to a stable release. It is already being
used as part of a larger project successfully, and this usage as helped us mature
the interface. As is, we believe the project is usable, and we don't anticipate
any major change before 1.0.0. We didn't commit to a stable release straight
away as we would like a bit more time using this library before doing so.


## Known issues

There is a bug in the OCaml typechecker which prevents us from directly
defining non-generic maps as instances of generic maps. To avoid this, non-generic maps use a separate value type (instead of just using `'b`)
```ocaml
type (_, 'b) snd = Snd of 'b [@@unboxed]
```
It should not incur any extra performance cost as it is unboxed, but can appear
when manipulating non-generic maps.

For more details about this issue, see [the OCaml discourse discussion](https://discuss.ocaml.org/t/weird-behaviors-with-first-order-polymorphism/13783)

## Comparison to other OCaml libraries

There are other implementations of Patricia Tree in OCaml, namely
[ptmap](https://github.com/backtracking/ptmap) and
[ptset](https://github.com/backtracking/ptset), both by J.C. Filliatre.
These are smaller and closer to OCaml's built-in Map and Set, however:
- Our library allows using any type `key` that comes with an injective `to_int`
  function, instead of requiring `key = int`.
- We support generic types for keys/elements.
- We support operation between sets and maps of different types.
- We use a big-endian representation, allowing easy access to min/max elements of
  maps and trees.

## Contributions and bug reports

Any contributions are welcome!

You can report any bug, issues, or desired features using the [Github issue tracker](https://github.com/codex-semantics-library/patricia-tree/issues).
Please include OCaml, dune, and Patricia Tree version information in you bug reports.

If you want to contribute code, feel free to fork and open a pull request. By doing
so you agree to release your code under this project's license ([LGPL-2.1](https://choosealicense.com/licenses/lgpl-2.1/)). There is no imposed coding style for this
repository, so use whichever you prefer as long as it is legible. Please consider
adding tests for new features if at all possible.
