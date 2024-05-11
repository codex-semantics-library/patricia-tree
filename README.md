# Patricia Tree

[![Latest version](https://img.shields.io/badge/version-0.10.0-yellow)](https://github.com/codex-semantics-library/patricia-tree/releases)
[![OCaml Version](https://img.shields.io/badge/OCaml-4.14_--_5.x-blue?logo=ocaml&logoColor=white)](https://github.com/codex-semantics-library/patricia-tree/blob/main/dune-project)
[![GitHub License](https://img.shields.io/github/license/codex-semantics-library/patricia-tree)](https://github.com/codex-semantics-library/patricia-tree/blob/main/LICENSE)
[![GitHub Actions Workflow Status](https://img.shields.io/github/actions/workflow/status/codex-semantics-library/patricia-tree/ocaml.yml)](https://github.com/codex-semantics-library/patricia-tree/actions/workflows/ocaml.yml)
[![Documentation](https://img.shields.io/website?url=https%3A%2F%2Fcodex.top%2Fpatricia-tree%2F&up_message=online&down_message=offline&label=documentation)](https://codex.top/patricia-tree/)

This is an [OCaml](https://ocaml.org/) library that implements sets and maps as
Patricia Trees, as described in Okasaki and Gill's 1998 paper [*Fast mergeable integer maps*](https://www.semanticscholar.org/paper/Fast-Mergeable-Integer-Maps-Okasaki-Gill/23003be706e5f586f23dd7fa5b2a410cc91b659d).
It is a space-efficient prefix trie over the big-endian representation of the key's integer identifier.

The documentation for this library can be found online at
[codex.top/patricia-tree/](https://codex.top/patricia-tree/).

This library was written by [Matthieu Lemerre](https://www.researchgate.net/profile/Matthieu-Lemerre) then further improved
by [Dorian Lesbre](https://www.normalesup.org/~dlesbre/),
as part of the [Codex semantics library](https://codex.top/), developed at [CEA List](https://list.cea.fr/en/).

**Table of Contents:**
<!-- TOC -->
- [Installation](#installation)
- [Features](#features)
- [Quick overview](#quick-overview)
  - [Functors](#functors)
  - [Interfaces](#interfaces)
- [Examples](#examples)
  - [Homogeneous map](#homogeneous-map)
  - [Heterogeneous map](#heterogeneous-map)
- [Release status](#release-status)
- [Known issues](#known-issues)
- [Comparison to other OCaml libraries](#comparison-to-other-ocaml-libraries)
  - [ptmap and ptset](#ptmap-and-ptset)
  - [dmap](#dmap)
- [Contributions and bug reports](#contributions-and-bug-reports)
<!-- /TOC -->

## Installation

This library can be installed with [opam](https://opam.ocaml.org/):
```bash
opam install patricia-tree
```
Alternatively, you can clone the source repository and install with [dune](https://dune.build/):
```bash
git clone git@github.com:codex-semantics-library/patricia-tree.git
cd patricia-tree
opan install . --deps-only
dune build
dune install
# To build documentation
opam install odoc
dune build @doc
```

## Features

- Similar to OCaml's `Map` and `Set`, using the same function names when possible
  and the same convention for order of arguments. This should allow switching to
  and from Patricia Tree with minimal effort.
- The functor parameters (`KEY` module) requires an injective `to_int : t -> int`
  function instead of a `compare` function. `to_int` should be fast and injective.
  This works well with [hash-consed](https://en.wikipedia.org/wiki/Hash_consing) types.
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
  sorted in increasing **unsigned order** of keys.
  This means negative keys are sorted above positive keys, with `-1` being the
  largest possible key, and `0` the smallest.
  This also avoids a bug in Okasaki's paper discussed in [*QuickChecking Patricia Trees*](https://www.cs.tufts.edu/comp/150FP/archive/jan-midtgaard/qc-patricia.pdf)
  by Jan Mitgaard.

  It also affects functions like `unsigned_min_binding` and `pop_unsigned_minimum`. They will return the smallest
  positive integer of both positive and negative keys are present; and not the smallest negative, as one might expect.
- Supports generic maps and sets: a `'m map` that maps `'k key` to `('k, 'm) value`.
  This is especially useful when using [GADTs](https://v2.ocaml.org/manual/gadts-tutorial.html) for the type of keys. This is also sometimes called a dependent map.
- Allows easy and fast operations across different types of maps and set
  which have the same type of keys (e.g. an intersection between a map and a set).
- Multiple choices for internal representation (`NODE`), which allows for efficient
  storage (no need to store a value for sets), or using weak nodes only (values removed from the tree if no other pointer to it exists). This system can also
  be extended to store size information in nodes if needed.
- Exposes a common interface (`view`) to allow users to write their own pattern
  matching on the tree structure without depending on the `NODE` being used.
- hash-consed versions of heterogeneous/homogeneous maps/sets are
  available. These provide constant time equality and comparison, and ensure
  maps/set with the same constants are always physically equal. It comes at the cost
  of more memory usage a slightly slower constructors.

## Quick overview

### Functors

This library contains a single module, `PatriciaTree`.
The main functors used to build our maps and sets are the following:
```ocaml
(** {2 Homogeneous maps and sets} *)

module MakeMap(Key: KEY) : MAP with type key = Key.t
module MakeSet(Key: KEY) : SET with type elt = Key.t

(** {2 Heterogeneous maps and sets} *)

module MakeHeterogeneousSet(Key: HETEROGENEOUS_KEY) : HETEROGENEOUS_SET
  with type 'a elt = 'a Key.t
module MakeHeterogeneousMap(Key: HETEROGENEOUS_KEY)(Value: HETEROGENEOUS_VALUE) :
  HETEROGENEOUS_MAP
  with type 'a key = 'a Key.t
   and type ('k,'m) value = ('k,'m) Value.t
```

There are also [hash-consed](https://en.wikipedia.org/wiki/Hash_consing) versions
of these four functors: `MakeHashconsedMap`, `MakeHashconsedSet`,
`MakeHashconsedHeterogeneousMap` and `MakeHashconsedHeterogeneousSet`.
These uniquely number their nodes, and ensure nodes with the same contents are
always physically equal. With this unique numbering:
- `equal` and `compare` become constant time operations;
- two maps with the same bindings (where keys are compared by `KEY.to_int` and
  values by `HASHED_VALUE.polyeq`) will always be physically equal;
- functions that benefit from sharing will see improved performance;
- constructors are slightly slower, as they now require a hash-table lookup;
- memory usage is increased: nodes store their tags inside themselves, and
  a global hash-table of all built nodes must be maintained;
- hash-consed maps assume their values are immutable;
- **WARNING:** when using physical equality as `HASHED_VALUE.polyeq`,
  some maps of different types may be given the same identifier. See the end of
  the documentation of `HASHED_VALUE.polyeq` for details.
  Note that this is the case in the default implementations `HashedValue`
  and `HeterogeneousHashedValue`.

### Interfaces

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

  The heterogeneous map functor also has a `HETEROGENEOUS_VALUE` parameter to specify the
  `('a, 'b) value` type
- The internal representations of our tree can be customized to use different
  internal `NODE`. Each node come with its own private constructors and destructors,
  as well as a cast to a uniform `view` type used for pattern matching.

  A number of implementations are provided:
  - `SimpleNode`: exactly the `NODE.view` type;
  - `WeakNode`: only store weak pointer to its elements;
  - `NodeWithId`: node which contains a unique identifier;
  - `SetNode`: optimized for sets, doesn't store the [unit] value;
  - `WeakSetNode`: both a `WeakNode` and as `SetNode`
  - `HashconsedNode`: performs hash-consing (it also stores a unique identifier, but checks when
    building a new node whether a node with similar content already exists);
  - `HashconsedSetNode`: both a `HashconsedNode` and a `SetNode`.

  Use the functors `MakeCustomMap` and `MakeCustomSet` (or their heterogeneous
  versions `MakeCustomHeterogeneousMap` and `MakeCustomHeterogeneousSet`) to build
  maps using these nodes, or any other custom nodes.

## Examples

### Homogeneous map

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
  { f = fun _key value () -> value } map set
```

### Heterogeneous map

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

For more details about this issue, see [the OCaml discourse discussion](https://discuss.ocaml.org/t/weird-behaviors-with-first-order-polymorphism/13783).

## Comparison to other OCaml libraries

### ptmap and ptset

There are other implementations of Patricia Tree in OCaml, namely
[ptmap](https://github.com/backtracking/ptmap) and
[ptset](https://github.com/backtracking/ptset), both by J.C. Filliatre.
These are smaller and closer to OCaml's built-in Map and Set, however:
- Our library allows using any type `key` that comes with an injective `to_int`
  function, instead of requiring `key = int`.
- We support generic (heterogeneous) types for keys/elements.
- We support operations between sets and maps of different types.
- We use a big-endian representation, allowing easy access to min/max elements of
  maps and trees.
- Our interface and implementation tries to maximize the sharing between different
  versions of the tree, and to benefit from this memory sharing. Theirs do not.
- These libraries work with older version of OCaml (`>= 4.05` I believe), whereas
  ours requires OCaml `>= 4.14` (for the new interface of `Ephemeron` used in
  `WeakNode`).

### dmap

Additionally, there is a dependent map library: [dmap](https://gitlab.inria.fr/bmontagu/dmap),
which gave us the idea of making our PatriciaTree dependent.
It allows creating type safe dependent maps similar to our heterogeneous maps.
However, its maps aren't Patricia trees. They are binary trees build using a
(polymorphic) comparison function, similarly to the maps of the standard library.

Another difference is that the type of values in the map is independent of the type of the keys,
allowing keys to be associated with different values in different maps. i.e.
we map `'a key` to any `('a, 'b) value` type, whereas dmap only maps `'a key`
to `'a` or `'a value`.

`dmap` also works with OCaml `>= 4.12`, whereas we require OCaml `>= 4.14`.

## Contributions and bug reports

Any contributions are welcome!

You can report any bug, issues, or desired features using the [Github issue tracker](https://github.com/codex-semantics-library/patricia-tree/issues).
Please include OCaml, dune, and library version information in you bug reports.

If you want to contribute code, feel free to fork [the repository on Github](https://github.com/codex-semantics-library/patricia-tree)
and open a pull request. By doing so you agree to release your code under this
project's license ([LGPL-2.1](https://choosealicense.com/licenses/lgpl-2.1/)).


There is no imposed coding style for this repository, here are just a few guidelines and conventions:
- Module type names should use `SCREAMING_SNAKE_CASE`.
- Module and functor names use `PascalCase`, functors names start with `Make`.
- Even though the library implements homogeneous maps as a specialization of
  heterogeneous ones, the naming convention is that no prefix means homogeneous,
  and all heterogeneous objects are prefixed with `heterogeneous`.
- Please document any new functions in the interface, using [ocamldoc style comments](https://v2.ocaml.org/manual/ocamldoc.html#s%3Aocamldoc-comments).
- Please consider adding test for new features/fixed bugs if at all possible.
  This library uses a [QuickCheck](https://www.ocaml.org/p/quickcheck/latest/doc/QuickCheck/index.html) framework for tests.
