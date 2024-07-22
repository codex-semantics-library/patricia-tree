# v0.11.0 - Unreleased

- Add `difference`, `domain_difference` and `diff` functions
- Internal refactor.

# v0.10.0 - 2024-06-01

## Main changes

- Added hash-consed nodes and functors to build hash-consed maps and sets.
- Added new functions `fold_on_nonequal_inter` and `fold_on_nonequal_union` to maps.
- Now support using negative keys, removed `zarith` dependency.
- Fixed some bugs

## Detailed changes

**Breaking changes:**
- Renamed `MakeCustom` to `MakeCustomMap`, added new functor `MakeCustomSet`.
  `MakeCustomMap` changed to take a new argument to specify the `'a value` type.
- Renamed `MakeCustomHeterogeneous` to `MakeCustomHeterogeneousMap`, added new functor
  `MakeCustomHeterogeneousSet`.
- Renamed `NODE_WITH_ID.get_id` to `NODE_WITH_ID.to_int`, this allows using
  instances `NODE_WITH_ID` directly as a `KEY`.
- Renamed `VALUE` to `HETEROGENEOUS_VALUE`, added a `VALUE` module type (previously unnamed).
- Renamed `min_binding`, `max_binding`, `pop_minimum`, `pop_maximum`, `min_elt`
  and `max_elt` to `unsigned_min_binding`, `unsigned_max_binding`,
  `pop_unsigned_minimum`, `pop_unsigned_maximum`, `unsigned_min_elt`
  and `unsigned_max_elt` respectively, to clarify that these functions consider
  negative numbers as larger than positive ones.

**New features:**
- Added new interface `MAP_WITH_VALUE` which is the same as `MAP` but with a custom
  type `'a value` instead of just `'a`.
- Added `HashconsedNode`, `HashconsedSetNode` as well as four functors to create
  hash-consed heterogeneous/homogeneous maps/sets: `MakeHashconsedMap`, `MakeHashconsedSet`,
  `MakeHashconsedHeterogeneousMap` and `MakeHashconsedHeterogeneousSet`.
- Now support using negative keys. Trees are built using the bitwise representation
  of integer, meaning they effectively use an unsigned order. Negative keys are
  considered bigger than positive keys, `0` is the minimal number and `-1` the maximal one.
- Added new functions `fold_on_nonequal_inter` and `fold_on_nonequal_union` to maps.

**Bug fixes:**
- Fixed a bug where `NodeWithId` wasn't incrementing ids properly
- `zarith` is no longer a dependency, used GCC's `__builtin_clz` as a faster
  method of finding an integer's highest bit.
- Fixed a bug where `pop_minimum` and `pop_maximum` could throw a private exception
  `Dissappeared` when using `WeakNode`.
- Fixed a possible assertion error when using `idempotent_subset_domain_forall2`
  with `WeakNode`.
- Fix compilation warnings when compiling on ocaml 5.2.

# v0.9.0 - 2024-04-18

- Initial release of Patricia Tree
