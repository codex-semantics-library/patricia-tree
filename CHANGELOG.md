# Unreleased

- Fixed a bug where NodeWithId wasn't incrementing ids properly
- `zarith` is no longer a dependency, used GCC's `__builtin_clz` as a faster
  method of finding an integer's highest bit

# v0.9.0 - 2024-04-18

- Initial release of Patricia Tree
