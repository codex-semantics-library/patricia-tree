# Release checklist

Step-by-step guide to creating and publishing a new release.

1. Check that file headers are up-to-date
2. Update version numbers in [dune-project](./dune-project) and [src/index.mld](./src/index.mld)
3. Fill in the [changelog](./CHANGELOG.md), it should start with
   ```md
   # vX.Y.Z - YYYY-MM-DD

   - bullet list of changes

   # <older versions>
   ```

4. Create a new tag for the release:
   ```bash
   dune-release tag
   ```
   This should auto-create a tag `vX.Y.Z` (name read from the CHANGELOG)

5. Push the new tag to Github:
   ```bash
   git push origin vX.Y.Z
   ```
   Check that [github-action](https://github.com/codex-semantics-library/patricia-tree/actions) succeeds (build, tests and documentation).
   It should create a new folder `vX.Y.Z` on the `gh-pages` branch.

6. On the [codex-semantics-library.github.io](https://github.com/codex-semantics-library/codex-semantics-library.github.io)
   repository:
   - update the `patricia-tree.latest-version` field in `_data/packages.yaml`
   - update the `api/patricia-tree.md` page to add a link to the new version.
   - run `dune build @doc-json`, copy the json files from
     `<this repo>/_build/default/_doc/html/patricia-tree` to
     `<website>/_data/api/patricia-tree/vX__Y__Z` (note the `__` instead of `.`),
     also copy the `db.js` file to `<website>/assets/js/sherlodoc-db/patricia-tree.X.Y.Z.js`

7. Run:
   ```bash
   dune-release publish distrib
   ```
   This will create a new Github release, it requires a Github Access Token.

8. Run:
   ```bash
   dune-release opam pkg
   ```
   To prepare the package for an opam release

9. Run:
   ```bash
   dune-release opam submit
   ```
   This will create a PR to [opam-repository](https://github.com/ocaml/opam-repository)
   to publish the new version. It requires a locally cloned fork of opam-repository.
