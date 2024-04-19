# Release checklist

Step-by-step guide to creating and publishing a new release.

1. Check that file headers are up-to-date
2. Fill in the [changelog](./CHANGELOG.md), it should start with
   ```md
   # vX.Y.Z - YYYY-MM-DD

   - bullet list of changes

   # <older versions>
   ```

3. Create a new tag for the release:
   ```bash
   dune-release tag
   ```
   This should auto-create a tag `vX.Y.Z` (name read from the CHANGELOG)

4. Push the new tag to Github:
   ```bash
   git push origin vX.Y.Z
   ```
   Check that [github-action](https://github.com/codex-semantics-library/patricia-tree/actions) succeeds (build, tests and documentation).
   It should create a new folder `vX.Y.Z` on the `gh-pages` branch.

5. On the `gh-pages` branch, edit `index.html` to add a link to the new version
   in the list of documentation versions. Push and switch back to the `main` branch.

6. Run:
   ```bash
   dune-release publish distrib
   ```
   This will create a new Github release, it requires a Github Access Token.

7. Run:
   ```bash
   dune-release opam pkg
   ```
   To prepare the package for an opam release

7. Run:
   ```bash
   dune-release opam submit
   ```
   This will create a PR to [opam-repository](https://github.com/ocaml/opam-repository)
   to publish the new version. It requires a locally cloned fork of opam-repository.
