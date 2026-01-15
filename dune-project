(lang dune 3.0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  This file is part of the Codex semantics library                      ;;
;;    (patricia-tree sub-component).                                      ;;
;;                                                                        ;;
;;  Copyright (C) 2024-2025                                               ;;
;;    CEA (Commissariat à l'énergie atomique et aux énergies              ;;
;;         alternatives)                                                  ;;
;;                                                                        ;;
;;  You can redistribute it and/or modify it under the terms of the GNU   ;;
;;  Lesser General Public License as published by the Free Software       ;;
;;  Foundation, version 2.1.                                              ;;
;;                                                                        ;;
;;  It is distributed in the hope that it will be useful,                 ;;
;;  but WITHOUT ANY WARRANTY; without even the implied warranty of        ;;
;;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         ;;
;;  GNU Lesser General Public License for more details.                   ;;
;;                                                                        ;;
;;  See the GNU Lesser General Public License version 2.1                 ;;
;;  for more details (enclosed in the file LICENSE).                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(name patricia-tree)

(version 0.11.0)

(using mdx 0.2)

(maintainers "Dorian Lesbre <dorian.lesbre@cea.fr>")

(authors
 "Matthieu Lemerre <matthieu.lemerre@cea.fr>"
 "Dorian Lesbre <dorian.lesbre@cea.fr>")

(license "LGPL-2.1-only")

(bug_reports
 "https://github.com/codex-semantics-library/patricia-tree/issues")

(homepage "https://codex.top/api/patricia-tree/")

(documentation "https://codex.top/api/patricia-tree/")

(source
 (github "codex-semantics-library/patricia-tree"))

(generate_opam_files)

(package
 (name patricia-tree)
 (synopsis
  "Patricia Tree data structure in OCaml for maps and sets. Supports generic key-value pairs")
 (depends
  (ocaml
   (>= 4.14))
  dune
  (qcheck-core
   (and
    (>= "0.21.2")
    :with-test))
  (ppx_inline_test
   (and
    (>= "v0.16.0")
    :with-test))
  (mdx
   (and
    (>= "2.4.1")
    :with-test))
  (odoc
   (and
    (>= "2.4.0")
    :with-doc))
  (sherlodoc :with-doc)
  ; Benchmark dependencies
  (bechamel :with-dev)
  (csv :with-dev)
  (qcheck :with-dev)))
