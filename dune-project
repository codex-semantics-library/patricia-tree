(lang dune 2.0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  This file is part of the Codex semantics library                      ;;
;;    (patricia-tree sub-component).                                      ;;
;;                                                                        ;;
;;  Copyright (C) 2024                                                    ;;
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

(version 0.9.0)

(maintainers "Dorian Lesbre <dorian.lesbre@cea.fr>")

(authors
 "Matthieu Lemerre <matthieu.lemerre@cea.fr>"
 "Dorian Lesbre <dorian.lesbre@cea.fr>")

(license "LGPL-2.1")

(bug_reports
 "https://github.com/codex-semantics-library/patricia-tree/issues")

(homepage "https://codex.top/patricia-tree/")

(documentation "https://codex.top/patricia-tree/")

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
  (qcheck-core
   (>= "0.21.2"))
  (zarith
   (>= "1.13"))
  (dune
   (>= "2.0"))
  (ppx_inline_test
   (>= "v0.16.0"))))
