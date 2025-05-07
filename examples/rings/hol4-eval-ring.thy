name: hol-eval-ring
version: 1.2
description: HOL ring theories
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-sort
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Relation"
main {
  article: "hol4-ring-eval-unint.art"
  interpretation: "../../opentheory/hol4.int"
}
