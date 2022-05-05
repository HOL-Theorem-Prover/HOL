name: hol-analysis
version: 1.1
description: HOL real analysis
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-set
requires: hol-real
show: "HOL4"
show: "Data.Bool"
show: "Data.Option"
show: "Data.Pair"
show: "Data.List"
show: "Function"
show: "Relation"
show: "Number.Natural"
show: "Number.Real"
main {
  article: "hol4-analysis-unint.art"
  interpretation: "../../opentheory/hol4.int"
}
