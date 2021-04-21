name: hol-analysis
version: 1.1
description: HOL real analysis
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-real
show: "HOL4"
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Relation"
main {
  article: "hol4-analysis-unint.art"
  interpretation: "../opentheory/hol4.int"
}
