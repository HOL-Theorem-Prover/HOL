name: hol-res-quan
version: 1.1
description: HOL theory about restricted quantifiers
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
show: "HOL4"
show: "Data.Bool"
show: "Function"
main {
  article: "res_quan.ot.art"
  interpretation: "../../opentheory/hol4.int"
}
