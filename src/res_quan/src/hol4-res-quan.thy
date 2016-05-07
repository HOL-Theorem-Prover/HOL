name: hol-res-quan
version: 1.0
description: HOL theory about restricted quantifiers
author: HOL developers <hol-developers@lists.sourceforge.net>
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
