name: hol-triple
version: 1.0
description: triple
author: HOL developers <hol-developers@lists.sourceforge.net>
license: MIT
requires: base
requires: hol-base
requires: hol-machine-code-hoare-triple
show: "Data.Bool"
main {
  article: "triple-unint.art"
  interpretation: "../../../src/opentheory/hol4.int"
}
