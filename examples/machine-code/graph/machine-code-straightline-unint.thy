name: machine-code-straightline-unint
version: 1.0
description: Hoare logic triple support for straightline code (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: graph
  import: straight
}
graph {
  article: "GraphLang.ot.art"
}
straight {
  import: graph
  article: "straightline.ot.art"
}
