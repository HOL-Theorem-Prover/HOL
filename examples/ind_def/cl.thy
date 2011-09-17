name: cl
version: 0.2
description: Combinatory logic example illustrating inductive definitions in HOL4
author: Ramana Kumar <ramana.kumar@gmail.com>
license: MIT
show: "combinatoryLogicExample"
show: "Data.Bool"
base {
  package: base-1.2
}
main {
  import: base
  article: "cl.art"
}
