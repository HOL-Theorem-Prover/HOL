name: hol-compatibility
version: 1.0
description: Interface between OpenTheory Standard Library and HOL4
author: Ramana Kumar <ramana@member.fsf.org>
license: GPL
requires: base
show: "Data.Bool"
bool {
  package: hol-bool-1.0
}
sat {
  import: bool
  package: hol-sat-1.0
}
combin {
  import: bool
  package: hol-combin-1.0
}
main {
  import: bool
  import: sat
  import: combin
}
