name: hol-combin
version: 1.0
description: Interface between OpenTheory Standard Library and HOL4 combinTheory
author: Ramana Kumar <ramana@member.fsf.org>
license: GPL
show: "Data.Bool"
requires: bool
requires: function
requires: hol-bool
combin {
  article: "HOL4combin.ot.art"
}
main {
  import: combin
  article: "../../combin/combin.ot.art"
}
