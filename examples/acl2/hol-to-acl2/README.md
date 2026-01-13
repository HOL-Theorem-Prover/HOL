# HOL to ACL2 Translation

This directory provides an automated translation from a subset of HOL
to ACL(zfc), a formalization of Set Theory in the ACL2 system. Details
of ACL2(zfc) can be found at
```
  https://github.com/acl2/acl2/tree/master/books/projects/set-theory
```

The modelling of the HOL logic in ACL2(zfc) is analogous to the
"Pitts" semantics of the HOL4 Logic Manual. It can be found at
```
https://github.com/acl2/acl2/tree/master/books/projects/hol-in-acl2/acl2
```

The translator itself can be seen in action in the `examples` directory.
Typing
```
  <holdir>/bin/Holmake cleanAll
  <holdir>/bin/Holmake
```
will create, for each `<x>Script.sml`, a corresponding file
`<x>.defhol`, comprising a list of so-called `defhol forms` which can
then be used in ACL2(zfc) to "recreate" the selected definitions,
theorems, and goals coming from the `<x>` formalization in HOL4.
