# HOL to ACL2 Translation

This directory provides an automated translation from a subset of HOL
to ACL2(zfc), a formalization of Set Theory in the ACL2 system. Details
of ACL2(zfc) can be found at
```
   https://github.com/acl2/acl2/tree/master/books/projects/set-theory
```

The modelling of the HOL logic in ACL2(zfc) is analogous to the
"Pitts" semantics of the HOL4 Logic Manual. It can be found at the `acl2/`
subdirectory of the HOL to ACL2 translation project in ACL2, here:
```
   https://github.com/acl2/acl2/tree/master/books/projects/hol-in-acl2/
```
The `examples/` subdirectory located there should be kept in sync with
the `examples/` directory located here.

The translator itself can be seen in action in the `examples` directory.
Typing
```
   <holdir>/bin/Holmake cleanAll
   <holdir>/bin/Holmake
```
will create, for each `<x>Script.sml`, a corresponding file
`<x>.defhol`, comprising a list of so-called `defhol` forms which can
then be used in ACL2(zfc) to create set theory translations of the
selected definitions, theorems, and goals from the `<x>` formalization
in HOL4.
