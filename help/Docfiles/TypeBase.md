## `TypeBase`

``` hol4
structure TypeBase
```

------------------------------------------------------------------------

A database of facts stemming from datatype declarations.

The structure `TypeBase` provides an interface to a database that is
updated when a new datatype is introduced with `Hol_datatype`. When a
new datatype is declared, a collection of theorems "about" the type can
be automatically derived. These are indeed proved, and are stored in the
current theory segment. They are also automatically stored in
`TypeBase`.

The interface to `TypeBase` is intended to provide support for writers
of high-level tools for reasoning about datatypes.

### Example

``` hol4
   > Datatype `tree = Leaf | Node 'a tree tree`;
   <<HOL message: Defined type: "tree">>
   val it = () : unit

   > TypeBase.read {Thy = current_theory(), Tyop = "tree"};
   val it =
      SOME
       -----------------------
       -----------------------
       HOL datatype: "scratch$tree"
       Primitive recursion:
        |- !f0 f1.
               ?fn.
                   (fn Leaf = f0) /\
                   !a0 a1 a2. fn (Node a0 a1 a2) = f1 a0 a1 a2 (fn a1) (fn a2)
       Case analysis:
        |- (!v f. tree_CASE Leaf v f = v) /\
           !a0 a1 a2 v f. tree_CASE (Node a0 a1 a2) v f = f a0 a1 a2
       Size:
        |- (!f. tree_size f Leaf = 0) /\
           !f a0 a1 a2.
               tree_size f (Node a0 a1 a2) =
               1 + (f a0 + (tree_size f a1 + tree_size f a2))
       Induction:
        |- !P.
               P Leaf /\ (!t t0. P t /\ P t0 ==> !a. P (Node a t t0)) ==>
               !t. P t
       Case completeness: |- !tt. (tt = Leaf) \/ ?a t t0. tt = Node a t t0
       Case-const equality split:
        |- (tree_CASE x v f = v') <=>
           (x = Leaf) /\ (v = v') \/
           ?a t t0. (x = Node a t t0) /\ (f a t t0 = v')
       Extras: [ ]
       One-to-one:
        |- !a0 a1 a2 a0' a1' a2'.
               (Node a0 a1 a2 = Node a0' a1' a2') <=>
               (a0 = a0') /\ (a1 = a1') /\ (a2 = a2')
       Distinctness: |- !a2 a1 a0. Leaf <> Node a0 a1 a2: tyinfo option
```

### See also

[`bossLib.Datatype`](#bossLib.Datatype)
