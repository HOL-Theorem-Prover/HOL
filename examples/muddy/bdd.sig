(* Copyright (C) 1997-2001 by Ken Friis Larsen and Jakob Lichtenberg. *)
signature bdd =
sig
    type bdd
    type varnum = int (* should be non-negative *)

    val init      : int -> int -> unit
    val setVarnum : int -> unit
    val getVarnum : unit -> int
    val isRunning : unit -> bool
    val done      : unit -> unit

    val toBool   : bdd -> bool
    val fromBool : bool -> bdd

    val TRUE     : bdd
    val FALSE    : bdd

    val equal    : bdd -> bdd -> bool
    val hash     : bdd -> int

    val ithvar  : varnum -> bdd
    val nithvar : varnum -> bdd

    val var     : bdd -> varnum
    val low     : bdd -> bdd
    val high    : bdd -> bdd

    datatype bddop =
	And | Xor | Or | Nand | Nor | Imp | Biimp
      | Diff | Lessth | Invimp

    type varSet
    val makeset  : varnum list -> varSet
    val makeset_ : varnum vector -> varSet
    val scanset  : varSet -> varnum vector
    val fromSet  : varSet -> bdd
    val toSet_   : bdd -> varSet

    val support  : bdd -> varSet

    val apply  : bdd -> bdd -> bddop -> bdd
    val exist  : varSet -> bdd -> bdd
    val forall : varSet -> bdd -> bdd
    val appex  : bdd -> bdd -> bddop -> varSet -> bdd
    val appall : bdd -> bdd -> bddop -> varSet -> bdd

    val DIFF   : bdd * bdd -> bdd
    val IMP    : bdd * bdd -> bdd
    val LESSTH : bdd * bdd -> bdd
    val BIIMP  : bdd * bdd -> bdd
    val OR     : bdd * bdd -> bdd
    val INVIMP : bdd * bdd -> bdd
    val NAND   : bdd * bdd -> bdd
    val NOR    : bdd * bdd -> bdd
    val AND    : bdd * bdd -> bdd
    val XOR    : bdd * bdd -> bdd

    val NOT : bdd -> bdd

    val ITE : bdd -> bdd -> bdd -> bdd

    type pairSet
    val makepairSet : (varnum * varnum) list -> pairSet
    val replace : bdd -> pairSet -> bdd


    type composeSet
    val composeSet : (varnum * bdd) list -> composeSet
    val compose    : (varnum * bdd) -> bdd -> bdd
    val veccompose : composeSet -> bdd -> bdd

    type assignment
    val assignment : (varnum * bool) list -> assignment
    val fromAssignment : assignment -> bdd
    val toAssignment_ : bdd -> assignment
    val getAssignment : assignment -> (varnum * bool) list


    val restrict : bdd -> assignment -> bdd

    val satone : bdd -> assignment
    val fullsatone : bdd -> assignment


    val simplify  : bdd -> bdd -> bdd

    eqtype fixed
    val FIXED : fixed
    val FREE  : fixed

    val addvarblock  : varnum -> varnum -> fixed -> unit
    val clrvarblocks : unit -> unit

    eqtype method
    val WIN2         : method
    val WIN2ITE      : method
    val SIFT         : method
    val SIFTITE      : method
    val RANDOM       : method
    val REORDER_NONE : method

    val reorder          : method -> unit
    val autoReorder      : method -> method
    val autoReorderTimes : method -> int -> method

    val getMethod : unit -> method
    val getTimes  : unit -> int

    val disableReorder : unit -> unit
    val enableReorder  : unit -> unit

    type level = int
    val varToLevel : varnum -> level
    val varAtLevel : level -> varnum

    val fnprintdot : string -> bdd -> unit
    val printdot   : bdd -> unit
    val fnprintset : string -> bdd -> unit
    val printset   : bdd -> unit

    val bddSave : string -> bdd -> unit
    val bddLoad : string -> bdd

    val satcount : bdd -> real

    type nodetable = int * (varnum * int * int) Vector.vector
    val nodetable  : bdd -> nodetable

    val nodecount : bdd -> int

    val setMaxincrease : int -> int
    val setCacheratio  : int -> int
    val verbosegc      : (string * string) option -> unit

    val stats    : unit -> {produced     : int,
			    nodenum      : int,
			    maxnodenum   : int,
			    freenodes    : int,
			    minfreenodes : int,
			    varnum       : int,
			    cachesize    : int,
			    gbcnum       : int}

end

(* Structure bdd provide an interface to Jørn Linds <jl@it.dtu.dk>
   BuDDy BDD library.

   Type [bdd] is the abstract type of BDDs.

   [init nodesize cachesize] initiates the bdd package and must be
   called before any bdd operations are done.  nodesize is the initial
   number of nodes in the nodetable and cachesize is the fixed size of
   the internal caches.  Typical values for nodesize are 10000 nodes
   for small test examples and up to 1000000 nodes for large examples.
   A cache size of 10000 seems to work good even for large examples,
   but lesser values should do it for smaller examples.

   The initial number of nodes is not critical for any bdd operation
   as the table will be resized whenever there are too few nodes left
   after a garbage collection.  But it does have some impact on the
   efficency of the operations.

   init and done should only be called once per session.

   [setvarnum num] is used to define the number of variables used in
   the bdd package. It may be called more than one time, but only to
   increase the number of variables. num is the number of variables to
   use.

   [done ()] frees all memory used by the bdd package and resets the
   package to its initial state.

   [toBool r] return the boolean represented by r.  Raises Domain if r
   can not be represented as true or false.

   [fromBool b] gives the bdd representing b.

   [equal x y] is true if x and y represent equivalent boolean
   expressions.

   [ithvar i] gives the bdd representing the i'th variable.  The
   requested variable must be in the range define by setvarnum
   starting with 0 being the first.

   [nithvar i] gives the bdd representing the negation of the i'th
   variable.  The requested variable must be in the range defined by
   setvarnum starting with 0 being the first.

   [var r] gets the variable labeling r.

   [low r] gets the false branch of r.

   [high r] gets the true branch of r.

   Type [varSet] is an effective representation of sets of variables.

   [makeset varlist] makes the varSet with the elements in varlist.
   There is no constraint on varlist: it may be empty, contain duplets,
   or negative numbers.  Duplets and negative numbers will just be
   filtered out.

   [makeset_ varvector] makes the varSet with the elements in
   varvector.  There are many constraints on varvector: it must be
   sorted in increasing order, it may not contain duplets nor negative
   numbers.  This function is more effictive than makeset, but it is
   highly unsafe and you should only use it when you can guarantee
   that the input satisfies the constraints.  If it doesn't satisfy the
   constraints "weird things" may happen, and your ML program may even
   "core dump"!

   [scanset varset] gives the vector of the variables in varset.

   [fromSet varset] gives the bdd representing the conjunction of
   all the variables in varset.

   [toSet_ r] converts the bdd r to a varSet; no checks are performed
   to check that r really represents a varSet therefore it should be
   used with care.

   [support r] gives the set of variables that r depends on.

   Type [bddop] represent the binary boolean operator which can be used
   when constructing bdds. Truth tables:

   x y  |  And  Xor  Or  Nand  Nor  Imp  Biimp  Diff  Lessth  Invimp
  ------|------------------------------------------------------------
   T T  |   T    F   T    F     F    T     T     F      F       T
   T F  |   F    T   T	  T     F    F     F     T      F       T
   F T  |   F    T   T	  T     F    T     F     F      T       F
   F F  |   F    F   F	  T     T    T     T     F      F       T

   [apply x y opr] constructs the bdd using the binary boolean
   operator.

   [exist varset r] constructs the existential quantification over all
   the variables in the varset of r.

   [forall varset r] constructs the universal quantification over all
   the variables in the varset of r.

   [appex x y opr varset] equivalent to 'exist varset (apply x y opr)'
   but more efficient.

   [appall x y opr varset] equivalent to 'forall varset (apply x y opr)'
   but more efficient.

   [DIFF(x,y)] equivalent to 'apply x y Diff', but this is nice for
   infix.

   [IMP(x,y)] equivalent to 'apply x y Imp', but this is nice for infix.

   [LESSTH(x,y)] equivalent to 'apply x y Lessth', but this is nice for
   infix.

   [BIIMP(x,y)] equivalent to 'apply x y Biimp', but this is nice for
   infix.

   [OR(x,y)] equivalent to 'apply x y Or', but this is nice for infix.

   [INVIMP(x,y)] equivalent to 'apply x y Invimp', but this is nice for
   infix.

   [NAND(x,y)] equivalent to 'apply x y Nand', but this is nice for infix.

   [NOR(x,y)] equivalent to 'apply x y Nor', but this is nice for infix.

   [AND(x,y)] equivalent to 'apply x y And', but this is nice for infix.

   [XOR(x,y)] equivalent to 'apply x y Xor', but this is nice for infix.

   [NOT r] construct the negation of r.

   [ITE x y z] equivalent to 'OR(AND(x, y), AND(NOT x, z))'; but more
   efficient.

   Type [pairSet] is used to represet substitutions of variables with
   other variables.

   [makepairSet [(x,x'),(y,y'),...,(z,z')]] creates the substitution
   which substitute x' for x, y' for y, ..., and z' for z.

   [replace r pairset] perfoms the substitution pairset on r.

   [compose (var, r2) r1] substitute r2 for var in r1.

   Type [assignment] represents an assignment of variables. The
   assignment [(x1,true), (x3,false), (x2, true)] corresponds to the
   bdd 'AND(x1,AND(NOT x3, x2))'.

   [restrict r assign] ... restrict the variables in assign to TRUE or
   FALSE in r.  [documentation not complete here].

   [satone r] finds a satisfying variable assignment.  Raises Domain
   if r is equal to FALSE.

   [simplify r dom] tries to simplify r by restricting it to domain d,
   ie. 'r AND dom  =  dom AND (simplify r dom)'.

   !!!! DOCUMENTATION IS MISSING ON VARIABLE REORDER STUFF !!!!

   [disableReorder()] diaples automatic reordering.  Reordering is
   enabled by default as soon as ant variable blocks have been
   defined.

   [enableReorder()] Re-enables reordering after a call to
   disableReorder.

   [satcount r] returns how many possible variable assignments there
   exist such that r is satisfied, taking all defined variables into
   account.

   [printdot r] prints r in a format suitable for use by the graph drawing
   program dot, on standard output
   (dot can be obtained from http://www.research.att.com/sw/tools/graphviz/)

   [fnprintdot fname r] prints r in a format suitable for use by the graph
   drawing program dot in the file fname.

   [printset r] prints all the truth assignments for r that would
   satisfy r, on standard output.

   [fnprintset fname r] prints all the truth assignments for r that would
   satisfy r, in the file fname.

   [bddSave name r] saves r in the file name.

   [bddLoad name] returns the bdd saved in the file name.

   [nodetable r] returns the nodetable for r.

   [setMaxincrease n] tells BuDDy that the maximum of new nodes added
   when doing an expansion of the nodetable should be n.  Return the
   old maximum.

   [setCacheratio n] sets the cache ratio to n.  For example, if n is
   four then the internal caches will be 1/4th the size of the
   nodetable.

   [verbosegc(SOME(pregc,postgc))] instructs BuDDy to print
   pregc when a BuDDy GC is initiated and print postgc when the
   BuDDy GC is completed.

   [stats()] gives various statstistical information from the
   underlying C library:
     produced     : total number of new nodes ever produced.
     nodenum      : currently allocated number of bdd nodes.
     maxnodenum   : user defined maximum number of bdd nodes.
     freenodes    : number of currently free nodes.
     minfreenodes : minimum number of nodes that should be left after
                    a garbage collection (in the bdd library).
     varnum       : number of defined bdd variables,
     cachesize    : number of entries in the internal caches.
     gbcnum       : number of garbage collection done in the bdd library.


*)
