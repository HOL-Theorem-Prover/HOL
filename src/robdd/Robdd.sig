signature Robdd =
sig
    type robdd
    type varnum = int

    val init      : int -> int -> unit
    val setvarnum : int -> unit
    val getvarnum : unit -> int
    val isRunning : unit -> bool
    val done      : unit -> unit

    val toBool   : robdd -> bool
    val fromBool : bool -> robdd

    val TRUE     : robdd
    val FALSE    : robdd

    val equal    : robdd -> robdd -> bool

    val ithvar  : varnum -> robdd
    val nithvar : varnum -> robdd

    val var     : robdd -> varnum
    val low     : robdd -> robdd
    val high    : robdd -> robdd
    

    datatype bddop =
	And | Xor | Or | Nand | Nor | Imp | Biimp
      | Diff | Lessth | Invimp

    type varSet
    val makeset  : varnum list -> varSet
    val makeset_ : varnum vector -> varSet
    val scanset  : varSet -> varnum vector
    val fromSet  : varSet -> robdd
    val toSet_   : robdd  -> varSet

    val apply  : robdd -> robdd -> bddop -> robdd
    val exist  : varSet -> robdd -> robdd
    val forall : varSet -> robdd -> robdd
    val appex  : robdd -> robdd -> bddop -> varSet -> robdd
    val appall : robdd -> robdd -> bddop -> varSet -> robdd

    val DIFF   : robdd * robdd -> robdd
    val IMP    : robdd * robdd -> robdd
    val LESSTH : robdd * robdd -> robdd
    val BIIMP  : robdd * robdd -> robdd
    val OR     : robdd * robdd -> robdd
    val INVIMP : robdd * robdd -> robdd
    val NAND   : robdd * robdd -> robdd
    val NOR    : robdd * robdd -> robdd
    val AND    : robdd * robdd -> robdd
    val XOR    : robdd * robdd -> robdd

    val NOT : robdd -> robdd


    type pairSet
    val makepairSet : (varnum * varnum) list -> pairSet
    val replace : robdd -> pairSet -> robdd

    val compose : robdd -> robdd -> varnum -> robdd


    type restriction 
    val makeRestriction : (varnum * bool) list -> restriction
    val restrict : robdd -> restriction -> robdd


    val simplify  : robdd -> robdd -> robdd


    val fnprintdot : string -> robdd -> unit
    val printdot   : robdd -> unit
    val fnprintset : string -> robdd -> unit
    val printset   : robdd -> unit

    val satcount : robdd -> real
    
    type nodetable = int * (varnum * int * int) Vector.vector
    val nodetable  : robdd -> nodetable 

    val stats    : unit -> {produced     : int,
			    nodenum      : int,
			    maxnodenum   : int,
			    freenodes    : int,
			    minfreenodes : int,
			    varnum       : int,
			    cachesize    : int,
			    gbcnum       : int}

end

(* Structue Robdd provide an interface to Jørn Linds <jl@it.dtu.dk>
   ROBDD C library.

   Type [robdd] is the abstract type of ROBDD.

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

   [fromBool b] gives the robdd representing b.

   [equal x y] is true if x and y represent equivalent boolean
   expressions. 

   [ithvar i] gives the robdd representing the i'th variable.  The
   requested variable must be in the range define by setvarnum
   starting with 0 being the first.

   [nithvar i] gives the robdd representing the negation of the i'th
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

   [fromSet varset] gives the robdd representing the conjunction of
   all the variables in varset.

   Type [bddop] represent the binary boolean operator which can be used
   when constructing robdds. Truth tables:

   x y  |  And  Xor  Or  Nand  Nor  Imp  Biimp  Diff  Lessth  Invimp
  ------|------------------------------------------------------------
   T T  |   T    F   T    F     F    T     T     F      F       T
   T F  |   F    T   T	  T     F    F     F     T      F       T
   F T  |   F    T   T	  T     F    T     F     F      T       F
   F F  |   F    F   F	  T     T    T     T     F      F       T

   [apply x y opr] constructs the robdd using the binary boolean
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

   Type [pairSet] is used to represet substitutions of variables with
   other variables.

   [makepairSet [(x,x'),(y,y'),...,(z,z')]] creates the substitution
   which substitute x' for x, y' for y, ..., and z' for z.

   [replace r pairset] perfoms the substitution pairset on r.

   [compose r1 r2 var] substitute r2 for var in r1.

   [restrict r vars] ... restrict the variables in vars to T or F in
   r.  [documentation not complete here].

   [simplify r dom] tries to simplify r by restricting it to domain d,
   ie. 'r AND dom  =  dom AND (simplify r dom)'.
   
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

   [nodetable r] returns the nodetable for r.

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
