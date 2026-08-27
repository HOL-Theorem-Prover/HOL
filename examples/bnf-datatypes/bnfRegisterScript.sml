Theory bnfRegister
Ancestors
  bnfInitial bnfFixBNF pred_set cardinal
Libs
  HolKernel Parse boolLib bossLib bnfBase bnfLib bnfFixLib testutils

(* ----------------------------------------------------------------------
    Turning a type the package defined back into a BNF.

    This is what nested recursion needs: once ‘mylist’ is a functor in
    the database, a later datatype can recurse through it.  Nothing here
    is written per datatype — the map and the set function come off the
    recursion principle and the laws off bnfFixBNFTheory — so what the
    script checks is that the theorems fixpointBNF derives are the ones
    a hand proof would have produced.

    The database is extended *in memory*: registering is a separate
    decision, and an intermediate type that only exists so that a mutual
    recursion can be built has no business being exported.
   ---------------------------------------------------------------------- *)

val db = bnfBase.fullDB()
val bnf = deriveBNFn db [alpha, “:'b1”] “:one + 'b1 # 'a”
val fix = defineFixpoint {tyname = "mylist", ABS = "mylist_ABS",
                          REP = "mylist_REP"} bnf
val cs = defineConstructors ["MyNil", "MyCons"] bnf fix

Theorem mylist_axiom = #existential_axiom cs
Theorem mylist_induction = valOf (#induction cs)
Theorem MyCons_11 = valOf (List.last (#one_one cs))
Theorem mylist_distinct = valOf (hd (#distinct cs))

(* ----------------------------------------------------------------------
    the BNF structure of the new type, derived
   ---------------------------------------------------------------------- *)

val mylist_bnf = fixpointBNF bnf fix
val bnfBase.bI mylist_info = #info mylist_bnf

(* the map and the set function are defined by the library, which saves
   their equations as mylistMAP_def and mylistSET_def *)
val mylistMAP_def = #map_thm mylist_bnf
val mylistSET_def = hd (#set_thms mylist_bnf)

Theorem mylistMAP_ID = #mapID mylist_info
Theorem mylistMAP_O = #mapO mylist_info
Theorem mylistMAPIMAGE = hd (#mapIMAGE mylist_info)
Theorem mylistMAPCONG = #mapCONG mylist_info
Theorem mylist_bnd = hd (#bndthms mylist_info)

(* equality up to the naming of type variables: a freshly parsed
   quotation invents its own *)
fun same t1 t2 = can (match_term t1) t2 andalso can (match_term t2) t1

fun checkthm nm th q =
    (tprint nm;
     if null (hyp th) andalso same (concl th) q then OK()
     else die (thm_to_string th ^ "\n  wanted: " ^ term_to_string q))

(* the map is the one the recursion principle gives: the parameter's
   function on the head, the map itself on the tail *)
val _ = checkthm "mylist's map" mylistMAP_def
   “∀f af. mylistMAP f (mylist_CONS af) =
           mylist_CONS (SUM_MAP I (f ## mylistMAP f) af)”

val _ = checkthm "mylist's map identity law" mylistMAP_ID “mylistMAP I = I”
val _ = checkthm "mylist's map composition law" mylistMAP_O
   “mylistMAP f ∘ mylistMAP g = mylistMAP (f ∘ g)”
val _ = checkthm "mylist's naturality law" mylistMAPIMAGE
   “∀f l. mylistSET (mylistMAP f l) = IMAGE f (mylistSET l)”
val _ = checkthm "mylist's congruence law" mylistMAPCONG
   “∀f g l. (∀a. a ∈ mylistSET l ⇒ f a = g a) ⇒ mylistMAP f l = mylistMAP g l”

(* the bound is the functor's own: a term has no more atoms than F's
   bound, because it has that many sub-terms and each holds that many *)
val _ = checkthm "mylist's bound" mylist_bnd “∀l. mylistSET l ≼ 𝕌(:num)”

(* the witness is the base case, and it needs no element of the
   parameter; MyNil is what it amounts to *)
val _ = tprint "mylist's witness needs no argument"
val _ =
    case #wits mylist_info of
        [(w,th)] =>
        if null (hyp th) andalso
           same (concl th) “∀a:'a1. mylistSET ((^w) a) ⊆ ∅”
        then OK() else die (thm_to_string th)
      | _ => die "not one witness"

val _ = tprint "mylist's set function is inhabited"
val _ =
    case #inhabits mylist_info of
        [(t,th)] =>
        if null (hyp th) andalso
           same (concl th) “∀v:'a1. v ∈ mylistSET ((^t) v)”
        then OK() else die (thm_to_string th)
      | _ => die "not one inhabitation fact"

(* ----------------------------------------------------------------------
    The constructor-level equations, which is the form a user reads the
    map and the set function in.  They are derived, not proved here: the
    equation the recursion principle gives is instantiated at each
    constructor's own argument and the functor simplified away.
   ---------------------------------------------------------------------- *)

val eqns = constructorEqns cs mylist_bnf

Theorem mylistMAP_thm[simp] = #map_eqns eqns
Theorem mylistSET_thm[simp] = hd (#set_eqns eqns)

val _ = checkthm "mylist's map, per constructor" mylistMAP_thm
   “(mylistMAP f MyNil = MyNil) ∧
    (mylistMAP f (MyCons a l) = MyCons (f a) (mylistMAP f l))”

(* both conjuncts are annotated because nothing links them: the parser
   would type them independently and the quotation would come out more
   general than the theorem *)
val _ = checkthm "mylist's set function, per constructor" mylistSET_thm
   “(mylistSET (MyNil : 'b1 mylist) = ∅) ∧
    (mylistSET (MyCons (a:'b1) l) = a INSERT mylistSET l)”

(* ----------------------------------------------------------------------
    extending the database with what was just derived
   ---------------------------------------------------------------------- *)

val db = bnfBase.insert (#key mylist_bnf, #info mylist_bnf) db

(* ----------------------------------------------------------------------
    and now a functor may recurse through it
   ---------------------------------------------------------------------- *)

val nested = deriveBNFn db [alpha, “:'b1”] “:one + 'b1 # 'a mylist”

val _ = tprint "deriving a functor that recurses under mylist"
val _ = if List.all (null o hyp)
                    ([#mapID nested, #mapO nested, #mapCONG nested] @
                     #mapIMAGE nested @ #bndthms nested)
        then OK() else die "hypotheses left"

(* the whole way: a datatype whose recursion goes under mylist *)
(* rose = RNode of one + 'b1 # rose mylist: the recursion goes under
   mylist, which is itself a type this package defined *)
val rose = defineFixpoint {tyname = "rose", ABS = "rose_ABS", REP = "rose_REP"}
                          nested

Theorem rose_recursion = #recursion rose
Theorem rose_prim_recursion = #prim_recursion rose

val _ = tprint "a datatype recursing under a package-defined type"
val _ =
    if #newty rose = “:'b1 rose” andalso
       null (hyp (#recursion rose)) andalso
       null (free_vars (concl (#recursion rose)))
    then OK() else die (thm_to_string (#recursion rose))

val rcs = defineConstructors ["RLeaf", "RNode"] nested rose
Theorem rose_axiom = #axiom rcs

(* ----------------------------------------------------------------------
    What a function definition over a nested recursion looks like.

    The recursive call arrives as ‘mylistMAP h l’ — the map of the type
    being recursed under — rather than as clauses replaying mylist's own
    recursion through an auxiliary function.  That is the BNF structure
    showing through: the constructor's argument is an F of the type, so
    the function's argument is an F of the results.
   ---------------------------------------------------------------------- *)

val _ = tprint "recursion through the nested map, not replayed clauses"
val _ =
    if same (concl rose_axiom)
            “∀f0 f1. ∃!h. h RLeaf = f0 ∧
                          ∀a0 a1. h (RNode a0 a1) = f1 a0 a1 (mylistMAP h a1)”
    then OK() else die (thm_to_string rose_axiom)

(* The matching induction principle is *not* the one Prim_rec derives —
   it counts recursive arguments by their type, and here the recursive
   results arrived under mylist.  The natural principle is the set-based
   one, with hypothesis "for every sub-term in mylistSET l". *)
val _ = tprint "legacy induction is declined for a nested recursion"
val _ = if not (isSome (#induction rcs)) then OK()
        else die "derived one anyway"


(* ----------------------------------------------------------------------
    Actually defining such a function.

    Prim_rec.new_recursive_definition cannot consume the nested axiom —
    it expects each recursive occurrence to be the function applied to a
    variable, and here it arrives under mylistMAP.  Going through the
    axiom directly is four lines and needs no termination argument:
    instantiate the parameters, take the existence half, and name the
    function.
   ---------------------------------------------------------------------- *)

val mylistSUM_def = Prim_rec.new_recursive_definition {
  name = "mylistSUM_def", rec_axiom = mylist_axiom,
  def = “(mylistSUM MyNil = 0n) ∧
         (mylistSUM (MyCons (n:num) l) = n + mylistSUM l)”}

val rsize_def =
    let val ax = INST_TYPE [alpha |-> numSyntax.num] rose_axiom
        val inst = SPECL [“0n”, “λ(a:'b1) (l:'b1 rose mylist) (r:num mylist).
                                    1 + mylistSUM r”] ax
    in
      new_specification ("rsize_def", ["rsize"],
                         CONV_RULE (DEPTH_CONV BETA_CONV) (EXISTENCE inst))
    end

val _ = tprint "a function whose recursive call is under a map"
val _ =
    (* the point is the shape of the recursive call, so look for it;
       matching rather than aconv, since a freshly parsed rsize gets its
       own name for the type variable *)
    if can (find_term (can (match_term “mylistMAP rsize”))) (concl rsize_def)
       andalso
       can (find_term (can (match_term “rsize RLeaf”))) (concl rsize_def)
       andalso
       null (hyp rsize_def)
    then OK() else die (thm_to_string rsize_def)

val _ = tprint "new_recursive_definition cannot take the nested axiom"
val _ =
    (ignore (Prim_rec.new_recursive_definition {
        name = "rsize2_def", rec_axiom = rose_axiom,
        def = “(rsize2 RLeaf = 0n) ∧
               (rsize2 (RNode a l) = 1 + mylistSUM (mylistMAP rsize2 l))”});
     die "accepted")
    handle HOL_ERR _ => OK()

val _ = tprint "set-based induction, split along the constructors"
val _ =
    if same (concl (#set_induction rcs))
            “∀P. P RLeaf ∧
                 (∀a l. (∀y. y ∈ mylistSET l ⇒ P y) ⇒ P (RNode a l)) ⇒
                 ∀r. P r”
    then OK() else die (thm_to_string (#set_induction rcs))
