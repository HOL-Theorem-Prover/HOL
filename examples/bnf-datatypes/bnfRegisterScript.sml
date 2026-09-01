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
val cs = defineConstructors noNames [("MyNil", 0), ("MyCons", 2)] bnf fix

Theorem mylist_axiom = #existential_axiom cs
Theorem mylist_induction = valOf (#induction cs)
Theorem MyCons_11 = valOf (List.last (#one_one cs))
Theorem mylist_distinct = valOf (hd (#distinct cs))

(* ----------------------------------------------------------------------
    the BNF structure of the new type, derived
   ---------------------------------------------------------------------- *)

val mylist_bnf = fixpointBNF noNames bnf fix
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

val rcs = defineConstructors noNames [("RLeaf", 0), ("RNode", 2)] nested rose
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
    (* the axiom names its answer type itself; the value for the nullary
       constructor is of that type *)
    let val answer = type_of (hd (#1 (strip_forall (concl rose_axiom))))
        val ax = INST_TYPE [answer |-> numSyntax.num] rose_axiom
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

(* ----------------------------------------------------------------------
    The case constant, and the TypeBase entry.

    This is the whole way: from the axiom the package derived, a case
    constant that `Prim_rec.define_case_constant` cannot build for a
    nested type, and then the entry the rest of HOL reads — after which
    the type's own tactics and the simplifier work as they do for a type
    the old package defined.
   ---------------------------------------------------------------------- *)

val mylist_case = hd (defineCases mylist_axiom)

(* each conjunct binds its own v and f, so nothing ties the two
   together: the annotations do it *)
val _ = checkthm "mylist's case constant" mylist_case
   “(∀(v:'r) f. mylist_CASE (MyNil : 'b1 mylist) v f = v) ∧
    (∀(a:'b1) l (v:'r) f. mylist_CASE (MyCons a l) v f = f a l)”

val rose_case = hd (defineCases rose_axiom)

val _ = tprint "define_case_constant cannot take the nested axiom"
val _ = (ignore (Prim_rec.define_case_constant rose_axiom); die "accepted")
        handle HOL_ERR _ => OK()

val _ = checkthm "and the nested type's case constant is derived anyway"
   rose_case
   “(∀(v:'r) f. rose_CASE (RLeaf : 'b1 rose) v f = v) ∧
    (∀(a:'b1) l (v:'r) f. rose_CASE (RNode a l) v f = f a l)”

val mylist_tyinfo =
    hd (typeBaseInfo {axiom = #axiom cs, induction = mylist_induction,
                      case_defs = [mylist_case],
                      rewrites = [[mylistMAP_thm, mylistSET_thm]],
                      names = [noNames]})

val _ = TypeBase.export [mylist_tyinfo]

val _ = tprint "the type is in TypeBase"
val _ =
    if isSome (TypeBase.read {Thy = current_theory(), Tyop = "mylist"}) andalso
       null (hyp (TypeBase.nchotomy_of “:'a mylist”)) andalso
       aconv (TypeBase.case_const_of “:'a mylist”)
             (repeat rator (lhs (#2 (strip_forall (hd (strip_conj
                                       (concl mylist_case)))))))
    then OK() else die "no entry"

(* and what the entry is for: the type's own tactics, its case syntax,
   and the map and set equations in the simplifier *)
val _ = tprint "induction and the simplifier over the new type"
val _ =
    let val th = Q.prove (‘∀l. mylistMAP I l = l’, Induct_on ‘l’ >> simp[])
    in
      if null (hyp th) then OK() else die (thm_to_string th)
    end

val _ = tprint "case expressions over the new type"
val _ =
    let val th = Q.prove (‘(case MyCons a l of MyNil => F | MyCons _ _ => T)’,
                          simp[])
    in
      if null (hyp th) then OK() else die (thm_to_string th)
    end

(* ----------------------------------------------------------------------
    And the whole way from a specification as written.

    The steps are the ones above, with the specification supplying what
    was written by hand there: the functor, the parameters and the
    constructors' names.
   ---------------------------------------------------------------------- *)

val spec = parseSpec `expr = Var 'a | Lit num | Op expr num expr`

val _ = tprint "a specification's functor"
val _ =
    if #tynames spec = ["expr"] andalso
       #constructors spec = [[("Var",1), ("Lit",1), ("Op",3)]] andalso
       List.map #1 (#functors spec) = [“:'b1 + num + 'a # num # 'a”]
    then OK()
    else die (String.concatWith ", "
                (List.map (type_to_string o #1) (#functors spec)))

val ebnf = deriveBNFn (bnfBase.fullDB()) (alpha :: #params spec)
                      (#1 (hd (#functors spec)))
val efix = defineFixpoint {tyname = "expr", ABS = "expr_ABS",
                           REP = "expr_REP"} ebnf
val ecs = defineConstructors noNames (hd (#constructors spec)) ebnf efix
val eres = fixpointBNF noNames ebnf efix
val eeqns = constructorEqns ecs eres

Theorem expr_axiom = #existential_axiom ecs
Theorem exprMAP_thm[simp] = #map_eqns eeqns
Theorem exprSET_thm[simp] = hd (#set_eqns eeqns)

val _ = TypeBase.export
          (typeBaseInfo {axiom = expr_axiom,
                         induction = valOf (#induction ecs),
                         case_defs = defineCases expr_axiom,
                         rewrites = [[exprMAP_thm, exprSET_thm]],
                         names = [noNames]})

val _ = tprint "a specified type behaves like a datatype"
val _ =
    let
      val th1 = Q.prove (‘∀e. exprMAP I e = e’, Induct_on ‘e’ >> simp[])
      val th2 = Q.prove (‘Var a ≠ Lit n ∧ (Op e1 n e2 = Op e3 n e4 ⇔
                                           e1 = e3 ∧ e2 = e4)’, simp[])
      val th3 = Q.prove (‘case Lit n of
                            Var a => F | Lit m => T | Op _ _ _ => F’,
                         simp[])
    in
      if List.all (null o hyp) [th1, th2, th3] then OK()
      else die "not proved"
    end

(* ----------------------------------------------------------------------
    The same definition, through the axiom rather than by hand.
   ---------------------------------------------------------------------- *)

val {definition = rsize2_def, unique = rsize2_unique} =
    defineRecursion {
      name = "rsize2_def",
      axiom = INST_TYPE [alpha |-> numSyntax.num] rose_axiom,
      def = “(rsize2 RLeaf = 0n) ∧
             (rsize2 (RNode a l) = 1 + mylistSUM (mylistMAP rsize2 l))”}

val _ = tprint "a nested definition, from its clauses"
val _ =
    if null (hyp rsize2_def) andalso
       (* the conjuncts share no variable, so the annotation is what
          ties their types together *)
       same (concl rsize2_def)
            “(rsize2 (RLeaf : 'p rose) = 0n) ∧
             ∀(a:'p) l. rsize2 (RNode a l) =
                        1 + mylistSUM (mylistMAP rsize2 l)”
    then OK() else die (thm_to_string rsize2_def)

(* the nested type's own entry: its induction principle is the
   set-based one, since a nested recursion has no other *)
(* the nested type's own entry: its induction principle is the
   set-based one, since a nested recursion has no other, and TypeBase
   reads the existence half of the axiom *)
val rose_tyinfos =
    typeBaseInfo {axiom = #axiom rcs,
                  induction = #set_induction rcs,
                  case_defs = [rose_case], rewrites = [[]],
                  names = [noNames]}
val _ = TypeBase.export rose_tyinfos

(* ----------------------------------------------------------------------
    What Define makes of the same type.

    With the entry in place, a definition written the way the axiom
    hands its recursive calls over — under the map — goes through
    Define as it stands.  One written the way the old package's nested
    axioms take them, with a function of its own over the operator
    recursed under, does not yet: that is a well-founded recursion, and
    the measure it wants is a size function, which the package does not
    define yet.
   ---------------------------------------------------------------------- *)

val _ = tprint "Define takes a definition in the shape the axiom hands over"
val _ =
    let val th = TotalDefn.Define
                   ‘rsize3 RLeaf = 0n ∧
                    rsize3 (RNode a l) = 1 + mylistSUM (mylistMAP rsize3 l)’
    in
      if null (hyp th) andalso
         can (find_term (can (match_term “mylistMAP rsize3”))) (concl th)
      then OK() else die (thm_to_string th)
    end

(* The other way round — a function of its own over the operator
   recursed under, which is how the old package's nested axioms take a
   definition — is a well-founded recursion.  What it wants is a
   measure, and the entry brought one: the size, and the lemma that
   connects its two shapes.

   `Define` itself cannot be called here: its wrapper hands a failure to
   `Feedback.render_exn`, which in a script prints and exits rather than
   raising.  One layer down raises the HOL_ERR it should. *)

val _ = tprint "a function of its own over the operator recursed under"
val _ =
    let val dfn = Defn.Hol_defn "rsize4_def"
                    ‘rsize4 RLeaf = 0n ∧
                     rsize4 (RNode a l) = 1 + rsizel l ∧
                     rsizel MyNil = 0n ∧
                     rsizel (MyCons r rs) = rsize4 r + rsizel rs’
    in
      case Lib.total TotalDefn.primDefine dfn of
          NONE => die "not accepted"
        | SOME _ => OK()   (* and no measure was supplied *)
    end

val _ = tprint "defineRecursion says so rather than guessing"
val _ =
    (ignore (defineRecursion {
        name = "rsize5_def",
        axiom = INST_TYPE [alpha |-> numSyntax.num] rose_axiom,
        def = “(rsize5 RLeaf = 0n) ∧
               (rsize5 (RNode a l) = 1 + rsizel5 l) ∧
               (rsizel5 MyNil = 0n) ∧
               (rsizel5 (MyCons r rs) = rsize5 r + rsizel5 rs)”});
     die "accepted")
    handle HOL_ERR e =>
           if String.isSubstring "Define is the route" (Feedback.message_of e)
           then OK() else die (Feedback.message_of e)

(* ----------------------------------------------------------------------
    What a termination proof needs, which the entry brought with it.

    A size of a nested argument is a fold — `mylist_size (rose_size f) l`
    — and what the axiom hands over is a map, so the size reads
    `mylist_size (λx. x) (mylistMAP (rose_size f) l)`.  The two are
    connected by a lemma the registration proves and exports as a
    *termination* simplification, and with it Define finds the
    well-founded relation for a definition written the old way by
    itself.
   ---------------------------------------------------------------------- *)

val _ = tprint "the size lemma the entry proved"
val _ =
    let val th = DB.fetch "-" "mylist_size_MAP"
    in
      if null (hyp th) andalso
         same (concl th)
              “∀f l. mylist_size (λx. x) (mylistMAP f l) = mylist_size f l”
      then OK() else die (thm_to_string th)
    end

val _ = tprint "a sub-term is smaller, with the sizes as defined"
val _ =
    let val th = Q.prove (‘∀f a l. mylist_size (rose_size f) l <
                                   rose_size f (RNode a l)’,
                          simp[#2 (TypeBase.size_of “:'a rose”),
                               #2 (TypeBase.size_of “:'a mylist”),
                               DB.fetch "-" "mylist_size_MAP"])
    in
      if null (hyp th) then OK() else die "not proved"
    end

val _ = tprint "the types' size functions"
val _ =
    let val (mtm, mth) = TypeBase.size_of “:'a mylist”
        val (rtm, rth) = TypeBase.size_of “:'a rose”
    in
      if same (concl mth)
              “∀f. mylist_size f MyNil = 0 ∧
                   ∀a l. mylist_size f (MyCons a l) =
                         1 + f a + mylist_size f l”
         andalso
         (* the nested argument's size is its own type's, at the map the
            axiom hands over *)
         same (concl rth)
              “∀f. rose_size f RLeaf = 0 ∧
                   ∀a l. rose_size f (RNode a l) =
                         1 + f a +
                         mylist_size (λx. x) (mylistMAP (rose_size f) l)”
      then OK() else die (thm_to_string rth)
    end

(* ----------------------------------------------------------------------
    Naming the constants the package generates.

    A type the rest of HOL already knows has names of its own for its
    map and its set function — `list` has MAP and LIST_TO_SET — and
    Overloading onto generated names will not do, because a user writes
    `list$MAP`, which needs a constant of that name in that theory.  So
    a declaration says the names in its attributes, and the package uses
    them where it would otherwise have named them after the type.
   ---------------------------------------------------------------------- *)

val nspec =
    parseSpec `stack[map=STMAP,set=stack_to_set,rel=STACK_REL,size=stack_sz] =
                 Empty | Push 'a stack`

val _ = tprint "a specification's names"
val _ =
    if #names nspec = [{map = SOME "STMAP", sets = [SOME "stack_to_set"],
                        relator = SOME "STACK_REL", size = SOME "stack_sz"}]
    then OK() else die "not as expected"

val nbnf = deriveBNFn (bnfBase.fullDB()) (alpha :: #params nspec)
                      (#1 (hd (#functors nspec)))
val nfix = defineFixpoint {tyname = "stack", ABS = "stack_ABS",
                           REP = "stack_REP"} nbnf
val ncs = defineConstructors noNames (hd (#constructors nspec)) nbnf nfix
val nres = fixpointBNF (hd (#names nspec)) nbnf nfix
val neqns = constructorEqns ncs nres

Theorem stack_axiom = #existential_axiom ncs
Theorem STMAP_thm[simp] = #map_eqns neqns
Theorem stack_to_set_thm[simp] = hd (#set_eqns neqns)

val _ = TypeBase.export
          (typeBaseInfo {axiom = stack_axiom,
                         induction = valOf (#induction ncs),
                         case_defs = defineCases stack_axiom,
                         rewrites = [[STMAP_thm, stack_to_set_thm]],
                         names = #names nspec})

val _ = tprint "the generated constants take the names asked for"
val _ =
    let val ns = List.map (#1 o dest_const) (Theory.constants "-")
        fun has s = Lib.mem s ns
    in
      if List.all has ["STMAP", "stack_to_set", "STACK_REL", "stack_sz"]
         andalso
         not (List.exists has ["stackMAP", "stackSET", "stackREL",
                               "stack_size"])
      then OK() else die "not as expected"
    end

val _ = tprint "and they are the type's own map, set and size"
val _ =
    let val th1 = Q.prove (‘∀s : 'a stack. STMAP I s = s’,
                           Induct_on ‘s’ >> simp[])
        val th2 = Q.prove (‘stack_to_set (Push a s) = a INSERT stack_to_set s’,
                           simp[])
        val (sztm, szth) = TypeBase.size_of “:'a stack”
    in
      if List.all (null o hyp) [th1, th2] andalso
         same (concl szth)
              “∀f. stack_sz f Empty = 0 ∧
                   ∀a s. stack_sz f (Push a s) = 1 + f a + stack_sz f s”
      then OK() else die "not as expected"
    end
