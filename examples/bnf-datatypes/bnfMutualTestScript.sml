Theory bnfMutualTest
Ancestors
  bnfInitial bnfFixBNF bnfMutual pred_set cardinal
Libs
  HolKernel Parse boolLib bossLib bnfBase bnfLib bnfFixLib testutils

(* ----------------------------------------------------------------------
    Mutual recursion, through the nesting.

    The specifications behind the two families below are

        mt1 = A 'p | B mt1 mt2      mt2 = C mt1 | D 'p mt2
        nt1 = E (nt2 option) | F 'p  nt2 = G nt1 | H nt2 nt2

    and their functors are what parse_bnf's translation produces: α for
    the type's own recursion and 'a1 for the sibling's slot.  The second
    family has the sibling under an option, so the recursion into it is
    nested twice over.

    What is checked is that the pair's recursion principle comes out
    ground and hypothesis-free — a free variable would mean one of
    bnfMutualTheory's parameters was never pinned down — and that it says
    what it should: each function is applied to its own type's
    occurrences and the other to the sibling's.
   ---------------------------------------------------------------------- *)

fun same t1 t2 = can (match_term t1) t2 andalso can (match_term t2) t1

val b1 = mk_vartype "'b1"

val mt = defineMutual {tyname1 = "mt1", tyname2 = "mt2"}
                      (bnfBase.fullDB()) [b1]
                      (“:'b1 + 'a # 'a1”, “:'a1 + 'b1 # 'a”)

val _ = tprint "the types a mutually recursive pair becomes"
val _ =
    if #ty1 mt = “:'b1 mt1” andalso #ty2 mt = “:('b1 mt1, 'b1) mt2” then OK()
    else die (type_to_string (#ty1 mt) ^ " and " ^ type_to_string (#ty2 mt))

Theorem mt_recursion = #recursion mt

val _ = tprint "the pair's recursion principle"
val _ =
    if null (hyp (#recursion mt)) andalso
       null (free_vars (concl (#recursion mt))) andalso
       same (concl (#recursion mt))
            “∀t1 t2.
               (∃h1 h2.
                  (∀af. h1 (mt1_CONS af) = t1 (SUM_MAP I (h1 ## h2) af)) ∧
                  (∀af. h2 (mt2_CONS af) = t2 (SUM_MAP h1 (I ## h2) af))) ∧
               ∀h1 h2 k1 k2.
                 ((∀af. h1 (mt1_CONS af) = t1 (SUM_MAP I (h1 ## h2) af)) ∧
                  (∀af. h2 (mt2_CONS af) = t2 (SUM_MAP h1 (I ## h2) af))) ∧
                 ((∀af. k1 (mt1_CONS af) = t1 (SUM_MAP I (k1 ## k2) af)) ∧
                  (∀af. k2 (mt2_CONS af) = t2 (SUM_MAP k1 (I ## k2) af))) ⇒
                 h1 = k1 ∧ h2 = k2”
    then OK() else die (thm_to_string (#recursion mt))

(* ----------------------------------------------------------------------
    the pair's induction principle: each clause gives the induction
    hypothesis for *both* types, through the two set functions of that
    type's functor — the type's own occurrences and the sibling's
   ---------------------------------------------------------------------- *)

val a1 = mk_vartype "'a1"
val bnfF1 = deriveBNFn (#db mt) [alpha, a1, b1] “:'b1 + 'a # 'a1”
val bnfF2 = deriveBNFn (#db mt) [alpha, a1, b1] “:'a1 + 'b1 # 'a”

(* A clause covers one type's constructor.  Its two hypotheses are the
   induction hypotheses for the two types, each through the set function
   of *this* functor for that type's argument, and in the functor's own
   argument order — the recursive argument first. *)
fun clauseOK h1 h2 (Pcon,cons) clause =
    let val (af, body) = dest_forall clause
        val (hyps, con) = dest_imp body
        fun memberOf (p,st) h =
            let val (v, b) = dest_forall h
                val (mem, app) = dest_imp b
            in
              aconv app (mk_comb (p, v)) andalso
              can (match_term st) (rator (rand mem)) andalso
              aconv (rand (rand mem)) af
            end
    in
      case strip_conj hyps of
          [c1,c2] => memberOf h1 c1 andalso memberOf h2 c2 andalso
                     aconv con (mk_comb (Pcon, mk_comb (cons, af)))
        | _ => false
    end

val _ = tprint "the pair's induction principle"
val _ =
    let val th = #induction mt
        val ([P1,P2], body) = strip_forall (concl th)
        val (clauses, con) = dest_imp body
        val (c1,c2) = pairSyntax.dest_pair (pairSyntax.mk_pair
                                              (hd (strip_conj clauses),
                                               List.last (strip_conj clauses)))
        val n = mk_var("n", #ty1 mt) and m = mk_var("m", #ty2 mt)
    in
      if null (hyp th) andalso null (free_vars (concl th)) andalso
         (* mt1's functor is 'b1 + mt1 # mt2, so its own argument comes
            first; mt2's is mt1 + 'b1 # mt2, so the sibling's does *)
         clauseOK (P1, hd (#sets bnfF1)) (P2, List.nth (#sets bnfF1, 1))
                  (P1, #cons1 mt) c1 andalso
         clauseOK (P1, List.nth (#sets bnfF2, 1)) (P2, hd (#sets bnfF2))
                  (P2, #cons2 mt) c2 andalso
         aconv con (mk_conj (mk_forall (n, mk_comb (P1,n)),
                             mk_forall (m, mk_comb (P2,m))))
      then OK() else die (thm_to_string th)
    end

(* the same principle in the form HOL's own datatype axioms take, where
   each function is handed the constructor's arguments as well as the
   results of the recursive calls *)
val _ = tprint "the pair's primitive recursion"
val _ =
    if null (hyp (#prim_recursion mt)) andalso
       null (free_vars (concl (#prim_recursion mt))) andalso
       same (concl (#prim_recursion mt))
            “∀t1 t2.
               (∃h1 h2.
                  (∀af. h1 (mt1_CONS af) =
                        t1 af (SUM_MAP I (h1 ## h2) af)) ∧
                  (∀af. h2 (mt2_CONS af) =
                        t2 af (SUM_MAP h1 (I ## h2) af))) ∧
               ∀h1 h2 k1 k2.
                 ((∀af. h1 (mt1_CONS af) =
                        t1 af (SUM_MAP I (h1 ## h2) af)) ∧
                  (∀af. h2 (mt2_CONS af) =
                        t2 af (SUM_MAP h1 (I ## h2) af))) ∧
                 ((∀af. k1 (mt1_CONS af) =
                        t1 af (SUM_MAP I (k1 ## k2) af)) ∧
                  (∀af. k2 (mt2_CONS af) =
                        t2 af (SUM_MAP k1 (I ## k2) af))) ⇒
                 h1 = k1 ∧ h2 = k2”
    then OK() else die (thm_to_string (#prim_recursion mt))

(* ----------------------------------------------------------------------
    and the same principle one constructor at a time, which is the form a
    proof is written against
   ---------------------------------------------------------------------- *)

val cs1 = defineConstructors ["A", "B"] (#bnf1 mt) (#fix1 mt)
val cs2 = defineConstructors ["C", "D"] (#bnf2 mt) (#fix2 mt)

Theorem mt_induction = mutualInduction (cs1, cs2) mt

val _ = tprint "the pair's induction, per constructor"
val _ =
    if null (hyp mt_induction) andalso
       same (concl mt_induction)
            “∀P1 P2.
               ((∀a0. P1 (A a0)) ∧ (∀a0 a1. P1 a0 ∧ P2 a1 ⇒ P1 (B a0 a1))) ∧
               ((∀a0. P1 a0 ⇒ P2 (C a0)) ∧
                (∀a0 a1. P2 a1 ⇒ P2 (D a0 a1))) ⇒
               (∀n. P1 n) ∧ ∀m. P2 m”
    then OK() else die (thm_to_string mt_induction)

(* the constructors' own theorems come from each type's construction: the
   second type's are those of the sibling functor, at the first *)
val _ = tprint "the pair's constructors are distinct and injective"
val _ =
    case (hd (#distinct cs1), List.last (#one_one cs2)) of
        (SOME d, SOME i) =>
          if null (hyp d) andalso null (hyp i) then OK()
          else die (thm_to_string d ^ "\n" ^ thm_to_string i)
      | _ => die "not derived"

(* ----------------------------------------------------------------------
    and with the sibling under a type operator of its own
   ---------------------------------------------------------------------- *)

val nt = defineMutual {tyname1 = "nt1", tyname2 = "nt2"} (#db mt) [b1]
                      (“:'a1 option + 'b1”, “:'a1 + 'a # 'a”)

(* the parameter is used by the first type alone, so the sibling's own
   operator does not take it: nt2 is a functor in the first type only *)
val _ = tprint "a sibling reached through another functor"
val _ =
    if #ty1 nt = “:'b1 nt1” andalso #ty2 nt = “:'b1 nt1 nt2” andalso
       null (hyp (#recursion nt)) andalso
       null (free_vars (concl (#recursion nt))) andalso
       null (hyp (#induction nt)) andalso
       null (free_vars (concl (#induction nt))) andalso
       same (concl (#recursion nt))
            “∀t1 t2.
               (∃h1 h2.
                  (∀af. h1 (nt1_CONS af) =
                        t1 (SUM_MAP (OPTION_MAP h2) I af)) ∧
                  (∀af. h2 (nt2_CONS af) = t2 (SUM_MAP h1 (h2 ## h2) af))) ∧
               ∀h1 h2 k1 k2.
                 ((∀af. h1 (nt1_CONS af) =
                        t1 (SUM_MAP (OPTION_MAP h2) I af)) ∧
                  (∀af. h2 (nt2_CONS af) = t2 (SUM_MAP h1 (h2 ## h2) af))) ∧
                 ((∀af. k1 (nt1_CONS af) =
                        t1 (SUM_MAP (OPTION_MAP k2) I af)) ∧
                  (∀af. k2 (nt2_CONS af) = t2 (SUM_MAP k1 (k2 ## k2) af))) ⇒
                 h1 = k1 ∧ h2 = k2”
    then OK() else die (thm_to_string (#recursion nt))

(* ----------------------------------------------------------------------
    A family of any size.

    The pair's reduction generalises by taking the family from the last
    member back, each type built with the earlier members' slots left as
    parameters and nested through the later ones.  The family below is

        ft1 = A 'p | B ft1 ft2 ;  ft2 = C ft3 | D 'p ft2 ;  ft3 = E ft1 | F ft3

    where every member is reached from every other, and the caller says
    which variable of each functor stands for which member — the
    translation of a specification numbers them per functor, so the same
    'a1 means different things in different ones.
   ---------------------------------------------------------------------- *)

val a1 = mk_vartype "'a1"
val a2 = mk_vartype "'a2"

val fam = defineFamily {tynames = ["ft1", "ft2", "ft3"]} (#db nt) [b1]
            [(“:'b1 + 'a # 'a1”, [alpha, a1, a2]),
             (“:'a2 + 'b1 # 'a”, [a1, alpha, a2]),
             (“:'a1 + 'a”,       [a1, a2, alpha])]

val _ = tprint "the types a three-member family becomes"
val _ =
    if #types fam = [“:'b1 ft1”, “:('b1, 'b1 ft1) ft2”, “:'b1 ft1 ft3”]
    then OK()
    else die (String.concatWith ", " (List.map type_to_string (#types fam)))

(* each member's constructor takes its own functor at the family's types:
   a member the specification does not mention is simply absent from it *)
val _ = tprint "the family's constructors"
val _ =
    let val tys = List.map type_of (#cons fam)
    in
      if tys = [“:'b1 + 'b1 ft1 # ('b1, 'b1 ft1) ft2 -> 'b1 ft1”,
                “:'b1 ft1 ft3 + 'b1 # ('b1, 'b1 ft1) ft2 ->
                  ('b1, 'b1 ft1) ft2”,
                “:'b1 ft1 + 'b1 ft1 ft3 -> 'b1 ft1 ft3”]
      then OK() else die (String.concatWith ", " (List.map type_to_string tys))
    end

(* and each is an ordinary datatype whose recursion is nested through the
   members after it *)
val _ = tprint "each member's own recursion"
val _ =
    let val ths = List.map #recursion (#fixes fam)
    in
      if List.all (null o hyp) ths andalso
         List.all (null o free_vars o concl) ths andalso
         same (concl (hd ths))
              “∀t. ∃!h. ∀af. h (ft1_CONS af) =
                             t (SUM_MAP I (h ## ft2MAP I h) af)”
      then OK() else die (thm_to_string (hd ths))
    end

(* ----------------------------------------------------------------------
    The sibling is a functor in the database, in memory: that is what the
    nesting was built on, and it is also what lets a *further* datatype
    recurse through the pair.
   ---------------------------------------------------------------------- *)

val _ = tprint "a datatype recursing through one of the pair"
val _ =
    let val d = deriveBNFn (#db nt) [alpha, b1] “:one + ('a, 'b1) mt2”
        val fix = defineFixpoint {tyname = "mrose", ABS = "mrose_ABS",
                                  REP = "mrose_REP"} d
    in
      if null (hyp (#recursion fix)) andalso
         null (free_vars (concl (#recursion fix))) andalso
         #newty fix = “:'b1 mrose”
      then OK() else die (thm_to_string (#recursion fix))
    end

(* ----------------------------------------------------------------------
    and the family's recursion principle, which is the pair's existence
    half with the sibling a family rather than a type
   ---------------------------------------------------------------------- *)

Theorem fam_recursion = familyRecursion fam

val _ = tprint "the family's recursion principle"
val _ =
    if null (hyp fam_recursion) andalso
       null (free_vars (concl fam_recursion)) andalso
       same (concl fam_recursion)
            “∀t0 t1 t2.
               ∃h0 h1 h2.
                 (∀af. h0 (ft1_CONS af) = t0 (SUM_MAP I (h0 ## h1) af)) ∧
                 (∀af. h1 (ft2_CONS af) = t1 (SUM_MAP h2 (I ## h1) af)) ∧
                 ∀af. h2 (ft3_CONS af) = t2 (SUM_MAP h0 h2 af)”
    then OK() else die (thm_to_string fam_recursion)

(* the pair is the two-member case of the same construction, and gives
   back what defineMutual's own reduction does *)
val fam2 = defineFamily {tynames = ["gt1", "gt2"]} (#db fam) [b1]
             [(“:'b1 + 'a # 'a1”, [alpha, a1]),
              (“:'a1 + 'b1 # 'a”, [a1, alpha])]

val _ = tprint "a two-member family's recursion principle"
val _ =
    let val th = familyRecursion fam2
    in
      if null (hyp th) andalso null (free_vars (concl th)) andalso
         same (concl th)
              “∀t0 t1.
                 ∃h0 h1.
                   (∀af. h0 (gt1_CONS af) = t0 (SUM_MAP I (h0 ## h1) af)) ∧
                   ∀af. h1 (gt2_CONS af) = t1 (SUM_MAP h0 (I ## h1) af)”
      then OK() else die (thm_to_string th)
    end

(* which is the existence half of what defineMutual proves for a pair,
   and the same holds of the principle that hears the arguments *)
val _ = tprint "a two-member family's primitive recursion"
val _ =
    let val th = familyPrimRecursion fam2
    in
      if null (hyp th) andalso null (free_vars (concl th)) andalso
         same (concl th)
              “∀t0 t1.
                 ∃h0 h1.
                   (∀af. h0 (gt1_CONS af) = t0 af (SUM_MAP I (h0 ## h1) af)) ∧
                   ∀af. h1 (gt2_CONS af) = t1 af (SUM_MAP h0 (I ## h1) af)”
      then OK() else die (thm_to_string th)
    end

(* ----------------------------------------------------------------------
    and the same principle one constructor at a time.

    Each member's constructors come from its own construction, where the
    members before it are still parameters; the axiom states them at the
    family's types.
   ---------------------------------------------------------------------- *)

val fnames = [["FA","FB"], ["FC","FD"], ["FE","FG"]]
val fcss = List.tabulate
             (3, fn j => defineConstructors (List.nth (fnames, j))
                                            (List.nth (#bnfs fam, j))
                                            (List.nth (#fixes fam, j)))

Theorem fam_axiom = familyAxiom fcss fam fam_recursion

val _ = tprint "the family's recursion, per constructor"
val _ =
    if null (hyp fam_axiom) andalso
       same (concl fam_axiom)
            “∀f0 f1 f2 f3 f4 f5.
               ∃h0 h1 h2.
                 (∀a0. h0 (FA a0) = f0 a0) ∧
                 (∀a0 a1. h0 (FB a0 a1) = f1 (h0 a0) (h1 a1)) ∧
                 (∀a0. h1 (FC a0) = f2 (h2 a0)) ∧
                 (∀a0 a1. h1 (FD a0 a1) = f3 a0 (h1 a1)) ∧
                 (∀a0. h2 (FE a0) = f4 (h0 a0)) ∧
                 ∀a0. h2 (FG a0) = f5 (h2 a0)”
    then OK() else die (thm_to_string fam_axiom)

(* and in the shape HOL's own axiom for a mutually recursive family
   takes, where a target hears the constructor's arguments as well *)

Theorem fam_prim_axiom = familyAxiom fcss fam (familyPrimRecursion fam)

val _ = tprint "the family's primitive recursion, per constructor"
val _ =
    if null (hyp fam_prim_axiom) andalso
       same (concl fam_prim_axiom)
            “∀f0 f1 f2 f3 f4 f5.
               ∃h0 h1 h2.
                 (∀a0. h0 (FA a0) = f0 a0) ∧
                 (∀a0 a1. h0 (FB a0 a1) = f1 a0 a1 (h0 a0) (h1 a1)) ∧
                 (∀a0. h1 (FC a0) = f2 a0 (h2 a0)) ∧
                 (∀a0 a1. h1 (FD a0 a1) = f3 a0 a1 (h1 a1)) ∧
                 (∀a0. h2 (FE a0) = f4 a0 (h0 a0)) ∧
                 ∀a0. h2 (FG a0) = f5 a0 (h2 a0)”
    then OK() else die (thm_to_string fam_prim_axiom)

(* ----------------------------------------------------------------------
    Uniqueness, and the induction principle that comes of it.

    A member's own function is determined by pairing it with the
    identity — that pairing solves member i's own recursion — and the
    sub-family's principle determines the rest, so the family's
    equations have exactly one solution.  Reading that at the booleans
    is an induction principle.
   ---------------------------------------------------------------------- *)

val fam_principle = familyPrinciple fam

Theorem fam_uniqueness = familyUniqueness fam_principle

val _ = tprint "the family's solutions are unique"
val _ =
    if null (hyp fam_uniqueness) andalso
       null (free_vars (concl fam_uniqueness)) andalso
       same (concl fam_uniqueness)
            “∀t0 t1 t2 h0 h1 h2 k0 k1 k2.
               ((∀af. h0 (ft1_CONS af) = t0 af (SUM_MAP I (h0 ## h1) af)) ∧
                (∀af. h1 (ft2_CONS af) = t1 af (SUM_MAP h2 (I ## h1) af)) ∧
                ∀af. h2 (ft3_CONS af) = t2 af (SUM_MAP h0 h2 af)) ∧
               ((∀af. k0 (ft1_CONS af) = t0 af (SUM_MAP I (k0 ## k1) af)) ∧
                (∀af. k1 (ft2_CONS af) = t1 af (SUM_MAP k2 (I ## k1) af)) ∧
                ∀af. k2 (ft3_CONS af) = t2 af (SUM_MAP k0 k2 af)) ⇒
               h0 = k0 ∧ h1 = k1 ∧ h2 = k2”
    then OK() else die (thm_to_string fam_uniqueness)

(* the set-based principle: each clause's hypothesis is what the
   functor's set function for a member's type holds of the argument *)
val fam_set_induction = familySetInduction fam fam_principle

val _ = tprint "the family's induction principle"
val _ =
    let val ([P0,P1,P2], body) = strip_forall (concl fam_set_induction)
        val (clauses, con) = dest_imp body
        (* a clause's hypotheses are those members' predicates the
           functor holds values of, through this functor's own sets *)
        fun clauseOK (j, Ps) clause =
            let val (af, imp) = dest_forall clause
                val (hyps, c) = dest_imp imp
                val bnf = List.nth (#functors fam, j)
                fun hypOK ((m,P), h) =
                    let val (y, b) = dest_forall h
                        val (mem, app) = dest_imp b
                    in
                      aconv app (mk_comb (P, y)) andalso
                      aconv (rand (rand mem)) af andalso
                      can (match_term (List.nth (#sets bnf, m)))
                          (rator (rand mem))
                    end
            in
              aconv c (mk_comb (List.nth ([P0,P1,P2], j),
                                mk_comb (List.nth (#cons fam, j), af))) andalso
              ListPair.allEq hypOK (Ps, strip_conj hyps)
            end
    in
      if null (hyp fam_set_induction) andalso
         null (free_vars (concl fam_set_induction)) andalso
         (* ft1's functor holds ft1s and ft2s, ft2's ft2s and ft3s, and
            ft3's ft1s and ft3s *)
         ListPair.allEq (fn ((j,Ps),c) => clauseOK (j,Ps) c)
                        ([(0, [(0,P0), (1,P1)]),
                          (1, [(1,P1), (2,P2)]),
                          (2, [(0,P0), (2,P2)])],
                         strip_conj clauses) andalso
         aconv con (list_mk_conj
                      (List.map (fn (ty,P) =>
                                    let val x = mk_var("x", ty)
                                    in mk_forall (x, mk_comb (P,x)) end)
                                (ListPair.zipEq (#types fam, [P0,P1,P2]))))
      then OK() else die (thm_to_string fam_set_induction)
    end

Theorem fam_induction = familyInduction fcss fam fam_set_induction

val _ = tprint "the family's induction, per constructor"
val _ =
    if null (hyp fam_induction) andalso
       same (concl fam_induction)
            “∀P0 P1 P2.
               (∀a0. P0 (FA a0)) ∧ (∀a0 a1. P0 a0 ∧ P1 a1 ⇒ P0 (FB a0 a1)) ∧
               (∀a0. P2 a0 ⇒ P1 (FC a0)) ∧
               (∀a0 a1. P1 a1 ⇒ P1 (FD a0 a1)) ∧
               (∀a0. P0 a0 ⇒ P2 (FE a0)) ∧ (∀a0. P2 a0 ⇒ P2 (FG a0)) ⇒
               (∀x. P0 x) ∧ (∀x. P1 x) ∧ ∀x. P2 x”
    then OK() else die (thm_to_string fam_induction)

(* ----------------------------------------------------------------------
    The map and the set functions of each member, one constructor at a
    time.

    A member is a functor in the parameters and in the slots of the
    members *before* it, so its map takes a function for each of those;
    what a user of the family reads as "map over ft2" is that map at the
    earlier members' own maps, which is exactly what turns up in ft1's
    own equation.
   ---------------------------------------------------------------------- *)

fun memberEqns j =
    constructorEqns (List.nth (fcss, j)) (valOf (List.nth (#maps fam, j)))
val fam_eqns = List.tabulate (3, memberEqns)

(* conjunct by conjunct: a theorem's conjuncts may name their arguments
   the same way and mean different types by it, and one quotation cannot
   say that *)
fun checkeqn nm th q =
    (tprint nm;
     let val (cs, qs) = (strip_conj (concl th), strip_conj q)
     in
       if null (hyp th) andalso length cs = length qs andalso
          ListPair.allEq (fn (c,q') => same c q') (cs, qs)
       then OK() else die (thm_to_string th)
     end)

(* the names in the quotations below are the test's own: what the
   theorem calls a0 in one conjunct and a0 in the next are two different
   variables of two different types *)
val _ = checkeqn "ft1's map, per constructor" (#map_eqns (hd fam_eqns))
   “(ft1MAP f (FA a) = FA (f a)) ∧
    (ft1MAP f (FB t u) = FB (ft1MAP f t) (ft2MAP f (ft1MAP f) u))”

val _ = checkeqn "ft2's map, per constructor"
   (#map_eqns (List.nth (fam_eqns, 1)))
   “(ft2MAP f1 f2 (FC z) = FC (ft3MAP f2 z)) ∧
    (ft2MAP f1 f2 (FD a t) = FD (f1 a) (ft2MAP f1 f2 t))”

(* ft1's own atoms are those it holds, those of its ft1 sub-terms, and
   those the ft2 sub-term holds — of both kinds, since an ft2 holds ft1s *)
val _ = checkeqn "ft1's set function, per constructor"
   (hd (#set_eqns (hd fam_eqns)))
   “(ft1SET (FA a) = {a}) ∧
    (ft1SET (FB t u) =
       ft2SET1 u ∪ (ft1SET t ∪ BIGUNION (IMAGE ft1SET (ft2SET2 u))))”

val _ = checkeqn "ft2's second set function, per constructor"
   (List.nth (#set_eqns (List.nth (fam_eqns, 1)), 1))
   “(ft2SET2 (FC z) = ft3SET z) ∧ (ft2SET2 (FD a t) = ft2SET2 t)”

(* ----------------------------------------------------------------------
    The case constants, which is the first thing a TypeBase entry needs.

    A family's later members are *instances* — `:('b1, 'b1 ft1) ft2` —
    rather than type operators over the specification's own variables,
    which is what a TypeBase entry is keyed on and what a user who wrote
    the specification expects.  Collapsing them onto fresh types is the
    step that has to come before a family reaches TypeBase; a single
    type needs none of it, and bnfRegisterScript takes that one all the
    way.
   ---------------------------------------------------------------------- *)

val fam_cases = defineCases fam_prim_axiom

val _ = checkeqn "the family's case constants" (hd fam_cases)
   “(∀a f g. ft1_CASE (FA a) f g = f a) ∧
    (∀t u f g. ft1_CASE (FB t u) f g = g t u)”

val _ = checkeqn "and one per member" (List.nth (fam_cases, 2))
   “(∀t f g. ft3_CASE (FE t) f g = f t) ∧
    (∀t f g. ft3_CASE (FG t) f g = g t)”

(* ----------------------------------------------------------------------
    Collapsing the family onto types of its own.

    The construction leaves member j an instance of an operator that
    also takes the earlier members' slots; the specification says each
    member is an operator over its own variables, and that is what a
    TypeBase entry is keyed on.  So once the family is built, and only
    then, each member is copied onto a type of its own and the
    constructors and the principle are carried across.
   ---------------------------------------------------------------------- *)

val coll = collapseFamily {tynames = ["ct1","ct2","ct3"]} fam fam_principle

val _ = tprint "the family's own types"
val _ =
    if #types coll = [“:'b1 ct1”, “:'b1 ct2”, “:'b1 ct3”] andalso
       List.map (type_of o #1) (ListPair.zipEq (#cons coll, #types coll)) =
       [“:'b1 + 'b1 ct1 # 'b1 ct2 -> 'b1 ct1”,
        “:'b1 ct3 + 'b1 # 'b1 ct2 -> 'b1 ct2”,
        “:'b1 ct1 + 'b1 ct3 -> 'b1 ct3”]
    then OK()
    else die (String.concatWith ", " (List.map type_to_string (#types coll)))

val _ = tprint "and its principle, carried across"
val _ =
    if null (hyp (#principle coll)) andalso
       null (free_vars (concl (#principle coll))) andalso
       same (concl (#principle coll))
            “∀t0 t1 t2.
               (∃h0 h1 h2.
                  (∀af. h0 (ct1_CONS af) = t0 af (SUM_MAP I (h0 ## h1) af)) ∧
                  (∀af. h1 (ct2_CONS af) = t1 af (SUM_MAP h2 (I ## h1) af)) ∧
                  ∀af. h2 (ct3_CONS af) = t2 af (SUM_MAP h0 h2 af)) ∧
               ∀h0 h1 h2 k0 k1 k2.
                 ((∀af. h0 (ct1_CONS af) = t0 af (SUM_MAP I (h0 ## h1) af)) ∧
                  (∀af. h1 (ct2_CONS af) = t1 af (SUM_MAP h2 (I ## h1) af)) ∧
                  ∀af. h2 (ct3_CONS af) = t2 af (SUM_MAP h0 h2 af)) ∧
                 ((∀af. k0 (ct1_CONS af) = t0 af (SUM_MAP I (k0 ## k1) af)) ∧
                  (∀af. k1 (ct2_CONS af) = t1 af (SUM_MAP k2 (I ## k1) af)) ∧
                  ∀af. k2 (ct3_CONS af) = t2 af (SUM_MAP k0 k2 af)) ⇒
                 h0 = k0 ∧ h1 = k1 ∧ h2 = k2”
    then OK() else die (thm_to_string (#principle coll))
val ccs = collapsedConstructors [["CA","CB"],["CC","CD"],["CE","CG"]] coll
val cdefs = List.map #defs ccs
val caxiom = familyAxiomOf cdefs (familyExistence (#principle coll))
val csetind = familySetInductionOf fam (#types coll, #cons coll)
                                   (#principle coll)
val cinduction = familyInductionOf cdefs csetind
val ccases = defineCases caxiom
val ctyinfos = typeBaseInfo {axiom = caxiom, induction = cinduction,
                             case_defs = ccases,
                             rewrites = [[], [], []]}
val _ = TypeBase.export ctyinfos

val _ = tprint "the family's TypeBase entries"
val _ =
    if List.map TypeBasePure.ty_of ctyinfos = #types coll andalso
       List.all (fn ty => isSome (TypeBase.read (dest_type ty |> #1 |>
                                    (fn tyop => {Thy = current_theory(),
                                                 Tyop = tyop}))))
                (#types coll) andalso
       aconv (concl (TypeBase.induction_of “:'b1 ct1”)) (concl cinduction)
    then OK() else die "no entries"

val _ = tprint "the family's members behave like datatypes"
val _ =
    let
      val th1 = Q.prove (‘∀x:'b1 ct2. (∃t. x = CC t) ∨ ∃a u. x = CD a u’,
                         Cases_on ‘x’ >> simp[])
      val th2 = Q.prove (‘CA a ≠ CB t u ∧
                          (CB t u = CB t' u' ⇔ t = t' ∧ u = u')’,
                         simp[])
      val th3 = Q.prove (‘(case CE x of CE t => T | CG u => F)’, simp[])
    in
      if List.all (null o hyp) [th1, th2, th3] then OK()
      else die "not proved"
    end

(* and functions over the family are defined by its axiom and proved
   about by its induction, which is the whole point of the entry *)
(* the answers are type variables in the axiom; a definition picks them *)
val caxiom_num =
    INST_TYPE (List.map (fn ty => ty |-> numSyntax.num)
                        (List.filter (fn ty => ty <> b1)
                                     (type_vars_in_term (concl caxiom))))
              caxiom

val ct_size_def =
    new_specification
      ("ct_size_def", ["ct1SZ", "ct2SZ", "ct3SZ"],
       CONV_RULE (DEPTH_CONV BETA_CONV)
         (Q.SPECL [‘λa. 1n’, ‘λt u r s. 1 + r + s’, ‘λt r. 1 + r’,
                   ‘λa u r. 1 + r’, ‘λt r. 1 + r’, ‘λu r. 1 + r’]
                  caxiom_num))

val _ = tprint "a function over the family, and induction over it"
val _ =
    let val th = Q.prove (‘(∀x:'p ct1. 0 < ct1SZ x) ∧
                           (∀y:'p ct2. 0 < ct2SZ y) ∧
                           ∀z:'p ct3. 0 < ct3SZ z’,
                          ho_match_mp_tac cinduction >> simp[ct_size_def])
    in
      if null (hyp th) then OK() else die (thm_to_string th)
    end
