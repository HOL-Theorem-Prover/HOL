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
