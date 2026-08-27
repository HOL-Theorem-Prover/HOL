Theory bnfInitialTest
Ancestors
  bnfInitial
Libs
  HolKernel Parse boolLib bossLib bnfLib bnfFixLib testutils

(* ----------------------------------------------------------------------
    The initial algebra, built for a range of functors straight out of
    deriveBNF.  What is checked is that the construction goes through
    with nothing left over: the theorems must be ground (a free variable
    means a parameter was never pinned down) and hypothesis-free.
   ---------------------------------------------------------------------- *)

fun check nm ty =
    let val _ = tprint ("initial algebra for " ^ type_to_string ty)
        val bnf = deriveBNF (bnfBase.fullDB()) ty
        val ia = initialAlgebra bnf
        val ths = [#bij ia, #init ia, #inhabited ia, #induction ia]
        fun ground th = null (free_vars (concl th)) andalso null (hyp th)
        val bijc = concl (#bij ia)
    in
      if not (List.all ground ths) then die "not ground"
      else if not (same_const (rator (rator (rator bijc)))
                              pred_setSyntax.bij_tm)
      then die "not a bijection"
      else if not (aconv (rand bijc) (#alg ia)) then die "wrong carrier"
      else OK()
    end

val _ = check "list" “:one + 'b1 # 'a”
val _ = check "option" “:'a option”
val _ = check "btree" “:'b1 + 'a # 'a”
val _ = check "infinitely branching" “:one + ('b2 -> 'a)”
val _ = check "nested" “:one + 'b1 # ('a option)”

(* a functor with no base case has no initial algebra with a non-empty
   carrier, and the construction must say so rather than build one *)
val _ = let val _ = tprint "no base case is rejected"
            val bnf = deriveBNF (bnfBase.fullDB()) “:'b1 # ('b2 -> 'a)”
        in
          (ignore (initialAlgebra bnf); die "accepted")
          handle HOL_ERR _ => OK()
        end

(* ----------------------------------------------------------------------
    A type, from the functor to the recursion principle.
   ---------------------------------------------------------------------- *)

(* equality up to the naming of type variables: the construction's
   target type variable and the parser's need not agree *)
fun same t1 t2 = can (match_term t1) t2 andalso can (match_term t2) t1

val _ = tprint "defining 'b1 mylist"
val mylist =
    defineFixpoint {tyname = "mylist", ABS = "mylist_ABS", REP = "mylist_REP"}
                   (deriveBNF (bnfBase.fullDB()) “:one + 'b1 # 'a”)
val _ =
    if not (#newty mylist = “:'b1 mylist”) then die "wrong type"
    else if not (null (hyp (#recursion mylist))) then die "hypotheses left"
    else if same (concl (#recursion mylist))
                 “∀t. ∃!h. ∀af. h (mylist_CONS af) = t (SUM_MAP I (I ## h) af)”
    then OK()
    else die ("recursion is " ^ thm_to_string (#recursion mylist))

val _ = tprint "defining 'b1 mytree"
val mytree =
    defineFixpoint {tyname = "mytree", ABS = "mytree_ABS", REP = "mytree_REP"}
                   (deriveBNF (bnfBase.fullDB()) “:'b1 + 'a # 'a”)
val _ =
    if not (#newty mytree = “:'b1 mytree”) then die "wrong type"
    else if same (concl (#recursion mytree))
                 “∀t. ∃!h. ∀af. h (mytree_CONS af) = t (SUM_MAP I (h ## h) af)”
    then OK()
    else die ("recursion is " ^ thm_to_string (#recursion mytree))

(* ----------------------------------------------------------------------
    The usual binary tree: Leaf | Node of btree # 'b1 # btree.  As well
    as the shape of the recursion theorem, this checks that the theorem
    is usable — that the constructors can be split out of it and the
    recursion equations recovered.
   ---------------------------------------------------------------------- *)

val btree =
    defineFixpoint {tyname = "btree", ABS = "btree_ABS", REP = "btree_REP"}
                   (deriveBNF (bnfBase.fullDB()) “:one + 'a # 'b1 # 'a”)
val btree_rec = #recursion btree

val _ = tprint "defining 'b1 btree"
val _ =
    if not (#newty btree = “:'b1 btree”) then die "wrong type"
    else if same (concl btree_rec)
                 “∀t. ∃!h. ∀af.
                    h (btree_CONS af) = t (SUM_MAP I (h ## I ## h) af)”
    then OK()
    else die ("recursion is " ^ thm_to_string btree_rec)

Definition Leaf_def:  Leaf = btree_CONS (INL ())
End
Definition Node_def:  Node l a rt = btree_CONS (INR (l,a,rt))
End

(* the sum-shaped t, split along the two constructors *)
val tcase = ‘λs. sum_CASE s (K lf) (λ(x,a,y). nd x a y)’

Theorem btree_recursion_exists:
  ∀lf nd. ∃h. h Leaf = lf ∧ ∀l a rt. h (Node l a rt) = nd (h l) a (h rt)
Proof
  rpt gen_tac >>
  qspec_then tcase strip_assume_tac (SRULE [EXISTS_UNIQUE_THM] btree_rec) >>
  qexists_tac ‘h’ >> gs[Leaf_def, Node_def]
QED

Theorem btree_recursion_unique:
  ∀lf nd h1 h2.
    (h1 Leaf = lf ∧ ∀l a rt. h1 (Node l a rt) = nd (h1 l) a (h1 rt)) ∧
    (h2 Leaf = lf ∧ ∀l a rt. h2 (Node l a rt) = nd (h2 l) a (h2 rt)) ⇒
    h1 = h2
Proof
  rpt gen_tac >> strip_tac >>
  qspec_then tcase (strip_assume_tac o SRULE [EXISTS_UNIQUE_THM]) btree_rec >>
  first_x_assum irule >> conj_tac >> Cases >> TRY (PairCases_on ‘y’) >>
  simp[GSYM Leaf_def, GSYM Node_def, oneTheory.one]
QED

Theorem btree_distinct:
  ∀l a rt. Leaf ≠ Node l a rt
Proof
  rpt gen_tac >>
  qspec_then ‘λs. sum_CASE s (K T) (λ(x,a,y). F)’
             (strip_assume_tac o SRULE [EXISTS_UNIQUE_THM]) btree_rec >>
  ‘h Leaf = T ∧ h (Node l a rt) = F’ by simp[Leaf_def, Node_def] >>
  strip_tac >> gs[]
QED
