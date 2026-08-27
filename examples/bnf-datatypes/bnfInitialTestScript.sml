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
