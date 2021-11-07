structure jrhUtils :> jrhUtils=
struct

(* Standard libs *)
open HolKernel boolLib liteLib numLib reduceLib
     pairTheory prim_recTheory numTheory arithmeticTheory;

infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;


val ERR = mk_HOL_ERR "jrhUtils";

(*---------------------------------------------------------------------------*)
(* Various utilities useful in building the theories.                        *)
(*---------------------------------------------------------------------------*)

fun HALF_MK_ABS qth =
  let val (x,body) = dest_forall (concl qth)
      val t = rhs body
      val gv = genvar (type_of x)
      val tfun = mk_abs(x,t) in
    EXT (GEN gv                 (* |- !gv. u gv =< (\x.t) gv  *)
         (TRANS (SPEC gv qth)
          (SYM (BETA_CONV (mk_comb(tfun,gv)))))) end;



(*===========================================================================*)
(* Various useful tactics, conversions etc.                                  *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* Proves tautologies: handy for propositional lemmas                        *)
(*---------------------------------------------------------------------------*)

val TAUT_CONV = tautLib.TAUT_PROVE;

(*---------------------------------------------------------------------------*)
(* More concise way to get an AC rewrite lemma                               *)
(*---------------------------------------------------------------------------*)

fun AC thp tm = EQT_ELIM(AC_CONV thp tm);

(*---------------------------------------------------------------------------*)
(* GEN_PAIR_TAC - Like GEN_TAC but "pairs" the relevant variable             *)
(*---------------------------------------------------------------------------*)

val GEN_PAIR_TAC =
  W(curry op THEN GEN_TAC o SUBST1_TAC o SYM o
    C ISPEC PAIR o fst o dest_forall o snd);

(*---------------------------------------------------------------------------*)
(* MK_COMB_TAC - reduces ?- f x = g y to ?- f = g and ?- x = y               *)
(*---------------------------------------------------------------------------*)

fun MK_COMB_TAC (asl,w) =
  let val (l,r) = dest_eq w
      val (l1,l2) = dest_comb l
      val (r1,r2) = dest_comb r in
  ([(asl,mk_eq(l1,r1)), (asl,mk_eq(l2,r2))],end_itlist (curry MK_COMB)) end;


(*---------------------------------------------------------------------------*)
(* BINOP_TAC - reduces "$op x y = $op u v" to "x = u" and "y = v"            *)
(*---------------------------------------------------------------------------*)

val BINOP_TAC = MK_COMB_TAC THENL [AP_TERM_TAC, ALL_TAC];

(*---------------------------------------------------------------------------*)
(* SYM_CANON_CONV - Canonicalizes single application of symmetric operator   *)
(* Rewrites "so as to make f true", e.g. fn = $<< or fn = curry$= "1" o fst  *)
(*---------------------------------------------------------------------------*)

fun SYM_CANON_CONV sym f =
  REWR_CONV sym o assert (op not o f o ((snd o dest_comb) ## I) o dest_comb);

(*---------------------------------------------------------------------------*)
(* IMP_SUBST_TAC - Implicational substitution for deepest matchable term     *)
(*---------------------------------------------------------------------------*)

fun IMP_SUBST_TAC th (asl,w) =
  case (sort free_in
           (find_terms (can (PART_MATCH (lhs o snd o dest_imp) th)) w))
   of [] => raise ERR "IMP_SUBST_TAC" ""
    | tm1::_ =>
        let val th1 = PART_MATCH (lhs o snd o dest_imp) th tm1
            val (a,conseq) = dest_imp (concl th1)
            val (l,r) = dest_eq conseq
            val gv = genvar (type_of l)
            val pat = subst[l |-> gv] w
        in
          ([(asl,a), (asl,subst[gv |-> r] pat)],
           fn [t1,t2] => SUBST[gv |-> SYM(MP th1 t1)] pat t2
            | _ => raise ERR "IMP_SUBST_TAC" "")
       end;

(*---------------------------------------------------------------------------*)
(* Tactic to introduce an abbreviation                                       *)
(*                                                                           *)
(* N.B. Just "ABBREV_TAC = CHOOSE_TAC o DEF_EXISTS_RULE" doesn't work if RHS *)
(* has free variables.                                                       *)
(*---------------------------------------------------------------------------*)

fun ABBREV_TAC tm =
  let val (v,t) = dest_eq tm in
  CHOOSE_THEN (fn th => SUBST_ALL_TAC th THEN ASSUME_TAC th)
              (EXISTS(mk_exists(v,mk_eq(t,v)),t) (REFL t)) end;

(*---------------------------------------------------------------*)
(* EXT_CONV "!x. f x = g x" = |- (!x. f x = g x) = (f = g)       *)
(*---------------------------------------------------------------*)

val EXT_CONV =  SYM o uncurry X_FUN_EQ_CONV o
      (I ## (mk_eq o (rator ## rator) o dest_eq)) o dest_forall;

(*---------------------------------------------------------------------------*)
(*   (\x. s[x]) = (\y. t[y])                                                 *)
(*  ========================= ABS_TAC                                        *)
(*         s[x] = t[x]                                                       *)
(*---------------------------------------------------------------------------*)

fun ABS_TAC (asl,w) =
  let val (l,r) = dest_eq w
      val (v1,b1) = dest_abs l
      val (v2,b2) = dest_abs r
      val v = variant (free_varsl (w::asl)) v1
      val subg = mk_eq(subst[v1 |-> v] b1,subst[v2 |-> v] b2) in
   ([(asl,subg)],CONV_RULE(LAND_CONV(ALPHA_CONV v1)) o
               CONV_RULE(RAND_CONV(ALPHA_CONV v2)) o ABS v o hd) end;

(*---------------------------------------------------------------------------*)
(* EQUAL_TAC - Strip down to unequal core (usually too enthusiastic)         *)
(*---------------------------------------------------------------------------*)

val EQUAL_TAC = REPEAT(FIRST [AP_TERM_TAC, AP_THM_TAC, ABS_TAC]);

(*---------------------------------------------------------------------------*)
(* X_BETA_CONV "v" "tm[v]" = |- tm[v] = (\v. tm[v]) v                        *)
(*---------------------------------------------------------------------------*)

fun X_BETA_CONV v tm = SYM(BETA_CONV(mk_comb(mk_abs(v,tm),v)));

(*---------------------------------------------------------------------------*)
(* EXACT_CONV - Rewrite with theorem matching exactly one in a list          *)
(*---------------------------------------------------------------------------*)

val EXACT_CONV =
  ONCE_DEPTH_CONV o FIRST_CONV o
  map (fn t => K t o assert(aconv (lhs(concl t))));

(*---------------------------------------------------------------------------*)
(* Rather ad-hoc higher-order fiddling conversion                            *)
(* |- (\x. f t1[x] ... tn[x]) = (\x. f ((\x. t1[x]) x) ... ((\x. tn[x]) x))  *)
(*---------------------------------------------------------------------------*)

fun HABS_CONV tm =
  let val (v,bod) = dest_abs tm
      val (hop,pl) = strip_comb bod
      val eql = rev(map (X_BETA_CONV v) pl) in
  ABS v (itlist (C(curry MK_COMB)) eql (REFL hop)) end;


(*---------------------------------------------------------------------------*)
(* Expand an abbreviation                                                    *)
(*---------------------------------------------------------------------------*)

fun EXPAND_TAC s = FIRST_ASSUM(SUBST1_TAC o SYM o
  assert(curry op = s o fst o dest_var o rhs o concl)) THEN BETA_TAC;


(*---------------------------------------------------------------------------
 * Added by Konrad, to make his life easier when installing the rewriting
 * upgrade 27.7.94.
 *---------------------------------------------------------------------------*)

val GEN_REWR_TAC = Lib.C Rewrite.GEN_REWRITE_TAC Rewrite.empty_rewrites;

end
