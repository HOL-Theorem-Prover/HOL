(* non-interactive mode
*)
open HolKernel Parse boolLib;
val _ = new_theory "abelian_group";

(* interactive mode
show_assums := true;
loadPath := union ["..", "../finished"] (!loadPath);
app load
["bossLib", "listTheory", "HurdUseful", "subtypeTools",
"res_quanTools", "res_quan2Theory", "pred_setTheory",
"extra_pred_setTheory", "arithContext", "relationTheory",
"ho_proverTools", "prob_extraTools", "prob_extraTheory",
"extra_listTheory", "subtypeTheory", "listContext",
"arithmeticTheory", "groupTheory", "groupContext", "extra_numTheory",
"gcdTheory", "dividesTheory", "primeTheory", "extra_arithTheory",
"finite_groupTheory", "finite_groupContext"];
*)

open bossLib listTheory hurdUtils subtypeTools res_quanTools
     pred_setTheory extra_pred_setTheory arithContext relationTheory
     ho_proverTools extra_listTheory
     subtypeTheory res_quanTheory listContext arithmeticTheory groupTheory
     groupContext extra_numTheory gcdTheory dividesTheory
     extra_arithTheory finite_groupTheory finite_groupContext;

val EXISTS_DEF = boolTheory.EXISTS_DEF;

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op!! = op REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val S_TAC = !! (POP_ASSUM MP_TAC) ++ !! RESQ_STRIP_TAC;

val RESQ_TAC =
  POP_ASSUM_TAC
  (simpLib.SIMP_TAC std_ss
  [RES_EXISTS_UNIQUE, RES_FORALL, RES_EXISTS, RES_SELECT,
   IN_FUNSET, IN_DFUNSET]);

val std_pc = precontext_mergel [arith_pc, list_pc];
val std_c = precontext_compile std_pc;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS std_c;

val (G_TAC, AG_TAC, G_TAC', AG_TAC') = SIMPLIFY_TACS finite_group_c;


(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val abelian_def = Define
  `abelian G = !g h :: gset G. gop G g h = gop G h g`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val ABELIAN_GPOW_GOP = store_thm
  ("ABELIAN_GPOW_GOP",
   ``!G :: finite_group. !g h :: gset G. !n.
       abelian G ==>
       (gpow G (gop G g h) n = gop G (gpow G g n) (gpow G h n))``,
   S_TAC
   ++ Induct_on `n` >> G_TAC []
   ++ G_TAC []
   ++ Suff
      `gop G (gop G h (gpow G g n)) (gpow G h n) =
       gop G (gop G (gpow G g n) h) (gpow G h n)`
   >> R_TAC [GROUP_ASSOC, FINITE_GROUP_GROUP, GPOW_SUBTYPE, GOP_SUBTYPE]
   ++ G_TAC []
   ++ Q.PAT_X_ASSUM `abelian G` MP_TAC
   ++ R_TAC [abelian_def]
   ++ DISCH_THEN (fn th => G_TAC [Q_RESQ_HALF_SPECL [`h`, `gpow G g n`] th]));

val ABELIAN_GORD_GCD_1 = store_thm
  ("ABELIAN_GORD_GCD_1",
   ``!G :: finite_group. !g h :: gset G.
       abelian G /\ (gcd (gord G g) (gord G h) = 1) ==>
       (gord G (gop G g h) = gord G g * gord G h)``,
   S_TAC
   ++ G_TAC [IS_GORD]
   ++ S_TAC
   >> (G_TAC [ABELIAN_GPOW_GOP]
       ++ Suff `gpow G h (gord G g * gord G h) = gid G`
       >> G_TAC []
       ++ ONCE_REWRITE_TAC [MULT_COMM]
       ++ G_TAC [])
   ++ Suff `gord G g * gord G h <= m` >> DECIDE_TAC
   ++ MATCH_MP_TAC DIVIDES_LE
   ++ S_TAC >> R_TAC []
   ++ R_TAC [GCD_1_LCM]
   ++ G_TAC [GSYM GPOW_GID_GORD]
   ++ AG_TAC [ABELIAN_GPOW_GOP]
   ++ Know `gpow G h m = ginv G (gpow G g m)`
   >> (ONCE_REWRITE_TAC [EQ_SYM_EQ]
       ++ G_TAC [IS_GINV])
   ++ G_TAC [GINV_GID]
   ++ POP_ASSUM K_TAC
   ++ S_TAC
   ++ G_TAC [GSYM GORD_GID_UNIQUE]
   ++ Suff `!p. prime p ==> ~divides p (gord G (gpow G g m))`
   >> PROVE_TAC [EXISTS_PRIME_DIVISOR]
   ++ S_TAC
   ++ Suff `divides p (gcd (gord G g) (gord G h))`
   >> (ASM_REWRITE_TAC []
       ++ R_TAC []
       ++ PROVE_TAC [NOT_PRIME_1])
   ++ R_TAC [DIVIDES_GCD]
   ++ CONJ_TAC
   >> (MP_TAC (Q_RESQ_HALF_SPECL [`G`, `g`] PRIME_DIVIDES_GORD_GPOW)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN MATCH_MP_TAC
       ++ PROVE_TAC [])
   ++ Suff `divides p (gord G (gpow G h m))`
   >> (MP_TAC (Q_RESQ_HALF_SPECL [`G`, `h`] PRIME_DIVIDES_GORD_GPOW)
       ++ Q.PAT_X_ASSUM `gpow G h m = x` K_TAC
       ++ ASM_REWRITE_TAC []
       ++ PROVE_TAC [])
   ++ G_TAC [GORD_GINV]);

(* The structure theorem *)

val STRUCTURE_LEMMA = store_thm
  ("STRUCTURE_LEMMA",
   ``!G :: finite_group.
       abelian G ==>
       !g1 g2 :: gset G. ?h :: gset G. gord G h = lcm (gord G g1) (gord G g2)``,
   NTAC 2 RESQ_STRIP_TAC
   ++ Suff
      `!g. !g1 g2 :: gset G.
         (gcd (gord G g1) (gord G g2) = g) ==>
         ?h :: gset G. gord G h = lcm (gord G g1) (gord G g2)`
   >> (S_TAC
       ++ Q.PAT_X_ASSUM `!g. P g` (MP_TAC o Q.SPEC `gcd (gord G g1) (gord G g2)`)
       ++ G_TAC [])
   ++ HO_MATCH_MP_TAC FACTOR_INDUCT
   ++ CONJ_TAC >> G_TAC []
   ++ CONJ_TAC
   >> (S_TAC
       ++ Q_RESQ_EXISTS_TAC `gop G g1 g2`
       ++ G_TAC' [lcm_def, GORD_EQ_0]
       ++ G_TAC [ABELIAN_GORD_GCD_1])
   ++ S_TAC
   ++ MP_TAC (Q.SPECL [`gord G g1`, `gord G g2`] FACTOR_GCD)
   ++ G_TAC []
   ++ DISCH_THEN (MP_TAC o Q.SPEC `p`)
   ++ R_TAC []
   ++ RESQ_STRIP_TAC <<
   [POP_ASSUM MP_TAC
    ++ Know `p * gord G (gpow G g2 p) = gord G g2`
    >> (G_TAC [GORD_GPOW_PRIME]
        ++ Suff `divides p (gord G g2)`
        >> (R_TAC [DIVIDES_ALT] ++ PROVE_TAC [MULT_COMM])
        ++ Suff `divides p (gcd (gord G g1) (gord G g2))`
        >> R_TAC [DIVIDES_GCD]
        ++ ASM_REWRITE_TAC []
        ++ R_TAC [])
    ++ DISCH_THEN
       (fn th =>
        CONV_TAC (RATOR_CONV (REWRITE_CONV [SYM th]))
        ++ R_TAC []
        ++ ASSUME_TAC th)
    ++ S_TAC
    ++ Q.PAT_X_ASSUM `!g1 :: gset G. P g1`
       (MP_TAC o Q_RESQ_HALF_SPECL [`g1`, `gpow G g2 p`])
    ++ G_TAC' []
    ++ Know `gcd (gord G g1) (gord G (gpow G g2 p)) = g`
    >> (POP_ASSUM MP_TAC
        ++ Cases_on `p` >> AR_TAC []
        ++ R_TAC [])
    ++ POP_ASSUM K_TAC
    ++ RESQ_STRIP_TAC
    ++ Suff `lcm (gord G g1) (gord G (gpow G g2 p)) =
                 lcm (gord G g1) (gord G g2)`
    >> R_TAC []
    ++ G_TAC [lcm_def, GORD_EQ_0]
    ++ Q.PAT_X_ASSUM `p * x = y` (R_TAC o wrap o SYM)
    ++ Know `gord G g1 * (p * gord G (gpow G g2 p)) =
                 p * (gord G g1 * gord G (gpow G g2 p))`
    >> PROVE_TAC [MULT_ASSOC, MULT_COMM]
    ++ R_TAC []
    ++ DISCH_THEN K_TAC
    ++ Suff `0 < g` >> R_TAC [DIV_CANCEL]
    ++ Suff `~(g = 0)` >> (R_TAC [] ++ DECIDE_TAC)
    ++ S_TAC
    ++ AG_TAC [GORD_EQ_0],
    POP_ASSUM MP_TAC
    ++ Know `p * gord G (gpow G g1 p) = gord G g1`
    >> (G_TAC [GORD_GPOW_PRIME]
        ++ Suff `divides p (gord G g1)`
        >> (R_TAC [DIVIDES_ALT] ++ PROVE_TAC [MULT_COMM])
        ++ Suff `divides p (gcd (gord G g1) (gord G g2))`
        >> R_TAC [DIVIDES_GCD]
        ++ ASM_REWRITE_TAC []
        ++ R_TAC [])
    ++ DISCH_THEN
       (fn th =>
        CONV_TAC (RATOR_CONV (REWRITE_CONV [SYM th]))
        ++ R_TAC []
        ++ ASSUME_TAC th)
    ++ S_TAC
    ++ Q.PAT_X_ASSUM `!g1 :: gset G. P g1`
       (MP_TAC o Q_RESQ_HALF_SPECL [`gpow G g1 p`, `g2`])
    ++ G_TAC' []
    ++ Know `gcd (gord G (gpow G g1 p)) (gord G g2) = g`
    >> (POP_ASSUM MP_TAC
        ++ Cases_on `p` >> AR_TAC []
        ++ R_TAC [])
    ++ POP_ASSUM K_TAC
    ++ RESQ_STRIP_TAC
    ++ Suff `lcm (gord G (gpow G g1 p)) (gord G g2) =
                 lcm (gord G g1) (gord G g2)`
    >> R_TAC []
    ++ G_TAC [lcm_def, GORD_EQ_0]
    ++ Q.PAT_X_ASSUM `p * x = y` (R_TAC o wrap o SYM)
    ++ Suff `0 < g` >> R_TAC [DIV_CANCEL, GSYM MULT_ASSOC]
    ++ Suff `~(g = 0)` >> DECIDE_TAC
    ++ S_TAC
    ++ AG_TAC [GORD_EQ_0]]);

val STRUCTURE_THM = store_thm
  ("STRUCTURE_THM",
   ``!G :: finite_group.
       abelian G ==> ?g :: gset G. !h :: gset G. gpow G h (gord G g) = gid G``,
   S_TAC
   ++ MP_TAC (Q_RESQ_SPEC `G` MAXIMAL_ORDER)
   ++ S_TAC
   ++ Q_RESQ_EXISTS_TAC `g`
   ++ R_TAC []
   ++ S_TAC
   ++ R_TAC [GPOW_GID_GORD]
   ++ MP_TAC (Q_RESQ_SPEC `G` STRUCTURE_LEMMA)
   ++ R_TAC []
   ++ DISCH_THEN (MP_TAC o Q_RESQ_SPECL [`g`, `h`])
   ++ S_TAC
   ++ Suff `gord G h' = gord G g` >> PROVE_TAC [DIVIDES_LCM_R]
   ++ Suff `gord G h' <= gord G g /\ gord G g <= gord G h'`
   >> DECIDE_TAC
   ++ S_TAC >> G_TAC []
   ++ MATCH_MP_TAC DIVIDES_LE
   ++ S_TAC
   >> (POP_ASSUM K_TAC
       ++ Suff `~(gord G h' = 0)` >> DECIDE_TAC
       ++ G_TAC [GORD_EQ_0])
   ++ PROVE_TAC [DIVIDES_LCM_L]);

(* non-interactive mode
*)
val _ = export_theory ();
