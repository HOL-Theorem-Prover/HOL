open HolKernel boolLib bossLib OpenTheoryBoolTheory lcsymtacs
val _ = new_theory"HOL4Compatibility"

val n = ref 0;
fun export (tm,tac) =
  store_thm(("th"^Int.toString(!n)),tm,tac)
  before n := !n+1

val res0 = export(``!t. F ==> t``,
  gen_tac >>
  qspec_then`t`(ACCEPT_TAC o C MATCH_MP OTbool136 o snd o EQ_IMP_RULE) OTbool98)
  (* DB.match["OpenTheoryBool"]``F ==> t`` *)

val res = export(``~~p ==> p``,
  qspec_then`p`(ACCEPT_TAC o fst o EQ_IMP_RULE) OTbool110)
  (* DB.match["OpenTheoryBool"]``~~p`` *)

val res = export(``~(p ==> q) ==> p``,
  strip_tac >>
  qspecl_then[`p`,`q`](ACCEPT_TAC o CONJUNCT1 o UNDISCH o fst o EQ_IMP_RULE) OTbool52)
  (* DB.match["OpenTheoryBool"]``~(p ==> q)`` *)

val res = export(``!x. x = (x = T)``,
  ACCEPT_TAC(GSYM OTbool106))
  (* DB.match["OpenTheoryBool"]``x = T`` *)

val res = export(``~(p ==> q) ==> ~q``,
  strip_tac >>
  qspecl_then[`p`,`q`](ACCEPT_TAC o CONJUNCT2 o UNDISCH o fst o EQ_IMP_RULE) OTbool52)
  (* DB.match["OpenTheoryBool"]``~(p ==> q)`` *)

val res = export(``~(p \/ q) ==> ~p``,
  strip_tac >>
  qspecl_then[`p`,`q`](ACCEPT_TAC o CONJUNCT1 o UNDISCH o fst o EQ_IMP_RULE) OTbool50)
  (* DB.match["OpenTheoryBool"]``~(p \/ q)`` *)

val res = export(``~(p \/ q) ==> ~q``,
  strip_tac >>
  qspecl_then[`p`,`q`](ACCEPT_TAC o CONJUNCT2 o UNDISCH o fst o EQ_IMP_RULE) OTbool50)
  (* DB.match["OpenTheoryBool"]``~(p \/ q)`` *)

val res7 = export(``!A. A ==> ~A ==> F``,
  gen_tac >> strip_tac >>
  disch_then(fn th => qspec_then`A`(mp_tac o C EQ_MP th o SYM)OTbool104) >>
  disch_then(fn th => pop_assum(ACCEPT_TAC o EQ_MP (SYM th))))
  (* DB.match["OpenTheoryBool"]``(F ⇔ t) ⇔ ~t`` *)

val res8 = export(``!t1 t2. (t1 ==> t2) ==> (t2 ==> t1) ==> (t1 <=> t2)``,
  deductAntisym
  (MP (ASSUME``t2 ==> t1``) (ASSUME``t2:bool``))
  (MP (ASSUME``t1 ==> t2``) (ASSUME``t1:bool``))
  |> DISCH``t2 ==> t1`` |> DISCH_ALL
  |> Q.GEN`t2` |> GEN_ALL
  |> ACCEPT_TAC)

val res = export(``!t. t ==> F <=> (t = F)``,
  res8
  |> Q.SPECL[`t==>F`,`t <=> F`]
  |> C MP (DISCH_ALL(SYM(UNDISCH(MATCH_MP res8 (SPEC_ALL res0)))))
  |> CONV_RULE(PATH_CONV"lrlr"(REWR_CONV (SPEC_ALL OTbool105) THENC
               RATOR_CONV(REWR_CONV OTbool132) THENC
               BETA_CONV))
  |> C MP (DISCH_ALL(ASSUME``t ==> F``))
  |> GEN_ALL
  |> ACCEPT_TAC)
  (* DB.match["OpenTheoryBool"]``(t <=> F) = ~t`` *)
  (* DB.match["OpenTheoryBool"]``$~ = x`` *)

val _ = export_theory()
