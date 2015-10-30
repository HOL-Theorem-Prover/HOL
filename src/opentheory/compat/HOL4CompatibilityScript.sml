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

val res2 = export(``~(p ==> q) ==> p``,
  strip_tac >>
  qspecl_then[`p`,`q`](ACCEPT_TAC o CONJUNCT1 o UNDISCH o fst o EQ_IMP_RULE) OTbool52)
  (* DB.match["OpenTheoryBool"]``~(p ==> q)`` *)

val res3 = export(``!x. x = (x = T)``,
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

val res9 = export(``!t. t ==> F <=> (t = F)``,
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

val res = export(``!x. (x = x) <=> T``,
  EQ_MP(SYM(Q.SPEC`x = x`OTbool106))(REFL``x:'a``)
  |> GEN_ALL |> ACCEPT_TAC)
  (* DB.match["OpenTheoryBool"]``(x = T)`` *)

val _ = OpenTheoryMap.OpenTheory_const_name{
  const={Thy="HOL4Compatibility",Name="literal_case"},
  name=(["HOL4"],"literal_case")}
val def = new_definition("literal_case_def",concl boolTheory.literal_case_DEF)
val res = export(``!f x. literal_case f x = f x``,
  rpt gen_tac >> CONV_TAC(PATH_CONV"lrll"(REWR_CONV def)) >>
  CONV_TAC(RATOR_CONV(RAND_CONV (RATOR_CONV BETA_CONV THENC BETA_CONV))) >>
  REFL_TAC);

val res = export(``(~A ==> F) ==> (A ==> F) ==> F``,
  CONV_TAC(PATH_CONV"lr"(REWR_CONV res9)) >>
  disch_then(fn th => CONV_TAC(RAND_CONV(REWR_CONV(SYM th)))) >>
  CONV_TAC(PATH_CONV"rl" (REWR_CONV OTbool132)) >>
  CONV_TAC(RAND_CONV BETA_CONV) >>
  disch_then ACCEPT_TAC)

val res = export(``!f g. (f = g) <=> !x. (f x = g x)``,
  ACCEPT_TAC(GSYM OTbool49))
  (* DB.match["OpenTheoryBool"]``!x. f x = g x`` *)

val res = export(``!t1 t2. ((if T then t1 else t2) = t1) ∧ ((if F then t1 else t2) = t2)``,
  rpt gen_tac >> ACCEPT_TAC (CONJ (SPEC_ALL OTbool75) (SPEC_ALL OTbool76)))
  (* DB.match["OpenTheoryBool"]``if a then b else c`` *)

val res = export(``(!t. ~~t <=> t) ∧ (~T <=> F) /\ (~F <=> T)``,
  ACCEPT_TAC (LIST_CONJ[OTbool110,OTbool134,OTbool135]))
  (* DB.match["OpenTheoryBool"]``~~ t <=> t`` *)
  (* DB.match["OpenTheoryBool"]``~T <=> F`` *)
  (* DB.match["OpenTheoryBool"]``~F <=> T`` *)

val res = export(``!t.
       ((T <=> t) <=> t) /\ ((t <=> T) <=> t) /\ ((F <=> t) <=> ~t) /\
       ((t <=> F) <=> ~t)``,
  ACCEPT_TAC (GEN_ALL(LIST_CONJ(map SPEC_ALL [OTbool107,OTbool106,OTbool104,OTbool105]))))
  (* DB.match["OpenTheoryBool"]``T = t`` *)
  (* DB.match["OpenTheoryBool"]``t = T`` *)
  (* DB.match["OpenTheoryBool"]``F = t`` *)
  (* DB.match["OpenTheoryBool"]``t = F`` *)

val res = export(``!t.
       (T /\ t <=> t) /\ (t /\ T <=> t) /\ (F /\ t <=> F) /\
       (t /\ F <=> F) /\ (t /\ t <=> t)``,
  ACCEPT_TAC (GEN_ALL(LIST_CONJ(map SPEC_ALL [OTbool102,OTbool100,OTbool103,OTbool101,OTbool99]))))
  (* DB.match["OpenTheoryBool"]``T ∧ t`` *)
  (* DB.match["OpenTheoryBool"]``t ∧ T`` *)
  (* DB.match["OpenTheoryBool"]``F ∧ t`` *)
  (* DB.match["OpenTheoryBool"]``t ∧ F`` *)
  (* DB.match["OpenTheoryBool"]``t ∧ t = t`` *)

val res = export(``!t.
       (T \/ t <=> T) /\ (t \/ T <=> T) /\ (F \/ t <=> t) /\
       (t \/ F <=> t) /\ (t \/ t <=> t)``,
  ACCEPT_TAC (GEN_ALL(LIST_CONJ(map SPEC_ALL [OTbool93,OTbool91,OTbool94,OTbool92,OTbool90]))))
  (* DB.match["OpenTheoryBool"]``T ∨ t`` *)
  (* DB.match["OpenTheoryBool"]``t ∨ T`` *)
  (* DB.match["OpenTheoryBool"]``F ∨ t`` *)
  (* DB.match["OpenTheoryBool"]``t ∨ F`` *)
  (* DB.match["OpenTheoryBool"]``t ∨ t = t`` *)

val res = export(``!t.
       (T ==> t <=> t) /\ (t ==> T <=> T) /\ (F ==> t <=> T) /\
       (t ==> t <=> T) /\ (t ==> F <=> ~t)``,
  ACCEPT_TAC (GEN_ALL(LIST_CONJ(map SPEC_ALL [OTbool97,OTbool96,OTbool98,
    EQ_MP (Q.SPEC`t ==> t`res3) (SPEC_ALL OTbool84), OTbool95]))))
  (* DB.match["OpenTheoryBool"]``T ⇒ t`` *)
  (* DB.match["OpenTheoryBool"]``t ⇒ T`` *)
  (* DB.match["OpenTheoryBool"]``F ⇒ t`` *)
  (* DB.match["OpenTheoryBool"]``t ⇒ t`` *)
  (* DB.match["OpenTheoryBool"]``t ⇒ F`` *)

(*
val res = export(``(p <=> ~q) <=> (p \/ q) /\ (~q \/ ~p)``,
  (* DB.match["OpenTheoryBool"]``(p <=> ~q)`` *)
  (* DB.match["OpenTheoryBool"]``q \/ ~p`` *)
*)

(*
val res = export(``~(~A \/ B) ==> F <=> A ==> ~B ==> F``,
  (* DB.match["OpenTheoryBool"]``~A \/ b`` *)
*)

(*
val res = export(``!A B. A ==> B <=> ~A \/ B``,
  OTbool51
  OTbool0
  (* DB.match["OpenTheoryBool"]``~A \/ b`` *)
  (* DB.match["OpenTheoryBool"]``if a then b else c`` *)
*)

(*
  |- ~(~A \/ B) ==> F <=> A ==> ~B ==> F
*)


val _ = export_theory()
