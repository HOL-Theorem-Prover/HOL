open HolKernel Parse boolLib

open bossLib simpLib

val _ = new_theory "cl";

val _ = (hide "S"; hide "K")
val _ = Datatype `cl = S | K | # cl cl`;

val _ = set_fixity "#"  (Infixl 1100);

val _ = set_mapped_fixity {tok = "-->", fixity = Infix(NONASSOC, 450),
                           term_name = "redn"}

Inductive redn:
    (!x y f. x --> y   ==>    f # x --> f # y) /\
    (!f g x. f --> g   ==>    f # x --> g # x) /\
    (!x y.   K # x # y --> x) /\
    (!f g x. S # f # g # x --> (f # x) # (g # x))
End

val _ = hide "RTC";

Inductive RTC:
    (!x.     RTC R x x) /\
    (!x y z. R x y /\ RTC R y z ==> RTC R x z)
End

Definition confluent_def:
  confluent R =
     !x y z. RTC R x y /\ RTC R x z ==>
             ?u. RTC R y u /\ RTC R z u
End

Definition normform_def: normform R x = !y. ~R x y
End

Theorem confluent_normforms_unique:
  !R. confluent R ==>
      !x y z. RTC R x y /\ normform R y /\ RTC R x z /\ normform R z ==>
              y = z
Proof
  rw[confluent_def] >>
  `?u. RTC R y u /\ RTC R z u` by metis_tac [] >>
  metis_tac [normform_def, RTC_cases]
QED

Definition diamond_def:
  diamond R ⇔ ∀x y z. R x y /\ R x z ==> ∃u. R y u /\ R z u
End

Theorem confluent_diamond_RTC:
  !R. confluent R = diamond (RTC R)
Proof rw[confluent_def, diamond_def]
QED

Theorem R_RTC_diamond:
  ∀R. diamond R ==>
      ∀x p z. RTC R x p ∧ R x z ⇒
              ∃u. RTC R p u /\ RTC R z u
Proof
  GEN_TAC >> STRIP_TAC >> Induct_on `RTC` >>
  metis_tac [diamond_def,RTC_rules]
QED

Theorem RTC_RTC:
  ∀R x y z. RTC R x y ∧ RTC R y z ⇒ RTC R x z
Proof
  gen_tac >> Induct_on `RTC R x y` >> metis_tac [RTC_rules]
QED

Theorem diamond_RTC:
  !R. diamond R ==> diamond (RTC R)
Proof
  strip_tac >> strip_tac >> simp[diamond_def] >>
  Induct_on `RTC R x y` >> rw[] >| [
    metis_tac[RTC_rules],
    `?v. RTC R x' v /\ RTC R z v` by metis_tac[R_RTC_diamond] >>
    metis_tac [RTC_RTC, RTC_rules]
  ]
QED

val _ = set_mapped_fixity {tok = "-||->", fixity = Infix(NONASSOC, 450),
                           term_name = "predn"}
Inductive predn:
  (!x. x -||-> x) /\
  (!x y u v. x -||-> y /\ u -||-> v ==> x # u -||-> y # v) /\
  (!x y. K # x # y -||-> x) /\
  (!f g x. S # f # g # x -||-> (f # x) # (g # x))
End

Theorem RTC_monotone:
  !R1 R2. (!x y. R1 x y ==> R2 x y) ==>
          (!x y. RTC R1 x y ==> RTC R2 x y)
Proof
  rpt GEN_TAC >> STRIP_TAC >> Induct_on `RTC` >>
  rpt STRIP_TAC >> metis_tac [RTC_rules]
QED

val _ = set_fixity "-->*" (Infix(NONASSOC, 450));
Overload "-->*" = “RTC redn”;

val _ = set_fixity "-||->*" (Infix(NONASSOC, 450));
Overload "-||->*" = ``RTC predn``;

Theorem RTCredn_RTCpredn:
  !x y. x -->* y   ==>   x -||->* y
Proof
  HO_MATCH_MP_TAC RTC_monotone >> Induct_on `x --> y` >>
  metis_tac [predn_rules]
QED

val RTCredn_ap_congruence = store_thm(
  "RTCredn_ap_congruence",
  ``!x y. x -->* y ==> !z. x # z -->* y # z /\ z # x -->* z # y``,
  Induct_on `RTC` >> metis_tac [RTC_rules, redn_rules]);

Theorem predn_RTCredn:
  !x y. x -||-> y  ==>  x -->* y
Proof
  Induct_on `x -||-> y` >>
  metis_tac [RTC_rules,redn_rules,RTC_RTC,RTCredn_ap_congruence]
QED

Theorem RTCpredn_RTCredn:
  !x y. x -||->* y   ==>  x -->* y
Proof Induct_on `RTC` >> metis_tac [predn_RTCredn, RTC_RTC, RTC_rules]
QED

Theorem RTCpredn_EQ_RTCredn:
  $-||->* = $-->*
Proof
  SIMP_TAC std_ss [FUN_EQ_THM] >>
  metis_tac [RTCpredn_RTCredn, RTCredn_RTCpredn]
QED

fun characterise t = SIMP_RULE (srw_ss()) [] (SPEC t predn_cases);

Theorem K_predn[local] = characterise ``K``;
Theorem S_predn[local] = characterise ``S``;
Theorem Sx_predn0[local] = characterise ``S # x``;

Theorem Sx_predn[local]:
  !x y. S # x -||-> y <=> ?z. (y = S # z) /\ (x -||-> z)
Proof rw[Sx_predn0, predn_rules, S_predn, EQ_IMP_THM]
QED

Theorem Kx_predn[local]:
  !x y. K # x -||-> y <=> ?z. (y = K # z) /\ (x -||-> z)
Proof
  rw[characterise ``K # x``, predn_rules, K_predn, EQ_IMP_THM]
QED

Theorem Kxy_predn[local]:
  !x y z. K # x # y -||-> z <=>
          (?u v. (z = K # u # v) /\ (x -||-> u) /\ (y -||-> v)) \/
          z = x
Proof rw[characterise “K # x # y”, predn_rules, Kx_predn, EQ_IMP_THM]
QED

Theorem Sxy_predn[local]:
  !x y z. S # x # y -||-> z <=>
          ?u v. z = S # u # v ∧ x -||-> u ∧ y -||-> v
Proof
  rw[characterise ``S # x # y``, predn_rules, EQ_IMP_THM,
     S_predn, Sx_predn]
QED

Theorem Sxyz_predn[local]:
  !w x y z. S # w # x # y -||-> z <=>
            (?p q r. (z = S # p # q # r) /\
                     w -||-> p /\ x -||-> q /\ y -||-> r) \/
            z = (w # y) # (x # y)
Proof
  rw[characterise ``S # w # x # y``, predn_rules, Sxy_predn, EQ_IMP_THM]
QED

Theorem x_ap_y_predn[local] = characterise ``x # y``;

Theorem predn_diamond_lemma[local]:
  !x y z. x -||-> y ∧ x -||-> z ==> ∃u. y -||-> u ∧ z -||-> u
Proof
  Induct_on ‘x -||-> y’ >> rw[] >~
  [‘∃z. x -||-> z ∧ y -||-> z’] >- metis_tac [predn_rules] >~
  [‘K # a # b -||-> c’] >- (gvs[Kxy_predn] >> metis_tac[predn_rules]) >~
  [‘S # f # g # x -||-> sres’] >- (gvs[Sxyz_predn] >> metis_tac[predn_rules]) >~
  [‘a0 # b0 -||-> c’, ‘a0 -||-> a1’, ‘b0 -||-> b1’]
  >- (qpat_x_assum ‘_ # _ -||-> _’ mp_tac >>
      simp[SimpL “$==>”, x_ap_y_predn] >> rw[] >~
      [‘K # _ -||-> _’] >- metis_tac[predn_rules, Kx_predn] >~
      [‘S # _ # _ -||-> _’] >- metis_tac[predn_rules, Sxy_predn] >>
      metis_tac[predn_rules])
QED

Theorem predn_diamond: diamond predn
Proof metis_tac [diamond_def, predn_diamond_lemma]
QED

Theorem confluent_redn:  confluent redn
Proof metis_tac [predn_diamond, confluent_diamond_RTC,
                 RTCpredn_EQ_RTCredn, diamond_RTC]
QED

val _ = export_theory();
