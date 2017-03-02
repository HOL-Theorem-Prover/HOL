open HolKernel Parse boolLib

open bossLib simpLib

val _ = new_theory "cl";

val _ = (hide "S"; hide "K")
val _ = Datatype `cl = S | K | # cl cl`;

val _ = set_fixity "#"  (Infixl 1100);

val _ = set_mapped_fixity {tok = "-->", fixity = Infix(NONASSOC, 450),
                           term_name = "redn"}

val (redn_rules, _, _) = Hol_reln `
    (!x y f. x --> y   ==>    f # x --> f # y) /\
    (!f g x. f --> g   ==>    f # x --> g # x) /\
    (!x y.   K # x # y --> x) /\
    (!f g x. S # f # g # x --> (f # x) # (g # x))`;

val _ = hide "RTC";

val (RTC_rules, _, RTC_cases) = Hol_reln `
    (!x.     RTC R x x) /\
    (!x y z. R x y /\ RTC R y z ==> RTC R x z)`;

val confluent_def = Define`
  confluent R =
     !x y z. RTC R x y /\ RTC R x z ==>
             ?u. RTC R y u /\ RTC R z u`;

val normform_def = Define `normform R x = !y. ~R x y`;


val confluent_normforms_unique = store_thm(
  "confluent_normforms_unique",
  ``!R. confluent R ==>
        !x y z. RTC R x y /\ normform R y /\ RTC R x z /\ normform R z
                  ==>
                (y = z)``,
  rw[confluent_def] >>
  `?u. RTC R y u /\ RTC R z u` by metis_tac [] >>
  metis_tac [normform_def, RTC_cases]);

val diamond_def = Define
    `diamond R = !x y z. R x y /\ R x z ==> ?u. R y u /\ R z u`;

val confluent_diamond_RTC = store_thm(
  "confluent_diamond_RTC",
  ``!R. confluent R = diamond (RTC R)``,
  rw[confluent_def, diamond_def]);

val R_RTC_diamond = store_thm(
  "R_RTC_diamond",
  ``!R. diamond R ==>
         !x p. RTC R x p ==>
               !z. R x z ==>
                   ?u. RTC R p u /\ RTC R z u``,
  GEN_TAC >> STRIP_TAC >> Induct_on `RTC` >>
  metis_tac [diamond_def,RTC_rules]);

val RTC_RTC = store_thm(
  "RTC_RTC",
  ``!R x y z. RTC R x y /\ RTC R y z ==> RTC R x z``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] >>
  GEN_TAC >> Induct_on `RTC` >> metis_tac [RTC_rules]);

val diamond_RTC_lemma = prove(
  ``!R.
       diamond R ==>
       !x y. RTC R x y ==> !z. RTC R x z ==>
                               ?u. RTC R y u /\ RTC R z u``,
  GEN_TAC >> STRIP_TAC >> Induct_on `RTC` >> rw[] >| [
    metis_tac[RTC_rules],
    `?v. RTC R x' v /\ RTC R z v` by metis_tac[R_RTC_diamond] >>
    metis_tac [RTC_RTC, RTC_rules]
  ]);

val diamond_RTC = store_thm(
  "diamond_RTC",
  ``!R. diamond R ==> diamond (RTC R)``,
  metis_tac [diamond_def,diamond_RTC_lemma]);

val _ = set_mapped_fixity {tok = "-||->", fixity = Infix(NONASSOC, 450),
                           term_name = "predn"}
val (predn_rules, predn_ind, predn_cases) = Hol_reln `
  (!x. x -||-> x) /\
  (!x y u v. x -||-> y /\ u -||-> v ==> x # u -||-> y # v) /\
  (!x y. K # x # y -||-> x) /\
  (!f g x. S # f # g # x -||-> (f # x) # (g # x))
`;

val RTC_monotone = store_thm(
  "RTC_monotone",
  ``!R1 R2. (!x y. R1 x y ==> R2 x y) ==>
            (!x y. RTC R1 x y ==> RTC R2 x y)``,
  rpt GEN_TAC >> STRIP_TAC >> Induct_on `RTC` >>
  rpt STRIP_TAC >> metis_tac [RTC_rules]);

val _ = set_fixity "-->*" (Infix(NONASSOC, 450));
val _ = overload_on ("-->*", ``RTC redn``)

val _ = set_fixity "-||->*" (Infix(NONASSOC, 450));
val _ = overload_on ("-||->*", ``RTC predn``)

val RTCredn_RTCpredn = store_thm(
  "RTCredn_RTCpredn",
  ``!x y. x -->* y   ==>   x -||->* y``,
  HO_MATCH_MP_TAC RTC_monotone >> Induct_on `x --> y` >>
  metis_tac [predn_rules]);

val RTCredn_ap_congruence = store_thm(
  "RTCredn_ap_congruence",
  ``!x y. x -->* y ==> !z. x # z -->* y # z /\ z # x -->* z # y``,
  Induct_on `RTC` >> metis_tac [RTC_rules, redn_rules]);

val predn_RTCredn = store_thm(
  "predn_RTCredn",
  ``!x y. x -||-> y  ==>  x -->* y``,
  Induct_on `x -||-> y` >>
  metis_tac [RTC_rules,redn_rules,RTC_RTC,RTCredn_ap_congruence]);

val RTCpredn_RTCredn = store_thm(
  "RTCpredn_RTCredn",
  ``!x y. x -||->* y   ==>  x -->* y``,
  Induct_on `RTC` >> metis_tac [predn_RTCredn, RTC_RTC, RTC_rules]);

val RTCpredn_EQ_RTCredn = store_thm(
  "RTCpredn_EQ_RTCredn",
  ``$-||->* = $-->*``,
  SIMP_TAC std_ss [FUN_EQ_THM] >>
  metis_tac [RTCpredn_RTCredn, RTCredn_RTCpredn]);

fun characterise t = SIMP_RULE (srw_ss()) [] (SPEC t predn_cases);

val K_predn = characterise ``K``;
val S_predn = characterise ``S``;
val Sx_predn0 = characterise ``S # x``;

val Sx_predn = prove(
  ``!x y. S # x -||-> y = ?z. (y = S # z) /\ (x -||-> z)``,
  rw[Sx_predn0, predn_rules, S_predn, EQ_IMP_THM]);

val Kx_predn = prove(
  ``!x y. K # x -||-> y = ?z. (y = K # z) /\ (x -||-> z)``,
  rw[characterise ``K # x``, predn_rules, K_predn, EQ_IMP_THM]);

val Kxy_predn = prove(
  ``!x y z. K # x # y -||-> z =
            (?u v. (z = K # u # v) /\ (x -||-> u) /\ (y -||-> v)) \/
            (z = x)``,
  rw[characterise ``K # x # y``, predn_rules, Kx_predn, EQ_IMP_THM]);


val Sxy_predn = prove(
  ``!x y z. S # x # y -||-> z =
            ?u v. (z = S # u # v) /\ (x -||-> u) /\ (y -||-> v)``,
  rw[characterise ``S # x # y``, predn_rules, EQ_IMP_THM,
     S_predn, Sx_predn]);

val Sxyz_predn = prove(
  ``!w x y z. S # w # x # y -||-> z =
              (?p q r. (z = S # p # q # r) /\
                       w -||-> p /\ x -||-> q /\ y -||-> r) \/
              (z = (w # y) # (x # y))``,
  rw[characterise ``S # w # x # y``, predn_rules, Sxy_predn, EQ_IMP_THM]);

val x_ap_y_predn = characterise ``x # y``;

val predn_diamond_lemma = prove(
  ``!x y. x -||-> y ==>
          !z. x -||-> z ==> ?u. y -||-> u /\ z -||-> u``,
  Induct_on `x -||-> y` >> rpt conj_tac >| [
    metis_tac [predn_rules],
    rw[] >>
    qpat_assum `x # y -||-> z`
      (strip_assume_tac o SIMP_RULE std_ss [x_ap_y_predn]) >>
    rw[] >| [
      metis_tac[predn_rules],
      metis_tac[predn_rules],
      `?w. (y = K # w) /\ (z -||-> w)` by metis_tac [Kx_predn] >>
      rw[] >> metis_tac [predn_rules],
      `?p q. (y = S # p # q) /\ (f -||-> p) /\ (g -||-> q)` by
         metis_tac [Sxy_predn] >>
      rw[] >> metis_tac [predn_rules]
    ],
    rw[Kxy_predn] >> metis_tac [predn_rules],
    rw[Sxyz_predn] >> metis_tac [predn_rules]
  ]);

val predn_diamond = store_thm(
  "predn_diamond",
  ``diamond predn``,
  metis_tac [diamond_def, predn_diamond_lemma]);

val confluent_redn = store_thm(
  "confluent_redn",
  ``confluent redn``,
  metis_tac [predn_diamond, confluent_diamond_RTC,
             RTCpredn_EQ_RTCredn, diamond_RTC]);


val _ = export_theory();
