open HolKernel Parse boolLib

open bossLib simpLib

local open OpenTheoryMap in
  val ns = "combinatoryLogicExample."
  fun c0 x y = OpenTheory_const_name {const={Thy="cl",Name=x},name=ns^y}
  fun c x = c0 x x
  fun t x = OpenTheory_tyop_name {tyop={Thy="cl",Tyop=x},name=ns^x}
  val _ = t "cl"
  val _ = c "S"
  val _ = c "K"
  val _ = c "#"
  val _ = c "-->"
  val _ = c "-||->"
  val _ = c "RTC"
  val _ = c "confluent"
  val _ = c "normform"
  val _ = c "diamond"
  val _ = c0 " @ind_typecl0" "ind_type.cl0"
  val _ = c0 " @ind_typecl1" "ind_type.cl1"
  val _ = c0 " @ind_typecl2" "ind_type.cl2"
  val _ = c0 "mk_cl" "ind_type.mk_cl"
  val _ = c0 "dest_cl" "ind_type.dest_cl"
  val _ = c0 "cl_case" "ind_type.cl_case"
  val _ = c0 "cl_size" "ind_type.cl_size"
  (* not sure how to deal with this properly: *)
  val _ = OpenTheory_const_name {const={Thy="arithmetic",Name="ZERO"},name="Number.Numeral.zero"}
end

val _ = new_theory "cl";

val _ = Hol_datatype `cl = S | K | # of cl => cl`;

val _ = set_fixity "#"  (Infixl 1100);

val _ = set_fixity "-->" (Infix(NONASSOC, 450))

val (redn_rules, _, redn_cases) = xHol_reln "redn" `
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
  RW_TAC std_ss [confluent_def] THEN
  `?u. RTC R y u /\ RTC R z u` by PROVE_TAC [] THEN
  PROVE_TAC [normform_def, RTC_cases]);

val diamond_def = Define
    `diamond R = !x y z. R x y /\ R x z ==> ?u. R y u /\ R z u`;

val confluent_diamond_RTC = store_thm(
  "confluent_diamond_RTC",
  ``!R. confluent R = diamond (RTC R)``,
  RW_TAC std_ss [confluent_def, diamond_def]);

val R_RTC_diamond = store_thm(
  "R_RTC_diamond",
  ``!R. diamond R ==>
         !x p. RTC R x p ==>
               !z. R x z ==>
                   ?u. RTC R p u /\ RTC R z u``,
  GEN_TAC THEN STRIP_TAC THEN Induct_on `RTC` THEN
  PROVE_TAC [diamond_def,RTC_rules]);

val RTC_RTC = store_thm(
  "RTC_RTC",
  ``!R x y z. RTC R x y /\ RTC R y z ==> RTC R x z``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN Induct_on `RTC` THEN PROVE_TAC [RTC_rules]);

val diamond_RTC_lemma = prove(
  ``!R.
       diamond R ==>
       !x y. RTC R x y ==> !z. RTC R x z ==>
                               ?u. RTC R y u /\ RTC R z u``,
  GEN_TAC THEN STRIP_TAC THEN Induct_on `RTC` THEN
    PROVE_TAC [RTC_RTC, RTC_rules, R_RTC_diamond]
  );

val diamond_RTC = store_thm(
  "diamond_RTC",
  ``!R. diamond R ==> diamond (RTC R)``,
  PROVE_TAC [diamond_def,diamond_RTC_lemma]);

val _ = set_fixity "-||->" (Infix(NONASSOC, 450))
val (predn_rules, predn_ind, predn_cases) = xHol_reln "predn" `
  (!x. x -||-> x) /\
  (!x y u v. x -||-> y /\ u -||-> v ==> x # u -||-> y # v) /\
  (!x y. K # x # y -||-> x) /\
  (!f g x. S # f # g # x -||-> (f # x) # (g # x))
`;

val RTC_monotone = store_thm(
  "RTC_monotone",
  ``!R1 R2. (!x y. R1 x y ==> R2 x y) ==>
            (!x y. RTC R1 x y ==> RTC R2 x y)``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN Induct_on `RTC` THEN
  REPEAT STRIP_TAC THEN PROVE_TAC [RTC_rules]);

val _ = set_fixity "-->*" (Infix(NONASSOC, 450));
val _ = overload_on ("-->*", ``RTC $-->``)

val _ = set_fixity "-||->*" (Infix(NONASSOC, 450));
val _ = overload_on ("-||->*", ``RTC $-||->``)

val RTCredn_RTCpredn = store_thm(
  "RTCredn_RTCpredn",
  ``!x y. x -->* y   ==>   x -||->* y``,
  HO_MATCH_MP_TAC RTC_monotone THEN Induct_on `$-->` THEN
  PROVE_TAC [predn_rules]);

val RTCredn_ap_congruence = store_thm(
  "RTCredn_ap_congruence",
  ``!x y. x -->* y ==> !z. x # z -->* y # z /\ z # x -->* z # y``,
  Induct_on `RTC` THEN PROVE_TAC [RTC_rules, redn_rules]);

val predn_RTCredn = store_thm(
  "predn_RTCredn",
  ``!x y. x -||-> y  ==>  x -->* y``,
  Induct_on `$-||->` THEN
  PROVE_TAC [RTC_rules,redn_rules,RTC_RTC,RTCredn_ap_congruence]);

val RTCpredn_RTCredn = store_thm(
  "RTCpredn_RTCredn",
  ``!x y. x -||->* y   ==>  x -->* y``,
  Induct_on `RTC` THEN PROVE_TAC [predn_RTCredn, RTC_RTC, RTC_rules]);

val RTCpredn_EQ_RTCredn = store_thm(
  "RTCpredn_EQ_RTCredn",
  ``$-||->* = $-->*``,
  SIMP_TAC std_ss [FUN_EQ_THM] THEN
  PROVE_TAC [RTCpredn_RTCredn, RTCredn_RTCpredn]);

fun characterise t = SIMP_RULE (srw_ss()) [] (SPEC t predn_cases);

val K_predn = characterise ``K``;
val S_predn = characterise ``S``;
val Sx_predn0 = characterise ``S # x``;

val Sx_predn = prove(
  ``!x y. S # x -||-> y = ?z. (y = S # z) /\ (x -||-> z)``,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  RW_TAC std_ss [Sx_predn0, predn_rules, S_predn]);

val Kx_predn = prove(
  ``!x y. K # x -||-> y = ?z. (y = K # z) /\ (x -||-> z)``,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  RW_TAC std_ss [characterise ``K # x``, predn_rules, K_predn]);

val Kxy_predn = prove(
  ``!x y z. K # x # y -||-> z =
            (?u v. (z = K # u # v) /\ (x -||-> u) /\ (y -||-> v)) \/
            (z = x)``,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  RW_TAC std_ss [characterise ``K # x # y``, predn_rules, Kx_predn]);


val Sxy_predn = prove(
  ``!x y z. S # x # y -||-> z =
            ?u v. (z = S # u # v) /\ (x -||-> u) /\ (y -||-> v)``,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  RW_TAC std_ss [characterise ``S # x # y``, predn_rules,
                 S_predn, Sx_predn]);

val Sxyz_predn = prove(
  ``!w x y z. S # w # x # y -||-> z =
              (?p q r. (z = S # p # q # r) /\
                       w -||-> p /\ x -||-> q /\ y -||-> r) \/
              (z = (w # y) # (x # y))``,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  RW_TAC std_ss [characterise ``S # w # x # y``, predn_rules, Sxy_predn]);

val x_ap_y_predn = characterise ``x # y``;

val predn_diamond_lemma = prove(
  ``!x y. x -||-> y ==>
          !z. x -||-> z ==> ?u. y -||-> u /\ z -||-> u``,
  Induct_on `$-||->` THEN REPEAT CONJ_TAC THENL [
    PROVE_TAC [predn_rules],
    REPEAT STRIP_TAC THEN
    Q.PAT_ASSUM `x # y -||-> z`
      (STRIP_ASSUME_TAC o SIMP_RULE std_ss [x_ap_y_predn]) THEN
    RW_TAC std_ss [] THEN
    TRY (PROVE_TAC [predn_rules]) THENL [
      `?w. (y = K # w) /\ (z -||-> w)` by PROVE_TAC [Kx_predn] THEN
      RW_TAC std_ss [] THEN PROVE_TAC [predn_rules],
      `?p q. (y = S # p # q) /\ (f -||-> p) /\ (g -||-> q)` by
         PROVE_TAC [Sxy_predn] THEN
      RW_TAC std_ss [] THEN PROVE_TAC [predn_rules]
    ],
    RW_TAC std_ss [Kxy_predn] THEN PROVE_TAC [predn_rules],
    RW_TAC std_ss [Sxyz_predn] THEN PROVE_TAC [predn_rules]
  ]);

val predn_diamond = store_thm(
  "predn_diamond",
  ``diamond $-||->``,
  PROVE_TAC [diamond_def, predn_diamond_lemma]);

val confluent_redn = store_thm(
  "confluent_redn",
  ``confluent $-->``,
  PROVE_TAC [predn_diamond, confluent_diamond_RTC,
             RTCpredn_EQ_RTCredn, diamond_RTC]);


val _ = export_theory();
