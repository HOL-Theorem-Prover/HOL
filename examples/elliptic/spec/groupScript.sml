(* ========================================================================= *)
(* Create "groupTheory" setting up the theory of groups                      *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories.                                          *)
(* (Comment out "load"s and "quietdec"s for compilation.)                    *)
(* ------------------------------------------------------------------------- *)
(*
val () = loadPath := [] @ !loadPath;
val () = app load
  ["Algebra",
   "bossLib", "metisLib", "res_quanTools",
   "optionTheory", "listTheory",
   "arithmeticTheory", "dividesTheory", "gcdTheory",
   "pred_setTheory", "pred_setSyntax",
   "primalityTools"];
val () = quietdec := true;
*)

open HolKernel Parse boolLib bossLib metisLib res_quanTools;
open optionTheory listTheory arithmeticTheory dividesTheory gcdTheory;
open pred_setTheory;
open primalityTools;

(*
val () = quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "group".                                        *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "group";

val ERR = mk_HOL_ERR "group";
val Bug = mlibUseful.Bug;
val Error = ERR "";

val Bug = fn s => (print ("\n\nBUG: " ^ s ^ "\n\n"); Bug s);

(* ------------------------------------------------------------------------- *)
(* Show oracle tags.                                                         *)
(* ------------------------------------------------------------------------- *)

val () = show_tags := true;

(* ------------------------------------------------------------------------- *)
(* The subtype context.                                                      *)
(* ------------------------------------------------------------------------- *)

val context = subtypeTools.empty2;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

(* ------------------------------------------------------------------------- *)
(* Helper proof tools.                                                       *)
(* ------------------------------------------------------------------------- *)

infixr 0 <<
infixr 1 ++ || THENC ORELSEC
infix 2 >>

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val REVERSE = Tactical.REVERSE;
val lemma = Tactical.prove;

val norm_rule =
    SIMP_RULE (simpLib.++ (pureSimps.pure_ss, resq_SS))
      [GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_IMP_THM,
       AND_IMP_INTRO, GSYM CONJ_ASSOC];

fun match_tac th =
    let
      val th = norm_rule th
      val (_,tm) = strip_forall (concl th)
    in
      (if is_imp tm then MATCH_MP_TAC else MATCH_ACCEPT_TAC) th
    end;

(* ------------------------------------------------------------------------- *)
(* Helper theorems.                                                          *)
(* ------------------------------------------------------------------------- *)

val FUNPOW_ADD = store_thm
  ("FUNPOW_ADD",
   ``!f p q x. FUNPOW f (p + q) x = FUNPOW f p (FUNPOW f q x)``,
   Induct_on `q`
   ++ RW_TAC arith_ss [FUNPOW, ADD_CLAUSES]);

val FUNPOW_MULT = store_thm
  ("FUNPOW_MULT",
   ``!f p q x. FUNPOW f (p * q) x = FUNPOW (\x. FUNPOW f p x) q x``,
   Induct_on `q`
   ++ RW_TAC arith_ss [FUNPOW, MULT_CLAUSES]
   ++ ONCE_REWRITE_TAC [ONCE_REWRITE_RULE [ADD_COMM] FUNPOW_ADD]
   ++ RW_TAC std_ss []);

val DELETE_INSERT = store_thm
  ("DELETE_INSERT",
   ``!e s. ~(e IN s) ==> ((e INSERT s) DELETE e = s)``,
   RW_TAC std_ss [EXTENSION, IN_DELETE, IN_INSERT]
   ++ METIS_TAC []);

val finite_image_card = store_thm
  ("finite_image_card",
   ``!f s. FINITE s ==> CARD (IMAGE f s) <= CARD s``,
   RW_TAC std_ss []
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`s`,`s`)
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss
        [INJ_DEF, CARD_INSERT, NOT_IN_EMPTY, SUBSET_DEF, IN_IMAGE,
         IMAGE_EMPTY, CARD_EMPTY, IN_INSERT, IMAGE_INSERT, IMAGE_FINITE]
   ++ RW_TAC arith_ss []);

val finite_inj_card = store_thm
  ("finite_inj_card",
   ``!f s t.
       FINITE s ==>
       (INJ f s t = IMAGE f s SUBSET t /\ (CARD s = CARD (IMAGE f s)))``,
   RW_TAC std_ss []
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`s`,`s`)
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss
        [INJ_DEF, CARD_INSERT, NOT_IN_EMPTY, SUBSET_DEF, IN_IMAGE,
         IMAGE_EMPTY, CARD_EMPTY, IN_INSERT, IMAGE_INSERT, IMAGE_FINITE]
   ++ REVERSE CASE_TAC >> PROVE_TAC []
   ++ MATCH_MP_TAC (PROVE [] ``~a /\ ~b ==> (a = b)``)
   ++ CONJ_TAC >> METIS_TAC []
   ++ RW_TAC std_ss []
   ++ DISJ2_TAC
   ++ MATCH_MP_TAC (DECIDE ``b <= a ==> ~(SUC a = b)``)
   ++ RW_TAC arith_ss [finite_image_card]);

val finite_inj_surj_imp = store_thm
  ("finite_inj_surj_imp",
   ``!f s. FINITE s /\ SURJ f s s ==> INJ f s s``,
   RW_TAC std_ss [IMAGE_SURJ, finite_inj_card, SUBSET_REFL]);

val finite_inj_surj_imp' = store_thm
  ("finite_inj_surj_imp'",
   ``!f s. FINITE s /\ INJ f s s ==> SURJ f s s``,
   RW_TAC std_ss [IMAGE_SURJ]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [finite_inj_card, IMAGE_FINITE, SUBSET_EQ_CARD]);

val finite_inj_surj = store_thm
  ("finite_inj_surj",
   ``!f s. FINITE s ==> (INJ f s s = SURJ f s s)``,
   METIS_TAC [finite_inj_surj_imp, finite_inj_surj_imp']);

val delete_absent = store_thm
  ("delete_absent",
   ``!s e. ~(e IN s) ==> (s DELETE e = s)``,
   RW_TAC std_ss [EXTENSION, IN_DELETE]
   ++ METIS_TAC []);

val commuting_itset = store_thm
  ("commuting_itset",
   ``!f.
       (!x y z. f x (f y z) = f y (f x z)) ==>
       !e s b.
         FINITE s /\ ~(e IN s) ==>
         (ITSET f (e INSERT s) b = f e (ITSET f s b))``,
   RW_TAC std_ss []
   ++ Know `s DELETE e = s` >> METIS_TAC [delete_absent]
   ++ MP_TAC (Q.SPECL [`f`,`e`,`s`,`b`] COMMUTING_ITSET_RECURSES)
   ++ RW_TAC std_ss []);

val finite_num = store_thm
  ("finite_num",
   ``!s. FINITE s = ?n : num. !m. m IN s ==> m < n``,
   RW_TAC std_ss []
   ++ EQ_TAC
   >> (Q.SPEC_TAC (`s`,`s`)
       ++ HO_MATCH_MP_TAC FINITE_INDUCT
       ++ RW_TAC arith_ss [NOT_IN_EMPTY, IN_INSERT]
       ++ Q.EXISTS_TAC `MAX n (SUC e)`
       ++ RW_TAC arith_ss []
       ++ RES_TAC
       ++ DECIDE_TAC)
   ++ STRIP_TAC
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`s`,`s`)
   ++ Induct_on `n`
   >> (RW_TAC arith_ss []
       ++ Suff `s = {}` >> RW_TAC std_ss [FINITE_EMPTY]
       ++ ONCE_REWRITE_TAC [EXTENSION]
       ++ RW_TAC std_ss [NOT_IN_EMPTY])
   ++ RW_TAC std_ss []
   ++ MATCH_MP_TAC
        (SIMP_RULE std_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]
         SUBSET_FINITE)
   ++ Q.EXISTS_TAC `n INSERT (s DELETE n)`
   ++ REVERSE CONJ_TAC
   >> (ONCE_REWRITE_TAC [EXTENSION]
       ++ RW_TAC std_ss [IN_INSERT, SUBSET_DEF, IN_DELETE])
   ++ RW_TAC std_ss [FINITE_INSERT]
   ++ FIRST_ASSUM MATCH_MP_TAC
   ++ RW_TAC arith_ss [IN_DELETE]
   ++ RES_TAC
   ++ DECIDE_TAC);

val DIVIDES_ONE = store_thm
  ("DIVIDES_ONE",
   ``!n. divides n 1 = (n = 1)``,
   RW_TAC std_ss [divides_def, MULT_EQ_1]);

val prime_one_lt = store_thm
  ("prime_one_lt",
   ``!p. prime p ==> 1 < p``,
   RW_TAC std_ss []
   ++ Suff `~(p = 0) /\ ~(p = 1)` >> DECIDE_TAC
   ++ METIS_TAC [NOT_PRIME_0, NOT_PRIME_1]);

(* ========================================================================= *)
(* Number Theory                                                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Basic definitions                                                         *)
(* ------------------------------------------------------------------------- *)

val totient_def = Define
  `totient n = CARD { i | 0 < i /\ i < n /\ (gcd n i = 1) }`;

(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem                                                   *)
(* ------------------------------------------------------------------------- *)

val mult_lcancel_gcd_imp = store_thm
  ("mult_lcancel_gcd_imp",
   ``!n a b c.
       0 < n /\ (gcd n a = 1) /\ ((a * b) MOD n = (a * c) MOD n) ==>
       (b MOD n = c MOD n)``,
   RW_TAC std_ss []
   ++ Cases_on `n = 1` >> METIS_TAC [MOD_1]
   ++ Cases_on `a = 0` >> METIS_TAC [GCD_0R]
   ++ MP_TAC (Q.SPECL [`a`,`n`] LINEAR_GCD)
   ++ RW_TAC std_ss []
   ++ Know
      `(p MOD n * (a MOD n * b MOD n)) MOD n =
       (p MOD n * (a MOD n * c MOD n)) MOD n`
   >> METIS_TAC [MOD_TIMES2, MOD_MOD]
   ++ REWRITE_TAC [MULT_ASSOC]
   ++ Suff `((p MOD n * a MOD n) MOD n) MOD n = 1`
   >> METIS_TAC [MOD_TIMES2, MOD_MOD, MULT_CLAUSES]
   ++ RW_TAC arith_ss [MOD_TIMES2]
   ++ MP_TAC (Q.SPEC `n` MOD_PLUS)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ RW_TAC std_ss [ONCE_REWRITE_RULE [MULT_COMM] MOD_EQ_0]
   ++ RW_TAC arith_ss [MOD_MOD]);

val mult_lcancel_gcd = store_thm
  ("mult_lcancel_gcd",
   ``!n a b c.
       0 < n /\ (gcd n a = 1) ==>
       (((a * b) MOD n = (a * c) MOD n) = (b MOD n = c MOD n))``,
   METIS_TAC [MOD_TIMES2, mult_lcancel_gcd_imp]);

val is_gcd_1 = store_thm
  ("is_gcd_1",
   ``!n. is_gcd n 1 1``,
   RW_TAC std_ss [is_gcd_def, ONE_DIVIDES_ALL]);

val gcd_1 = store_thm
  ("gcd_1",
   ``!n. gcd n 1 = 1``,
   METIS_TAC [is_gcd_1, GCD_IS_GCD, IS_GCD_UNIQUE]);

val divides_gcd = store_thm
  ("divides_gcd",
   ``!a b. divides (gcd a b) a /\ divides (gcd a b) b``,
   Suff `!a b. divides (gcd a b) a` >> METIS_TAC [GCD_SYM]
   ++ RW_TAC std_ss []
   ++ Know `is_gcd a b (gcd a b)` >> METIS_TAC [GCD_IS_GCD]
   ++ RW_TAC std_ss [is_gcd_def]);

val is_gcd_1_mult_imp = store_thm
  ("is_gcd_1_mult_imp",
   ``!n a b. is_gcd n a 1 /\ is_gcd n b 1 ==> is_gcd n (a * b) 1``,
   RW_TAC std_ss [is_gcd_def, ONE_DIVIDES_ALL]
   ++ Cases_on `gcd a d = 1`
   >> (MP_TAC (Q.SPECL [`a`,`d`,`b`] L_EUCLIDES)
       ++ RW_TAC std_ss [])
   ++ FULL_SIMP_TAC std_ss [DIVIDES_ONE]
   ++ Suff `F` >> METIS_TAC []
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `!i. P i` (K ALL_TAC)
   ++ Q.PAT_ASSUM `!i. P i` MATCH_MP_TAC
   ++ METIS_TAC [DIVIDES_TRANS,  divides_gcd]);

val gcd_1_mult_imp = store_thm
  ("gcd_1_mult_imp",
   ``!n a b. (gcd n a = 1) /\ (gcd n b = 1) ==> (gcd n (a * b) = 1)``,
   METIS_TAC [is_gcd_1_mult_imp, GCD_IS_GCD, IS_GCD_UNIQUE]);

val gcd_modr = store_thm
  ("gcd_modr",
   ``!n a. 0 < n ==> (gcd n (a MOD n) = gcd n a)``,
   METIS_TAC [GCD_SYM, DECIDE ``0 < n ==> ~(n = 0)``, GCD_EFFICIENTLY]);

val euler_totient = store_thm
  ("euler_totient",
   ``!n a. (gcd n a = 1) ==> (a ** totient n MOD n = 1 MOD n)``,
   RW_TAC std_ss []
   ++ Cases_on `n = 0`
   >> RW_TAC bool_ss
        [totient_def, prim_recTheory.NOT_LESS_0, GSPEC_F,
         CARD_EMPTY, EXP]
   ++ Cases_on `n = 1` >> RW_TAC bool_ss [MOD_1]
   ++ Know `0 < n` >> DECIDE_TAC
   ++ STRIP_TAC
   ++ MATCH_MP_TAC mult_lcancel_gcd_imp
   ++ Q.EXISTS_TAC
      `ITSET (\y z. y * z) { i | 0 < i /\ i < n /\ (gcd n i = 1) } 1`
   ++ Know `FINITE { i | 0 < i /\ i < n /\ (gcd n i = 1) }`
   >> (RW_TAC std_ss [finite_num, GSPECIFICATION]
       ++ METIS_TAC [])
   ++ RW_TAC arith_ss []
   >> (Suff
       `!s b.
          FINITE s /\ (!i. i IN s ==> (gcd n i = 1)) /\ (gcd n b = 1) ==>
          (gcd n (ITSET (\y z. y * z) s b) = 1)`
       >> (DISCH_THEN MATCH_MP_TAC
           ++ RW_TAC std_ss [GSPECIFICATION, gcd_1])
       ++ HO_MATCH_MP_TAC (GEN_ALL ITSET_IND)
       ++ Q.EXISTS_TAC `\y z. y * z`
       ++ RW_TAC std_ss []
       ++ RW_TAC std_ss [ITSET_THM]
       ++ FIRST_ASSUM (MATCH_MP_TAC o CONV_RULE (REWR_CONV AND_IMP_INTRO))
       ++ RW_TAC std_ss [REST_DEF, FINITE_DELETE, IN_DELETE]
       ++ MATCH_MP_TAC gcd_1_mult_imp
       ++ METIS_TAC [CHOICE_DEF])
   ++ Know `INJ (\i. (i * a) MOD n) {i | 0 < i /\ i < n /\ (gcd n i = 1)} UNIV`
   >> (RW_TAC std_ss [INJ_DEF, IN_UNIV]
       ++ Know `i MOD n = i' MOD n`
       >> METIS_TAC [mult_lcancel_gcd_imp, MULT_COMM]
       ++ FULL_SIMP_TAC std_ss [GSPECIFICATION]
       ++ METIS_TAC [LESS_MOD])
   ++ STRIP_TAC
   ++ Know
      `IMAGE (\i. (i * a) MOD n) {i | 0 < i /\ i < n /\ (gcd n i = 1)} =
       {i | 0 < i /\ i < n /\ (gcd n i = 1)}`
   >> (RW_TAC std_ss [GSYM IMAGE_SURJ, GSYM finite_inj_surj]
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC bool_ss [INJ_DEF, IN_UNIV]
       ++ Q.PAT_ASSUM `!i i'. P i i'` (K ALL_TAC)
       ++ FULL_SIMP_TAC std_ss [GSPECIFICATION, DIVISION]
       ++ MATCH_MP_TAC (PROVE [] ``(~a ==> ~b) /\ b ==> a /\ b``)
       ++ CONJ_TAC
       >> (Cases_on `(i * a) MOD n`
           ++ RW_TAC arith_ss [GCD_0R])
       ++ RW_TAC std_ss [gcd_modr]
       ++ METIS_TAC [gcd_1_mult_imp])
   ++ DISCH_THEN (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th])))
   ++ RW_TAC std_ss [totient_def]
   ++ POP_ASSUM MP_TAC
   ++ POP_ASSUM MP_TAC
   ++ Suff
      `!s.
         FINITE s ==>
         INJ (\i. (i * a) MOD n) s UNIV ==>
         ((ITSET (\y z. y * z) s 1 * a ** CARD s) MOD n =
          ITSET (\y z. y * z) (IMAGE (\i. (i * a) MOD n) s) 1 MOD n)`
   >> RW_TAC arith_ss []
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss
        [CARD_EMPTY, ITSET_EMPTY, IMAGE_EMPTY, EXP, MULT_CLAUSES,
         CARD_INSERT, IMAGE_INSERT]
   ++ Q.PAT_ASSUM `X ==> Y` MP_TAC
   ++ POP_ASSUM MP_TAC
   ++ SIMP_TAC bool_ss [INJ_DEF, IN_UNIV]
   ++ STRIP_TAC
   ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
   ++ CONJ_TAC >> METIS_TAC [IN_INSERT]
   ++ STRIP_TAC
   ++ MP_TAC (Q.ISPEC `\y z : num. y * z` commuting_itset)
   ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
   ++ SIMP_TAC std_ss []
   ++ CONJ_TAC >> METIS_TAC [MULT_ASSOC, MULT_COMM]
   ++ DISCH_THEN
      (fn th =>
       MP_TAC (Q.SPECL [`(e * a) MOD n`,`IMAGE (\i. (i * a) MOD n) s`,`1`] th)
       ++ MP_TAC (Q.SPECL [`e`,`s`,`1`] th))
   ++ RW_TAC std_ss [IMAGE_FINITE]
   ++ POP_ASSUM MP_TAC
   ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
   ++ CONJ_TAC
   >> (Q.PAT_ASSUM `!i i'. P i i'` (MP_TAC o Q.SPEC `e`)
       ++ RW_TAC std_ss [IN_IMAGE, IN_INSERT]
       ++ METIS_TAC [])
   ++ DISCH_THEN (fn th => RW_TAC std_ss [th])
   ++ POP_ASSUM (K ALL_TAC)
   ++ Q.PAT_ASSUM `!i i'. P i i'` (K ALL_TAC)
   ++ MATCH_MP_TAC
      (METIS_PROVE [MULT_ASSOC, MULT_COMM]
       ``(((a * c) * (b * d)) MOD n = X) ==> ((a * b * (c * d)) MOD n = X)``)
   ++ MP_TAC (Q.SPEC `n` MOD_TIMES2)
   ++ ASM_SIMP_TAC std_ss []
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ RW_TAC std_ss [MOD_MOD]);

val prime_is_gcd_1 = store_thm
  ("prime_is_gcd_1",
   ``!p a. prime p ==> (is_gcd p a 1 = ~divides p a)``,
   RW_TAC std_ss [is_gcd_def, DIVIDES_ONE, ONE_DIVIDES_ALL]
   ++ EQ_TAC
   >> (DISCH_THEN (MP_TAC o Q.SPEC `p`)
       ++ METIS_TAC [DIVIDES_REFL, NOT_PRIME_1])
   ++ RW_TAC std_ss []
   ++ MP_TAC (Q.SPEC `p` prime_def)
   ++ RW_TAC std_ss []
   ++ POP_ASSUM (MP_TAC o Q.SPEC `d`)
   ++ ASM_REWRITE_TAC []
   ++ STRIP_TAC
   ++ RW_TAC std_ss []
   ++ METIS_TAC []);

val prime_gcd_1 = store_thm
  ("prime_gcd_1",
   ``!p a. prime p ==> ((gcd p a = 1) = ~divides p a)``,
   METIS_TAC [prime_is_gcd_1, GCD_IS_GCD, IS_GCD_UNIQUE]);

val prime_totient = store_thm
  ("prime_totient",
   ``!p. prime p ==> (totient p = p - 1)``,
   RW_TAC std_ss [totient_def, prime_gcd_1]
   ++ Suff `{i | 0 < i /\ i < p /\ ~divides p i} = count p DELETE 0`
   >> (RW_TAC std_ss [CARD_DELETE, FINITE_COUNT, CARD_COUNT]
       ++ Suff `F` >> METIS_TAC []
       ++ POP_ASSUM (K ALL_TAC)
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC std_ss [count_def, GSPECIFICATION]
       ++ METIS_TAC [NOT_PRIME_0, DECIDE ``0 < p = ~(p = 0)``])
   ++ RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_DELETE, count_def]
   ++ Suff `0 < x /\ x < p ==> ~divides p x`
   >> METIS_TAC [DECIDE ``0 < p = ~(p = 0)``]
   ++ METIS_TAC [DIVIDES_LE, DECIDE ``~(a : num < b) = b <= a``]);

val fermat_little = store_thm
  ("fermat_little",
   ``!p a. prime p /\ ~divides p a ==> (a ** (p - 1) MOD p = 1)``,
   RW_TAC std_ss []
   ++ MP_TAC (Q.SPECL [`p`,`a`] euler_totient)
   ++ RW_TAC std_ss [prime_gcd_1, prime_totient]
   ++ Suff `0 < p /\ 1 < p` >> METIS_TAC [X_MOD_Y_EQ_X]
   ++ Suff `~(p = 0) /\ ~(p = 1)` >> DECIDE_TAC
   ++ METIS_TAC [NOT_PRIME_0, NOT_PRIME_1]);

(* ========================================================================= *)
(* Groups                                                                    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The basic definitions                                                     *)
(* ------------------------------------------------------------------------- *)

val () = Hol_datatype
  `group = <| carrier : 'a -> bool;
              id : 'a;
              inv : 'a -> 'a;
              mult : 'a -> 'a -> 'a |>`;

val Group_def = Define
  `Group =
   { (g : 'a group) |
     g.id IN g.carrier /\
     (!x y :: (g.carrier). g.mult x y IN g.carrier) /\
     (!x :: (g.carrier). g.inv x IN g.carrier) /\
     (!x :: (g.carrier). g.mult g.id x = x) /\
     (!x :: (g.carrier). g.mult (g.inv x) x = g.id) /\
     (!x y z :: (g.carrier). g.mult (g.mult x y) z = g.mult x (g.mult y z)) }`;

val group_exp_def = Define
  `(group_exp G g 0 = G.id) /\
   (group_exp G g (SUC n) = G.mult g (group_exp G g n))`;

val AbelianGroup_def = Define
  `AbelianGroup =
   { (g : 'a group) |
     g IN Group /\ !x y :: (g.carrier). g.mult x y = g.mult y x }`;

val FiniteGroup_def = Define
  `FiniteGroup = { (g : 'a group) | g IN Group /\ FINITE g.carrier }`;

val FiniteAbelianGroup_def = Define
  `FiniteAbelianGroup =
   { (g : 'a group) | g IN FiniteGroup /\ g IN AbelianGroup }`;

val group_accessors = fetch "-" "group_accessors";

(* Syntax operations *)

val group_inv_tm = ``group_inv``;

fun dest_group_inv tm =
    let
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm group_inv_tm orelse raise ERR "group_inv_neg" ""
    in
      (f,x)
    end;

val is_group_inv = can dest_group_inv;

val group_mult_tm = ``group_mult``;

fun dest_group_mult tm =
    let
      val (tm,y) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm group_mult_tm orelse raise ERR "dest_group_mult" ""
    in
      (f,x,y)
    end;

val is_group_mult = can dest_group_mult;

val group_exp_tm = ``group_exp``;

fun dest_group_exp tm =
    let
      val (tm,n) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm group_exp_tm orelse raise ERR "dest_group_exp" ""
    in
      (f,x,n)
    end;

val is_group_exp = can dest_group_exp;

(* Theorems *)

val AbelianGroup_Group = store_thm
  ("AbelianGroup_Group",
   ``!g. g IN AbelianGroup ==> g IN Group``,
   RW_TAC std_ss [AbelianGroup_def, GSPECIFICATION]);

val context = subtypeTools.add_judgement2 AbelianGroup_Group context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val FiniteGroup_Group = store_thm
  ("FiniteGroup_Group",
   ``!g. g IN FiniteGroup ==> g IN Group``,
   RW_TAC std_ss [FiniteGroup_def, GSPECIFICATION]);

val context = subtypeTools.add_judgement2 FiniteGroup_Group context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val FiniteAbelianGroup_FiniteGroup = store_thm
  ("FiniteAbelianGroup_FiniteGroup",
   ``!g. g IN FiniteAbelianGroup ==> g IN FiniteGroup``,
   RW_TAC std_ss [FiniteAbelianGroup_def, GSPECIFICATION]);

val context = subtypeTools.add_judgement2 FiniteAbelianGroup_FiniteGroup context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val FiniteAbelianGroup_AbelianGroup = store_thm
  ("FiniteAbelianGroup_AbelianGroup",
   ``!g. g IN FiniteAbelianGroup ==> g IN AbelianGroup``,
   RW_TAC std_ss [FiniteAbelianGroup_def, GSPECIFICATION]);

val context =
    subtypeTools.add_judgement2 FiniteAbelianGroup_AbelianGroup context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val FiniteAbelianGroup_alt = store_thm
  ("FiniteAbelianGroup_alt",
   ``FiniteAbelianGroup =
     { (g : 'a group) |
       g IN Group /\
       (!x y :: (g.carrier). g.mult x y = g.mult y x) /\
       FINITE g.carrier }``,
   RW_TAC std_ss
     [FiniteAbelianGroup_def, FiniteGroup_def, AbelianGroup_def,
      EXTENSION, GSPECIFICATION]
   ++ METIS_TAC []);

val group_id_carrier = store_thm
  ("group_id_carrier",
   ``!g :: Group. g.id IN g.carrier``,
   RW_TAC resq_ss [Group_def, GSPECIFICATION]);

val context = subtypeTools.add_reduction2 group_id_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_inv_carrier = store_thm
  ("group_inv_carrier",
   ``!g :: Group. !x :: (g.carrier). g.inv x IN g.carrier``,
   RW_TAC resq_ss [Group_def, GSPECIFICATION]);

val context = subtypeTools.add_reduction2 group_inv_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_mult_carrier = store_thm
  ("group_mult_carrier",
   ``!g :: Group. !x y :: (g.carrier). g.mult x y IN g.carrier``,
   RW_TAC resq_ss [Group_def, GSPECIFICATION]);

val context = subtypeTools.add_reduction2 group_mult_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_lid = store_thm
  ("group_lid",
   ``!g :: Group. !x :: (g.carrier). g.mult g.id x = x``,
   RW_TAC resq_ss [Group_def, GSPECIFICATION]);

val context = subtypeTools.add_rewrite2 group_lid context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_linv = store_thm
  ("group_linv",
   ``!g :: Group. !x :: (g.carrier). g.mult (g.inv x) x = g.id``,
   RW_TAC resq_ss [Group_def, GSPECIFICATION]);

val context = subtypeTools.add_rewrite2 group_linv context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_assoc = store_thm
  ("group_assoc",
   ``!g :: Group. !x y z :: (g.carrier).
       g.mult (g.mult x y) z = g.mult x (g.mult y z)``,
   RW_TAC resq_ss [Group_def, GSPECIFICATION]);

val context = subtypeTools.add_rewrite2'' group_assoc context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_comm = store_thm
  ("group_comm",
   ``!g :: AbelianGroup. !x y :: (g.carrier). g.mult x y = g.mult y x``,
   RW_TAC resq_ss [AbelianGroup_def, GSPECIFICATION]);

val group_comm' = store_thm
  ("group_comm'",
   ``!g :: AbelianGroup. !x y z :: (g.carrier).
        g.mult x (g.mult y z) = g.mult y (g.mult x z)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss [GSYM group_assoc]
   ++ METIS_TAC [group_comm]);

val group_rinv = store_thm
  ("group_rinv",
   ``!g :: Group. !x :: (g.carrier). g.mult x (g.inv x) = g.id``,
   RW_TAC resq_ss []
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult g.id (g.mult x (g.inv x))`
   ++ CONJ_TAC
   >> (match_tac (GSYM group_lid)
       ++ METIS_TAC [group_inv_carrier, group_mult_carrier])
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC
        `g.mult (g.mult (g.inv (g.inv x)) (g.inv x)) (g.mult x (g.inv x))`
   ++ CONJ_TAC
   >> (REPEAT (AP_TERM_TAC || AP_THM_TAC)
       ++ match_tac (GSYM group_linv)
       ++ METIS_TAC [group_inv_carrier, group_mult_carrier])
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC
        `g.mult (g.inv (g.inv x)) (g.mult (g.inv x) (g.mult x (g.inv x)))`
   ++ CONJ_TAC
   >> (match_tac group_assoc
       ++ METIS_TAC [group_inv_carrier, group_mult_carrier])
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC
        `g.mult (g.inv (g.inv x)) (g.mult (g.mult (g.inv x) x) (g.inv x))`
   ++ CONJ_TAC
   >> (AP_TERM_TAC
       ++ match_tac (GSYM group_assoc)
       ++ METIS_TAC [group_inv_carrier, group_mult_carrier])
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult (g.inv (g.inv x)) (g.mult g.id (g.inv x))`
   ++ CONJ_TAC
   >> (REPEAT (AP_TERM_TAC || AP_THM_TAC)
       ++ match_tac group_linv
       ++ METIS_TAC [group_inv_carrier, group_mult_carrier])
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult (g.inv (g.inv x)) (g.inv x)`
   ++ CONJ_TAC
   >> (REPEAT (AP_TERM_TAC || AP_THM_TAC)
       ++ match_tac group_lid
       ++ METIS_TAC [group_inv_carrier, group_mult_carrier])
   ++ match_tac group_linv
   ++ METIS_TAC [group_inv_carrier, group_mult_carrier]);

val context = subtypeTools.add_rewrite2 group_rinv context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_rid = store_thm
  ("group_rid",
   ``!g :: Group. !x :: (g.carrier). g.mult x g.id = x``,
   RW_TAC resq_ss []
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult x (g.mult (g.inv x) x)`
   ++ CONJ_TAC
   >> (REPEAT (AP_TERM_TAC || AP_THM_TAC)
       ++ match_tac (GSYM group_linv)
       ++ METIS_TAC [group_inv_carrier, group_mult_carrier])
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult (g.mult x (g.inv x)) x`
   ++ CONJ_TAC
   >> (match_tac (GSYM group_assoc)
       ++ METIS_TAC [group_inv_carrier, group_mult_carrier])
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult g.id x`
   ++ CONJ_TAC
   >> (REPEAT (AP_TERM_TAC || AP_THM_TAC)
       ++ match_tac group_rinv
       ++ METIS_TAC [group_inv_carrier, group_mult_carrier])
   ++ match_tac group_lid
   ++ METIS_TAC [group_inv_carrier, group_mult_carrier]);

val context = subtypeTools.add_rewrite2 group_rid context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_lcancel = store_thm
  ("group_lcancel",
   ``!g :: Group. !x y z :: (g.carrier). (g.mult x y = g.mult x z) = (y = z)``,
   RW_TAC resq_ss []
   ++ REVERSE EQ_TAC >> RW_TAC std_ss []
   ++ RW_TAC std_ss []
   ++ Suff `g.mult g.id y = g.mult g.id z`
   >> METIS_TAC [group_lid]
   ++ Suff `g.mult (g.mult (g.inv x) x) y = g.mult (g.mult (g.inv x) x) z`
   >> METIS_TAC [group_linv]
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult (g.inv x) (g.mult x y)`
   ++ CONJ_TAC
   >> (match_tac group_assoc ++ METIS_TAC [group_inv_carrier])
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult (g.inv x) (g.mult x z)`
   ++ REVERSE CONJ_TAC
   >> (match_tac (GSYM group_assoc) ++ METIS_TAC [group_inv_carrier])
   ++ RW_TAC std_ss []);

val context = subtypeTools.add_rewrite2' group_lcancel context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_lcancel_imp = store_thm
  ("group_lcancel_imp",
   ``!g :: Group. !x y z :: (g.carrier).
       (g.mult x y = g.mult x z) ==> (y = z)``,
   METIS_TAC [group_lcancel]);

val group_lcancel_id = store_thm
  ("group_lcancel_id",
   ``!g :: Group. !x y :: (g.carrier). (g.mult x y = x) = (y = g.id)``,
   RW_TAC resq_ss []
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult x y = g.mult x g.id`
   ++ CONJ_TAC
   >> RW_TAC std_ss [group_rid]
   ++ match_tac group_lcancel
   ++ RW_TAC std_ss [group_id_carrier]);

val context = subtypeTools.add_rewrite2' group_lcancel_id context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_lcancel_id_imp = store_thm
  ("group_lcancel_id_imp",
   ``!g :: Group. !x y :: (g.carrier). (g.mult x y = x) ==> (y = g.id)``,
   METIS_TAC [group_lcancel_id]);

val group_lcancel_id_imp' = store_thm
  ("group_lcancel_id_imp'",
   ``!g :: Group. !x y :: (g.carrier). (y = g.id) ==> (g.mult x y = x)``,
   METIS_TAC [group_lcancel_id]);

val group_rcancel = store_thm
  ("group_rcancel",
   ``!g :: Group. !x y z :: (g.carrier). (g.mult y x = g.mult z x) = (y = z)``,
   RW_TAC resq_ss []
   ++ REVERSE EQ_TAC >> RW_TAC std_ss []
   ++ RW_TAC std_ss []
   ++ Suff `g.mult y g.id = g.mult z g.id`
   >> METIS_TAC [group_rid]
   ++ Suff `g.mult y (g.mult x (g.inv x)) = g.mult z (g.mult x (g.inv x))`
   >> METIS_TAC [group_rinv]
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult (g.mult y x) (g.inv x)`
   ++ CONJ_TAC
   >> (match_tac (GSYM group_assoc) ++ METIS_TAC [group_inv_carrier])
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult (g.mult z x) (g.inv x)`
   ++ REVERSE CONJ_TAC
   >> (match_tac group_assoc ++ METIS_TAC [group_inv_carrier])
   ++ RW_TAC std_ss []);

val context = subtypeTools.add_rewrite2' group_rcancel context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_rcancel_imp = store_thm
  ("group_rcancel_imp",
   ``!g :: Group. !x y z :: (g.carrier).
       (g.mult y x = g.mult z x) ==> (y = z)``,
   METIS_TAC [group_rcancel]);

val group_rcancel_id = store_thm
  ("group_rcancel_id",
   ``!g :: Group. !x y :: (g.carrier). (g.mult y x = x) = (y = g.id)``,
   RW_TAC resq_ss []
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult y x = g.mult g.id x`
   ++ CONJ_TAC
   >> RW_TAC std_ss [group_lid]
   ++ match_tac group_rcancel
   ++ RW_TAC std_ss [group_id_carrier]);

val context = subtypeTools.add_rewrite2' group_rcancel_id context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_rcancel_id_imp = store_thm
  ("group_rcancel_id_imp",
   ``!g :: Group. !x y :: (g.carrier). (g.mult y x = x) ==> (y = g.id)``,
   METIS_TAC [group_rcancel_id]);

val group_rcancel_id_imp' = store_thm
  ("group_rcancel_id_imp'",
   ``!g :: Group. !x y :: (g.carrier). (y = g.id) ==> (g.mult y x = x)``,
   METIS_TAC [group_rcancel_id]);

val group_inv_cancel_imp = store_thm
  ("group_inv_cancel_imp",
   ``!g :: Group. !x y :: (g.carrier). (g.inv x = g.inv y) ==> (x = y)``,
   RW_TAC resq_ss []
   ++ match_tac group_lcancel_imp
   ++ Q.EXISTS_TAC `g`
   ++ Q.EXISTS_TAC `g.inv x`
   ++ RW_TAC std_ss [group_inv_carrier]
   ++ METIS_TAC [group_linv]);

val group_inv_cancel = store_thm
  ("group_inv_cancel",
   ``!g :: Group. !x y :: (g.carrier). (g.inv x = g.inv y) = (x = y)``,
   METIS_TAC [group_inv_cancel_imp]);

val context = subtypeTools.add_rewrite2' group_inv_cancel context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_inv_inv = store_thm
  ("group_inv_inv",
   ``!g :: Group. !x :: (g.carrier). g.inv (g.inv x) = x``,
   RW_TAC resq_ss []
   ++ match_tac group_lcancel_imp
   ++ Q.EXISTS_TAC `g`
   ++ Q.EXISTS_TAC `g.inv x`
   ++ RW_TAC std_ss [group_inv_carrier]
   ++ METIS_TAC [group_inv_carrier, group_linv, group_rinv]);

val context = subtypeTools.add_rewrite2 group_inv_inv context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_inv_eq_swap_imp = store_thm
  ("group_inv_eq_swap_imp",
   ``!g :: Group. !x y :: (g.carrier). (g.inv x = y) ==> (x = g.inv y)``,
   METIS_TAC [group_inv_inv]);

val group_inv_eq_swap = store_thm
  ("group_inv_eq_swap",
   ``!g :: Group. !x y :: (g.carrier). (g.inv x = y) = (x = g.inv y)``,
   METIS_TAC [group_inv_eq_swap_imp]);

val group_inv_eq_swap_imp' = store_thm
  ("group_inv_eq_swap_imp'",
   ``!g :: Group. !x y :: (g.carrier). (x = g.inv y) ==> (g.inv x = y)``,
   METIS_TAC [group_inv_eq_swap]);

val group_inv_id = store_thm
  ("group_inv_id",
   ``!g :: Group. g.inv g.id = g.id``,
   RW_TAC resq_ss []
   ++ match_tac group_lcancel_imp
   ++ Q.EXISTS_TAC `g`
   ++ Q.EXISTS_TAC `g.id`
   ++ RW_TAC std_ss [group_inv_carrier, group_id_carrier, group_rinv]
   ++ RW_TAC std_ss [group_lid, group_id_carrier]);

val context = subtypeTools.add_rewrite2 group_inv_id context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_inv_eq_imp = store_thm
  ("group_inv_eq_imp",
   ``!g :: Group. !x y :: (g.carrier). (g.inv x = y) ==> (g.mult x y = g.id)``,
   RW_TAC resq_ss [group_rinv]);

val group_inv_eq_imp' = store_thm
  ("group_inv_eq_imp'",
   ``!g :: Group. !x y :: (g.carrier). (g.mult x y = g.id) ==> (g.inv x = y)``,
   RW_TAC resq_ss []
   ++ match_tac group_lcancel_imp
   ++ Q.EXISTS_TAC `g`
   ++ Q.EXISTS_TAC `x`
   ++ RW_TAC std_ss [group_inv_carrier, group_rinv]);

val group_inv_eq = store_thm
  ("group_inv_eq",
   ``!g :: Group. !x y :: (g.carrier). (g.inv x = y) = (g.mult x y = g.id)``,
   METIS_TAC [group_inv_eq_imp, group_inv_eq_imp']);

val group_inv_mult = store_thm
  ("group_inv_mult",
   ``!g :: Group. !x y :: (g.carrier).
       g.inv (g.mult x y) = g.mult (g.inv y) (g.inv x)``,
   RW_TAC resq_ss []
   ++ match_tac group_inv_eq_imp'
   ++ RW_TAC std_ss [group_mult_carrier, group_inv_carrier]
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult x (g.mult y (g.mult (g.inv y) (g.inv x)))`
   ++ CONJ_TAC
   >> (match_tac group_assoc
       ++ METIS_TAC [group_mult_carrier, group_inv_carrier])
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult x (g.mult (g.mult y (g.inv y)) (g.inv x))`
   ++ CONJ_TAC
   >> (AP_TERM_TAC
       ++ match_tac (GSYM group_assoc)
       ++ METIS_TAC [group_mult_carrier, group_inv_carrier])
   ++ RW_TAC std_ss [group_rinv, group_lid, group_inv_carrier]);

val context = subtypeTools.add_rewrite2'' group_inv_mult context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_exp_carrier = store_thm
  ("group_exp_carrier",
   ``!g :: Group. !x :: (g.carrier). !n. group_exp g x n IN g.carrier``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [group_exp_def]
   ++ METIS_TAC [group_id_carrier, group_mult_carrier]);

val context = subtypeTools.add_reduction2 group_exp_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_id_exp = store_thm
  ("group_id_exp",
   ``!g :: Group. !n. group_exp g g.id n = g.id``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [group_exp_def, group_lid, group_id_carrier]);

val context = subtypeTools.add_rewrite2 group_id_exp context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_comm_exp = store_thm
  ("group_comm_exp",
   ``!g :: Group. !x y :: (g.carrier). !n.
        (g.mult x y = g.mult y x) ==>
        (g.mult (group_exp g x n) y = g.mult y (group_exp g x n))``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [group_exp_def, group_lid, group_rid]
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult x (g.mult (group_exp g x n) y)`
   ++ CONJ_TAC
   >> (match_tac group_assoc
       ++ METIS_TAC [group_mult_carrier, group_exp_carrier])
   ++ RW_TAC std_ss []
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult (g.mult x y) (group_exp g x n)`
   ++ CONJ_TAC
   >> (match_tac (GSYM group_assoc)
       ++ METIS_TAC [group_mult_carrier, group_exp_carrier])
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult (g.mult y x) (group_exp g x n)`
   ++ REVERSE CONJ_TAC
   >> (match_tac group_assoc
       ++ METIS_TAC [group_mult_carrier, group_exp_carrier])
   ++ ASM_REWRITE_TAC []);

val group_exp_comm = store_thm
  ("group_exp_comm",
   ``!g :: Group. !x :: (g.carrier). !n.
        g.mult (group_exp g x n) x = g.mult x (group_exp g x n)``,
   RW_TAC resq_ss []
   ++ match_tac group_comm_exp
   ++ RW_TAC std_ss []);

val group_mult_exp = store_thm
  ("group_mult_exp",
   ``!g :: Group. !x y :: (g.carrier). !n.
        (g.mult x y = g.mult y x) ==>
        (group_exp g (g.mult x y) n =
         g.mult (group_exp g x n) (group_exp g y n))``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss
        [group_exp_def, group_exp_carrier, group_lid, group_id_carrier]
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC
        `g.mult x (g.mult y (g.mult (group_exp g x n) (group_exp g y n)))`
   ++ CONJ_TAC
   >> (match_tac group_assoc
       ++ METIS_TAC [group_mult_carrier, group_exp_carrier])
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC
        `g.mult x (g.mult (group_exp g x n) (g.mult y (group_exp g y n)))`
   ++ REVERSE CONJ_TAC
   >> (match_tac (GSYM group_assoc)
       ++ METIS_TAC [group_mult_carrier, group_exp_carrier])
   ++ AP_TERM_TAC
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult (g.mult y (group_exp g x n)) (group_exp g y n)`
   ++ CONJ_TAC
   >> (match_tac (GSYM group_assoc)
       ++ METIS_TAC [group_mult_carrier, group_exp_carrier])
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `g.mult (g.mult (group_exp g x n) y) (group_exp g y n)`
   ++ REVERSE CONJ_TAC
   >> (match_tac group_assoc
       ++ METIS_TAC [group_mult_carrier, group_exp_carrier])
   ++ AP_THM_TAC
   ++ AP_TERM_TAC
   ++ match_tac (GSYM group_comm_exp)
   ++ METIS_TAC []);

val group_exp_add = store_thm
  ("group_exp_add",
   ``!g :: Group. !x :: (g.carrier). !m n.
        group_exp g x (m + n) = g.mult (group_exp g x m) (group_exp g x n)``,
   RW_TAC resq_ss []
   ++ Induct_on `m`
   ++ RW_TAC std_ss [group_exp_def, group_lid, group_exp_carrier, ADD]
   ++ match_tac (GSYM group_assoc)
   ++ RW_TAC std_ss [group_exp_carrier]);

val group_exp_mult = store_thm
  ("group_exp_mult",
   ``!g :: Group. !x :: (g.carrier). !m n.
        group_exp g x (m * n) = group_exp g (group_exp g x m) n``,
   RW_TAC resq_ss []
   ++ Induct_on `m`
   ++ RW_TAC std_ss [group_exp_def, group_id_exp, group_exp_carrier, MULT]
   ++ ONCE_REWRITE_TAC [ADD_COMM]
   ++ RW_TAC std_ss [group_exp_carrier, group_exp_add]
   ++ MATCH_MP_TAC EQ_SYM
   ++ match_tac group_mult_exp
   ++ RW_TAC std_ss [group_exp_carrier]
   ++ match_tac (GSYM group_exp_comm)
   ++ METIS_TAC []);

val group_id_alt = store_thm
  ("group_id_alt",
   ``!g :: Group. !x :: (g.carrier). (g.mult x x = x) = (x = g.id)``,
   RW_TAC alg_ss []);

val group_ac_conv =
    {name = "group_ac_conv",
     key = ``g.mult x y``,
     conv = subtypeTools.binop_ac_conv
              {term_compare = compare,
               dest_binop = dest_group_mult,
               dest_inv = dest_group_inv,
               dest_exp = dest_group_exp,
               assoc_th = group_assoc,
               comm_th = group_comm,
               comm_th' = group_comm',
               id_ths = [],
               simplify_ths = [],
               combine_ths = [],
               combine_ths' = []}};

val context = subtypeTools.add_conversion2'' group_ac_conv context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_exp_eval = store_thm
  ("group_exp_eval",
   ``!g :: Group. !x :: (g.carrier). !n.
       group_exp g x n =
       if n = 0 then g.id
       else
         let x' = g.mult x x in
         let n' = n DIV 2 in
         if EVEN n then group_exp g x' n' else g.mult x (group_exp g x' n')``,
   RW_TAC resq_ss [LET_DEF]
   ++ RW_TAC alg_ss [group_exp_def, group_mult_exp, GSYM group_exp_add]
   ++ RW_TAC alg_ss [GSYM group_exp_def]
   ++ REPEAT AP_TERM_TAC
   ++ MP_TAC (Q.SPEC `2` DIVISION)
   ++ SIMP_TAC alg_ss [MOD_2]
   ++ DISCH_THEN (MP_TAC o Q.SPEC `n`)
   ++ RW_TAC std_ss []
   ++ DECIDE_TAC);

(* ------------------------------------------------------------------------- *)
(* Homomorphisms, isomorphisms, endomorphisms, automorphisms and subgroups.  *)
(* ------------------------------------------------------------------------- *)

val GroupHom_def = Define
  `GroupHom g h =
   { f |
     (!x :: (g.carrier). f x IN h.carrier) /\
     (f (g.id) = h.id) /\
     (!x :: (g.carrier). f (g.inv x) = h.inv (f x)) /\
     (!x y :: (g.carrier). f (g.mult x y) = h.mult (f x) (f y)) }`;

val GroupIso_def = Define
  `GroupIso g h =
   { f |
     f IN GroupHom g h /\
     (!y :: (h.carrier). ?!x :: (g.carrier). f x = y) }`;

val GroupEndo_def = Define `GroupEndo g = GroupHom g g`;

val GroupAuto_def = Define `GroupAuto g = GroupIso g g`;

val subgroup_def = Define `subgroup g h = I IN GroupHom g h`;

(* ------------------------------------------------------------------------- *)
(* The trivial group.                                                        *)
(* ------------------------------------------------------------------------- *)

val trivial_group_def = Define
  `trivial_group e : 'a group =
   <| carrier := {e}; id := e; inv := (\x. e); mult := (\x y. e) |>`;

val trivial_group = store_thm
  ("trivial_group",
   ``!e. trivial_group e IN FiniteAbelianGroup``,
   RW_TAC resq_ss
     [FiniteAbelianGroup_def, GSPECIFICATION, FiniteGroup_def, Group_def,
      AbelianGroup_def, trivial_group_def, FINITE_INSERT, FINITE_EMPTY,
      IN_INSERT, NOT_IN_EMPTY, combinTheory.K_THM]);

val context = subtypeTools.add_reduction2 trivial_group context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

(* ------------------------------------------------------------------------- *)
(* The cyclic group.                                                         *)
(* ------------------------------------------------------------------------- *)

val cyclic_group_def = Define
  `cyclic_group e f : 'a group =
   <| carrier := { x | ?n. FUNPOW f n e = x };
      id := e;
      inv := (\x. @y. ?yi. !xi.
                (FUNPOW f yi e = y) /\
                ((FUNPOW f xi e = x) ==> (FUNPOW f (xi + yi) e = e)));
      mult := (\x y. @z. !xi yi.
                (FUNPOW f xi e = x) /\ (FUNPOW f yi e = y) ==>
                (FUNPOW f (xi + yi) e = z)) |>`;

val cyclic_group_alt = store_thm
  ("cyclic_group_alt",
   ``!e f n.
       (?k. ~(k = 0) /\ (FUNPOW f k e = e)) /\
       (n = LEAST k. ~(k = 0) /\ (FUNPOW f k e = e)) ==>
       ((cyclic_group e f).carrier = { FUNPOW f k e | k < n }) /\
       ((cyclic_group e f).id = e) /\
       (!i.
          (cyclic_group e f).inv (FUNPOW f i e) =
          FUNPOW f ((n - i MOD n) MOD n) e) /\
       (!i j.
          (cyclic_group e f).mult (FUNPOW f i e) (FUNPOW f j e) =
          FUNPOW f ((i + j) MOD n) e)``,
   REPEAT GEN_TAC
   ++ SIMP_TAC std_ss [whileTheory.LEAST_EXISTS]
   ++ Q.SPEC_TAC (`LEAST k. ~(k = 0) /\ (FUNPOW f k e = e)`,`k`)
   ++ GEN_TAC
   ++ STRIP_TAC
   ++ Know `0 < k` >> DECIDE_TAC
   ++ STRIP_TAC
   ++ Know `!p q. (FUNPOW f p e = FUNPOW f q e) = (p MOD k = q MOD k)`
   >> (REPEAT STRIP_TAC
       ++ MP_TAC (Q.SPEC `k` DIVISION)
       ++ ASM_SIMP_TAC std_ss []
       ++ DISCH_THEN (fn th => MP_TAC (Q.SPEC `p` th) ++ MP_TAC (Q.SPEC `q` th))
       ++ DISCH_THEN (fn th1 => DISCH_THEN (fn th2 =>
            CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th1,th2]))))
       ++ ONCE_REWRITE_TAC [ONCE_REWRITE_RULE [ADD_COMM] FUNPOW_ADD]
       ++ ONCE_REWRITE_TAC [ONCE_REWRITE_RULE [MULT_COMM] FUNPOW_MULT]
       ++ Know `!n. FUNPOW (\x. FUNPOW f k x) n e = e`
       >> (Induct ++ RW_TAC std_ss [FUNPOW])
       ++ DISCH_THEN (fn th => RW_TAC std_ss [th])
       ++ REVERSE EQ_TAC >> RW_TAC std_ss []
       ++ STRIP_TAC
       ++ Know `!m n : num. ~(m < n) /\ ~(n < m) ==> (m = n)` >> DECIDE_TAC
       ++ DISCH_THEN MATCH_MP_TAC
       ++ POP_ASSUM MP_TAC
       ++ MATCH_MP_TAC
           (PROVE []
            ``((a = b) ==> ~c) /\ ((b = a) ==> ~d) ==> ((a = b) ==> ~c /\ ~d)``)
       ++ Q.SPEC_TAC (`q`,`q`)
       ++ Q.SPEC_TAC (`p`,`p`)
       ++ SIMP_TAC std_ss [FORALL_AND_THM]
       ++ MATCH_MP_TAC (PROVE [] ``(a ==> b) /\ a ==> a /\ b``)
       ++ CONJ_TAC >> METIS_TAC []
       ++ RW_TAC std_ss []
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPEC `(k - q MOD k) + p MOD k`)
       ++ ASM_SIMP_TAC std_ss [FUNPOW_ADD]
       ++ SIMP_TAC std_ss [GSYM FUNPOW_ADD]
       ++ MP_TAC (Q.SPEC `k` DIVISION)
       ++ ASM_SIMP_TAC std_ss []
       ++ DISCH_THEN (MP_TAC o CONJUNCT2 o Q.SPEC `q`)
       ++ ASM_SIMP_TAC arith_ss [])
   ++ RW_TAC resq_ss
        [cyclic_group_def, combinTheory.K_THM, GSPECIFICATION, EXTENSION]
   << [REVERSE EQ_TAC >> METIS_TAC []
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `n MOD k`
       ++ METIS_TAC [DIVISION, MOD_MOD],
       normalForms.SELECT_TAC
       ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
       ++ CONJ_TAC
       >> (Q.EXISTS_TAC `FUNPOW f (k - i MOD k) e`
           ++ Q.EXISTS_TAC `k - i MOD k`
           ++ RW_TAC std_ss []
           ++ Know `e = FUNPOW f 0 e` >> RW_TAC std_ss [FUNPOW]
           ++ DISCH_THEN
                (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
           ++ RW_TAC std_ss []
           ++ MP_TAC (Q.SPEC `k` MOD_PLUS)
           ++ ASM_SIMP_TAC std_ss []
           ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
           ++ RW_TAC std_ss []
           ++ MP_TAC (Q.SPEC `k` MOD_MOD)
           ++ ASM_REWRITE_TAC []
           ++ DISCH_THEN (fn th =>
                CONV_TAC
                  (LAND_CONV
                     (LAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [GSYM th])))))
           ++ ASM_SIMP_TAC std_ss [MOD_PLUS]
           ++ Know `i MOD k < k` >> METIS_TAC [DIVISION]
           ++ RW_TAC arith_ss [])
       ++ RW_TAC std_ss []
       ++ POP_ASSUM (MP_TAC o Q.SPEC `i`)
       ++ RW_TAC std_ss []
       ++ RW_TAC std_ss []
       ++ MP_TAC (Q.SPEC `k` MOD_MOD)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN
            (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM th])))
       ++ Know `!a. a = 0 MOD k + a` >> RW_TAC arith_ss [ZERO_MOD]
       ++ DISCH_THEN
            (fn th =>
               CONV_TAC (RAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [th]))))
       ++ POP_ASSUM MP_TAC
       ++ Know `FUNPOW f 0 e = e` >> RW_TAC std_ss [FUNPOW]
       ++ DISCH_THEN
            (fn th =>
               CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))))
       ++ ASM_REWRITE_TAC []
       ++ Q.UNDISCH_TAC `0 < k`
       ++ POP_ASSUM_LIST (K ALL_TAC)
       ++ STRIP_TAC
       ++ MP_TAC (Q.SPEC `k` MOD_PLUS)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN
            (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM th])))
       ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
       ++ MP_TAC (Q.SPEC `k` MOD_MOD)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN (fn th =>
            CONV_TAC
              (RAND_CONV
                 (LAND_CONV
                    (LAND_CONV
                      (LAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [GSYM th])))))))
       ++ MP_TAC (Q.SPEC `k` MOD_PLUS)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN (fn th => CONV_TAC (ONCE_REWRITE_CONV [th]))
       ++ MP_TAC (Q.SPEC `k` MOD_PLUS)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN (fn th => CONV_TAC (ONCE_REWRITE_CONV [GSYM th]))
       ++ MP_TAC (Q.SPEC `k` MOD_MOD)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN (fn th => CONV_TAC (REWRITE_CONV [th]))
       ++ MP_TAC (Q.SPEC `k` MOD_PLUS)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN (fn th => CONV_TAC (ONCE_REWRITE_CONV [th]))
       ++ Know `i MOD k < k` >> METIS_TAC [DIVISION]
       ++ RW_TAC arith_ss []
       ++ MP_TAC (Q.SPEC `k` MOD_PLUS)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN (fn th => CONV_TAC (ONCE_REWRITE_CONV [GSYM th]))
       ++ RW_TAC arith_ss [DIVMOD_ID],
       normalForms.SELECT_TAC
       ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
       ++ CONJ_TAC
       >> (Q.EXISTS_TAC `FUNPOW f (i + j) e`
           ++ RW_TAC std_ss []
           ++ MP_TAC (Q.SPEC `k` MOD_PLUS)
           ++ ASM_REWRITE_TAC []
           ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
           ++ RW_TAC std_ss [])
       ++ RW_TAC std_ss []
       ++ POP_ASSUM (MP_TAC o Q.SPECL [`i`,`j`])
       ++ RW_TAC std_ss []
       ++ RW_TAC std_ss []
       ++ METIS_TAC [DIVISION]]);

val cyclic_group = store_thm
  ("cyclic_group",
   ``!e f.
       (?n. ~(n = 0) /\ (FUNPOW f n e = e)) ==>
       cyclic_group e f IN FiniteAbelianGroup``,
   REPEAT GEN_TAC
   ++ DISCH_THEN ASSUME_TAC
   ++ MP_TAC (Q.SPECL [`e`,`f`,`LEAST n. ~(n = 0) /\ (FUNPOW f n e = e)`]
                cyclic_group_alt)
   ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
   ++ CONJ_TAC >> (RW_TAC std_ss [] ++ METIS_TAC [])
   ++ POP_ASSUM MP_TAC
   ++ SIMP_TAC std_ss [whileTheory.LEAST_EXISTS]
   ++ Q.SPEC_TAC (`LEAST n. ~(n = 0) /\ (FUNPOW f n e = e)`,`k`)
   ++ REPEAT GEN_TAC
   ++ STRIP_TAC
   ++ Know `0 < k` >> DECIDE_TAC
   ++ STRIP_TAC
   ++ (RW_TAC resq_ss [FiniteAbelianGroup_alt, Group_def, GSPECIFICATION]
       ++ RW_TAC std_ss [])
   << [Q.EXISTS_TAC `0`
       ++ RW_TAC arith_ss [FUNPOW],
       METIS_TAC [DIVISION],
       Q.EXISTS_TAC `(k - k' MOD k) MOD k`
       ++ RW_TAC arith_ss [FUNPOW]
       ++ METIS_TAC [DIVISION],
       Know `FUNPOW f 0 e = e` >> RW_TAC std_ss [FUNPOW]
       ++ DISCH_THEN (fn th =>
            CONV_TAC (LAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [GSYM th]))))
       ++ RW_TAC std_ss []
       ++ RW_TAC arith_ss [],
       Suff `((k - k' MOD k) MOD k + k') MOD k = 0 MOD k`
       >> RW_TAC std_ss [ZERO_MOD, FUNPOW]
       ++ MP_TAC (Q.SPEC `k` MOD_PLUS)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN
            (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM th]
                                           THENC ONCE_REWRITE_CONV [GSYM th])))
       ++ MP_TAC (Q.SPEC `k` MOD_MOD)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN (fn th =>
            CONV_TAC (LAND_CONV (LAND_CONV (LAND_CONV (REWRITE_CONV [th])))))
       ++ MP_TAC (Q.SPEC `k` MOD_PLUS)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN (fn th => CONV_TAC (ONCE_REWRITE_CONV [th]))
       ++ Know `k' MOD k < k` >> METIS_TAC [DIVISION]
       ++ RW_TAC arith_ss [],
       AP_THM_TAC
       ++ AP_TERM_TAC
       ++ MP_TAC (Q.SPEC `k` MOD_PLUS)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN
            (fn th => CONV_TAC (BINOP_CONV
                        (LAND_CONV (ONCE_REWRITE_CONV [GSYM th])
                         THENC ONCE_REWRITE_CONV [GSYM th])))
       ++ MP_TAC (Q.SPEC `k` MOD_MOD)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN (fn th =>
            CONV_TAC
              (LAND_CONV (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [GSYM th])))
               THENC
               RAND_CONV (LAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [GSYM th])))))
       ++ MP_TAC (Q.SPEC `k` MOD_PLUS)
       ++ ASM_REWRITE_TAC []
       ++ METIS_TAC [ADD_ASSOC],
       METIS_TAC [ADD_COMM],
       Know `{FUNPOW f k' e | k' < k} =
             IMAGE (\k'. FUNPOW f k' e) {k' | k' < k}`
       >> RW_TAC std_ss [IMAGE_DEF, GSPECIFICATION]
       ++ RW_TAC std_ss []
       ++ MATCH_MP_TAC IMAGE_FINITE
       ++ RW_TAC std_ss [finite_num]
       ++ Q.EXISTS_TAC `k`
       ++ RW_TAC std_ss [GSPECIFICATION]]);

(* ------------------------------------------------------------------------- *)
(* The group of addition modulo n.                                           *)
(* ------------------------------------------------------------------------- *)

val Nonzero_def = Define `Nonzero = { n | ~(n = 0) }`;

val add_mod_def = Define
  `add_mod n =
   <| carrier := { i | i < n };
      id := 0;
      inv := (\i. (n - i) MOD n);
      mult := (\i j. (i + j) MOD n) |>`;

val group_add_mod = store_thm
  ("group_add_mod",
   ``!n :: Nonzero. add_mod n IN Group``,
   RW_TAC resq_ss
     [Group_def,GSPECIFICATION,add_mod_def,combinTheory.K_THM,Nonzero_def]
   ++ Know `0 < n /\ !m. m < n = (m MOD n = m)` >> RW_TAC arith_ss []
   ++ RW_TAC bool_ss [ZERO_MOD, MOD_MOD, ADD_CLAUSES]
   << [METIS_TAC [],
       Suff `((n - x) MOD n + x MOD n) MOD n = 0`
       >> METIS_TAC []
       ++ MP_TAC (Q.SPEC `n` MOD_PLUS)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN (fn th => REWRITE_TAC [th])
       ++ POP_ASSUM (K ALL_TAC)
       ++ RW_TAC arith_ss [],
       Suff `((x + y) MOD n + z MOD n) MOD n = (x MOD n + (y + z) MOD n) MOD n`
       >> METIS_TAC []
       ++ MP_TAC (Q.SPEC `n` MOD_PLUS)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN (fn th => REWRITE_TAC [th])
       ++ POP_ASSUM (K ALL_TAC)
       ++ RW_TAC arith_ss []]);

val add_mod = store_thm
  ("add_mod",
   ``!n :: Nonzero. add_mod n IN FiniteAbelianGroup``,
   RW_TAC resq_ss
     [group_add_mod,FiniteAbelianGroup_def,AbelianGroup_def,
      GSPECIFICATION,combinTheory.K_THM,FiniteGroup_def,Nonzero_def]
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC arith_ss [add_mod_def, finite_num, GSPECIFICATION]
   ++ METIS_TAC []);

val context = subtypeTools.add_reduction2 add_mod context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

(* ------------------------------------------------------------------------- *)
(* The group of multiplication modulo p.                                     *)
(* ------------------------------------------------------------------------- *)

val Prime_def = Define `Prime = { n | prime n }`;

val mult_mod_def = Define
  `mult_mod p =
   <| carrier := { i | ~(i = 0) /\ i < p };
      id := 1;
      inv := (\i. i ** (p - 2) MOD p);
      mult := (\i j. (i * j) MOD p) |>`;

val Prime_Nonzero = store_thm
  ("Prime_Nonzero",
   ``!p. p IN Prime ==> p IN Nonzero``,
   RW_TAC std_ss [Prime_def, Nonzero_def, GSPECIFICATION]
   ++ METIS_TAC [NOT_PRIME_0]);

val context = subtypeTools.add_judgement2 Prime_Nonzero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val group_mult_mod = store_thm
  ("group_mult_mod",
   ``!p :: Prime. mult_mod p IN Group``,
   RW_TAC resq_ss
     [Group_def,GSPECIFICATION,mult_mod_def,combinTheory.K_THM,Prime_def]
   ++ RW_TAC arith_ss [prime_one_lt]
   ++ Cases_on `p = 0` >> METIS_TAC [NOT_PRIME_0]
   ++ Know `0 < p` >> DECIDE_TAC ++ STRIP_TAC
   ++ RW_TAC std_ss [DIVISION, GSYM primalityTheory.divides_mod_zero]
   << [STRIP_TAC
       ++ MP_TAC (Q.SPECL [`p`,`x`,`y`] P_EUCLIDES)
       ++ RW_TAC std_ss []
       ++ Know `0 < x` >> DECIDE_TAC ++ STRIP_TAC
       ++ Know `0 < y` >> DECIDE_TAC ++ STRIP_TAC
       ++ METIS_TAC [DIVIDES_LE, NOT_LESS],
       Know `0 < x` >> DECIDE_TAC ++ STRIP_TAC
       ++ Q.SPEC_TAC (`p - 2`, `k`)
       ++ Induct
       >> (RW_TAC std_ss [EXP]
           ++ STRIP_TAC
           ++ Know `p <= 1` >> METIS_TAC [DIVIDES_LE, DECIDE ``0 < 1``]
           ++ METIS_TAC [NOT_LESS, prime_one_lt])
       ++ RW_TAC std_ss [EXP]
       ++ STRIP_TAC
       ++ MP_TAC (Q.SPECL [`p`,`x`,` x ** k`] P_EUCLIDES)
       ++ RW_TAC std_ss []
       ++ STRIP_TAC
       ++ Know `p <= x` >> METIS_TAC [DIVIDES_LE]
       ++ METIS_TAC [NOT_LESS],
       MP_TAC (Q.SPEC `p` MOD_TIMES2)
       ++ ASM_REWRITE_TAC []
       ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
       ++ RW_TAC bool_ss [MOD_MOD]
       ++ RW_TAC bool_ss [MOD_TIMES2]
       ++ REWRITE_TAC [GSYM EXP]
       ++ Know `SUC (p - 2) = p - 1`
       >> (Suff `1 <= p` >> DECIDE_TAC
           ++ DECIDE_TAC)
       ++ DISCH_THEN (fn th => REWRITE_TAC [th])
       ++ RW_TAC std_ss [EXP]
       ++ Suff `~divides p x` >> METIS_TAC [fermat_little]
       ++ METIS_TAC
            [DIVIDES_LE, DECIDE ``~(x : num = 0) = 0 < x``,
             DECIDE ``~(a : num < b) = b <= a``],
       MP_TAC (Q.SPEC `p` MOD_MOD)
       ++ MP_TAC (Q.SPEC `p` MOD_TIMES2)
       ++ ASM_REWRITE_TAC []
       ++ POP_ASSUM_LIST (K ALL_TAC)
       ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th] ++ ASSUME_TAC th)
       ++ DISCH_THEN (fn th => REWRITE_TAC [th])
       ++ ASM_REWRITE_TAC []
       ++ METIS_TAC [MULT_ASSOC, MULT_COMM]]);

val mult_mod = store_thm
  ("mult_mod",
   ``!p :: Prime. mult_mod p IN FiniteAbelianGroup``,
   RW_TAC resq_ss
     [group_mult_mod,FiniteAbelianGroup_def,AbelianGroup_def,
      GSPECIFICATION,combinTheory.K_THM,FiniteGroup_def,Nonzero_def]
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC arith_ss [mult_mod_def, finite_num, GSPECIFICATION]
   ++ METIS_TAC [MULT_COMM]);

val context = subtypeTools.add_reduction2 mult_mod context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

(* ========================================================================= *)
(* Cryptography based on groups                                              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* ElGamal encryption                                                        *)
(* ------------------------------------------------------------------------- *)

val elgamal_encrypt_def = Define
  `elgamal_encrypt G g h m k =
   (group_exp G g k, G.mult (group_exp G h k) m)`;

val elgamal_decrypt_def = Define
  `elgamal_decrypt G x (a,b) = G.mult (G.inv (group_exp G a x)) b`;

val elgamal_correctness = store_thm
  ("elgamal_correctness",
   ``!G :: Group. !g h m :: (G.carrier). !k x.
       (h = group_exp G g x) ==>
       (elgamal_decrypt G x (elgamal_encrypt G g h m k) = m)``,
   RW_TAC resq_ss [elgamal_encrypt_def, elgamal_decrypt_def]
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC
      `G.mult (G.mult (G.inv (group_exp G (group_exp G g k) x))
                 (group_exp G (group_exp G g x) k)) m`
   ++ CONJ_TAC
   >> RW_TAC alg_ss' []
   ++ RW_TAC alg_ss [GSYM group_exp_mult]
   ++ MP_TAC (Q.SPECL [`x`,`k`] MULT_COMM)
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   ++ RW_TAC alg_ss []);

val () = export_theory ();
