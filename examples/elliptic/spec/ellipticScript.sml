(* ========================================================================= *)
(* Create "ellipticTheory" setting up the theory of elliptic curves          *)
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
open primalityTools subtypeTools;

(*
val () = quietdec := false;
*)
fun installPP _ = ();

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "elliptic".                                     *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "elliptic";

val ERR = mk_HOL_ERR "elliptic";
val Bug = mlibUseful.Bug;
val Error = ERR "";

val Bug = fn s => (print ("\n\nBUG: " ^ s ^ "\n\n"); Bug s);

(* ------------------------------------------------------------------------- *)
(* Sort out the parser.                                                      *)
(* ------------------------------------------------------------------------- *)

val () = Parse.add_infix ("/", 600, HOLgrammars.LEFT);

(* ------------------------------------------------------------------------- *)
(* Show oracle tags.                                                         *)
(* ------------------------------------------------------------------------- *)

val () = show_tags := true;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun poly_eval [] x = 0.0
  | poly_eval (c :: cs) x = c + x * poly_eval cs x;

fun poly_diff p =
    let
      fun f _ [] = []
        | f n (c :: cs) = Real.fromInt n * c :: f (n + 1) cs
    in
      case tl p of
        [] => [0.0]
      | l => f 1 l
    end;

val epsilon = 1e~6;

fun binary_search go_left (a,b) =
    if b - a < epsilon then a
    else
      let
        val c = (a + b) / 2.0
      in
        binary_search go_left (if go_left c then (a,c) else (c,b))
      end;

fun poly_roots p =
    case let val m = List.last p in map (fn c => c / m) p end of
      [_] => raise Fail "poly_roots: constant poly"
    | [c0,c1] => [~c0 / c1]
    | p =>
      let
        val f = poly_eval p
        fun root x = Real.== (f x, 0.0)
        fun pos x = 0.0 < f x

        fun check _ [] = []
          | check a (b :: bs) =
            (if root a then [a]
             else if root b then []
             else if pos a = pos b then []
             else [binary_search (equal (pos b) o pos) (a,b)]) @ check b bs

        val turning_points = poly_roots (poly_diff p)

        val infty = foldl (fn (c,z) => z + Real.abs c) 0.0 p
      in
        check (~infty) (turning_points @ [infty])
      end;

(*
fun roots alpha =
    poly_roots [~(alpha * alpha), ~(1.0 + 2.0 * alpha), ~1.0, 1.0];
fun go_left x = length (roots x) = 3;
binary_search go_left (~10.0,0.0);
*)

(* ------------------------------------------------------------------------- *)
(* Helper proof tools.                                                       *)
(* ------------------------------------------------------------------------- *)

infixr 0 <<
infixr 1 ++ || THENC ORELSEC ORELSER ## orelse_bdd_conv
infix 2 >>

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val REVERSE = Tactical.REVERSE;
val lemma = Tactical.prove;

fun bool_compare (true,false) = LESS
  | bool_compare (false,true) = GREATER
  | bool_compare _ = EQUAL;

fun trace_conv name conv tm =
    let
      val th = conv tm
      val () = (print (name ^ ": "); print_thm th; print "\n")
    in
      th
    end
    handle e as HOL_ERR _ =>
      (print (name ^ ": "); print_term tm; print " --> HOL_ERR\n"; raise e)

fun trans_conv c th =
    let
      val (_,tm) = dest_eq (concl th)
      val th' = c tm
    in
      TRANS th th'
    end;

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

val clean_assumptions =
    let
      fun eq x y = aconv (concl x) (concl y)
    in
      POP_ASSUM_LIST (STRIP_ASSUME_TAC o LIST_CONJ o rev o op_mk_set eq)
    end;

fun flexible_solver solver cond =
    let
      val cond_th = solver cond
      val cond_tm = concl cond_th
    in
      if cond_tm = cond then cond_th
      else if cond_tm = mk_eq (cond,T) then EQT_ELIM cond_th
      else raise Bug "flexible_solver: solver didn't prove condition"
    end;

fun cond_rewr_conv rewr =
    let
      val rewr = SPEC_ALL (norm_rule rewr)
      val rewr_tm = concl rewr
      val (no_cond,eq) =
          case total dest_imp_only rewr_tm of
            NONE => (true,rewr_tm)
          | SOME (_,eq) => (false,eq)
      val pat = lhs eq
    in
      fn solver => fn tm =>
      let
        val sub = match_term pat tm
        val th = INST_TY_TERM sub rewr
      in
        if no_cond then th
        else MP th (flexible_solver solver (rand (rator (concl th))))
      end
    end;

fun cond_rewrs_conv ths =
    let
      val solver_convs = map cond_rewr_conv ths
      fun mk_conv solver solver_conv = solver_conv solver
    in
      fn solver => FIRST_CONV (map (mk_conv solver) solver_convs)
    end;

fun repeat_rule (rule : rule) th =
    repeat_rule rule (rule th) handle HOL_ERR _ => th;

fun first_rule [] _ = raise ERR "first_rule" ""
  | first_rule ((rule : rule) :: rules) th =
    rule th handle HOL_ERR _ => first_rule rules th;

val dest_in = dest_binop pred_setSyntax.in_tm (ERR "dest_in" "");

val is_in = can dest_in;

val abbrev_tm = ``Abbrev``;

fun dest_abbrev tm =
    let
      val (c,t) = dest_comb tm
      val () = if same_const c abbrev_tm then () else raise ERR "dest_abbrev" ""
    in
      dest_eq t
    end;

val is_abbrev = can dest_abbrev;

fun solver_conv_to_simpset_conv solver_conv =
    let
      val {name : string, key : term, conv : conv -> conv} = solver_conv
      val key = SOME ([] : term list, key)
      and conv = fn c => fn tms : term list => conv (c tms)
      and trace = 2
    in
      {name = name, key = key, conv = conv, trace = trace}
    end;

(* ------------------------------------------------------------------------- *)
(* Helper theorems.                                                          *)
(* ------------------------------------------------------------------------- *)

val THREE = DECIDE ``3 = SUC 2``;

val DIV_THEN_MULT = store_thm
  ("DIV_THEN_MULT",
   ``!p q. SUC q * (p DIV SUC q) <= p``,
   NTAC 2 STRIP_TAC
   ++ Know `?r. p = (p DIV SUC q) * SUC q + r`
   >> (Know `0 < SUC q` >> DECIDE_TAC
       ++ PROVE_TAC [DIVISION])
   ++ STRIP_TAC
   ++ Suff `p = SUC q * (p DIV SUC q) + r`
   >> (POP_ASSUM_LIST (K ALL_TAC) ++ DECIDE_TAC)
   ++ PROVE_TAC [MULT_COMM]);

val MOD_EXP = store_thm
  ("MOD_EXP",
   ``!a n m. 0 < m ==> (((a MOD m) ** n) MOD m = (a ** n) MOD m)``,
   RW_TAC std_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [EXP]
   ++ MP_TAC (Q.SPEC `m` MOD_TIMES2)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ ASM_SIMP_TAC std_ss [MOD_MOD]);

val MULT_EXP = store_thm
  ("MULT_EXP",
   ``!a b n. (a * b) ** n = (a ** n) * (b ** n)``,
   RW_TAC std_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [EXP, EQ_MULT_LCANCEL, GSYM MULT_ASSOC]
   ++ RW_TAC std_ss
        [EXP, ONCE_REWRITE_RULE [MULT_COMM] EQ_MULT_LCANCEL, MULT_ASSOC]
   ++ METIS_TAC [MULT_COMM]);

val EXP_EXP = store_thm
  ("EXP_EXP",
   ``!a b c. (a ** b) ** c = a ** (b * c)``,
   RW_TAC std_ss []
   ++ Induct_on `b`
   ++ RW_TAC std_ss [EXP, MULT, EXP_1]
   ++ RW_TAC std_ss [MULT_EXP, EXP_ADD]
   ++ METIS_TAC [MULT_COMM]);

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

val EL_ETA = store_thm
  ("EL_ETA",
   ``!l1 l2.
       (LENGTH l1 = LENGTH l2) /\ (!n. n < LENGTH l1 ==> (EL n l1 = EL n l2)) =
       (l1 = l2)``,
   Induct
   >> (Cases ++ RW_TAC arith_ss [LENGTH])
   ++ STRIP_TAC
   ++ Cases
   ++ RW_TAC arith_ss [LENGTH]
   ++ REVERSE (Cases_on `h = h'`)
   >> (RW_TAC std_ss []
       ++ DISJ2_TAC
       ++ Q.EXISTS_TAC `0`
       ++ RW_TAC arith_ss [EL, HD])
   ++ RW_TAC arith_ss []
   ++ Q.PAT_ASSUM `!x. P x` (fn th => REWRITE_TAC [GSYM th])
   ++ EQ_TAC
   >> (RW_TAC std_ss []
       ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `SUC n`)
       ++ RW_TAC arith_ss [EL, TL])
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `n < SUC X` MP_TAC
   ++ Cases_on `n`
   ++ RW_TAC arith_ss [EL, HD, TL]);

val el_append = store_thm
  ("el_append",
   ``!n p q.
       n < LENGTH p + LENGTH q ==>
       (EL n (APPEND p q) =
        if n < LENGTH p then EL n p else EL (n - LENGTH p) q)``,
   Induct
   ++ Cases
   ++ RW_TAC arith_ss [EL, HD, TL, APPEND, LENGTH]);

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

val alg_context = alg_add_judgement AbelianGroup_Group alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val FiniteGroup_Group = store_thm
  ("FiniteGroup_Group",
   ``!g. g IN FiniteGroup ==> g IN Group``,
   RW_TAC std_ss [FiniteGroup_def, GSPECIFICATION]);

val alg_context = alg_add_judgement FiniteGroup_Group alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val FiniteAbelianGroup_FiniteGroup = store_thm
  ("FiniteAbelianGroup_FiniteGroup",
   ``!g. g IN FiniteAbelianGroup ==> g IN FiniteGroup``,
   RW_TAC std_ss [FiniteAbelianGroup_def, GSPECIFICATION]);

val alg_context = alg_add_judgement FiniteAbelianGroup_FiniteGroup alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val FiniteAbelianGroup_AbelianGroup = store_thm
  ("FiniteAbelianGroup_AbelianGroup",
   ``!g. g IN FiniteAbelianGroup ==> g IN AbelianGroup``,
   RW_TAC std_ss [FiniteAbelianGroup_def, GSPECIFICATION]);

val alg_context =
    alg_add_judgement FiniteAbelianGroup_AbelianGroup alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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

val alg_context = alg_add_reduction group_id_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val group_inv_carrier = store_thm
  ("group_inv_carrier",
   ``!g :: Group. !x :: (g.carrier). g.inv x IN g.carrier``,
   RW_TAC resq_ss [Group_def, GSPECIFICATION]);

val alg_context = alg_add_reduction group_inv_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val group_mult_carrier = store_thm
  ("group_mult_carrier",
   ``!g :: Group. !x y :: (g.carrier). g.mult x y IN g.carrier``,
   RW_TAC resq_ss [Group_def, GSPECIFICATION]);

val alg_context = alg_add_reduction group_mult_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val group_lid = store_thm
  ("group_lid",
   ``!g :: Group. !x :: (g.carrier). g.mult g.id x = x``,
   RW_TAC resq_ss [Group_def, GSPECIFICATION]);

val alg_context = alg_add_rewrite group_lid alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val group_linv = store_thm
  ("group_linv",
   ``!g :: Group. !x :: (g.carrier). g.mult (g.inv x) x = g.id``,
   RW_TAC resq_ss [Group_def, GSPECIFICATION]);

val alg_context = alg_add_rewrite group_linv alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val group_assoc = store_thm
  ("group_assoc",
   ``!g :: Group. !x y z :: (g.carrier).
       g.mult (g.mult x y) z = g.mult x (g.mult y z)``,
   RW_TAC resq_ss [Group_def, GSPECIFICATION]);

val alg_context = alg_add_rewrite'' group_assoc alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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

val alg_context = alg_add_rewrite group_rinv alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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

val alg_context = alg_add_rewrite group_rid alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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

val alg_context = alg_add_rewrite' group_lcancel alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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

val alg_context = alg_add_rewrite' group_lcancel_id alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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

val alg_context = alg_add_rewrite' group_rcancel alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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

val alg_context = alg_add_rewrite' group_rcancel_id alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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

val alg_context = alg_add_rewrite' group_inv_cancel alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val group_inv_inv = store_thm
  ("group_inv_inv",
   ``!g :: Group. !x :: (g.carrier). g.inv (g.inv x) = x``,
   RW_TAC resq_ss []
   ++ match_tac group_lcancel_imp
   ++ Q.EXISTS_TAC `g`
   ++ Q.EXISTS_TAC `g.inv x`
   ++ RW_TAC std_ss [group_inv_carrier]
   ++ METIS_TAC [group_inv_carrier, group_linv, group_rinv]);

val alg_context = alg_add_rewrite group_inv_inv alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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

val alg_context = alg_add_rewrite group_inv_id alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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

val alg_context = alg_add_rewrite'' group_inv_mult alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val group_exp_carrier = store_thm
  ("group_exp_carrier",
   ``!g :: Group. !x :: (g.carrier). !n. group_exp g x n IN g.carrier``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [group_exp_def]
   ++ METIS_TAC [group_id_carrier, group_mult_carrier]);

val alg_context = alg_add_reduction group_exp_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val group_id_exp = store_thm
  ("group_id_exp",
   ``!g :: Group. !n. group_exp g g.id n = g.id``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [group_exp_def, group_lid, group_id_carrier]);

val alg_context = alg_add_rewrite group_id_exp alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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
     conv = alg_binop_ac_conv
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

val alg_context = alg_add_conversion'' group_ac_conv alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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

val alg_context = alg_add_reduction trivial_group alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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

val alg_context = alg_add_reduction add_mod alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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

val alg_context = alg_add_judgement Prime_Nonzero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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

val alg_context = alg_add_reduction mult_mod alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

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

(* ========================================================================= *)
(* Fields                                                                    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The basic definitions                                                     *)
(* ------------------------------------------------------------------------- *)

val () = Hol_datatype
  `field = <| carrier : 'a -> bool;
              sum : 'a group;
              prod : 'a group |>`;

val field_accessors = fetch "-" "field_accessors";

val field_zero_def = Define `field_zero (f : 'a field) = f.sum.id`;

val field_one_def = Define `field_one (f : 'a field) = f.prod.id`;

val field_neg_def = Define `field_neg (f : 'a field) = f.sum.inv`;

val field_inv_def = Define `field_inv (f : 'a field) = f.prod.inv`;

val field_add_def = Define `field_add (f : 'a field) = f.sum.mult`;

val field_sub_def = Define
  `field_sub (f : 'a field) x y = field_add f x (field_neg f y)`;

val field_mult_def = Define `field_mult (f : 'a field) = f.prod.mult`;

val field_div_def = Define
  `field_div (f : 'a field) x y = field_mult f x (field_inv f y)`;

val field_nonzero_def = Define
  `field_nonzero f = f.carrier DIFF {field_zero f}`;

val field_num_def = Define
  `(field_num (f : 'a field) 0 = field_zero f) /\
   (field_num (f : 'a field) (SUC n) =
    field_add f (field_num f n) (field_one f))`;

val field_exp_def = Define
  `(field_exp (f : 'a field) x 0 = field_one f) /\
   (field_exp (f : 'a field) x (SUC n) = field_mult f x (field_exp f x n))`;

val Field_def = Define
  `Field =
   { (f : 'a field) |
     f.sum IN AbelianGroup /\
     f.prod IN AbelianGroup /\
     (f.sum.carrier = f.carrier) /\
     (f.prod.carrier = field_nonzero f) /\
     (!x :: (f.carrier). field_mult f (field_zero f) x = field_zero f) /\
     (!x y z :: (f.carrier).
        field_mult f x (field_add f y z) =
        field_add f (field_mult f x y) (field_mult f x z)) }`;

val FiniteField_def = Define
  `FiniteField = { (f : 'a field) | f IN Field /\ FINITE f.carrier }`;

val alg_context = alg_add_rewrite'' field_sub_def alg_context;
(***val alg_context = alg_add_rewrite'' field_div_def alg_context;***)
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

(* Syntax operations *)

val field_ty_op = "field";

fun mk_field_type ty = mk_type (field_ty_op,[ty]);

fun dest_field_type ty =
    case dest_type ty of
      (ty_op,[a]) => if ty_op = field_ty_op then a
                     else raise ERR "dest_field_type" ""
    | _ => raise ERR "dest_field_type" "";

val is_field_type = can dest_field_type;

val field_zero_tm = ``field_zero : 'a field -> 'a``;

fun mk_field_zero f =
    let
      val ty = dest_field_type (type_of f)
      val zero_tm = inst [{redex = alpha, residue = ty}] field_zero_tm
    in
      mk_comb (zero_tm,f)
    end;

fun dest_field_zero tm =
    let
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_zero_tm orelse raise ERR "dest_field_zero" ""
    in
      f
    end;

val is_field_zero = can dest_field_zero;

val field_one_tm = ``field_one : 'a field -> 'a``;

fun mk_field_one f =
    let
      val ty = dest_field_type (type_of f)
      val one_tm = inst [{redex = alpha, residue = ty}] field_one_tm
    in
      mk_comb (one_tm,f)
    end;

fun dest_field_one tm =
    let
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_one_tm orelse raise ERR "dest_field_one" ""
    in
      f
    end;

val is_field_one = can dest_field_one;

val field_num_tm = ``field_num : 'a field -> num -> 'a``;

fun mk_field_num (f,n) =
    let
      val ty = dest_field_type (type_of f)
      val num_tm = inst [{redex = alpha, residue = ty}] field_num_tm
    in
      list_mk_comb (num_tm,[f,n])
    end;

fun dest_field_num tm =
    let
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_num_tm orelse raise ERR "dest_field_num" ""
    in
      (f,x)
    end;

val is_field_num = can dest_field_num;

val field_neg_tm = ``field_neg : 'a field -> 'a -> 'a``;

fun mk_field_neg (f,x) =
    let
      val ty = dest_field_type (type_of f)
      val neg_tm = inst [{redex = alpha, residue = ty}] field_neg_tm
    in
      list_mk_comb (neg_tm,[f,x])
    end;

fun dest_field_neg tm =
    let
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_neg_tm orelse raise ERR "dest_field_neg" ""
    in
      (f,x)
    end;

val is_field_neg = can dest_field_neg;

val field_add_tm = ``field_add : 'a field -> 'a -> 'a -> 'a``;

fun mk_field_add (f,x,y) =
    let
      val ty = dest_field_type (type_of f)
      val add_tm = inst [{redex = alpha, residue = ty}] field_add_tm
    in
      list_mk_comb (add_tm,[f,x,y])
    end;

fun dest_field_add tm =
    let
      val (tm,y) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_add_tm orelse raise ERR "dest_field_add" ""
    in
      (f,x,y)
    end;

val is_field_add = can dest_field_add;

val field_sub_tm = ``field_sub : 'a field -> 'a -> 'a -> 'a``;

fun mk_field_sub (f,x,y) =
    let
      val ty = dest_field_type (type_of f)
      val sub_tm = inst [{redex = alpha, residue = ty}] field_sub_tm
    in
      list_mk_comb (sub_tm,[f,x,y])
    end;

fun dest_field_sub tm =
    let
      val (tm,y) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_sub_tm orelse raise ERR "dest_field_sub" ""
    in
      (f,x,y)
    end;

val is_field_sub = can dest_field_sub;

val field_inv_tm = ``field_inv : 'a field -> 'a -> 'a``;

fun mk_field_inv (f,x) =
    let
      val ty = dest_field_type (type_of f)
      val inv_tm = inst [{redex = alpha, residue = ty}] field_inv_tm
    in
      list_mk_comb (inv_tm,[f,x])
    end;

fun dest_field_inv tm =
    let
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_inv_tm orelse raise ERR "dest_field_inv" ""
    in
      (f,x)
    end;

val is_field_inv = can dest_field_inv;

val field_mult_tm = ``field_mult : 'a field -> 'a -> 'a -> 'a``;

fun mk_field_mult (f,x,y) =
    let
      val ty = dest_field_type (type_of f)
      val mult_tm = inst [{redex = alpha, residue = ty}] field_mult_tm
    in
      list_mk_comb (mult_tm,[f,x,y])
    end;

fun dest_field_mult tm =
    let
      val (tm,y) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_mult_tm orelse raise ERR "dest_field_mult" ""
    in
      (f,x,y)
    end;

val is_field_mult = can dest_field_mult;

val field_exp_tm = ``field_exp : 'a field -> 'a -> num -> 'a``;

fun mk_field_exp (f,x,n) =
    let
      val ty = dest_field_type (type_of f)
      val exp_tm = inst [{redex = alpha, residue = ty}] field_exp_tm
    in
      list_mk_comb (exp_tm,[f,x,n])
    end;

fun dest_field_exp tm =
    let
      val (tm,n) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_exp_tm orelse raise ERR "dest_field_exp" ""
    in
      (f,x,n)
    end;

val is_field_exp = can dest_field_exp;

val field_div_tm = ``field_div : 'a field -> 'a -> 'a -> 'a``;

fun mk_field_div (f,x,y) =
    let
      val ty = dest_field_type (type_of f)
      val div_tm = inst [{redex = alpha, residue = ty}] field_div_tm
    in
      list_mk_comb (div_tm,[f,x,y])
    end;

fun dest_field_div tm =
    let
      val (tm,y) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_div_tm orelse raise ERR "dest_field_div" ""
    in
      (f,x,y)
    end;

val is_field_div = can dest_field_div;

fun mk_field_num_mult (f,x,n) = mk_field_mult (f, mk_field_num (f,n), x);

fun dest_field_num_mult tm =
    let
      val (f,t,x) = dest_field_mult tm
      val (_,n) = dest_field_num t
    in
      (f,x,n)
    end;

val is_field_num_mult = can dest_field_num_mult;

fun field_compare (x,y) =
    case (total dest_field_num x, total dest_field_num y) of
      (NONE,NONE) => compare (x,y)
    | (SOME _, NONE) => LESS
    | (NONE, SOME _) => GREATER
    | (SOME (_,x), SOME (_,y)) => compare (x,y);

(* A pretty printer for field operations *)

val field_pretty_print = ref true;
val field_pretty_print_max_size = ref 1000;

fun field_print sys gravs d pp =
    let
      open Portable term_pp_types

      fun field_num tm =
          let
            val (_,x) = dest_field_num tm
          in
            sys gravs (d - 1) x
          end

      fun field_unop dest s prec tm =
          let
            val (_,x) = dest tm
          in
            begin_block pp INCONSISTENT 0;
            add_string pp s;
            add_break pp (1,0);
            sys (Prec (prec,s), Top, Top) (d - 1) x;
            end_block pp
          end

      fun field_binop_prec x s =
          let
            val (p,l,r) = gravs
            val b =
                (case p of Prec (y,_) => y > x | _ => false) orelse
                (case l of Prec (y,_) => y >= x | _ => false) orelse
                (case r of Prec (y,_) => y > x | _ => false)
            val p = Prec (x,s)
            and l = if b then Top else l
            and r = if b then Top else r
          in
            (b,p,l,r)
          end

      fun field_binop dest s prec tm =
          let
            val (_,x,y) = dest tm
            val (b,p,l,r) = field_binop_prec prec s
            val n = term_size tm
          in
            if n > !field_pretty_print_max_size then
              (begin_block pp INCONSISTENT 0;
               add_string pp ("<<" ^ int_to_string n ^ ">>");
               end_block pp)
            else
              (begin_block pp INCONSISTENT (if b then 1 else 0);
               if b then add_string pp "(" else ();
               sys (p,l,p) (d - 1) x;
               add_string pp (" " ^ s);
               add_break pp (1,0);
               sys (p,p,r) (d - 1) y;
               if b then add_string pp ")" else ();
               end_block pp)
          end

      fun first_printer [] _ = raise term_pp_types.UserPP_Failed
        | first_printer (p :: ps) tm =
          (p tm handle HOL_ERR _ => first_printer ps tm)
    in
      fn tm =>
      if not (!field_pretty_print) then raise term_pp_types.UserPP_Failed
      else
        first_printer
          [field_num,
           field_unop dest_field_neg "~" 900,
           field_binop dest_field_add "+" 500,
           field_binop dest_field_sub "-" 500,
           field_binop dest_field_mult "*" 600,
           field_binop dest_field_div "/" 600,
           field_binop dest_field_exp "**" 700]
          tm
    end;

val () = temp_add_user_printer ({Tyop = "", Thy = ""}, field_print);

(* Theorems *)

val FiniteField_Field = store_thm
  ("FiniteField_Field",
   ``!f. f IN FiniteField ==> f IN Field``,
   RW_TAC std_ss [FiniteField_def, GSPECIFICATION]);

val alg_context = alg_add_judgement FiniteField_Field alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_nonzero_carrier = store_thm
  ("field_nonzero_carrier",
   ``!f :: Field. !x :: field_nonzero f. x IN f.carrier``,
   RW_TAC resq_ss [field_nonzero_def, IN_DIFF]);

val alg_context = alg_add_judgement field_nonzero_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_nonzero_alt = store_thm
  ("field_nonzero_alt",
   ``!f x. x IN f.carrier /\ ~(x = field_zero f) ==> x IN field_nonzero f``,
   RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]);

val field_nonzero_eq = store_thm
  ("field_nonzero_eq",
   ``!f :: Field. !x :: (f.carrier).
       ~(x = field_zero f) = x IN field_nonzero f``,
   RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]);

val field_zero_carrier = store_thm
  ("field_zero_carrier",
   ``!f :: Field. field_zero f IN f.carrier``,
   RW_TAC resq_ss [Field_def, field_one_def, GSPECIFICATION, field_zero_def]
   ++ Q.UNDISCH_TAC `f.sum IN AbelianGroup`
   ++ RW_TAC std_ss [AbelianGroup_def, GSPECIFICATION, Group_def]);

val alg_context = alg_add_reduction field_zero_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_one_carrier = store_thm
  ("field_one_carrier",
   ``!f :: Field. field_one f IN f.carrier``,
   RW_TAC resq_ss [Field_def, field_one_def, GSPECIFICATION, field_zero_def]
   ++ Q.UNDISCH_TAC `f.prod IN AbelianGroup`
   ++ RW_TAC std_ss
        [AbelianGroup_def, GSPECIFICATION, Group_def, IN_DIFF,
         field_nonzero_def]);

val field_one_zero = store_thm
  ("field_one_zero",
   ``!f :: Field. ~(field_one f = field_zero f)``,
   RW_TAC resq_ss
     [Field_def, field_one_def, field_zero_def, GSPECIFICATION,
      AbelianGroup_def, field_nonzero_def]
   ++ Know `f.prod.id IN f.prod.carrier`
   >> METIS_TAC [group_id_carrier]
   ++ RW_TAC std_ss [IN_DIFF, IN_SING]);

val alg_context = alg_add_rewrite field_one_zero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_zero_one = store_thm
  ("field_zero_one",
   ``!f :: Field. ~(field_zero f = field_one f)``,
   RW_TAC alg_ss []);

val field_one_nonzero = store_thm
  ("field_one_nonzero",
   ``!f :: Field. field_one f IN field_nonzero f``,
   RW_TAC resq_ss
     [field_nonzero_def, IN_DIFF, IN_SING, field_one_carrier, field_one_zero]);

val alg_context = alg_add_reduction field_one_nonzero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_neg_carrier = store_thm
  ("field_neg_carrier",
   ``!f :: Field. !x :: (f.carrier). field_neg f x IN f.carrier``,
   RW_TAC resq_ss [Field_def, GSPECIFICATION, field_neg_def, AbelianGroup_def]
   ++ METIS_TAC [group_inv_carrier]);

val alg_context = alg_add_reduction field_neg_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_add_carrier = store_thm
  ("field_add_carrier",
   ``!f :: Field. !x y :: (f.carrier). field_add f x y IN f.carrier``,
   RW_TAC resq_ss [Field_def, GSPECIFICATION, field_add_def, AbelianGroup_def]
   ++ METIS_TAC [group_mult_carrier]);

val alg_context = alg_add_reduction field_add_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_add_assoc = store_thm
  ("field_add_assoc",
   ``!f :: Field. !x y z :: (f.carrier).
       field_add f (field_add f x y) z = field_add f x (field_add f y z)``,
   RW_TAC resq_ss
     [Field_def, GSPECIFICATION, field_add_def, AbelianGroup_def,
      Group_def]);

val alg_context = alg_add_rewrite'' field_add_assoc alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_add_comm = store_thm
  ("field_add_comm",
   ``!f :: Field. !x y :: (f.carrier). field_add f x y = field_add f y x``,
   RW_TAC resq_ss
     [Field_def, GSPECIFICATION, field_add_def, AbelianGroup_def]);

val field_add_comm' = store_thm
  ("field_add_comm'",
   ``!f :: Field. !x y z :: (f.carrier).
        field_add f x (field_add f y z) = field_add f y (field_add f x z)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss [GSYM field_add_assoc]
   ++ METIS_TAC [field_add_comm]);

val field_num_zero = store_thm
  ("field_num_zero",
   ``!f. field_num f 0 = field_zero f``,
   RW_TAC std_ss [field_num_def]);

val alg_context = alg_add_rewrite field_num_zero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_add_lzero = store_thm
  ("field_add_lzero",
   ``!f :: Field. !x :: (f.carrier). field_add f (field_zero f) x = x``,
   RW_TAC resq_ss
     [Field_def, GSPECIFICATION, field_add_def, field_zero_def,
      AbelianGroup_def]
   ++ match_tac group_lid
   ++ RW_TAC std_ss []);

val alg_context = alg_add_rewrite field_add_lzero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_num_one = store_thm
  ("field_num_one",
   ``!f :: Field. field_num f 1 = field_one f``,
   REWRITE_TAC [ONE, field_num_def]
   ++ RW_TAC alg_ss []);

val alg_context = alg_add_rewrite'' (GSYM field_num_one) alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_add_lzero' = store_thm
  ("field_add_lzero'",
   ``!f :: Field. !x :: (f.carrier). field_add f (field_num f 0) x = x``,
   RW_TAC alg_ss [field_num_zero]);

val alg_context = alg_add_rewrite field_add_lzero' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_add_rzero = store_thm
  ("field_add_rzero",
   ``!f :: Field. !x :: (f.carrier). field_add f x (field_zero f) = x``,
   METIS_TAC [field_add_lzero, field_add_comm, field_zero_carrier]);

val alg_context = alg_add_rewrite field_add_rzero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_add_rzero' = store_thm
  ("field_add_rzero'",
   ``!f :: Field. !x :: (f.carrier). field_add f x (field_num f 0) = x``,
   RW_TAC alg_ss [field_num_zero]);

val alg_context = alg_add_rewrite field_add_rzero' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_lneg = store_thm
  ("field_lneg",
   ``!f :: Field. !x :: (f.carrier).
       (field_add f (field_neg f x) x = field_zero f)``,
   RW_TAC resq_ss
     [Field_def, GSPECIFICATION, field_add_def, field_zero_def,
      AbelianGroup_def, field_neg_def]
   ++ match_tac group_linv
   ++ RW_TAC std_ss [IN_DIFF, IN_SING]);

val alg_context = alg_add_rewrite field_lneg alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_lneg' = store_thm
  ("field_lneg'",
   ``!f :: Field. !x y :: (f.carrier).
       (field_add f (field_neg f x) (field_add f x y) = y)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss [GSYM field_add_assoc]);

val alg_context = alg_add_rewrite field_lneg' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_rneg = store_thm
  ("field_rneg",
   ``!f :: Field. !x :: (f.carrier).
       (field_add f x (field_neg f x) = field_zero f)``,
   METIS_TAC [field_lneg, field_add_comm, field_neg_carrier]);

val alg_context = alg_add_rewrite field_rneg alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_rneg' = store_thm
  ("field_rneg'",
   ``!f :: Field. !x y :: (f.carrier).
       (field_add f x (field_add f (field_neg f x) y) = y)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss [GSYM field_add_assoc]);

val alg_context = alg_add_rewrite field_rneg' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_add_lcancel_imp = store_thm
  ("field_add_lcancel_imp",
   ``!f :: Field. !x y z :: (f.carrier).
       (field_add f x y = field_add f x z) ==> (y = z)``,
   RW_TAC resq_ss [Field_def, GSPECIFICATION, AbelianGroup_def, field_add_def]
   ++ match_tac group_lcancel_imp
   ++ Q.EXISTS_TAC `f.sum`
   ++ Q.EXISTS_TAC `x`
   ++ RW_TAC std_ss []);

val field_add_lcancel = store_thm
  ("field_add_lcancel",
   ``!f :: Field. !x y z :: (f.carrier).
       (field_add f x y = field_add f x z) = (y = z)``,
   METIS_TAC [field_add_lcancel_imp]);

val alg_context = alg_add_rewrite' field_add_lcancel alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_add_rcancel_imp = store_thm
  ("field_add_rcancel_imp",
   ``!f :: Field. !x y z :: (f.carrier).
       (field_add f y x = field_add f z x) ==> (y = z)``,
   METIS_TAC [field_add_lcancel_imp, field_add_comm]);

val field_add_rcancel = store_thm
  ("field_add_rcancel",
   ``!f :: Field. !x y z :: (f.carrier).
       (field_add f y x = field_add f z x) = (y = z)``,
   METIS_TAC [field_add_rcancel_imp]);

val alg_context = alg_add_rewrite' field_add_rcancel alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_inv_nonzero = store_thm
  ("field_inv_nonzero",
   ``!f :: Field. !x :: field_nonzero f. field_inv f x IN field_nonzero f``,
   RW_TAC resq_ss [Field_def, GSPECIFICATION, field_nonzero_def]
   ++ Suff `field_inv f x IN f.prod.carrier`
   >> RW_TAC std_ss []
   ++ Know `x IN f.prod.carrier`
   >> RW_TAC std_ss [IN_DIFF, IN_INSERT, NOT_IN_EMPTY]
   ++ Q.UNDISCH_TAC `f.prod IN AbelianGroup`
   ++ POP_ASSUM_LIST (K ALL_TAC)
   ++ RW_TAC std_ss
        [AbelianGroup_def, GSPECIFICATION, Group_def, field_inv_def]);

val alg_context = alg_add_reduction field_inv_nonzero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_lzero = store_thm
  ("field_mult_lzero",
   ``!f :: Field. !x :: (f.carrier).
       field_mult f (field_zero f) x = field_zero f``,
   RW_TAC resq_ss [Field_def, GSPECIFICATION]);

val alg_context = alg_add_rewrite field_mult_lzero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_lzero' = store_thm
  ("field_mult_lzero'",
   ``!f :: Field. !x :: (f.carrier).
       field_mult f (field_num f 0) x = field_zero f``,
   RW_TAC alg_ss [field_num_zero]);

val alg_context = alg_add_rewrite field_mult_lzero' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_distrib_ladd = store_thm
  ("field_distrib_ladd",
   ``!f :: Field. !x y z :: (f.carrier).
       field_mult f x (field_add f y z) =
       field_add f (field_mult f x y) (field_mult f x z)``,
   RW_TAC resq_ss [Field_def, GSPECIFICATION]);

(***
val alg_context = alg_add_rewrite'' field_distrib_ladd alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;
***)

val field_mult_rzero = store_thm
  ("field_mult_rzero",
   ``!f :: Field. !x :: (f.carrier).
       field_mult f x (field_zero f) = field_zero f``,
   RW_TAC resq_ss []
   ++ Cases_on `x = field_zero f`
   >> METIS_TAC [field_mult_lzero]
   ++ Know `field_mult f x (field_zero f) IN f.carrier`
   >> (Suff
         `field_mult f x (field_add f (field_one f) (field_neg f (field_one f)))
          IN f.carrier`
       >> RW_TAC alg_ss [field_rneg]
       ++ RW_TAC alg_ss [field_distrib_ladd]
       ++ match_tac field_add_carrier
       ++ Q.UNDISCH_TAC `f IN Field`
       ++ RW_TAC std_ss
            [GSPECIFICATION, Field_def, AbelianGroup_def, field_one_def,
             field_mult_def, field_neg_def, field_nonzero_def]
       >> (Suff `f.prod.mult x f.prod.id IN f.prod.carrier`
           >> RW_TAC std_ss [IN_DIFF]
           ++ match_tac group_mult_carrier
           ++ RW_TAC std_ss [group_id_carrier, IN_DIFF, IN_SING])
       ++ Suff `f.prod.mult x (f.sum.inv f.prod.id) IN f.prod.carrier`
       >> RW_TAC std_ss [IN_DIFF]
       ++ Q.PAT_ASSUM `f.sum.carrier = f.carrier`
            (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ])
       ++ STRIP_TAC
       ++ match_tac group_mult_carrier
       ++ ASM_SIMP_TAC std_ss [IN_DIFF, IN_SING]
       ++ Know `f.prod.id IN f.prod.carrier`
       >> RW_TAC std_ss [group_id_carrier]
       ++ ASM_SIMP_TAC std_ss [IN_DIFF, IN_SING]
       ++ FULL_SIMP_TAC std_ss [field_zero_def]
       ++ RW_TAC std_ss []
       >> (match_tac group_inv_carrier
           ++ RW_TAC std_ss [])
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `~(X = Y)` MP_TAC
       ++ RW_TAC std_ss []
       ++ match_tac group_lcancel_imp
       ++ Q.EXISTS_TAC `f.sum`
       ++ Q.EXISTS_TAC `f.sum.inv f.prod.id`
       ++ CONJ_TAC >> METIS_TAC [group_linv, group_id_carrier]
       ++ CONJ_TAC >> METIS_TAC [group_linv, group_id_carrier]
       ++ CONJ_TAC >> METIS_TAC [group_linv, group_id_carrier]
       ++ CONJ_TAC >> METIS_TAC [group_linv, group_id_carrier]
       ++ POP_ASSUM (fn th => CONV_TAC (RAND_CONV (REWRITE_CONV [th])))
       ++ RW_TAC std_ss [group_linv, group_lid, group_id_carrier])
   ++ RW_TAC std_ss []
   ++ Suff
        `field_add f (field_mult f x (field_zero f))
                     (field_mult f x (field_zero f)) =
         field_add f (field_zero f) (field_mult f x (field_zero f))`
   >> RW_TAC alg_ss []
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC
        `field_mult f x (field_add f (field_zero f) (field_zero f))`
   ++ REVERSE CONJ_TAC
   >> RW_TAC alg_ss []
   ++ MATCH_MP_TAC EQ_SYM
   ++ match_tac field_distrib_ladd
   ++ RW_TAC alg_ss []);

val alg_context = alg_add_rewrite field_mult_rzero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_rzero' = store_thm
  ("field_mult_rzero'",
   ``!f :: Field. !x :: (f.carrier).
       field_mult f x (field_num f 0) = field_zero f``,
   RW_TAC alg_ss [field_num_zero]);

val alg_context = alg_add_rewrite field_mult_rzero' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_nonzero = store_thm
  ("field_mult_nonzero",
   ``!f :: Field. !x y :: field_nonzero f.
       field_mult f x y IN field_nonzero f``,
   RW_TAC resq_ss
     [Field_def, GSPECIFICATION, field_mult_def, AbelianGroup_def,
      field_nonzero_def]
   ++ Suff `f.prod.mult x y IN f.prod.carrier`
   >> RW_TAC std_ss []
   ++ match_tac group_mult_carrier
   ++ RW_TAC std_ss []);

val alg_context = alg_add_reduction field_mult_nonzero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_carrier = store_thm
  ("field_mult_carrier",
   ``!f :: Field. !x y :: (f.carrier). field_mult f x y IN f.carrier``,
   RW_TAC resq_ss []
   ++ Cases_on `x = field_zero f`
   >> RW_TAC std_ss [field_mult_lzero]
   ++ Cases_on `y = field_zero f`
   >> RW_TAC std_ss [field_mult_rzero]
   ++ match_tac field_nonzero_carrier
   ++ RW_TAC std_ss []
   ++ match_tac field_mult_nonzero
   ++ RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]);

val alg_context = alg_add_reduction field_mult_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_assoc = store_thm
  ("field_mult_assoc",
   ``!f :: Field. !x y z :: (f.carrier).
       field_mult f (field_mult f x y) z = field_mult f x (field_mult f y z)``,
   RW_TAC resq_ss []
   ++ Cases_on `x = field_zero f`
   >> RW_TAC std_ss [field_mult_lzero, field_mult_rzero, field_mult_carrier]
   ++ Cases_on `y = field_zero f`
   >> RW_TAC std_ss [field_mult_lzero, field_mult_rzero, field_mult_carrier]
   ++ Cases_on `z = field_zero f`
   >> RW_TAC std_ss [field_mult_lzero, field_mult_rzero, field_mult_carrier]
   ++ Q.UNDISCH_TAC `f IN Field`
   ++ RW_TAC std_ss
        [Field_def, GSPECIFICATION, field_add_def, AbelianGroup_def,
         Group_def, field_mult_def, field_nonzero_def]
   ++ FIRST_ASSUM match_tac
   ++ RW_TAC std_ss [IN_DIFF, IN_SING]);

val alg_context = alg_add_rewrite'' field_mult_assoc alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_comm = store_thm
  ("field_mult_comm",
   ``!f :: Field. !x y :: (f.carrier). field_mult f x y = field_mult f y x``,
   RW_TAC resq_ss []
   ++ Cases_on `x = field_zero f`
   >> RW_TAC std_ss [field_mult_lzero, field_mult_rzero]
   ++ Cases_on `y = field_zero f`
   >> RW_TAC std_ss [field_mult_lzero, field_mult_rzero]
   ++ Q.UNDISCH_TAC `f IN Field`
   ++ RW_TAC std_ss
        [Field_def, GSPECIFICATION, field_mult_def, AbelianGroup_def,
         field_nonzero_def]
   ++ Q.PAT_ASSUM `!x y :: (f.prod.carrier). P x y` match_tac
   ++ RW_TAC std_ss [IN_DIFF, IN_INSERT, NOT_IN_EMPTY]);

val field_mult_comm' = store_thm
  ("field_mult_comm'",
   ``!f :: Field. !x y z :: (f.carrier).
        field_mult f x (field_mult f y z) = field_mult f y (field_mult f x z)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss [GSYM field_mult_assoc]
   ++ METIS_TAC [field_mult_comm]);

val field_entire = store_thm
  ("field_entire",
   ``!f :: Field. !x y :: (f.carrier).
       (field_mult f x y = field_zero f) =
       (x = field_zero f) \/ (y = field_zero f)``,
   RW_TAC resq_ss []
   ++ REVERSE EQ_TAC
   >> (STRIP_TAC ++ RW_TAC std_ss [field_mult_lzero, field_mult_rzero])
   ++ MATCH_MP_TAC (PROVE [] ``(~b ==> ~a) ==> (a ==> b)``)
   ++ Know `field_mult f x y IN f.carrier`
   >> METIS_TAC [field_mult_carrier]
   ++ RW_TAC std_ss []
   ++ Q.UNDISCH_TAC `f IN Field`
   ++ RW_TAC std_ss
        [Field_def, GSPECIFICATION, AbelianGroup_def, field_nonzero_def]
   ++ Suff `f.prod.mult x y IN f.prod.carrier`
   >> RW_TAC std_ss [IN_DIFF, IN_INSERT, NOT_IN_EMPTY, field_mult_def]
   ++ match_tac group_mult_carrier
   ++ RW_TAC std_ss [IN_DIFF, IN_INSERT, NOT_IN_EMPTY]);

val alg_context = alg_add_rewrite' field_entire alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_lone = store_thm
  ("field_mult_lone",
   ``!f :: Field. !x :: (f.carrier). field_mult f (field_one f) x = x``,
   RW_TAC resq_ss []
   ++ Cases_on `x = field_zero f`
   >> RW_TAC std_ss [field_mult_rzero, field_one_carrier]
   ++ Q.UNDISCH_TAC `f IN Field`
   ++ RW_TAC std_ss
        [Field_def, GSPECIFICATION, field_mult_def, field_one_def,
         AbelianGroup_def, field_nonzero_def]
   ++ match_tac group_lid
   ++ RW_TAC std_ss [IN_DIFF, IN_INSERT, NOT_IN_EMPTY]);

val alg_context = alg_add_rewrite field_mult_lone alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_lone' = store_thm
  ("field_mult_lone'",
   ``!f :: Field. !x :: (f.carrier). field_mult f (field_num f 1) x = x``,
   RW_TAC alg_ss [field_num_one]);

val alg_context = alg_add_rewrite field_mult_lone' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_rone = store_thm
  ("field_mult_rone",
   ``!f :: Field. !x :: (f.carrier). field_mult f x (field_one f) = x``,
   METIS_TAC [field_mult_lone, field_mult_comm, field_one_carrier]);

val alg_context = alg_add_rewrite field_mult_rone alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_rone' = store_thm
  ("field_mult_rone'",
   ``!f :: Field. !x :: (f.carrier). field_mult f x (field_num f 1) = x``,
   RW_TAC alg_ss [field_num_one]);

val alg_context = alg_add_rewrite field_mult_rone' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_linv = store_thm
  ("field_linv",
   ``!f :: Field. !x :: field_nonzero f.
       field_mult f (field_inv f x) x = field_one f``,
   RW_TAC resq_ss
     [Field_def, GSPECIFICATION, field_mult_def, field_one_def,
      AbelianGroup_def, field_inv_def, field_nonzero_def]
   ++ match_tac group_linv
   ++ RW_TAC std_ss []);

val alg_context = alg_add_rewrite field_linv alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_linv' = store_thm
  ("field_linv'",
   ``!f :: Field. !x :: field_nonzero f. !y :: (f.carrier).
       (field_mult f (field_inv f x) (field_mult f x y) = y)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss [GSYM field_mult_assoc]);

val alg_context = alg_add_rewrite field_linv' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_rinv = store_thm
  ("field_rinv",
   ``!f :: Field. !x :: field_nonzero f.
       (field_mult f x (field_inv f x) = field_one f)``,
   METIS_TAC
     [field_linv, field_mult_comm, field_inv_nonzero, field_nonzero_carrier]);

val alg_context = alg_add_rewrite field_rinv alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_rinv' = store_thm
  ("field_rinv'",
   ``!f :: Field. !x :: field_nonzero f. !y :: (f.carrier).
       (field_mult f x (field_mult f (field_inv f x) y) = y)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss [GSYM field_mult_assoc]);

val alg_context = alg_add_rewrite field_rinv' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_lcancel_imp = store_thm
  ("field_mult_lcancel_imp",
   ``!f :: Field. !x :: field_nonzero f. !y z :: (f.carrier).
       (field_mult f x y = field_mult f x z) ==> (y = z)``,
   RW_TAC resq_ss [field_nonzero_def, IN_DIFF, IN_SING]
   ++ POP_ASSUM MP_TAC
   ++ Cases_on `y = field_zero f`
   >> RW_TAC std_ss [field_mult_rzero, field_entire]
   ++ Cases_on `z = field_zero f`
   >> RW_TAC std_ss [field_mult_rzero, field_entire]
   ++ Q.UNDISCH_TAC `f IN Field`
   ++ RW_TAC std_ss
        [field_mult_def, Field_def, GSPECIFICATION, AbelianGroup_def,
         field_nonzero_def]
   ++ match_tac group_lcancel_imp
   ++ Q.EXISTS_TAC `f.prod`
   ++ Q.EXISTS_TAC `x`
   ++ RW_TAC std_ss [IN_DIFF, IN_INSERT, NOT_IN_EMPTY]);

val field_mult_lcancel = store_thm
  ("field_mult_lcancel",
   ``!f :: Field. !x :: field_nonzero f. !y z :: (f.carrier).
       (field_mult f x y = field_mult f x z) = (y = z)``,
   METIS_TAC [field_mult_lcancel_imp]);

val alg_context = alg_add_rewrite' field_mult_lcancel alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_rcancel_imp = store_thm
  ("field_mult_rcancel_imp",
   ``!f :: Field. !x :: field_nonzero f. !y z :: (f.carrier).
       (field_mult f y x = field_mult f z x) ==> (y = z)``,
   METIS_TAC [field_mult_lcancel_imp, field_mult_comm, field_nonzero_carrier]);

val field_mult_rcancel = store_thm
  ("field_mult_rcancel",
   ``!f :: Field. !x :: field_nonzero f. !y z :: (f.carrier).
       (field_mult f y x = field_mult f z x) = (y = z)``,
   METIS_TAC [field_mult_rcancel_imp]);

val alg_context = alg_add_rewrite' field_mult_rcancel alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_neg_neg = store_thm
  ("field_neg_neg",
   ``!f :: Field. !x :: (f.carrier). field_neg f (field_neg f x) = x``,
   RW_TAC resq_ss [field_neg_def, Field_def, GSPECIFICATION, AbelianGroup_def]
   ++ METIS_TAC [group_inv_inv]);

val alg_context = alg_add_rewrite field_neg_neg alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_neg_cancel = store_thm
  ("field_neg_cancel",
   ``!f :: Field. !x y :: (f.carrier).
       (field_neg f x = field_neg f y) = (x = y)``,
   RW_TAC resq_ss [field_neg_def, Field_def, GSPECIFICATION, AbelianGroup_def]
   ++ METIS_TAC [group_inv_cancel]);

val alg_context = alg_add_rewrite field_neg_cancel alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_neg_cancel_imp = store_thm
  ("field_neg_cancel_imp",
   ``!f :: Field. !x y :: (f.carrier).
       (field_neg f x = field_neg f y) ==> (x = y)``,
   METIS_TAC [field_neg_cancel]);

val field_neg_eq_swap_imp = store_thm
  ("field_neg_eq_swap_imp",
   ``!f :: Field. !x y :: (f.carrier).
       (field_neg f x = y) ==> (x = field_neg f y)``,
   METIS_TAC [field_neg_neg]);

val field_neg_eq_swap = store_thm
  ("field_neg_eq_swap",
   ``!f :: Field. !x y :: (f.carrier).
       (field_neg f x = y) = (x = field_neg f y)``,
   METIS_TAC [field_neg_eq_swap_imp]);

val field_neg_eq_swap_imp' = store_thm
  ("field_neg_eq_swap_imp'",
   ``!f :: Field. !x y :: (f.carrier).
       (x = field_neg f y) ==> (field_neg f x = y)``,
   METIS_TAC [field_neg_eq_swap]);

val field_neg_eq_imp = store_thm
  ("field_neg_eq_imp",
   ``!f :: Field. !x y :: (f.carrier).
       (field_neg f x = y) ==> (field_add f x y = field_zero f)``,
   RW_TAC resq_ss [field_rneg]);

val field_neg_eq_imp' = store_thm
  ("field_neg_eq_imp'",
   ``!f :: Field. !x y :: (f.carrier).
       (field_add f x y = field_zero f) ==> (field_neg f x = y)``,
   RW_TAC resq_ss []
   ++ match_tac field_add_lcancel_imp
   ++ Q.EXISTS_TAC `f`
   ++ Q.EXISTS_TAC `x`
   ++ RW_TAC std_ss [field_neg_carrier, field_rneg]);

val field_neg_eq = store_thm
  ("field_neg_eq",
   ``!f :: Field. !x y :: (f.carrier).
       (field_neg f x = y) = (field_add f x y = field_zero f)``,
   METIS_TAC [field_neg_eq_imp, field_neg_eq_imp']);

val field_neg_zero = store_thm
  ("field_neg_zero",
   ``!f :: Field. field_neg f (field_zero f) = field_zero f``,
   RW_TAC resq_ss
     [Field_def, GSPECIFICATION, AbelianGroup_def, field_zero_def,
      field_neg_def]
   ++ METIS_TAC [group_inv_id]);

val alg_context = alg_add_rewrite field_neg_zero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_add_eq = store_thm
  ("field_add_eq",
   ``!f x1 y1 x2 y2.
       (x1 = x2) /\ (y1 = y2) ==> (field_add f x1 y1 = field_add f x2 y2)``,
   RW_TAC std_ss []);

val field_distrib_radd = store_thm
  ("field_distrib_radd",
   ``!f :: Field. !x y z :: (f.carrier).
       field_mult f (field_add f y z) x =
       field_add f (field_mult f y x) (field_mult f z x)``,
   RW_TAC resq_ss []
   ++ METIS_TAC [field_mult_comm, field_add_carrier, field_distrib_ladd]);

(***
val alg_context = alg_add_rewrite'' field_distrib_radd alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;
***)

val field_distrib = save_thm
  ("field_distrib", CONJ field_distrib_ladd field_distrib_radd);

val field_mult_lneg = store_thm
  ("field_mult_lneg",
   ``!f :: Field. !x y :: (f.carrier).
       field_mult f (field_neg f x) y = field_neg f (field_mult f x y)``,
   RW_TAC resq_ss []
   ++ match_tac (GSYM field_neg_eq_imp')
   ++ RW_TAC std_ss [field_mult_carrier, field_neg_carrier]
   ++ RW_TAC std_ss
        [GSYM field_distrib_radd, field_neg_carrier, field_rneg,
         field_mult_lzero]);

val alg_context = alg_add_rewrite field_mult_lneg alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_rneg = store_thm
  ("field_mult_rneg",
   ``!f :: Field. !x y :: (f.carrier).
       field_mult f x (field_neg f y) = field_neg f (field_mult f x y)``,
   METIS_TAC [field_mult_lneg, field_mult_comm, field_neg_carrier]);

val alg_context = alg_add_rewrite field_mult_rneg alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_inv_mult' = store_thm
  ("field_inv_mult'",
   ``!f :: Field. !x y :: field_nonzero f.
       field_inv f (field_mult f x y) =
       field_mult f (field_inv f y) (field_inv f x)``,
   RW_TAC resq_ss
     [field_mult_def, Field_def, GSPECIFICATION, field_inv_def,
      AbelianGroup_def, field_nonzero_def]
   ++ match_tac group_inv_mult
   ++ RW_TAC std_ss []);

val field_inv_mult = store_thm
  ("field_inv_mult",
   ``!f :: Field. !x y :: field_nonzero f.
       field_inv f (field_mult f x y) =
       field_mult f (field_inv f x) (field_inv f y)``,
   METIS_TAC [field_inv_nonzero, field_nonzero_carrier, field_mult_comm,
              field_inv_mult']);

val alg_context = alg_add_rewrite'' field_inv_mult alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_carrier = store_thm
  ("field_exp_carrier",
   ``!f :: Field. !x :: (f.carrier). !n. field_exp f x n IN f.carrier``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [field_exp_def, field_one_carrier, field_mult_carrier]);

val alg_context = alg_add_reduction field_exp_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_nonzero = store_thm
  ("field_exp_nonzero",
   ``!f :: Field. !x :: field_nonzero f. !n.
       field_exp f x n IN field_nonzero f``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [field_exp_def, field_one_nonzero, field_mult_nonzero]);

val alg_context = alg_add_reduction field_exp_nonzero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_num_carrier = store_thm
  ("field_num_carrier",
   ``!f :: Field. !n. field_num f n IN f.carrier``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC alg_ss [field_num_def]);

val alg_context = alg_add_reduction field_num_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_small = store_thm
  ("field_mult_small",
   ``!f :: Field. !x :: (f.carrier).
       (field_mult f (field_num f 0) x = field_zero f) /\
       (field_mult f (field_num f 1) x = x) /\
       (field_mult f (field_num f 2) x = field_add f x x) /\
       (field_mult f (field_num f 3) x =
        field_add f x (field_mult f (field_num f 2) x))``,
   RW_TAC (simpLib.++ (std_ss, numSimps.SUC_FILTER_ss)) [field_num_def]
   ++ RW_TAC alg_ss [field_distrib_radd, field_add_assoc]);

val field_exp_small = store_thm
  ("field_exp_small",
   ``!f :: Field. !x :: (f.carrier).
       (field_exp f x 0 = field_one f) /\
       (field_exp f x 1 = x) /\
       (field_exp f x 2 = field_mult f x x) /\
       (field_exp f x 3 = field_mult f x (field_exp f x 2)) /\
       (field_exp f x 4 = field_mult f x (field_exp f x 3)) /\
       (field_exp f x 5 = field_mult f x (field_exp f x 4)) /\
       (field_exp f x 6 = field_mult f x (field_exp f x 5)) /\
       (field_exp f x 7 = field_mult f x (field_exp f x 6)) /\
       (field_exp f x 8 = field_mult f x (field_exp f x 7)) /\
       (field_exp f x 9 = field_mult f x (field_exp f x 8))``,
   RW_TAC (simpLib.++ (std_ss, numSimps.SUC_FILTER_ss))
     [field_exp_def, field_mult_rone]);

val field_inv_one = store_thm
  ("field_inv_one",
   ``!f :: Field. field_inv f (field_one f) = field_one f``,
   RW_TAC resq_ss [field_inv_def, field_one_def, Field_def, GSPECIFICATION]
   ++ RW_TAC alg_ss []);

val alg_context = alg_add_rewrite field_inv_one alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_zero = store_thm
  ("field_exp_zero",
   ``!f :: Field. !x :: (f.carrier). field_exp f x 0 = field_one f``,
   RW_TAC alg_ss [field_exp_def]);

val alg_context = alg_add_rewrite field_exp_zero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_one = store_thm
  ("field_exp_one",
   ``!f :: Field. !x :: (f.carrier). field_exp f x 1 = x``,
   REWRITE_TAC [ONE, field_exp_def]
   ++ RW_TAC alg_ss []);

val alg_context = alg_add_rewrite field_exp_one alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_neg_add' = store_thm
  ("field_neg_add'",
   ``!f :: Field. !x y :: (f.carrier).
       field_neg f (field_add f x y) =
       field_add f (field_neg f y) (field_neg f x)``,
   RW_TAC resq_ss
     [field_add_def, Field_def, GSPECIFICATION, field_neg_def,
      AbelianGroup_def]
   ++ match_tac group_inv_mult
   ++ RW_TAC std_ss []);

val field_neg_add = store_thm
  ("field_neg_add",
   ``!f :: Field. !x y :: (f.carrier).
       field_neg f (field_add f x y) =
       field_add f (field_neg f x) (field_neg f y)``,
   METIS_TAC [field_neg_carrier, field_add_comm, field_neg_add']);

val alg_context = alg_add_rewrite'' field_neg_add alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_suc = store_thm
  ("field_exp_suc",
   ``!f :: Field. !x :: (f.carrier). !n.
       field_exp f x (SUC n) = field_mult f (field_exp f x n) x``,
   RW_TAC alg_ss [field_exp_def]
   ++ METIS_TAC [field_mult_comm, field_exp_carrier]);

val field_num_suc = store_thm
  ("field_num_suc",
   ``!f :: Field. !n.
       field_num f (SUC n) = field_add f (field_one f) (field_num f n)``,
   RW_TAC alg_ss [field_num_def]
   ++ METIS_TAC [field_add_comm, field_one_carrier, field_num_carrier]);

val field_num_add = store_thm
  ("field_num_add",
   ``!f :: Field. !m n.
       field_add f (field_num f m) (field_num f n) = field_num f (m + n)``,
   RW_TAC resq_ss []
   ++ Induct_on `m`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_num_suc, ADD, field_add_assoc]);

val alg_context = alg_add_rewrite field_num_add alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_num_add' = store_thm
  ("field_num_add'",
   ``!f :: Field. !m n. !x :: (f.carrier).
       field_add f (field_num f m) (field_add f (field_num f n) x) =
       field_add f (field_num f (m + n)) x``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_num_add]);

val alg_context = alg_add_rewrite'' field_num_add' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_num_mult = store_thm
  ("field_num_mult",
   ``!f :: Field. !m n.
       field_mult f (field_num f m) (field_num f n) = field_num f (m * n)``,
   RW_TAC resq_ss []
   ++ Induct_on `m`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_num_def, MULT, field_distrib_radd]);

val alg_context = alg_add_rewrite field_num_mult alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_num_mult' = store_thm
  ("field_num_mult'",
   ``!f :: Field. !m n. !x :: (f.carrier).
       field_mult f (field_num f m) (field_mult f (field_num f n) x) =
       field_mult f (field_num f (m * n)) x``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_num_mult]);

val alg_context = alg_add_rewrite'' field_num_mult' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_num_exp = store_thm
  ("field_num_exp",
   ``!f :: Field. !m n.
       field_exp f (field_num f m) n = field_num f (m ** n)``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC alg_ss [EXP, field_num_one, field_exp_def]);

val alg_context = alg_add_rewrite field_num_exp alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_single_add_single = store_thm
  ("field_single_add_single",
   ``!f :: Field. !x :: (f.carrier).
       field_add f x x = field_mult f (field_num f 2) x``,
   RW_TAC alg_ss [field_mult_small]);

val alg_context = alg_add_rewrite'' field_single_add_single alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_single_add_single' = store_thm
  ("field_single_add_single'",
   ``!f :: Field. !x y :: (f.carrier).
       field_add f x (field_add f x y) =
       field_add f (field_mult f (field_num f 2) x) y``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_single_add_single]);

val alg_context = alg_add_rewrite'' field_single_add_single' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_single_add_mult = store_thm
  ("field_single_add_mult",
   ``!f :: Field. !x :: (f.carrier). !n.
       field_add f x (field_mult f (field_num f n) x) =
       field_mult f (field_num f (n + 1)) x``,
   RW_TAC bool_ss [field_num_suc, GSYM ADD1]
   ++ RW_TAC alg_ss [field_distrib_radd]);

val alg_context = alg_add_rewrite'' field_single_add_mult alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_single_add_mult' = store_thm
  ("field_single_add_mult'",
   ``!f :: Field. !x y :: (f.carrier). !n.
       field_add f x (field_add f (field_mult f (field_num f n) x) y) =
       field_add f (field_mult f (field_num f (n + 1)) x) y``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_single_add_mult]);

val alg_context = alg_add_rewrite'' field_single_add_mult' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_single_add_neg_mult = store_thm
  ("field_single_add_neg_mult",
   ``!f :: Field. !x :: (f.carrier). !n.
       field_add f x (field_neg f (field_mult f (field_num f n) x)) =
       (if n = 0 then x
        else field_neg f (field_mult f (field_num f (n - 1)) x))``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss []
   ++ Cases_on `n`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_num_suc, field_distrib_radd]
   ++ RW_TAC alg_ss [field_neg_add, GSYM field_add_assoc]);

val alg_context = alg_add_rewrite'' field_single_add_neg_mult alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_single_add_neg_mult' = store_thm
  ("field_single_add_neg_mult'",
   ``!f :: Field. !x y :: (f.carrier). !n.
       field_add f x
         (field_add f (field_neg f (field_mult f (field_num f n) x)) y) =
       (if n = 0 then field_add f x y
        else field_add f
               (field_neg f (field_mult f (field_num f (n - 1)) x)) y)``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_single_add_neg_mult]
   ++ RW_TAC resq_ss []
   ++ RW_TAC resq_ss []);

val alg_context = alg_add_rewrite'' field_single_add_neg_mult' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_add_mult = store_thm
  ("field_mult_add_mult",
   ``!f :: Field. !x :: (f.carrier). !m n.
       field_add f (field_mult f (field_num f m) x)
         (field_mult f (field_num f n) x) =
       field_mult f (field_num f (m + n)) x``,
   RW_TAC resq_ss []
   ++ Induct_on `m`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_num_suc, field_distrib_radd, ADD]
   ++ POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
   ++ RW_TAC alg_ss [field_add_assoc]);

val alg_context = alg_add_rewrite'' field_mult_add_mult alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_add_mult' = store_thm
  ("field_mult_add_mult'",
   ``!f :: Field. !x y :: (f.carrier). !m n.
       field_add f (field_mult f (field_num f m) x)
         (field_add f (field_mult f (field_num f n) x) y) =
       field_add f (field_mult f (field_num f (m + n)) x) y``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_mult_add_mult]);

val alg_context = alg_add_rewrite'' field_mult_add_mult' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_add_neg = store_thm
  ("field_mult_add_neg",
   ``!f :: Field. !x :: (f.carrier). !n.
       field_add f (field_mult f (field_num f n) x) (field_neg f x) =
       (if n = 0 then field_neg f x
        else field_mult f (field_num f (n - 1)) x)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss []
   ++ Cases_on `n`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_num_def, field_distrib_radd, field_add_assoc]);

val alg_context = alg_add_rewrite'' field_mult_add_neg alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_add_neg' = store_thm
  ("field_mult_add_neg'",
   ``!f :: Field. !x y :: (f.carrier). !n.
       field_add f (field_mult f (field_num f n) x)
         (field_add f (field_neg f x) y) =
       (if n = 0 then field_add f (field_neg f x) y
        else field_add f (field_mult f (field_num f (n - 1)) x) y)``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_mult_add_neg]
   ++ RW_TAC resq_ss []
   ++ RW_TAC resq_ss []);

val alg_context = alg_add_rewrite'' field_mult_add_neg' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_add_neg_mult = store_thm
  ("field_mult_add_neg_mult",
   ``!f :: Field. !x :: (f.carrier). !m n.
       field_add f (field_mult f (field_num f m) x)
         (field_neg f (field_mult f (field_num f n) x)) =
       (if m < n then field_neg f (field_mult f (field_num f (n - m)) x)
        else field_mult f (field_num f (m - n)) x)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss []
   << [Know `m <= n` >> DECIDE_TAC
       ++ POP_ASSUM (K ALL_TAC)
       ++ Induct_on `m`
       ++ RW_TAC alg_ss []
       ++ Cases_on `n = SUC m` >> RW_TAC alg_ss' []
       ++ Q.PAT_ASSUM `X ==> Y` MP_TAC
       ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
       ++ CONJ_TAC >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_num_suc, field_distrib_radd, field_add_assoc]
       ++ Know `n - m = SUC (n - SUC m)` >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_num_suc, field_distrib_radd,
                         GSYM field_add_assoc, field_neg_add],
       Know `n <= m` >> DECIDE_TAC
       ++ POP_ASSUM (K ALL_TAC)
       ++ Induct_on `m`
       ++ RW_TAC alg_ss []
       ++ Cases_on `n = SUC m` >> RW_TAC alg_ss' []
       ++ Q.PAT_ASSUM `X ==> Y` MP_TAC
       ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
       ++ CONJ_TAC >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_num_suc, field_distrib_radd, field_add_assoc]
       ++ Know `SUC m - n = SUC (m - n)` >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_num_suc, field_distrib_radd,
                         GSYM field_add_assoc, field_neg_add]]);

val alg_context = alg_add_rewrite'' field_mult_add_neg_mult alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_add_neg_mult' = store_thm
  ("field_mult_add_neg_mult'",
   ``!f :: Field. !x y :: (f.carrier). !m n.
       field_add f (field_mult f (field_num f m) x)
         (field_add f (field_neg f (field_mult f (field_num f n) x)) y) =
       (if m < n then
          field_add f (field_neg f (field_mult f (field_num f (n - m)) x)) y
        else field_add f (field_mult f (field_num f (m - n)) x) y)``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_mult_add_neg_mult]
   ++ RW_TAC resq_ss []
   ++ RW_TAC resq_ss []);

val alg_context = alg_add_rewrite'' field_mult_add_neg_mult' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_neg_add_neg = store_thm
  ("field_neg_add_neg",
   ``!f :: Field. !x :: (f.carrier).
       field_add f (field_neg f x) (field_neg f x) =
       field_neg f (field_mult f (field_num f 2) x)``,
   RW_TAC alg_ss [field_mult_small, field_neg_add]);

val alg_context = alg_add_rewrite'' field_neg_add_neg alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_neg_add_neg' = store_thm
  ("field_neg_add_neg'",
   ``!f :: Field. !x y :: (f.carrier).
       field_add f (field_neg f x) (field_add f (field_neg f x) y) =
       field_add f (field_neg f (field_mult f (field_num f 2) x)) y``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_neg_add_neg]);

val alg_context = alg_add_rewrite'' field_neg_add_neg' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_neg_add_neg_mult = store_thm
  ("field_neg_add_neg_mult",
   ``!f :: Field. !x :: (f.carrier). !n.
       field_add f (field_neg f x)
         (field_neg f (field_mult f (field_num f n) x)) =
       field_neg f (field_mult f (field_num f (n + 1)) x)``,
   RW_TAC alg_ss [GSYM field_single_add_mult]
   ++ RW_TAC alg_ss' []);

val alg_context = alg_add_rewrite'' field_neg_add_neg_mult alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_neg_add_neg_mult' = store_thm
  ("field_neg_add_neg_mult'",
   ``!f :: Field. !x y :: (f.carrier). !n.
       field_add f (field_neg f x)
         (field_add f (field_neg f (field_mult f (field_num f n) x)) y) =
       field_add f (field_neg f (field_mult f (field_num f (n + 1)) x)) y``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_neg_add_neg_mult]);

val alg_context = alg_add_rewrite'' field_neg_add_neg_mult' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_neg_mult_add_neg_mult = store_thm
  ("field_neg_mult_add_neg_mult",
   ``!f :: Field. !x :: (f.carrier). !m n.
       field_add f (field_neg f (field_mult f (field_num f m) x))
         (field_neg f (field_mult f (field_num f n) x)) =
       field_neg f (field_mult f (field_num f (m + n)) x)``,
   RW_TAC resq_ss []
   ++ Induct_on `m`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_num_suc, field_distrib_radd, ADD, field_neg_add]
   ++ POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
   ++ RW_TAC alg_ss [field_add_assoc]);

val alg_context = alg_add_rewrite'' field_neg_mult_add_neg_mult alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_neg_mult_add_neg_mult' = store_thm
  ("field_neg_mult_add_neg_mult'",
   ``!f :: Field. !x y :: (f.carrier). !m n.
       field_add f (field_neg f (field_mult f (field_num f m) x))
         (field_add f (field_neg f (field_mult f (field_num f n) x)) y) =
       field_add f (field_neg f (field_mult f (field_num f (m + n)) x)) y``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_neg_mult_add_neg_mult]);

val alg_context = alg_add_rewrite'' field_neg_mult_add_neg_mult' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_single_mult_single = store_thm
  ("field_single_mult_single",
   ``!f :: Field. !x :: (f.carrier). field_mult f x x = field_exp f x 2``,
   RW_TAC alg_ss' [field_exp_small]);

val alg_context = alg_add_rewrite'' field_single_mult_single alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_single_mult_single' = store_thm
  ("field_single_mult_single'",
   ``!f :: Field. !x y :: (f.carrier).
       field_mult f x (field_mult f x y) = field_mult f (field_exp f x 2) y``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_single_mult_single]);

val alg_context = alg_add_rewrite'' field_single_mult_single' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_single_mult_exp = store_thm
  ("field_single_mult_exp",
   ``!f :: Field. !x :: (f.carrier). !n.
       field_mult f x (field_exp f x n) = field_exp f x (n + 1)``,
   METIS_TAC [field_exp_def, ADD1]);

val alg_context = alg_add_rewrite'' field_single_mult_exp alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_single_mult_exp' = store_thm
  ("field_single_mult_exp'",
   ``!f :: Field. !x y :: (f.carrier). !n.
       field_mult f x (field_mult f (field_exp f x n) y) =
       field_mult f (field_exp f x (n + 1)) y``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_single_mult_exp]);

val alg_context = alg_add_rewrite'' field_single_mult_exp' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_single_mult_inv_exp = store_thm
  ("field_single_mult_inv_exp",
   ``!f :: Field. !x :: field_nonzero f. !n.
       field_mult f x (field_inv f (field_exp f x n)) =
       (if n = 0 then x else field_inv f (field_exp f x (n - 1)))``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss []
   ++ Cases_on `n`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_exp_def, GSYM field_mult_assoc, field_inv_mult]);

val alg_context = alg_add_rewrite'' field_single_mult_inv_exp alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_single_mult_inv_exp' = store_thm
  ("field_single_mult_inv_exp'",
   ``!f :: Field. !x :: field_nonzero f. !n. !y :: (f.carrier).
       field_mult f x (field_mult f (field_inv f (field_exp f x n)) y) =
       (if n = 0 then field_mult f x y
        else field_mult f (field_inv f (field_exp f x (n - 1))) y)``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_single_mult_inv_exp]
   ++ RW_TAC resq_ss []
   ++ RW_TAC resq_ss []);

val alg_context = alg_add_rewrite'' field_single_mult_inv_exp' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_mult_exp = store_thm
  ("field_exp_mult_exp",
   ``!f :: Field. !x :: (f.carrier). !m n.
       field_mult f (field_exp f x m) (field_exp f x n) =
       field_exp f x (m + n)``,
   RW_TAC resq_ss []
   ++ Induct_on `m`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_exp_def, ADD_CLAUSES]
   ++ POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
   ++ RW_TAC alg_ss [field_mult_assoc]);

val alg_context = alg_add_rewrite'' field_exp_mult_exp alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_mult_exp' = store_thm
  ("field_exp_mult_exp'",
   ``!f :: Field. !x y :: (f.carrier). !m n.
       field_mult f (field_exp f x m) (field_mult f (field_exp f x n) y) =
       field_mult f (field_exp f x (m + n)) y``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_exp_mult_exp]);

val alg_context = alg_add_rewrite'' field_exp_mult_exp' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_mult_inv = store_thm
  ("field_exp_mult_inv",
   ``!f :: Field. !x :: field_nonzero f. !n.
       field_mult f (field_exp f x n) (field_inv f x) =
       (if n = 0 then field_inv f x else field_exp f x (n - 1))``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss []
   ++ Cases_on `n`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_exp_suc, field_mult_assoc]);

val alg_context = alg_add_rewrite'' field_exp_mult_inv alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_mult_inv' = store_thm
  ("field_exp_mult_inv'",
   ``!f :: Field. !x :: field_nonzero f. !n. !y :: (f.carrier).
       field_mult f (field_exp f x n) (field_mult f (field_inv f x) y) =
       (if n = 0 then field_mult f (field_inv f x) y
        else field_mult f (field_exp f x (n - 1)) y)``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_exp_mult_inv]
   ++ RW_TAC resq_ss []
   ++ RW_TAC resq_ss []);

val alg_context = alg_add_rewrite'' field_exp_mult_inv' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_mult_inv_exp = store_thm
  ("field_exp_mult_inv_exp",
   ``!f :: Field. !x :: field_nonzero f. !m n.
       field_mult f (field_exp f x m) (field_inv f (field_exp f x n)) =
       (if m < n then field_inv f (field_exp f x (n - m))
        else field_exp f x (m - n))``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss []
   << [Know `m <= n` >> DECIDE_TAC
       ++ POP_ASSUM (K ALL_TAC)
       ++ Induct_on `m`
       ++ RW_TAC alg_ss []
       ++ Cases_on `n = SUC m` >> RW_TAC alg_ss []
       ++ Q.PAT_ASSUM `X ==> Y` MP_TAC
       ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
       ++ CONJ_TAC >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_exp_def, field_mult_assoc]
       ++ Know `n - m = SUC (n - SUC m)` >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_exp_def, GSYM field_mult_assoc, field_inv_mult],
       Know `n <= m` >> DECIDE_TAC
       ++ POP_ASSUM (K ALL_TAC)
       ++ Induct_on `m`
       ++ RW_TAC alg_ss []
       ++ Cases_on `n = SUC m` >> RW_TAC alg_ss []
       ++ Q.PAT_ASSUM `X ==> Y` MP_TAC
       ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
       ++ CONJ_TAC >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_exp_def, field_mult_assoc]
       ++ Know `SUC m - n = SUC (m - n)` >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_exp_def, GSYM field_mult_assoc]]);

val alg_context = alg_add_rewrite'' field_exp_mult_inv_exp alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_mult_inv_exp' = store_thm
  ("field_exp_mult_inv_exp'",
   ``!f :: Field. !x :: field_nonzero f. !m n. !y :: (f.carrier).
       field_mult f (field_exp f x m)
         (field_mult f (field_inv f (field_exp f x n)) y) =
       (if m < n then field_mult f (field_inv f (field_exp f x (n - m))) y
        else field_mult f (field_exp f x (m - n)) y)``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_exp_mult_inv_exp]
   ++ RW_TAC resq_ss []
   ++ RW_TAC resq_ss []);

val alg_context = alg_add_rewrite'' field_exp_mult_inv_exp' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_inv_mult_inv = store_thm
  ("field_inv_mult_inv",
   ``!f :: Field. !x :: field_nonzero f.
       field_mult f (field_inv f x) (field_inv f x) =
       field_inv f (field_exp f x 2)``,
   RW_TAC alg_ss [field_exp_small, field_inv_mult]);

val alg_context = alg_add_rewrite'' field_inv_mult_inv alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_inv_mult_inv' = store_thm
  ("field_inv_mult_inv'",
   ``!f :: Field. !x :: field_nonzero f. !y :: (f.carrier).
       field_mult f (field_inv f x) (field_mult f (field_inv f x) y) =
       field_mult f (field_inv f (field_exp f x 2)) y``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_inv_mult_inv]);

val alg_context = alg_add_rewrite'' field_inv_mult_inv' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_inv_mult_inv_exp = store_thm
  ("field_inv_mult_inv_exp",
   ``!f :: Field. !x :: field_nonzero f. !n.
       field_mult f (field_inv f x) (field_inv f (field_exp f x n)) =
       field_inv f (field_exp f x (n + 1))``,
   RW_TAC alg_ss [GSYM field_single_mult_exp]
   ++ RW_TAC alg_ss' []);

val alg_context = alg_add_rewrite'' field_inv_mult_inv_exp alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_inv_mult_inv_exp' = store_thm
  ("field_inv_mult_inv_exp'",
   ``!f :: Field. !x :: field_nonzero f. !n. !y :: (f.carrier).
       field_mult f (field_inv f x)
         (field_mult f (field_inv f (field_exp f x n)) y) =
       field_mult f (field_inv f (field_exp f x (n + 1))) y``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_inv_mult_inv_exp]);

val alg_context = alg_add_rewrite'' field_inv_mult_inv_exp' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_inv_exp_mult_inv_exp = store_thm
  ("field_inv_exp_mult_inv_exp",
   ``!f :: Field. !x :: field_nonzero f. !m n.
       field_mult f (field_inv f (field_exp f x m))
         (field_inv f (field_exp f x n)) =
       field_inv f (field_exp f x (m + n))``,
   RW_TAC resq_ss []
   ++ Induct_on `m`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_exp_def, ADD_CLAUSES, field_inv_mult]
   ++ POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
   ++ RW_TAC alg_ss [field_mult_assoc]);

val alg_context = alg_add_rewrite'' field_inv_exp_mult_inv_exp alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_inv_exp_mult_inv_exp' = store_thm
  ("field_inv_exp_mult_inv_exp'",
   ``!f :: Field. !x :: field_nonzero f. !m n. !y :: (f.carrier).
       field_mult f (field_inv f (field_exp f x m))
         (field_mult f (field_inv f (field_exp f x n)) y) =
       field_mult f (field_inv f (field_exp f x (m + n))) y``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_inv_exp_mult_inv_exp]);

val alg_context = alg_add_rewrite'' field_inv_exp_mult_inv_exp' alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_one_exp = store_thm
  ("field_one_exp",
   ``!f :: Field. !n. field_exp f (field_one f) n = field_one f``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [field_exp_def, field_mult_rone, field_one_carrier]);

val alg_context = alg_add_rewrite field_one_exp alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_zero_exp = store_thm
  ("field_zero_exp",
   ``!f :: Field. !n.
       field_exp f (field_zero f) n =
       (if n = 0 then field_one f else field_zero f)``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss
        [field_exp_def, field_mult_rone, field_one_carrier]
   ++ RW_TAC alg_ss []);

val alg_context = alg_add_rewrite field_zero_exp alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_eq_zero = store_thm
  ("field_exp_eq_zero",
   ``!f :: Field. !x :: (f.carrier). !n.
       (field_exp f x n = field_zero f) = ~(n = 0) /\ (x = field_zero f)``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss
        [field_exp_def, field_one_zero, field_entire, field_exp_carrier]
   ++ METIS_TAC []);

val alg_context = alg_add_rewrite field_exp_eq_zero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_neg = store_thm
  ("field_exp_neg",
   ``!f :: Field. !x :: (f.carrier). !n.
       field_exp f (field_neg f x) n =
       if EVEN n then field_exp f x n else field_neg f (field_exp f x n)``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC alg_ss [EVEN, field_exp_def]);

val alg_context = alg_add_rewrite'' field_exp_neg alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_exp = store_thm
  ("field_exp_exp",
   ``!f :: Field. !x :: (f.carrier). !m n.
       field_exp f (field_exp f x m) n = field_exp f x (m * n)``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   >> RW_TAC alg_ss [field_exp_def]
   ++ RW_TAC alg_ss [field_exp_def, ONCE_REWRITE_RULE [MULT_COMM] MULT]
   ++ ONCE_REWRITE_TAC [ADD_COMM]
   ++ RW_TAC alg_ss [GSYM field_exp_mult_exp]);

val alg_context = alg_add_rewrite'' field_exp_exp alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_sub_eq_zero = store_thm
  ("field_sub_eq_zero",
   ``!f :: Field. !x y :: (f.carrier).
       (field_sub f x y = field_zero f) = (x = y)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss' []
   ++ RW_TAC alg_ss [GSYM field_neg_eq]);

local
  val field_sub_eq_zero_conv =
      let
        val th = CONV_RULE RES_FORALL_CONV (GSYM field_sub_eq_zero)
      in
        fn f => cond_rewr_conv (ISPEC f th)
      end;

  fun left_conv solver tm =
      let
        val (x,y) = dest_eq tm
        val _ = not (is_field_zero y) orelse
                raise ERR "field_sub_eq_zero_conv (left)" "looping"
        val (f,_,_) = dest_field_add x
      in
        field_sub_eq_zero_conv f solver
      end tm;

  fun right_conv solver tm =
      let
        val (_,y) = dest_eq tm
        val (f,_,_) = dest_field_add y
(***
        val _ = print "right_conv\n";
***)
      in
        field_sub_eq_zero_conv f solver
      end tm;
in
  val field_sub_eq_zero_l_conv =
      {name = "field_sub_eq_zero_conv (left)",
       key = ``field_add (f : 'a field) x y = z``,
       conv = left_conv}
  and field_sub_eq_zero_r_conv =
      {name = "field_sub_eq_zero_conv (right)",
       key = ``x = field_add (f : 'a field) y z``,
       conv = right_conv};
end;

val alg_context = alg_add_conversion'' field_sub_eq_zero_r_conv alg_context;
val alg_context = alg_add_conversion'' field_sub_eq_zero_l_conv alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_sub_eq_zero_imp = store_thm
  ("field_sub_eq_zero_imp",
   ``!f :: Field. !x y :: (f.carrier).
       (field_sub f x y = field_zero f) ==> (x = y)``,
   RW_TAC std_ss [field_sub_eq_zero]);

val field_inv_inv = store_thm
  ("field_inv_inv",
   ``!f :: Field. !x :: field_nonzero f. field_inv f (field_inv f x) = x``,
   RW_TAC resq_ss
     [field_inv_def, Field_def, GSPECIFICATION, AbelianGroup_def,
      field_nonzero_def]
   ++ METIS_TAC [group_inv_inv]);

val alg_context = alg_add_rewrite field_inv_inv alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_sub_carrier = store_thm
  ("field_sub_carrier",
   ``!f :: Field. !x y :: (f.carrier). field_sub f x y IN f.carrier``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss' []);

val alg_context = alg_add_reduction field_sub_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_neg_nonzero = store_thm
  ("field_neg_nonzero",
   ``!f :: Field. !x :: field_nonzero f. field_neg f x IN field_nonzero f``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss [GSYM field_nonzero_eq]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC alg_ss [field_nonzero_def, GSPECIFICATION, IN_DIFF, IN_SING]
   ++ STRIP_TAC
   ++ Q.PAT_ASSUM `~(X = Y)` MP_TAC
   ++ RW_TAC alg_ss []
   ++ match_tac field_add_lcancel_imp
   ++ Q.EXISTS_TAC `f`
   ++ Q.EXISTS_TAC `field_neg f x`
   ++ RW_TAC std_ss [field_lneg]
   ++ RW_TAC alg_ss []);

val alg_context = alg_add_reduction field_neg_nonzero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_inv_neg = store_thm
  ("field_inv_neg",
   ``!f :: Field. !x :: field_nonzero f.
       field_inv f (field_neg f x) = field_neg f (field_inv f x)``,
   RW_TAC resq_ss []
   ++ match_tac field_mult_lcancel_imp
   ++ Q.EXISTS_TAC `f`
   ++ Q.EXISTS_TAC `field_neg f x`
   ++ SIMP_TAC bool_ss [CONJ_ASSOC]
   ++ CONJ_TAC >> RW_TAC alg_ss []
   ++ Know
      `field_mult f (field_neg f x) (field_inv f (field_neg f x)) = field_one f`
   >> (match_tac field_rinv ++ RW_TAC alg_ss [])
   ++ RW_TAC std_ss []
   ++ RW_TAC alg_ss' []);
  
val alg_context = alg_add_rewrite'' field_inv_neg alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_mult = store_thm
  ("field_exp_mult",
   ``!f :: Field. !x y :: (f.carrier). !n.
       field_exp f (field_mult f x y) n =
       field_mult f (field_exp f x n) (field_exp f y n)``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC alg_ss [field_exp_def]
   ++ RW_TAC alg_ss [field_mult_assoc]
   ++ AP_TERM_TAC
   ++ RW_TAC alg_ss [GSYM field_mult_assoc]
   ++ AP_THM_TAC
   ++ AP_TERM_TAC
   ++ match_tac field_mult_comm
   ++ RW_TAC alg_ss []);

val alg_context = alg_add_rewrite'' field_exp_mult alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_exp_inv = store_thm
  ("field_exp_inv",
   ``!f :: Field. !x :: field_nonzero f. !n.
       field_exp f (field_inv f x) n = field_inv f (field_exp f x n)``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_exp_def]
   ++ RW_TAC alg_ss' []);

val alg_context = alg_add_rewrite'' field_exp_inv alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_add_ac_conv =
    {name = "field_add_ac_conv",
     key = ``field_add f x y``,
     conv =
       alg_binop_ac_conv
         {term_compare = field_compare,
          dest_binop = dest_field_add,
          dest_inv = dest_field_neg,
          dest_exp = dest_field_num_mult,
          assoc_th = field_add_assoc,
          comm_th = field_add_comm,
          comm_th' = field_add_comm',
          id_ths =
            [field_add_lzero,
             field_add_lzero',
             field_add_rzero,
             field_add_rzero'],             
          simplify_ths =
            [GSYM field_num_one,
             field_neg_zero,
             field_neg_neg,
             field_neg_add,
             field_mult_lzero,
             field_mult_lzero',
             field_mult_rzero,
             field_mult_rzero',
             field_mult_lone,
             field_mult_lone',
             field_mult_rone,
             field_mult_rone'],
          combine_ths =
            [field_single_add_single,
             field_single_add_mult,
             field_rneg,
             field_single_add_neg_mult,
             field_mult_add_mult,
             field_mult_add_neg,
             field_mult_add_neg_mult,
             field_neg_add_neg,
             field_neg_add_neg_mult,
             field_neg_mult_add_neg_mult],
          combine_ths' =
            [field_single_add_single',
             field_single_add_mult',
             field_rneg',
             field_single_add_neg_mult',
             field_mult_add_mult',
             field_mult_add_neg',
             field_mult_add_neg_mult',
             field_neg_add_neg',
             field_neg_add_neg_mult',
             field_neg_mult_add_neg_mult']}};
    
val alg_context = alg_add_conversion'' field_add_ac_conv alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_mult_ac_conv =
    {name = "field_mult_ac_conv",
     key = ``field_mult f x y``,
     conv =
       alg_binop_ac_conv
         {term_compare = field_compare,
          dest_binop = dest_field_mult,
          dest_inv = dest_field_inv,
          dest_exp = dest_field_exp,
          assoc_th = field_mult_assoc,
          comm_th = field_mult_comm,
          comm_th' = field_mult_comm',
          id_ths =
            [field_mult_lone,
             field_mult_lone',
             field_mult_rone,
             field_mult_rone'],
          simplify_ths =
            [field_inv_one,
             field_inv_inv,
             field_inv_mult,
             field_exp_zero,
             field_exp_one,
             field_exp_exp,
             field_exp_mult,
             field_exp_inv],
          combine_ths =
            [field_single_mult_single,
             field_single_mult_exp,
             field_rinv,
             field_single_mult_inv_exp,
             field_exp_mult_exp,
             field_exp_mult_inv,
             field_exp_mult_inv_exp,
             field_inv_mult_inv,
             field_inv_mult_inv_exp,
             field_inv_exp_mult_inv_exp],
          combine_ths' =
            [field_single_mult_single',
             field_single_mult_exp',
             field_rinv',
             field_single_mult_inv_exp',
             field_exp_mult_exp',
             field_exp_mult_inv',
             field_exp_mult_inv_exp',
             field_inv_mult_inv',
             field_inv_mult_inv_exp',
             field_inv_exp_mult_inv_exp']}};
    
val alg_context = alg_add_conversion'' field_mult_ac_conv alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_binomial_2 = store_thm
  ("field_binomial_2",
   ``!f :: Field. !x y :: (f.carrier).
       field_exp f (field_add f x y) 2 =
       field_add f (field_exp f x 2)
         (field_add f (field_mult f (field_num f 2) (field_mult f x y))
            (field_exp f y 2))``,
   RW_TAC alg_ss [field_exp_small]
   ++ RW_TAC alg_ss' [field_distrib]);

val field_binomial_3 = store_thm
  ("field_binomial_3",
   ``!f :: Field. !x y :: (f.carrier).
       field_exp f (field_add f x y) 3 =
       field_add f
         (field_exp f x 3)
         (field_add f
           (field_mult f (field_num f 3) (field_mult f (field_exp f x 2) y))
           (field_add f
             (field_mult f (field_num f 3) (field_mult f x (field_exp f y 2)))
             (field_exp f y 3)))``,
   RW_TAC alg_ss [field_exp_small]
   ++ RW_TAC alg_ss' [field_distrib, field_binomial_2]);

val field_binomial_4 = store_thm
  ("field_binomial_4",
   ``!f :: Field. !x y :: (f.carrier).
       field_exp f (field_add f x y) 4 =
       field_add f
         (field_exp f x 4)
         (field_add f
           (field_mult f (field_num f 4) (field_mult f (field_exp f x 3) y))
           (field_add f
             (field_mult f
               (field_num f 6)
               (field_mult f (field_exp f x 2) (field_exp f y 2)))
             (field_add f
               (field_mult f (field_num f 4) (field_mult f x (field_exp f y 3)))
               (field_exp f y 4))))``,
   RW_TAC alg_ss [field_exp_small]
   ++ RW_TAC alg_ss' [field_distrib, field_binomial_2, field_binomial_3]);

val field_div_carrier = store_thm
  ("field_div_carrier",
   ``!f :: Field. !x :: (f.carrier). !y :: field_nonzero f.
       field_div f x y IN f.carrier``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss' [field_div_def]);

val alg_context = alg_add_reduction field_div_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_div_nonzero = store_thm
  ("field_div_nonzero",
   ``!f :: Field. !x y :: field_nonzero f. field_div f x y IN field_nonzero f``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss' [field_div_def]);

val alg_context = alg_add_reduction field_div_nonzero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_div_lneg = store_thm
  ("field_div_lneg",
   ``!f :: Field. !x :: (f.carrier). !y :: field_nonzero f.
       field_div f (field_neg f x) y = field_neg f (field_div f x y)``,
   RW_TAC alg_ss' [field_div_def]);

val field_div_rneg = store_thm
  ("field_div_rneg",
   ``!f :: Field. !x :: (f.carrier). !y :: field_nonzero f.
       field_div f x (field_neg f y) = field_neg f (field_div f x y)``,
   RW_TAC alg_ss' [field_inv_neg, field_div_def]);

val field_div_addl = store_thm
  ("field_div_addl",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_add f x (field_div f y z) =
       field_div f (field_add f (field_mult f x z) y) z``,
   RW_TAC alg_ss' [field_div_def, field_distrib]);

val field_div_addr = store_thm
  ("field_div_addr",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_add f (field_div f y z) x =
       field_div f (field_add f y (field_mult f x z)) z``,
   RW_TAC alg_ss' [field_div_def, field_distrib]);

val field_div_subl = store_thm
  ("field_div_subl",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_sub f x (field_div f y z) =
       field_div f (field_sub f (field_mult f x z) y) z``,
   RW_TAC alg_ss' [field_div_def, field_distrib]);

val field_div_subr = store_thm
  ("field_div_subr",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_sub f (field_div f y z) x =
       field_div f (field_sub f y (field_mult f x z)) z``,
   RW_TAC alg_ss' [field_div_def, field_distrib]);

val field_div_multl = store_thm
  ("field_div_multl",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_mult f x (field_div f y z) =
       field_div f (field_mult f x y) z``,
   RW_TAC alg_ss' [field_div_def]);

val field_div_multr = store_thm
  ("field_div_multr",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_mult f (field_div f y z) x =
       field_div f (field_mult f y x) z``,
   RW_TAC alg_ss' [field_div_def]);

val field_div_exp = store_thm
  ("field_div_exp",
   ``!f :: Field. !x :: (f.carrier). !y :: field_nonzero f. !n.
       field_exp f (field_div f x y) n =
       field_div f (field_exp f x n) (field_exp f y n)``,
   RW_TAC alg_ss' [field_div_def, field_exp_mult, field_exp_inv]);

val field_div_divl = store_thm
  ("field_div_divl",
   ``!f :: Field. !x :: (f.carrier). !y z :: field_nonzero f.
       field_div f (field_div f x y) z =
       field_div f x (field_mult f y z)``,
   RW_TAC alg_ss' [field_div_def]);

val field_div_divr = store_thm
  ("field_div_divr",
   ``!f :: Field. !x :: (f.carrier). !y z :: field_nonzero f.
       field_div f x (field_div f y z) =
       field_div f (field_mult f x z) y``,
   RW_TAC alg_ss' [field_div_def]);

val field_add_divl = store_thm
  ("field_add_divl",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_add f (field_div f y z) x =
       field_div f (field_add f y (field_mult f z x)) z``,
   RW_TAC alg_ss [field_div_def]
   ++ RW_TAC alg_ss' [field_distrib]);

val field_add_divl' = store_thm
  ("field_add_divl'",
   ``!f :: Field. !x y t :: (f.carrier). !z :: field_nonzero f.
       field_add f (field_div f y z) (field_add f x t) =
       field_add f (field_div f (field_add f y (field_mult f z x)) z) t``,
   RW_TAC alg_ss [GSYM field_add_assoc]
   ++ RW_TAC resq_ss []
   ++ match_tac field_add_divl
   ++ RW_TAC alg_ss []);

val field_add_divr = store_thm
  ("field_add_divr",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_add f x (field_div f y z) =
       field_div f (field_add f (field_mult f z x) y) z``,
   RW_TAC alg_ss [field_div_def]
   ++ RW_TAC alg_ss' [field_distrib]);

val field_add_divr' = store_thm
  ("field_add_divr'",
   ``!f :: Field. !x y t :: (f.carrier). !z :: field_nonzero f.
       field_add f x (field_add f (field_div f y z) t) =
       field_add f (field_div f (field_add f (field_mult f z x) y) z) t``,
   RW_TAC alg_ss [GSYM field_add_assoc]
   ++ RW_TAC resq_ss []
   ++ match_tac field_add_divr
   ++ RW_TAC alg_ss []);

val field_add_div = store_thm
  ("field_add_div",
   ``!f :: Field. !v w :: (f.carrier). !x y z :: field_nonzero f.
       field_add f
         (field_div f v (field_mult f x y))
         (field_div f w (field_mult f x z)) =
       field_div f
         (field_add f (field_mult f z v) (field_mult f y w))
         (field_mult f x (field_mult f y z))``,
   RW_TAC alg_ss [field_div_def]
   ++ RW_TAC alg_ss' [field_distrib]);

val field_add_div' = store_thm
  ("field_add_div'",
   ``!f :: Field. !v w t :: (f.carrier). !x y z :: field_nonzero f.
       field_add f
         (field_div f v (field_mult f x y))
         (field_add f (field_div f w (field_mult f x z)) t) =
       field_add f
         (field_div f
           (field_add f (field_mult f z v) (field_mult f y w))
           (field_mult f x (field_mult f y z))) t``,
   RW_TAC alg_ss [GSYM field_add_assoc]
   ++ RW_TAC resq_ss []
   ++ match_tac field_add_div
   ++ RW_TAC alg_ss []);

val field_div_cancel = store_thm
  ("field_div_cancel",
   ``!f :: Field. !x z :: field_nonzero f. !y :: (f.carrier).
       (field_div f (field_mult f x y) (field_mult f x z) = field_div f y z)``,
   RW_TAC resq_ss [field_div_def]
   ++ RW_TAC alg_ss' []);

val field_inv_eq_zero = store_thm
  ("field_inv_eq_zero",
   ``!f :: Field. !x :: field_nonzero f. ~(field_inv f x = field_zero f)``,
   RW_TAC resq_ss []
   ++ STRIP_TAC
   ++ Know `field_inv f x IN field_nonzero f` >> METIS_TAC [field_inv_nonzero]
   ++ RW_TAC alg_ss [field_nonzero_def, IN_DIFF, IN_SING]);

val alg_context = alg_add_rewrite field_inv_eq_zero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_div_eq_zero = store_thm
  ("field_div_eq_zero",
   ``!f :: Field. !x :: (f.carrier). !y :: field_nonzero f.
       (field_div f x y = field_zero f) = (x = field_zero f)``,
   RW_TAC resq_ss [field_div_def]
   ++ RW_TAC alg_ss [field_entire]);

val alg_context = alg_add_rewrite field_div_eq_zero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

(* ------------------------------------------------------------------------- *)
(* Proof tools for field expressions.                                        *)
(* ------------------------------------------------------------------------- *)

local
  fun field_field tm =
      case total dest_field_zero tm of
        SOME f => f
      | NONE =>
        case total dest_field_one tm of
          SOME f => f
        | NONE =>
          case total dest_field_num tm of
            SOME (f,_) => f
          | NONE =>
            case total dest_field_neg tm of
              SOME (f,_) => f
            | NONE =>
              case total dest_field_add tm of
                SOME (f,_,_) => f
              | NONE =>
                case total dest_field_mult tm of
                  SOME (f,_,_) => f
                | NONE =>
                  case total dest_field_exp tm of
                    SOME (f,_,_) => f
                  | NONE => raise ERR "field_field" "";

  fun field_to_exp tm varmap =
      case total dest_field_zero tm of
        SOME _ => (Algebra.fromInt 0, varmap)
      | NONE =>
        case total dest_field_one tm of
          SOME _ => (Algebra.fromInt 1, varmap)
        | NONE =>
          case total dest_field_num tm of
            SOME (_,n) => (Algebra.fromInt (numLib.int_of_term n), varmap)
          | NONE =>
            case total dest_field_neg tm of
              SOME (_,a) =>
              let
                val (a,varmap) = field_to_exp a varmap
              in
                (Algebra.negate a, varmap)
              end
            | NONE =>
              case total dest_field_add tm of
                SOME (_,a,b) =>
                let
                  val (a,varmap) = field_to_exp a varmap
                  val (b,varmap) = field_to_exp b varmap
                in
                  (Algebra.add (a,b), varmap)
                end
              | NONE =>
                case total dest_field_sub tm of
                  SOME (_,a,b) =>
                  let
                    val (a,varmap) = field_to_exp a varmap
                    val (b,varmap) = field_to_exp b varmap
                  in
                    (Algebra.subtract (a,b), varmap)
                  end
                | NONE =>
                  case total dest_field_mult tm of
                    SOME (_,a,b) =>
                    let
                      val (a,varmap) = field_to_exp a varmap
                      val (b,varmap) = field_to_exp b varmap
                    in
                      (Algebra.multiply (a,b), varmap)
                    end
                  | NONE =>
                    case total dest_field_exp tm of
                      SOME (_,a,n) =>
                      let
                        val (a,varmap) = field_to_exp a varmap
                      in
                        (Algebra.power (a, numLib.int_of_term n), varmap)
                      end
                    | NONE =>
                      let
                        val s = term_to_string tm
                        val v = Algebra.Var s
                      in
                        case List.find (equal s o fst) varmap of
                          NONE => (v, (s,tm) :: varmap)
                        | SOME (_,tm') =>
                          let
                            val _ = tm = tm' orelse raise Bug "field_to_exp"
                          in
                            (v,varmap)
                          end
                      end;

  fun exp_to_field f varmap e =
      case Algebra.toInt e of
        SOME n =>
        if 0 <= n then mk_field_num (f, numLib.term_of_int n)
        else mk_field_neg (f, mk_field_num (f, numLib.term_of_int (~n)))
      | NONE =>
        case e of
          Algebra.Var v =>
          (case List.find (equal v o fst) varmap of
             NONE => raise Bug "exp_to_field: variable not found"
           | SOME (_,tm) => tm)
        | Algebra.Sum m =>
          (case map (exp_sum_to_field f varmap) (rev (Map.toList m)) of
             [] => raise Bug "exp_to_field: empty sum"
           | x :: xs => foldl (fn (y,z) => mk_field_add (f,y,z)) x xs)
        | Algebra.Prod m =>
          (case map (exp_prod_to_field f varmap) (rev (Map.toList m)) of
             [] => raise Bug "exp_to_field: empty product"
           | x :: xs => foldl (fn (y,z) => mk_field_mult (f,y,z)) x xs)
  and exp_sum_to_field f varmap (e,n) =
      let
        val e = exp_to_field f varmap e
      in
        if n = 1 then e
        else if n = ~1 then mk_field_neg (f,e)
        else if 0 <= n then mk_field_num_mult (f, e, numLib.term_of_int n)
        else mk_field_neg (f, mk_field_num_mult (f, e, numLib.term_of_int (~n)))
      end
  and exp_prod_to_field f varmap (e,n) =
      let
        val e = exp_to_field f varmap e
      in
        if n = 1 then e
        else if n = ~1 then mk_field_inv (f,e)
        else if 0 <= n then mk_field_exp (f, e, numLib.term_of_int n)
        else mk_field_inv (f, mk_field_exp (f, e, numLib.term_of_int (~n)))
      end;
in
  fun ORACLE_field_poly_conv term_normalize_ths _ tm =
      let
        val field = field_field tm

        val _ = print ("ORACLE_field_poly_conv: input =\n"
                       ^ term_to_string tm ^ "\n")

        val _ = print ("ORACLE_field_poly_conv: reducing with "
                       ^ int_to_string (length term_normalize_ths)
                       ^ " equations.\n")

        val _ = print ("ORACLE_field_poly_conv: field = "
                       ^ term_to_string field ^ "\n")

        val (exp,varmap) = field_to_exp tm []

        fun mk_eqn th varmap =
            let
              val (l_tm,r_tm) = dest_eq (concl th)
              val (l_exp,varmap) = field_to_exp l_tm varmap
              val (r_exp,varmap) = field_to_exp r_tm varmap
            in
              ((l_exp,r_exp),varmap)
            end

        val (eqns,varmap) = Useful.maps mk_eqn term_normalize_ths varmap

        val _ = print ("ORACLE_field_poly_conv: variables =\n\""
                       ^ Useful.join "\" \"" (map fst varmap) ^ "\"\n")

        val exp = Algebra.normalize {equations = eqns} exp

        val tm' = exp_to_field field varmap exp

        val _ = print ("ORACLE_field_poly_conv: result =\n"
                       ^ term_to_string tm' ^ "\n")

        val _ = tm <> tm' orelse raise ERR "ORACLE_field_poly_conv" "unchanged"
      in
        mk_oracle_thm "field_poly" ([], mk_eq (tm,tm'))
      end;
end;

local
  val field_single_mult_exp_alt = lemma
    (``!f x n.
         f IN Field /\ x IN f.carrier ==>
         (field_exp f x (SUC n) = field_mult f x (field_exp f x n))``,
     METIS_TAC [field_single_mult_exp, ADD1]);

  val field_exp_mult_exp_alt = lemma
    (``!f x m n.
         f IN Field /\ x IN f.carrier ==>
         (field_exp f x (m + n) =
          field_mult f (field_exp f x m) (field_exp f x n))``,
     METIS_TAC [field_exp_mult_exp]);

  val field_mult_lone_conv =
      let
        val th = CONV_RULE RES_FORALL_CONV (GSYM field_mult_lone)
      in
        fn f => cond_rewr_conv (ISPEC f th)
      end;

  val field_mult_rone_conv =
      let
        val th = CONV_RULE RES_FORALL_CONV (GSYM field_mult_rone)
      in
        fn f => cond_rewr_conv (ISPEC f th)
      end;

  fun field_single_mult_exp_conv f x n =
      let
        val th = ISPECL [f, x, numLib.term_of_int n] field_single_mult_exp_alt
        val conv = RAND_CONV (LAND_CONV (RAND_CONV reduceLib.SUC_CONV))
        val th = CONV_RULE conv th
      in
        cond_rewr_conv th
      end;

  fun field_exp_mult_exp_conv f x m n =
      let
        val th = field_exp_mult_exp_alt
        val th = ISPECL [f, x, numLib.term_of_int m, numLib.term_of_int n] th
        val conv = RAND_CONV (LAND_CONV (RAND_CONV reduceLib.ADD_CONV))
        val th = CONV_RULE conv th
      in
        cond_rewr_conv th
      end;

  fun field_mult_presimp_conv solver =
(***
      trace_conv "field_mult_presimp_conv"
***)
        (QCONV (TRY_CONV (#conv field_mult_ac_conv solver) THENC
                reduceLib.REDUCE_CONV));

  fun field_mult_postsimp_conv solver =
      BINOP_CONV (field_mult_presimp_conv solver);

  fun dest_field_power tm =
      case total dest_field_exp tm of
        NONE => (tm,NONE)
      | SOME (_,t,n) => (t, SOME (numLib.int_of_term n))

  fun hcf_power_conv2 f (a,b) =
      if aconv a b then (field_mult_rone_conv f, field_mult_rone_conv f)
      else
        let
          val _ = not (is_field_mult a) orelse raise Bug "a is a mult"
          and _ = not (is_field_mult b) orelse raise Bug "b is a mult"

          val (at,an) = dest_field_power a
          and (bt,bn) = dest_field_power b

          val _ = aconv at bt orelse raise Bug "at <> bt"

          val _ = (case an of NONE => true | SOME n => n >= 2) orelse
                  raise Bug "exponenent of a is less than 2 (nyi)"

          val _ = (case bn of NONE => true | SOME n => n >= 2) orelse
                  raise Bug "exponenent of b is less than 2 (nyi)"
        in
          case (an,bn) of
            (NONE,NONE) => raise Bug "a = b"
          | (SOME an, NONE) =>
            (field_single_mult_exp_conv f at (an - 1), field_mult_rone_conv f)
          | (NONE, SOME bn) =>
            (field_mult_rone_conv f, field_single_mult_exp_conv f bt (bn - 1))
          | (SOME an, SOME bn) =>
            (case Int.compare (an,bn) of
               LESS => (field_mult_rone_conv f,
                        field_exp_mult_exp_conv f bt an (bn - an))
             | EQUAL => raise Bug "a = b (power)"
             | GREATER => (field_exp_mult_exp_conv f at bn (an - bn),
                           field_mult_rone_conv f))
        end;

  local
    val field_mult_comm_conv' = cond_rewr_conv field_mult_comm';

    val field_mult_assoc_conv = cond_rewr_conv field_mult_assoc;

    val field_mult_assoc_conv' = cond_rewr_conv (GSYM field_mult_assoc);
  in
    fun push_conv solver a_th =
        RAND_CONV (K a_th) THENC field_mult_comm_conv' solver;

    fun double_push_conv solver ac a_th =
        LAND_CONV (ac solver) THENC
        field_mult_assoc_conv solver THENC
        RAND_CONV (push_conv solver a_th) THENC
        field_mult_assoc_conv' solver;
  end;

  fun hcf_conv2 f solver (a,b) =
      if is_field_one a orelse is_field_one b then
        (field_mult_lone_conv f solver a,
         field_mult_lone_conv f solver b)
      else if not (is_field_mult a) then
        let
          val a_th = field_mult_rone_conv f solver a
          val (a_th',b_th) = hcf_conv2 f solver (rhs (concl a_th), b)
        in
          (TRANS a_th a_th', b_th)
        end
      else if not (is_field_mult b) then
        let
          val b_th = field_mult_rone_conv f solver b
          val (a_th,b_th') = hcf_conv2 f solver (a, rhs (concl b_th))
        in
          (a_th, TRANS b_th b_th')
        end
      else
        let
          val (a1,a2) =
              case total dest_field_mult a of
                NONE => raise Bug "a not a mult"
              | SOME (_,a1,a2) => (a1,a2)

          val (b1,b2) =
              case total dest_field_mult b of
                NONE => raise Bug "b not a mult"
              | SOME (_,b1,b2) => (b1,b2)

          val (at,an) = dest_field_power a1
          and (bt,bn) = dest_field_power b1
        in
          case field_compare (at,bt) of
            LESS =>
            let
              val (a_th,b_th) = hcf_conv2 f solver (a2,b)
            in
              (push_conv solver a_th a, b_th)
            end
          | EQUAL => 
            let
              val (ac,bc) = hcf_power_conv2 f (a1,b1)
              val (a_th,b_th) = hcf_conv2 f solver (a2,b2)
            in
              (double_push_conv solver ac a_th a,
               double_push_conv solver bc b_th b)
            end
          | GREATER =>
            let
              val (a_th,b_th) = hcf_conv2 f solver (a,b2)
            in
              (a_th, push_conv solver b_th b)
            end
        end;
in
  fun field_hcf_conv2 f solver (a,b) =
      let
(*
        val () = (print "field_hcf_conv2: "; print_term a; print ", ";
                  print_term b; print "\n")
*)
        val a_th = field_mult_presimp_conv solver a
        and b_th = field_mult_presimp_conv solver b
(*
        val () = (print "field_hcf_conv2: "; print_thm a_th; print ", ";
                  print_thm b_th; print "\n")
*)
        val (a',b') = (rhs (concl a_th), rhs (concl b_th))
        val (a_th',b_th') = hcf_conv2 f solver (a',b')
        val a_th'' = field_mult_postsimp_conv solver (rhs (concl a_th'))
        and b_th'' = field_mult_postsimp_conv solver (rhs (concl b_th'))
        val a_th = TRANS a_th (TRANS a_th' a_th'')
        and b_th = TRANS b_th (TRANS b_th' b_th'')
(***
        val () = (print "field_hcf_conv2: "; print_thm a_th; print ", ";
                  print_thm b_th; print "\n")
***)
      in
        (a_th,b_th)
      end;
end;

local
  val has_nested_divs = can (find_term (same_const field_div_tm));

  fun is_normal_numerator tm = not (has_nested_divs tm);

  fun is_normal_denominator tm = not (has_nested_divs tm);

  fun is_normal_fraction is_div tm =
      if not is_div then is_normal_numerator tm
      else
        let
          val (_,n,d) = dest_field_div tm
        in
          is_normal_numerator n andalso is_normal_denominator d
        end;

  fun check_normal_fraction is_div tm =
      if is_normal_fraction is_div tm then ()
      else raise ERR "check_normal_fraction" "";

  val field_add_divl_conv = cond_rewr_conv field_add_divl
  and field_add_divr_conv = cond_rewr_conv field_add_divr
  and field_add_div2_conv = cond_rewr_conv field_add_div
  and field_add_divl_conv' = cond_rewr_conv field_add_divl'
  and field_add_divr_conv' = cond_rewr_conv field_add_divr'
  and field_add_div2_conv' = cond_rewr_conv field_add_div';

  fun field_add_div_hcf solver x1 x2 =
      let
        val (f,a1,b1) = dest_field_div x1
        and (_,a2,b2) = dest_field_div x2
      in
        field_hcf_conv2 f solver (b1,b2)
      end;

  fun field_add_div_hcf_conv (th1,th2) solver =
      LAND_CONV (RAND_CONV (K th1)) THENC
      RAND_CONV (RAND_CONV (K th2)) THENC
      field_add_div2_conv solver;

  fun field_add_div_hcf_conv' (th1,th2) solver =
      LAND_CONV (RAND_CONV (K th1)) THENC
      RAND_CONV (LAND_CONV (RAND_CONV (K th2))) THENC
      field_add_div2_conv' solver;

  fun field_add_div_conv solver tm =
(***
      trace_conv "field_add_div_conv"
***)
      let
        val (f,a,b) = dest_field_add tm
        val ap = is_field_div a
        and bp = is_field_div b
        val () = check_normal_fraction ap a
        and () = check_normal_fraction bp b
      in
        case (ap,bp) of
          (false,false) => raise ERR "field_add_div_conv" "no div"
        | (true,false) => field_add_divl_conv solver
        | (false,true) => field_add_divr_conv solver
        | (true,true) =>
          field_add_div_hcf_conv (field_add_div_hcf solver a b) solver
      end tm;

  fun field_add_div_conv' solver tm =
(***
      trace_conv "field_add_div_conv'"
***)
      let
        val (f,a,b) = dest_field_add tm
        val (_,b,_) = dest_field_add b
        val ap = is_field_div a
        and bp = is_field_div b
        val () = check_normal_fraction ap a
        and () = check_normal_fraction bp b
      in
        case (ap,bp) of
          (false,false) => raise ERR "field_add_div_conv'" "no div"
        | (true,false) => field_add_divl_conv' solver
        | (false,true) => field_add_divr_conv' solver
        | (true,true) =>
          field_add_div_hcf_conv' (field_add_div_hcf solver a b) solver
      end tm;
in
  val field_add_div_conv_left =
      {name = "field_add_div_conv (left)",
       key = ``field_add (f : 'a field) (field_div f x y) z``,
       conv = field_add_div_conv}
  and field_add_div_conv_right =
      {name = "field_add_div_conv (right)",
       key = ``field_add (f : 'a field) x (field_div f y z)``,
       conv = field_add_div_conv}
  and field_add_div_conv_left' =
      {name = "field_add_div_conv' (left)",
       key = ``field_add (f : 'a field) (field_div f x y) (field_add f z p)``,
       conv = field_add_div_conv'}
  and field_add_div_conv_right' =
      {name = "field_add_div_conv' (right)",
       key = ``field_add (f : 'a field) x (field_add f (field_div f y z) p)``,
       conv = field_add_div_conv'};
end;

fun alg_field_div_elim_ss alg_context =
    let
      val rewrs =
          [field_sub_def,
           field_neg_add,
           GSYM field_div_lneg, field_div_rneg,
           field_div_multl,field_div_multr,
           field_div_divl,field_div_divr,
           field_div_exp,
           field_mult_assoc,
           field_single_mult_single,
           field_single_mult_single']

      val convs =
          map
            solver_conv_to_simpset_conv
            [field_add_div_conv_left,
             field_add_div_conv_right]

      val data =
          simpLib.SSFRAG
            {ac = [], congs = [], convs = convs, rewrs = rewrs,
             dprocs = [], filter = NONE}

      val {simplify = alg_ss, ...} = alg_simpsets alg_context
    in
      simpLib.++ (alg_ss,data)
    end;

local
  val add_assoc_conv = cond_rewr_conv field_add_assoc
  and neg_neg_conv = cond_rewr_conv field_neg_neg
  and neg_add_conv = cond_rewr_conv field_neg_add
  and mult_lneg_conv = cond_rewr_conv field_mult_lneg
  and mult_rneg_conv = cond_rewr_conv field_mult_rneg
  and distrib_ladd_conv = cond_rewr_conv field_distrib_ladd
  and distrib_radd_conv = cond_rewr_conv field_distrib_radd
  and mult_assoc_conv = cond_rewr_conv field_mult_assoc
  and exp_zero_conv = cond_rewr_conv field_exp_zero
  and exp_one_conv = cond_rewr_conv field_exp_one
  and exp_num_conv = cond_rewr_conv field_num_exp
  and exp_exp_conv = cond_rewr_conv field_exp_exp
  and exp_mult_conv = cond_rewr_conv field_exp_mult
  and exp_neg_conv = cond_rewr_conv field_exp_neg
  and binomial_2_conv = cond_rewr_conv field_binomial_2
  and binomial_3_conv = cond_rewr_conv field_binomial_3
  and binomial_4_conv = cond_rewr_conv field_binomial_4;

  val num_conv =
      cond_rewrs_conv [field_num_exp,field_num_mult,field_num_mult'];
in
  val ORACLE_field_poly = ref false;

  val field_poly_print_term = ref false;

  fun field_poly_conv term_normalize_ths solver tm =
      if !ORACLE_field_poly then
        ORACLE_field_poly_conv term_normalize_ths solver tm
      else
(***
        trace_conv "field_poly_conv" 
***)
        let
          val term_normalize_conv = PURE_REWRITE_CONV term_normalize_ths

          fun exp_conv tm =
              let
                val (_,a,n) = dest_field_exp tm
              in
                FIRST_CONV
                  [exp_zero_conv solver,
                   exp_one_conv solver,
                   exp_num_conv solver THENC RAND_CONV reduceLib.EXP_CONV,
                   exp_exp_conv solver THENC
                     TRY_CONV (RAND_CONV reduceLib.MUL_CONV) THENC
                     TRY_CONV exp_conv,
                   exp_mult_conv solver,
                   exp_neg_conv solver THENC
                     RATOR_CONV (LAND_CONV reduceLib.EVEN_CONV) THENC
                     COND_CONV,
                   binomial_2_conv solver,
                   binomial_3_conv solver,
                   binomial_4_conv solver]
              end tm

          fun mult_conv tm =
              (case total dest_field_mult tm of
                 NONE => exp_conv THENC TRY_CONV mult_conv
               | SOME (_,a,b) =>
                 FIRST_CONV
                   [mult_lneg_conv solver,
                    mult_rneg_conv solver,
                    distrib_radd_conv solver,
                    distrib_ladd_conv solver,
                    mult_assoc_conv solver THENC TRY_CONV mult_conv,
                    LAND_CONV exp_conv THENC TRY_CONV mult_conv,
                    RAND_CONV mult_conv THENC TRY_CONV mult_conv]) tm
              
          fun term_conv tm =
              (mult_conv ORELSEC
               CHANGED_CONV
                 (TRY_CONV (#conv field_mult_ac_conv solver) THENC
                  DEPTH_CONV (num_conv solver) THENC
                  reduceLib.REDUCE_CONV THENC
                  term_normalize_conv)) tm

          fun neg_conv tm =
              (case total dest_field_neg tm of
                 NONE => term_conv THENC TRY_CONV neg_conv
               | SOME (_,a) =>
                 FIRST_CONV
                   [neg_neg_conv solver,
                    neg_add_conv solver,
                    RAND_CONV term_conv THENC TRY_CONV neg_conv]) tm

          fun add_conv n tm =
              (case total dest_field_add tm of
                 NONE => neg_conv THENC TRY_CONV (add_conv n)
               | SOME (_,a,b) =>
                 let
                   fun print_term_conv conv tm =
                       let
                         val n = n + term_size a
                         val () = print ("term<<" ^ int_to_string n ^ ">>: ")
                         val () = print_term a
                         val () = print "\n"
                       in
                         conv n tm
                       end
                 in
                   FIRST_CONV
                     [add_assoc_conv solver THENC TRY_CONV (add_conv n),
                      LAND_CONV neg_conv THENC TRY_CONV (add_conv n),
                      print_term_conv (RAND_CONV o add_conv)]
                 end) tm

          val cancel_conv = #conv field_add_ac_conv solver

          val poly_conv =
              (add_conv 0 THENC TRY_CONV cancel_conv) ORELSEC cancel_conv
        in
          poly_conv
        end tm;
end;

val field_op_patterns =
    [``field_add (f : 'a field) x y``,
     ``field_neg (f : 'a field) x``,
     ``field_mult (f : 'a field) x y``,
     ``field_exp (f : 'a field) x n``,
     ``field_num (f : 'a field) n``];

val field_op_blocking_congs =
    let
      fun in_pattern pattern =
          let
            val (_,l) = strip_comb pattern
            val ty = hd (snd (dest_type (type_of (hd l)))) --> bool
          in
            pred_setSyntax.mk_in (pattern, mk_var ("s",ty))
          end

      val patterns = field_op_patterns
    in
      map REFL patterns @ map (REFL o in_pattern) patterns
    end;

fun alg_field_poly_ss alg_context term_normalize_ths =
    let
      val patterns = field_op_patterns

      val congs = field_op_blocking_congs

      val convs =
          map
            (fn (n,key) =>
             solver_conv_to_simpset_conv
             {name = "field_poly_conv (" ^ int_to_string n ^ ")",
              key = key,
              conv = field_poly_conv term_normalize_ths})
            (enumerate 0 patterns)

      val data =
          simpLib.SSFRAG
            {ac = [], congs = congs, convs = convs, rewrs = [],
             dprocs = [], filter = NONE}

      val {simplify = alg_ss, ...} = alg_simpsets alg_context
    in
      simpLib.++ (alg_ss,data)
    end;

local
  val push_disch =
      let
        val f = MATCH_MP (PROVE [] ``(a ==> (b = c)) ==> (a ==> b = a ==> c)``)
      in
        fn d => fn th => f (DISCH d th)
      end;

  val and_imp_intro = CONV_RULE (BINOP_CONV (REWR_CONV AND_IMP_INTRO));
in
  fun field_poly_basis_conv solver tm =
      let
        fun f [] _ = raise Bug "field_poly_basis_conv"
          | f [eqn] th = push_disch eqn th
          | f (eqn :: (eqns as _ :: _)) th =
            and_imp_intro (push_disch eqn (f eqns th))

        val (eqns,tm) = dest_imp_only tm
        val eqns = strip_conj eqns
        val reduce_ths = map ASSUME eqns

(***
        val _ = print ("field_poly_basis_conv: reducing with "
                       ^ int_to_string (length eqns) ^ " equations.\n")
***)

        val th = f eqns (LAND_CONV (field_poly_conv reduce_ths solver) tm)

        val _ = (print "field_poly_basis_conv: result thm =\n";
                 print_thm th; print "\n")
      in
        th
      end;
end;
 
fun alg_field_poly_basis_ss alg_context =
    let
      val patterns =
          [``((x : 'a) = y) ==> (z = field_zero (f : 'a field))``,
           ``((x : 'a) = y) /\ E ==> (z = field_zero (f : 'a field))``]

      val congs = map REFL patterns @ field_op_blocking_congs

      val convs =
          map
            (fn (n,key) =>
             solver_conv_to_simpset_conv
             {name = "field_poly_basis_conv (" ^ int_to_string n ^ ")",
              key = key,
              conv = field_poly_basis_conv})
            (enumerate 0 patterns)

      val data =
          simpLib.SSFRAG
            {ac = [], congs = [], convs = convs, rewrs = [],
             dprocs = [], filter = NONE}

      val {simplify = alg_ss, ...} = alg_simpsets alg_context
    in
      simpLib.++ (alg_ss,data)
    end;

(* ------------------------------------------------------------------------- *)
(* Homomorphisms, isomorphisms, endomorphisms, automorphisms and subfields.  *)
(* ------------------------------------------------------------------------- *)

val FieldHom_def = Define
  `FieldHom g h =
   { f |
     (!x :: (g.carrier). f x IN h.carrier) /\
     f IN GroupHom (g.sum) (h.sum) /\
     f IN GroupHom (g.prod) (h.prod) }`;

val FieldIso_def = Define
  `FieldIso g h =
   { f |
     f IN FieldHom g h /\
     (!y :: (h.carrier). ?!x :: (g.carrier). f x = y) }`;

val FieldEndo_def = Define `FieldEndo g = FieldHom g g`;

val FieldAuto_def = Define `FieldAuto g = FieldIso g g`;

val subfield_def = Define `subfield g h = I IN FieldHom g h`;

(* ------------------------------------------------------------------------- *)
(* Polynomials over fields.                                                  *)
(* ------------------------------------------------------------------------- *)

val () = type_abbrev ("poly", Type `:'a list`);

val poly_zero_def = Define `poly_zero = ([] : 'a poly)`;

val Poly_def = Define
  `Poly (f : 'a field) =
   { (p : 'a poly) |
     (p = poly_zero) \/
     (EVERY (\c. c IN f.carrier) p /\ ~(LAST p = field_zero f)) }`;

val poly_degree_def = Define
  `poly_degree (p : 'a poly) = if (p = poly_zero) then 0 else LENGTH p - 1`;

val poly_eval_def = Define
  `(poly_eval (f : 'a field) [] x = field_zero f) /\
   (poly_eval (f : 'a field) (c :: cs) x =
    field_add f c (field_mult f x (poly_eval f cs x)))`;

val AlgebraicallyClosedField_def = Define
  `AlgebraicallyClosedField =
   { (f : 'a field) |
     f IN Field /\ 
     !p :: Poly f.
       (poly_degree p = 0) \/
       ?z :: (f.carrier). poly_eval f p z = field_zero f }`;

(* ------------------------------------------------------------------------- *)
(* The trivial field.                                                        *)
(* ------------------------------------------------------------------------- *)

val trivial_field_def = Define
  `(trivial_field zero_elt one_elt) : 'a field =
   <| carrier := {zero_elt; one_elt};
      sum := <| carrier := {zero_elt; one_elt};
                id := zero_elt;
                inv := (\x. x);
                mult := (\x y. if x = zero_elt then y
                               else if y = zero_elt then x
                               else zero_elt) |>;
      prod := <| carrier := {one_elt};
                 id := one_elt;
                 inv := (\x. x);
                 mult := (\x y. if x = zero_elt then zero_elt
                                else if y = zero_elt then zero_elt
                                else one_elt) |> |>`;

val trivial_field = store_thm
  ("trivial_field",
   ``!zero_elt one_elt.
       ~(zero_elt = one_elt) ==>
       trivial_field zero_elt one_elt IN FiniteField``,
   RW_TAC resq_ss
     [trivial_field_def, FiniteField_def, Field_def, GSPECIFICATION,
      combinTheory.K_THM, field_add_def, field_mult_def, field_zero_def,
      AbelianGroup_def, Group_def, IN_INSERT, NOT_IN_EMPTY, EXTENSION,
      FINITE_INSERT, FINITE_EMPTY, IN_DIFF, field_nonzero_def]
   ++ RW_TAC std_ss []
   ++ METIS_TAC []);  

(* ------------------------------------------------------------------------- *)
(* GF(p).                                                                    *)
(* ------------------------------------------------------------------------- *)

val (modexp_def, modexp_ind) = Defn.tprove
  (Hol_defn "modexp"
   `modexp a n m =
    if n = 0 then 1
    else if n MOD 2 = 0 then modexp ((a * a) MOD m) (n DIV 2) m
    else (a * modexp ((a * a) MOD m) (n DIV 2) m) MOD m`,
   WF_REL_TAC `measure (\(x,y,z). y)`
   ++ RW_TAC arith_ss []
   ++ Know `2 * (n DIV 2) <= n`
   >> PROVE_TAC [TWO, DIV_THEN_MULT]
   ++ DECIDE_TAC)

val _ = save_thm ("modexp_def", modexp_def);
val _ = save_thm ("modexp_ind", modexp_ind);

val GF_def = Define
  `GF p = 
   <| carrier := { n | n < p };
      sum := add_mod p;
      prod := mult_mod p |>`;

val modexp = store_thm
  ("modexp",
   ``!a n m. 1 < m ==> (modexp a n m = (a ** n) MOD m)``,
   recInduct modexp_ind
   ++ RW_TAC std_ss []
   ++ ONCE_REWRITE_TAC [modexp_def]
   ++ Cases_on `n = 0` >> RW_TAC arith_ss [EXP]
   ++ ASM_SIMP_TAC bool_ss []
   ++ REPEAT (Q.PAT_ASSUM `X ==> Y` (K ALL_TAC))
   ++ Know `0 < m` >> DECIDE_TAC
   ++ STRIP_TAC
   ++ MP_TAC (Q.SPEC `m` MOD_TIMES2)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (MP_TAC o Q.SPECL [`a`,`a`])
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ ASM_SIMP_TAC bool_ss [MOD_MOD, MOD_EXP]
   ++ Know `a MOD m * a MOD m = (a MOD m) ** 2`
   >> RW_TAC bool_ss [TWO, ONE, EXP, REWRITE_RULE [ONE] MULT_CLAUSES]
   ++ DISCH_THEN (fn th => ASM_SIMP_TAC bool_ss [th])
   ++ ASM_SIMP_TAC bool_ss [EXP_EXP]
   ++ MP_TAC (Q.SPEC `m` MOD_TIMES2)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ MP_TAC (Q.SPECL [`a`,`n`,`m`] MOD_EXP)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ Q.SPEC_TAC (`a MOD m`,`a`)
   ++ MP_TAC (Q.SPEC `m` MOD_TIMES2)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ ASM_SIMP_TAC bool_ss [MOD_MOD]
   ++ ASM_SIMP_TAC bool_ss [MOD_TIMES2, GSYM EXP]
   ++ Know `(n MOD 2 = 0) \/ (n MOD 2 = 1)`
   >> (Suff `n MOD 2 < 2` >> DECIDE_TAC
       ++ RW_TAC std_ss [DIVISION])
   ++ ASM_SIMP_TAC bool_ss [ADD1]
   ++ Suff `n = 2 * (n DIV 2) + n MOD 2`
   >> METIS_TAC [ADD_CLAUSES]
   ++ METIS_TAC [DIVISION, DECIDE ``0 < 2``, MULT_COMM]);

val GF_carrier = store_thm
  ("GF_carrier",
   ``!p. (GF p).carrier = { n | n < p}``,
   RW_TAC std_ss [GF_def, field_accessors]);

val GF_in_carrier = store_thm
  ("GF_in_carrier",
   ``!p x. x IN (GF p).carrier = x < p``,
   RW_TAC std_ss [GF_carrier, GSPECIFICATION]);

val GF_in_carrier_imp = store_thm
  ("GF_in_carrier_imp",
   ``!p x. x < p ==> x IN (GF p).carrier``,
   METIS_TAC [GF_in_carrier]);

val alg_context = alg_add_judgement GF_in_carrier_imp alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val GF_zero = store_thm
  ("GF_zero",
   ``!p. field_zero (GF p) = 0``,
   RW_TAC std_ss [GF_def, field_accessors, field_zero_def, add_mod_def]);

val GF_one = store_thm
  ("GF_one",
   ``!p. field_one (GF p) = 1``,
   RW_TAC std_ss [GF_def, field_accessors, field_one_def, mult_mod_def]);

val GF_neg = store_thm
  ("GF_neg",
   ``!p x. field_neg (GF p) x = (p - x) MOD p``,
   RW_TAC std_ss [GF_def, field_accessors, field_neg_def, add_mod_def]);

val GF_add = store_thm
  ("GF_add",
   ``!p x y. field_add (GF p) x y = (x + y) MOD p``,
   RW_TAC std_ss [GF_def, field_accessors, field_add_def, add_mod_def]);

val GF_sub = store_thm
  ("GF_sub",
   ``!p :: Prime. !x y. field_sub (GF p) x y = (x + (p - y)) MOD p``,
   RW_TAC resq_ss [GF_add, GF_neg, field_sub_def, Prime_def, GSPECIFICATION]
   ++ Know `~(p = 0)` >> METIS_TAC [NOT_PRIME_0]
   ++ STRIP_TAC
   ++ MP_TAC (Q.SPEC `p` MOD_PLUS)
   ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
   ++ CONJ_TAC >> DECIDE_TAC
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ RW_TAC arith_ss [MOD_MOD]);

val GF_inv = store_thm
  ("GF_inv",
   ``!p :: Prime. !x y. field_inv (GF p) x = modexp x (p - 2) p``,
  RW_TAC resq_ss
    [GF_def, field_accessors, field_inv_def, mult_mod_def,
     combinTheory.K_THM, Prime_def, GSPECIFICATION]
  ++ match_tac (GSYM modexp)
  ++ Suff `~(p = 0) /\ ~(p = 1)` >> DECIDE_TAC
  ++ METIS_TAC [NOT_PRIME_0, NOT_PRIME_1]);

val GF_mult = store_thm
  ("GF_mult",
   ``!p x y. field_mult (GF p) x y = (x * y) MOD p``,
  RW_TAC std_ss [GF_def, field_accessors, field_mult_def, mult_mod_def]);

val GF_div = store_thm
  ("GF_div",
   ``!p x y. field_div (GF p) x y = field_mult (GF p) x (field_inv (GF p) y)``,
  RW_TAC std_ss [field_div_def]);

val GF_exp = store_thm
  ("GF_exp",
   ``!p :: Prime. !x n. field_exp (GF p) x n = modexp x n p``,
   RW_TAC resq_ss [Prime_def, GSPECIFICATION]
   ++ Know `1 < p`
   >> (Suff `~(p = 0) /\ ~(p = 1)` >> DECIDE_TAC
       ++ METIS_TAC [NOT_PRIME_0, NOT_PRIME_1])
   ++ STRIP_TAC
   ++ Know `0 < p` >> DECIDE_TAC
   ++ STRIP_TAC
   ++ RW_TAC bool_ss [modexp]
   ++ (Induct_on `n`
       ++ RW_TAC bool_ss [field_exp_def, GF_one, GF_mult, EXP])
   >> METIS_TAC [LESS_MOD]
   ++ METIS_TAC [MOD_MOD, MOD_TIMES2]);

val GF_num = store_thm
  ("GF_num",
   ``!p :: Prime. !n. field_num (GF p) n = n MOD p``,
   RW_TAC resq_ss []
   ++ Know `p IN Nonzero` >> RW_TAC alg_ss []
   ++ RW_TAC std_ss [Nonzero_def, GSPECIFICATION]
   ++ Know `0 < p` >> DECIDE_TAC
   ++ POP_ASSUM_LIST (K ALL_TAC)
   ++ RW_TAC std_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [field_num_def, GF_zero, ZERO_MOD, GF_add, GF_one]
   ++ REWRITE_TAC [ADD1]
   ++ MP_TAC (Q.SPEC `p` MOD_PLUS)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ RW_TAC arith_ss [MOD_MOD]);

val GF_alt = store_thm
  ("GF_alt",
   ``!p :: Prime. !x y n.
       (field_zero (GF p) = 0) /\
       (field_one (GF p) = 1) /\
       (field_neg (GF p) x = (p - x) MOD p) /\
       (field_add (GF p) x y = (x + y) MOD p) /\
       (field_sub (GF p) x y = (x + (p - y)) MOD p) /\
       (field_inv (GF p) x = modexp x (p - 2) p) /\
       (field_mult (GF p) x y = (x * y) MOD p) /\
       (field_div (GF p) x y = field_mult (GF p) x (field_inv (GF p) y)) /\
       (field_exp (GF p) x n = modexp x n p) /\
       (field_num (GF p) x = x MOD p)``,
   RW_TAC std_ss
     [GF_zero, GF_one, GF_neg, GF_add, GF_sub, GF_inv, GF_mult, GF_div,
      GF_exp, GF_num]);

val GF = store_thm
  ("GF",
   ``!p :: Prime. GF p IN FiniteField``,
   RW_TAC resq_ss [FiniteField_def, GSPECIFICATION, Field_def]
   << [RW_TAC alg_ss [GF_def, combinTheory.K_THM],
       RW_TAC alg_ss [GF_def, combinTheory.K_THM],
       RW_TAC alg_ss [GF_def, combinTheory.K_THM, add_mod_def],
       RW_TAC alg_ss [GF_alt]
       ++ RW_TAC alg_ss
            [GF_def, combinTheory.K_THM, mult_mod_def,
             EXTENSION, IN_DIFF, GSPECIFICATION, IN_SING, field_nonzero_def,
             field_zero_def, add_mod_def]
       ++ METIS_TAC [],
       RW_TAC std_ss [GF_alt, MULT]
       ++ MATCH_MP_TAC ZERO_MOD
       ++ Suff `p IN Nonzero` >> RW_TAC arith_ss [Nonzero_def, GSPECIFICATION]
       ++ RW_TAC alg_ss [],
       RW_TAC std_ss [GF_alt]
       ++ Know `0 < p`
       >> (Suff `p IN Nonzero` >> RW_TAC arith_ss [Nonzero_def, GSPECIFICATION]
           ++ RW_TAC alg_ss [])
       ++ STRIP_TAC
       ++ RW_TAC std_ss [Once (GSYM MOD_TIMES2), MOD_MOD]
       ++ RW_TAC std_ss [MOD_TIMES2, LEFT_ADD_DISTRIB, MOD_PLUS],
       RW_TAC std_ss [GF_def, finite_num, GSPECIFICATION]
       ++ METIS_TAC []]);

val alg_context = alg_add_reduction GF alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

(* ------------------------------------------------------------------------- *)
(* GF(2^n).                                                                  *)
(* ------------------------------------------------------------------------- *)

(* GF(2^n) = polynomials over GF(2) modulo an irreducible degree n poly *)

(***
val GF_2_def = Define
  `GF_2 n = 
   <| carrier := ;
      sum := ;
      prod :=  |>`;
***)

(* ========================================================================= *)
(* Vector spaces                                                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The basic definitions                                                     *)
(* ------------------------------------------------------------------------- *)

val () = type_abbrev ("vector", Type `:'a list`);

val dimension_def = Define `dimension = (LENGTH : 'a vector -> num)`;

val coord_def = Define `coord = (EL : num -> 'a vector -> 'a)`;

val coords_def = Define `coords (v : 'a vector) = { i | i < dimension v }`;

val vector_space_def = Define
  `vector_space (f : 'a field) n =
   { v | (dimension v = n) /\ !i :: coords v. coord i v IN f.carrier }`;

val origin_def = Define
  `(origin (f : 'a field) 0 = []) /\
   (origin (f : 'a field) (SUC n) = field_zero f :: origin f n)`;

val nonorigin_def = Define
  `nonorigin (f : 'a field) =
   { v | v IN vector_space f (dimension v) /\ ~(v = origin f (dimension v)) }`;

val vector_space_origin = store_thm
  ("vector_space_origin",
   ``!f :: Field. !n. origin f n IN vector_space f n``,
   RW_TAC resq_ss
     [vector_space_def, dimension_def, coord_def, GSYM EVERY_EL,
      coords_def, GSPECIFICATION]
   >> (Induct_on `n` ++ RW_TAC std_ss [origin_def, LENGTH])
   ++ Induct_on `n`
   ++ RW_TAC std_ss [origin_def, EVERY_DEF, field_zero_carrier]);

val origin_eq = store_thm
  ("origin_eq",
   ``!f n p.
       (p = origin f n) =
       (dimension p = n) /\ !i :: coords p. coord i p = field_zero f``,
   RW_TAC resq_ss
     [dimension_def, coord_def, GSYM EVERY_EL, coords_def, GSPECIFICATION]
   ++ Q.SPEC_TAC (`p`,`p`)
   ++ (Induct_on `n`
       ++ RW_TAC std_ss [origin_def, LENGTH_NIL, LENGTH_CONS])
   >> (EQ_TAC ++ RW_TAC std_ss [EVERY_DEF])
   ++ EQ_TAC
   ++ RW_TAC std_ss []
   ++ FULL_SIMP_TAC std_ss [EVERY_DEF]
   ++ METIS_TAC []);

val origin_eq' = store_thm
  ("origin_eq'",
   ``!f n p.
       (origin f n = p) =
       (dimension p = n) /\ !i :: coords p. coord i p = field_zero f``,
   METIS_TAC [origin_eq]);

val nonorigin_alt = store_thm
  ("nonorigin_alt",
   ``!f p.
       p IN nonorigin f =
       EVERY (\x. x IN f.carrier) p /\
       ~(EVERY (\x. x = field_zero f) p)``,
   RW_TAC resq_ss
     [nonorigin_def, GSPECIFICATION, dimension_def, coords_def, coord_def,
      vector_space_def, origin_eq, GSYM EVERY_EL]);

(* ========================================================================= *)
(* Projective geometry                                                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The basic definitions                                                     *)
(* ------------------------------------------------------------------------- *)

(* Tuned to always be an equivalence relation on type 'a when f is a Field *)
val project_def = Define
  `project (f : 'a field) v1 v2 =
   (v1 = v2) \/
   (v1 IN nonorigin f /\ v2 IN nonorigin f /\
    (dimension v1 = dimension v2) /\
    ?c :: (f.carrier). !i :: coords v1.
      field_mult f c (coord i v1) = coord i v2)`;

(* Must use the primitive GSPEC to get around the set binding heuristic *)
val projective_space_def = Define
  `projective_space (f : 'a field) n =
   GSPEC (\v. (project f v, v IN (vector_space f (n + 1) INTER nonorigin f)))`;

val affine_def = Define `affine f v = project f (v ++ [field_one f])`;

val project_refl = store_thm
  ("project_refl",
   ``!f p. project f p p``,
   RW_TAC std_ss [project_def]);

val project_refl' = store_thm
  ("project_refl'",
   ``!f p q. (p = q) ==> project f p q``,
   METIS_TAC [project_refl]);

val project_sym = store_thm
  ("project_sym",
   ``!f :: Field. !p1 p2. project f p1 p2 ==> project f p2 p1``,
   SIMP_TAC resq_ss [project_def, nonorigin_def, vector_space_def]
   ++ RW_TAC std_ss [GSPECIFICATION, coords_def, dimension_def, coord_def]
   ++ DISJ2_TAC
   ++ RW_TAC std_ss []
   ++ Know `c IN field_nonzero f`
   >> (RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]
       ++ STRIP_TAC
       ++ RW_TAC std_ss []
       ++ Q.PAT_ASSUM `~(p2 = X)` MP_TAC
       ++ RW_TAC resq_ss
            [origin_eq, EVERY_EL, dimension_def, coords_def,
             coord_def, GSPECIFICATION]
       ++ Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPEC `i`)
       ++ RW_TAC std_ss [field_mult_lzero])
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `field_inv f c`
   ++ RW_TAC alg_ss []
   ++ match_tac field_mult_lcancel_imp
   ++ Q.EXISTS_TAC `f`
   ++ Q.EXISTS_TAC `c`
   ++ RW_TAC alg_ss []
   ++ Q.PAT_ASSUM `!i. i < LENGTH p2 ==> X` (MP_TAC o Q.SPEC `i`)
   ++ RW_TAC alg_ss []);

val project_trans = store_thm
  ("project_trans",
   ``!f :: Field. !p1 p2 p3.
       project f p1 p2 /\ project f p2 p3 ==> project f p1 p3``,
   SIMP_TAC resq_ss [project_def, nonorigin_def, vector_space_def]
   ++ RW_TAC std_ss [GSPECIFICATION, coords_def, dimension_def, coord_def]
   << [METIS_TAC [],
       METIS_TAC [],
       DISJ2_TAC
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `field_mult f c' c`
       ++ RW_TAC std_ss [field_mult_carrier]
       ++ RW_TAC std_ss [field_mult_assoc]]);

val project_eq = store_thm
  ("project_eq",
   ``!f :: Field. !v1 v2.
       ((project f v1 = project f v2) = project f v1 v2)``,
   RW_TAC resq_ss []
   ++ MATCH_MP_TAC EQ_SYM
   ++ Q.SPEC_TAC (`v2`,`v2`)
   ++ Q.SPEC_TAC (`v1`,`v1`)
   ++ SIMP_TAC std_ss [GSYM relationTheory.ALT_equivalence]
   ++ RW_TAC std_ss [relationTheory.equivalence_def]
   << [RW_TAC std_ss [relationTheory.reflexive_def]
       ++ METIS_TAC [project_refl],
       RW_TAC std_ss [relationTheory.symmetric_def]
       ++ METIS_TAC [project_sym],
       RW_TAC std_ss [relationTheory.transitive_def]
       ++ METIS_TAC [project_trans]]);

val affine_eq = store_thm
  ("affine_eq",
   ``!f :: Field. !v1 v2. (affine f v1 = affine f v2) = (v1 = v2)``,
   RW_TAC resq_ss [project_eq, affine_def, project_def, APPEND_11]
   ++ REVERSE EQ_TAC >> RW_TAC std_ss []
   ++ RW_TAC resq_ss
        [dimension_def, coords_def, GSPECIFICATION, nonorigin_alt, coord_def]
   ++ REPEAT (Q.PAT_ASSUM `~(EVERY P L)` (K ALL_TAC))
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC std_ss [EVERY_APPEND, LENGTH_APPEND, LENGTH, GSYM ADD1, EVERY_DEF]
   ++ RW_TAC std_ss [GSYM EL_ETA]
   ++ Suff `c = field_one f`
   >> (Q.PAT_ASSUM `!i. P i` (MP_TAC o Q.SPEC `n`)
       ++ RW_TAC arith_ss [el_append]
       ++ POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
       ++ MATCH_MP_TAC EQ_SYM
       ++ match_tac field_mult_lone
       ++ Q.PAT_ASSUM `EVERY P v1` MP_TAC
       ++ RW_TAC std_ss [EVERY_EL])
   ++ Q.PAT_ASSUM `!i. P i` (MP_TAC o Q.SPEC `LENGTH v1`)
   ++ RW_TAC arith_ss [el_append, LENGTH, EL, HD]
   ++ POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ MATCH_MP_TAC EQ_SYM
   ++ match_tac field_mult_rone
   ++ RW_TAC std_ss []);

(* ========================================================================= *)
(* Elliptic curves                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The basic definitions                                                     *)
(* ------------------------------------------------------------------------- *)

val () = Hol_datatype
  `curve =
   <| field : 'a field;
      a1 : 'a;
      a2 : 'a;
      a3 : 'a;
      a4 : 'a;
      a6 : 'a |>`;

val curve_accessors = fetch "-" "curve_accessors";

val curve_b2_def = Define
  `curve_b2 e =
   let f = e.field in
   let $& = field_num f in
   let $+ = field_add f in
   let $* = field_mult f in
   let $** = field_exp f in
   let a1 = e.a1 in
   let a2 = e.a2 in
   a1 ** 2 + & 4 * a2`;

val curve_b4_def = Define
  `curve_b4 e =
   let f = e.field in
   let $& = field_num f in
   let $+ = field_add f in
   let $* = field_mult f in
   let a1 = e.a1 in
   let a3 = e.a3 in
   let a4 = e.a4 in
   a1 * a3 + & 2 * a4`;

val curve_b6_def = Define
  `curve_b6 e =
   let f = e.field in
   let $& = field_num f in
   let $+ = field_add f in
   let $* = field_mult f in
   let $** = field_exp f in
   let a3 = e.a3 in
   let a6 = e.a6 in
   a3 ** 2 + & 4 * a6`;

val curve_b8_def = Define
  `curve_b8 e =
   let f = e.field in
   let $& = field_num f in
   let $+ = field_add f in
   let $- = field_sub f in
   let $* = field_mult f in
   let $** = field_exp f in
   let a1 = e.a1 in
   let a2 = e.a2 in
   let a3 = e.a3 in
   let a4 = e.a4 in
   let a6 = e.a6 in
   a1 ** 2 * a6 + & 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 ** 2 - a4 ** 2`;

val discriminant_def = Define
  `discriminant e =
   let f = e.field in
   let $& = field_num f in
   let $- = field_sub f in
   let $* = field_mult f in
   let $** = field_exp f in
   let b2 = curve_b2 e in
   let b4 = curve_b4 e in
   let b6 = curve_b6 e in
   let b8 = curve_b8 e in
   & 9 * b2 * b4 * b6 - b2 * b2 * b8 - & 8 * b4 ** 3 - & 27 * b6 ** 2`;

val non_singular_def = Define
  `non_singular e = ~(discriminant e = field_zero e.field)`;

val Curve_def = Define
  `Curve =
   { e |
     e.field IN Field /\
     e.a1 IN e.field.carrier /\
     e.a2 IN e.field.carrier /\
     e.a3 IN e.field.carrier /\
     e.a4 IN e.field.carrier /\
     e.a6 IN e.field.carrier /\
     non_singular e }`;

val curve_points_def = Define
  `curve_points e =
   let f = e.field in
   let $+ = field_add f in
   let $* = field_mult f in
   let $** = field_exp f in
   let a1 = e.a1 in
   let a2 = e.a2 in
   let a3 = e.a3 in
   let a4 = e.a4 in
   let a6 = e.a6 in
   GSPEC (\ (x,y,z).
     (project f [x; y; z],
      [x; y; z] IN nonorigin f /\
      (y ** 2 * z + a1 * x * y * z + a3 * y * z ** 2 =
       x ** 3 + a2 * x ** 2 * z + a4 * x * z ** 2 + a6 * z ** 3)))`;

val curve_zero_def = Define
  `curve_zero e =
   project e.field
     [field_zero e.field; field_one e.field; field_zero e.field]`;

val affine_case_def = Define
  `affine_case e z f p =
   if p = curve_zero e then z
   else @t. ?x y. (p = affine e.field [x; y]) /\ (t = f x y)`;

val curve_neg_def = Define
  `curve_neg e =
   let f = e.field in
   let $~ = field_neg f in
   let $+ = field_add f in
   let $- = field_sub f in
   let $* = field_mult f in
   let a1 = e.a1 in
   let a3 = e.a3 in
   affine_case e (curve_zero e)
     (\x1 y1.
        let x = x1 in
        let y = ~y1 - a1 * x1 - a3 in
        affine f [x; y])`;

val curve_double_def = Define
  `curve_double e =
   let f = e.field in
   let $& = field_num f in
   let $~ = field_neg f in
   let $+ = field_add f in
   let $- = field_sub f in
   let $* = field_mult f in
   let $/ = field_div f in
   let $** = field_exp f in
   let a1 = e.a1 in
   let a2 = e.a2 in
   let a3 = e.a3 in
   let a4 = e.a4 in
   let a6 = e.a6 in
   affine_case e (curve_zero e)
     (\x1 y1.
        let d = & 2 * y1 + a1 * x1 + a3 in
        if d = field_zero f then curve_zero e
        else
          let l = (& 3 * x1 ** 2 + & 2 * a2 * x1 + a4 - a1 * y1) / d in
          let m = (~(x1 ** 3) + a4 * x1 + & 2 * a6 - a3 * y1) / d in
          let x = l ** 2 + a1 * l - a2 - &2 * x1 in
          let y = ~(l + a1) * x - m - a3 in
          affine e.field [x; y])`;

val curve_add_def = Define
  `curve_add e p1 p2 =
   if p1 = p2 then curve_double e p1
   else
     let f = e.field in
     let $& = field_num f in
     let $~ = field_neg f in
     let $+ = field_add f in
     let $- = field_sub f in
     let $* = field_mult f in
     let $/ = field_div f in
     let $** = field_exp f in
     let a1 = e.a1 in
     let a2 = e.a2 in
     let a3 = e.a3 in
     let a4 = e.a4 in
     let a6 = e.a6 in
     affine_case e p2
       (\x1 y1.
          affine_case e p1
            (\x2 y2.
               if x1 = x2 then curve_zero e
               else
                 let d = x2 - x1 in
                 let l = (y2 - y1) / d in
                 let m = (y1 * x2 - y2 * x1) / d in
                 let x = l ** 2 + a1 * l - a2 - x1 - x2 in
                 let y = ~(l + a1) * x - m - a3 in
                 affine e.field [x; y]) p2) p1`;

val curve_mult_def = Define
  `(curve_mult (e : 'a curve) p 0 = curve_zero e) /\
   (curve_mult (e : 'a curve) p (SUC n) = curve_add e p (curve_mult e p n))`;

val curve_group_def = Define
  `curve_group e =
   <| carrier := curve_points e;
      id := curve_zero e;
      inv := curve_neg e;
      mult := curve_add e |>`;

val curve_field = store_thm
  ("curve_field",
   ``!e :: Curve. e.field IN Field``,
   RW_TAC resq_ss [Curve_def, GSPECIFICATION]);

val alg_context = alg_add_reduction curve_field alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val curve_a1_carrier = store_thm
  ("curve_a1_carrier",
   ``!e :: Curve. e.a1 IN e.field.carrier``,
   RW_TAC resq_ss [Curve_def, GSPECIFICATION]);

val alg_context = alg_add_reduction curve_a1_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val curve_a2_carrier = store_thm
  ("curve_a2_carrier",
   ``!e :: Curve. e.a2 IN e.field.carrier``,
   RW_TAC resq_ss [Curve_def, GSPECIFICATION]);

val alg_context = alg_add_reduction curve_a2_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val curve_a3_carrier = store_thm
  ("curve_a3_carrier",
   ``!e :: Curve. e.a3 IN e.field.carrier``,
   RW_TAC resq_ss [Curve_def, GSPECIFICATION]);

val alg_context = alg_add_reduction curve_a3_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val curve_a4_carrier = store_thm
  ("curve_a4_carrier",
   ``!e :: Curve. e.a4 IN e.field.carrier``,
   RW_TAC resq_ss [Curve_def, GSPECIFICATION]);

val alg_context = alg_add_reduction curve_a4_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val curve_a6_carrier = store_thm
  ("curve_a6_carrier",
   ``!e :: Curve. e.a6 IN e.field.carrier``,
   RW_TAC resq_ss [Curve_def, GSPECIFICATION]);

val alg_context = alg_add_reduction curve_a6_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val curve_cases = store_thm
  ("curve_cases",
   ``!e :: Curve. !p :: curve_points e.
       (p = curve_zero e) \/
       ?x y :: (e.field.carrier). p = affine e.field [x; y]``,
   RW_TAC resq_ss
     [curve_points_def, curve_zero_def,
      GSPECIFICATION, LET_DEF, affine_def, APPEND]
   ++ POP_ASSUM MP_TAC
   ++ Know `?x1 y1 z1. x = (x1,y1,z1)`
   >> METIS_TAC [pairTheory.ABS_PAIR_THM]
   ++ STRIP_TAC
   ++ RW_TAC alg_ss [project_eq]
   ++ Q.PAT_ASSUM `X IN Y` MP_TAC
   ++ RW_TAC resq_ss
        [nonorigin_def, GSPECIFICATION, coords_def, dimension_def,
         vector_space_def, coord_def, GSYM EVERY_EL, EVERY_DEF]
   ++ Cases_on `z1 = field_zero e.field`
   << [RW_TAC std_ss []
       ++ DISJ1_TAC
       ++ Q.PAT_ASSUM `X = Y` MP_TAC
       ++ RW_TAC alg_ss []
       ++ Q.PAT_ASSUM `~(X = Y)` MP_TAC
       ++ RW_TAC resq_ss
            [origin_eq, dimension_def, coords_def, GSPECIFICATION,
             coord_def, GSYM EVERY_EL, EVERY_DEF]
       ++ RW_TAC resq_ss
            [project_def, nonorigin_alt, EVERY_DEF, field_one_carrier,
             field_one_zero, dimension_def, LENGTH]
       ++ DISJ2_TAC
       ++ Know `y1 IN field_nonzero e.field`
       >> RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]
       ++ RW_TAC alg_ss []
       ++ Q.EXISTS_TAC `field_inv e.field y1`
       ++ RW_TAC alg_ss
            [coords_def, GSPECIFICATION, dimension_def, LENGTH]
       ++ Know `(i = 0) \/ (i = SUC 0) \/ (i = SUC (SUC 0))`
       >> DECIDE_TAC
       ++ STRIP_TAC
       ++ RW_TAC bool_ss [EL, HD, TL, coord_def]
       ++ RW_TAC alg_ss [],
       Q.PAT_ASSUM `X = Y` (K ALL_TAC)
       ++ DISJ2_TAC
       ++ Q.EXISTS_TAC `field_mult e.field (field_inv e.field z1) x1`
       ++ Know `z1 IN field_nonzero e.field`
       >> RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]
       ++ RW_TAC alg_ss []
       ++ Q.EXISTS_TAC `field_mult e.field (field_inv e.field z1) y1`
       ++ RW_TAC alg_ss []
       ++ RW_TAC resq_ss
            [project_def, nonorigin_alt, EVERY_DEF, dimension_def, LENGTH]
       ++ RW_TAC alg_ss []
       ++ DISJ2_TAC
       ++ Q.EXISTS_TAC `field_inv e.field z1`
       ++ RW_TAC alg_ss
            [coords_def, dimension_def, LENGTH, coord_def, GSPECIFICATION]
       ++ Know `(i = 0) \/ (i = SUC 0) \/ (i = SUC (SUC 0))`
       >> DECIDE_TAC
       ++ STRIP_TAC
       ++ RW_TAC bool_ss [EL, HD, TL, coord_def]
       ++ RW_TAC alg_ss []]);

local
  val case_th =
      CONV_RULE
        (RES_FORALL_CONV THENC
         QUANT_CONV
           (RAND_CONV RES_FORALL_CONV THENC
            RIGHT_IMP_FORALL_CONV THENC
            QUANT_CONV
              (REWR_CONV AND_IMP_INTRO))) curve_cases;

  fun cases_on e p = MP_TAC (SPECL [e,p] case_th);
in
  fun ec_cases_on e p (asl,g) =
      let
        val fvs = free_varsl (g :: asl)
        val e_tm = Parse.parse_in_context fvs e
        and p_tm = Parse.parse_in_context fvs p
      in
        cases_on e_tm p_tm
      end (asl,g);
end;

val curve_distinct = store_thm
  ("curve_distinct",
   ``!e :: Curve. !x y.
       ~(curve_zero e = affine e.field [x; y])``,
   RW_TAC resq_ss
     [affine_case_def, affine_def, Curve_def, GSPECIFICATION,
      curve_zero_def, APPEND, project_eq]
   ++ STRIP_TAC
   ++ FULL_SIMP_TAC resq_ss
        [project_def, field_zero_one, coords_def, GSPECIFICATION,
         dimension_def, coord_def, LENGTH]
   >> (POP_ASSUM MP_TAC
       ++ RW_TAC std_ss [field_zero_one])
   ++ Q.PAT_ASSUM `!i. P i` (MP_TAC o Q.SPEC `SUC (SUC 0)`)
   ++ RW_TAC arith_ss [EL, HD, TL, field_mult_rzero, field_zero_one]);

val affine_case = store_thm
  ("affine_case",
   ``!e :: Curve. !z f.
       (affine_case e z f (curve_zero e) = z) /\
       !x y. affine_case e z f (affine e.field [x; y]) = f x y``,
   RW_TAC resq_ss
     [affine_case_def, affine_eq, Curve_def, GSPECIFICATION,
      curve_distinct]);

(*
val curve_quadratic = store_thm
  ("curve_quadratic",
   ``!e :: Curve. !x1 y1 y2 :: (e.field.carrier).
       let f = e.field in
       let $~ = field_neg f in
       let $+ = field_add f in
       let $* = field_mult f in
       let a1 = e.a1 in
       let a3 = e.a3 in
       affine [x1; y1] IN curve_points e /\
       affine [x1; y2] IN curve_points e ==>
       (y2 = y1) \/ (y2 = ~(y1 + a1 * x1 + a3))``,
*)

val curve_zero_eq = store_thm
  ("curve_zero_eq",
   ``!e :: Curve. !x y z :: (e.field.carrier).
       (project e.field [x; y; z] = curve_zero e) =
       (x = field_zero e.field) /\
       ~(y = field_zero e.field) /\
       (z = field_zero e.field)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss
        [GSPECIFICATION, curve_zero_def,
         project_eq, project_def, nonorigin_alt, EVERY_DEF, dimension_def,
         LENGTH, field_zero_carrier, field_one_carrier, field_one_zero,
         coords_def, coord_def]
   ++ RW_TAC resq_ss [GSPECIFICATION]
   ++ REVERSE (Cases_on `x = field_zero e.field`)
   >> (RW_TAC std_ss []
       ++ REVERSE (Cases_on `c IN e.field.carrier`)
       ++ RW_TAC std_ss []
       ++ MATCH_MP_TAC (PROVE [] ``(~c ==> F) ==> c``)
       ++ STRIP_TAC
       ++ Know `~(c = field_zero e.field)`
       >> (STRIP_TAC
           ++ Q.PAT_ASSUM `~X` MP_TAC
           ++ RW_TAC std_ss []
           ++ Q.EXISTS_TAC `SUC 0`
           ++ RW_TAC std_ss [EL, HD, TL]
           ++ RW_TAC alg_ss [])
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `~?x. P x` MP_TAC
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `0`
       ++ RW_TAC alg_ss [EL, HD, TL])
   ++ REVERSE (Cases_on `z = field_zero e.field`)
   >> (RW_TAC std_ss []
       ++ REVERSE (Cases_on `c IN e.field.carrier`)
       ++ RW_TAC std_ss []
       ++ MATCH_MP_TAC (PROVE [] ``(~c ==> F) ==> c``)
       ++ STRIP_TAC
       ++ Know `~(c = field_zero e.field)`
       >> (STRIP_TAC
           ++ Q.PAT_ASSUM `~X` MP_TAC
           ++ RW_TAC std_ss []
           ++ Q.EXISTS_TAC `SUC 0`
           ++ RW_TAC std_ss [EL, HD, TL]
           ++ RW_TAC alg_ss [])
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `~?x. P x` MP_TAC
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `SUC (SUC 0)`
       ++ RW_TAC alg_ss [EL, HD, TL])
   ++ RW_TAC alg_ss []
   ++ Cases_on `y = field_zero e.field`
   ++ RW_TAC alg_ss []
   ++ DISJ2_TAC
   ++ Know `y IN field_nonzero e.field`
   >> RW_TAC alg_ss [field_nonzero_alt]
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `field_inv e.field y`
   ++ RW_TAC alg_ss []
   ++ Know `(i = 0) \/ (i = SUC 0) \/ (i = SUC (SUC 0))` >> DECIDE_TAC
   ++ STRIP_TAC
   ++ RW_TAC alg_ss [EL, HD, TL]);

val curve_zero_eq' = store_thm
  ("curve_zero_eq'",
   ``!e :: Curve. !x y z :: (e.field.carrier).
       (curve_zero e = project e.field [x; y; z]) =
       (x = field_zero e.field) /\
       ~(y = field_zero e.field) /\
       (z = field_zero e.field)``,
   RW_TAC std_ss [curve_zero_eq]);

val curve_neg_optimized = store_thm
  ("curve_neg_optimized",
   ``!e :: Curve. !x1 y1 z1 :: (e.field.carrier).
       project e.field [x1; y1; z1] IN curve_points e ==>
       (curve_neg e (project e.field [x1; y1; z1]) =
        let f = e.field in
        let $~ = field_neg f in
        let $+ = field_add f in
        let $* = field_mult f in
        let a1 = e.a1 in
        let a3 = e.a3 in
        let x = x1 in
        let y = ~(y1 + a1 * x1 + a3 * z1) in
        let z = z1 in
        project f [x; y; z])``,
   RW_TAC resq_ss [LET_DEF, curve_neg_def]
   ++ Know `e IN Curve` >> RW_TAC std_ss []
   ++ REWRITE_TAC [Curve_def]
   ++ RW_TAC std_ss [GSPECIFICATION]
   ++ ec_cases_on `e` `project e.field [x1; y1; z1]`
   ++ RW_TAC resq_ss []
   >> (RW_TAC std_ss [affine_case]
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC std_ss [curve_zero_eq]
       ++ RW_TAC std_ss [field_mult_rzero, field_add_rzero]
       ++ RW_TAC std_ss [curve_zero_eq', field_neg_carrier]
       ++ RW_TAC std_ss [field_neg_eq_swap, field_neg_zero])
   ++ RW_TAC std_ss [affine_case]
   ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ])
   ++ ASM_SIMP_TAC resq_ss [affine_def, APPEND, project_eq]
   ++ CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [project_def]))
   ++ RW_TAC resq_ss
        [dimension_def, coords_def, coord_def, LENGTH, GSPECIFICATION]
   >> (MATCH_MP_TAC project_refl'
       ++ RW_TAC std_ss []
       ++ RW_TAC alg_ss' [])
   ++ Know `~(c = field_zero e.field)`
   >> (STRIP_TAC
       ++ Q.PAT_ASSUM `X IN nonorigin Y` MP_TAC
       ++ Q.PAT_ASSUM `!i. P i`
            (fn th => MP_TAC (Q.SPEC `0` th)
                      ++ MP_TAC (Q.SPEC `SUC 0` th)
                      ++ MP_TAC (Q.SPEC `SUC (SUC 0)` th))
       ++ RW_TAC std_ss
            [EL, HD, TL, nonorigin_alt, field_mult_lzero, field_one_carrier,
             EVERY_DEF])
   ++ STRIP_TAC
   ++ Know `~(z1 = field_zero e.field)`
   >> (STRIP_TAC
       ++ Q.PAT_ASSUM `!i. P i` (MP_TAC o Q.SPEC `SUC (SUC 0)`)
       ++ RW_TAC std_ss
            [EL, HD, TL, field_entire, field_one_carrier, field_one_zero])
   ++ STRIP_TAC
   ++ RW_TAC resq_ss
        [project_def, GSPECIFICATION, dimension_def, LENGTH, nonorigin_alt,
         EVERY_DEF, coords_def, coord_def, field_one_carrier, field_one_zero]
   ++ DISJ2_TAC
   ++ CONJ_TAC >> RW_TAC alg_ss []
   ++ CONJ_TAC >> RW_TAC alg_ss []
   ++ Q.EXISTS_TAC `z1`
   ++ RW_TAC std_ss [field_mult_carrier]
   ++ Q.PAT_ASSUM `!i. P i` (fn th => MP_TAC (Q.SPEC `0` th)
                                      ++ MP_TAC (Q.SPEC `SUC 0` th)
                                      ++ MP_TAC (Q.SPEC `SUC (SUC 0)` th))
   ++ RW_TAC std_ss [EL, HD, TL]
   ++ Know `(i = 0) \/ (i = SUC 0) \/ (i = SUC (SUC 0))` >> DECIDE_TAC
   ++ STRIP_TAC
   ++ RW_TAC std_ss [EL, HD, TL, field_mult_rone]
   ++ RW_TAC alg_ss' [field_distrib]);

val curve_affine = store_thm
  ("curve_affine",
   ``!e :: Curve. !x y :: (e.field.carrier).
       affine e.field [x; y] IN curve_points e =
       let f = e.field in
       let $+ = field_add f in
       let $* = field_mult f in
       let $** = field_exp f in
       let a1 = e.a1 in
       let a2 = e.a2 in
       let a3 = e.a3 in
       let a4 = e.a4 in
       let a6 = e.a6 in
       y ** 2 + a1 * x * y + a3 * y =
       x ** 3 + a2 * x ** 2 + a4 * x + a6``,
   RW_TAC resq_ss
     [curve_points_def, LET_DEF, affine_def, GSPECIFICATION, APPEND]
   ++ REVERSE EQ_TAC
   >> (RW_TAC alg_ss []
       ++ Q.EXISTS_TAC `(x, y, field_one e.field)`
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC alg_ss [nonorigin_alt, EVERY_DEF])
   ++ STRIP_TAC
   ++ POP_ASSUM MP_TAC
   ++ Know `?x1 y1 z1. x' = (x1,y1,z1)`
   >> METIS_TAC [pairTheory.ABS_PAIR_THM]
   ++ STRIP_TAC
   ++ RW_TAC alg_ss []
   ++ Q.PAT_ASSUM `X IN Y` MP_TAC
   ++ RW_TAC std_ss [nonorigin_alt]
   ++ Q.PAT_ASSUM `EVERY P L` MP_TAC
   ++ RW_TAC std_ss [EVERY_DEF]
   ++ Q.PAT_ASSUM `project X Y = Z` (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ])
   ++ RW_TAC alg_ss [project_eq, project_def]
   >> (Q.PAT_ASSUM `X = Y` MP_TAC
       ++ RW_TAC alg_ss' [])
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC resq_ss
        [dimension_def, coords_def, coord_def, LENGTH, GSPECIFICATION]
   ++ Q.PAT_ASSUM `!i. P i` (fn th => MP_TAC (Q.SPEC `0` th)
                                      ++ MP_TAC (Q.SPEC `SUC 0` th)
                                      ++ MP_TAC (Q.SPEC `SUC (SUC 0)` th))
   ++ RW_TAC std_ss [EL, HD, TL]
   ++ Know `c IN field_nonzero e.field`
   >> (RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `X = field_one Y` MP_TAC
       ++ RW_TAC alg_ss [])
   ++ Know `z1 IN field_nonzero e.field`
   >> (RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `X = field_one Y` MP_TAC
       ++ RW_TAC alg_ss [])
   ++ RW_TAC std_ss []
   ++ Know `c = field_inv e.field z1`
   >> (match_tac field_mult_rcancel_imp
       ++ Q.EXISTS_TAC `e.field`
       ++ Q.EXISTS_TAC `z1`
       ++ ASM_REWRITE_TAC []
       ++ RW_TAC alg_ss [])
   ++ RW_TAC std_ss []
   ++ match_tac field_mult_lcancel_imp
   ++ Q.EXISTS_TAC `e.field`
   ++ Q.EXISTS_TAC `field_exp e.field z1 3`
   ++ REPEAT (Q.PAT_ASSUM `X = Y` MP_TAC)
   ++ RW_TAC alg_ss' [field_distrib]);

val curve_affine_reduce_3 = store_thm
  ("curve_affine_reduce_3",
   ``!e :: Curve. !x y :: (e.field.carrier).
       affine e.field [x; y] IN curve_points e =
       (field_exp e.field x 3 =
        field_add e.field
          (field_neg e.field e.a6)
          (field_add e.field
            (field_mult e.field e.a3 y)
            (field_add e.field
              (field_exp e.field y 2)
              (field_add e.field
                (field_neg e.field (field_mult e.field e.a4 x))
                (field_add e.field
                  (field_mult e.field e.a1 (field_mult e.field x y))
                  (field_neg e.field
                    (field_mult e.field e.a2 (field_exp e.field x 2))))))))``,
   RW_TAC resq_ss []
   ++ CONV_TAC (RAND_CONV (REWR_CONV EQ_SYM_EQ))
   ++ RW_TAC alg_ss [curve_affine, LET_DEF]
   ++ RW_TAC alg_ss' []);

local
  val exp_tm = ``field_exp e.field (x : 'a)``;

  val context_tms = strip_conj
      ``e IN Curve /\ (x : 'a) IN e.field.carrier /\ y IN e.field.carrier``;

  val affine_tm = ``affine e.field [(x : 'a); y] IN curve_points e``;

  val context = map ASSUME context_tms;

  val affine = ASSUME affine_tm;

  val reduce_3_eq =
      (repeat UNDISCH o SPEC_ALL)
        (CONV_RULE
           (REDEPTH_CONV (RES_FORALL_CONV ORELSEC
                          HO_REWR_CONV (GSYM RIGHT_FORALL_IMP_THM) ORELSEC
                          REWR_CONV (GSYM AND_IMP_INTRO)))
         curve_affine_reduce_3);

  val reduce_3 = EQ_MP reduce_3_eq affine;

  val field_poly_ss = alg_field_poly_ss alg_context

  fun reduce_n 3 = [reduce_3]
    | reduce_n n =
      let
        val reduce_ths = reduce_n (n - 1)
        val n1_tm = numLib.term_of_int (n - 1)
        val suc_th = reduceLib.SUC_CONV (numSyntax.mk_suc n1_tm)
        val reduce_tm = mk_comb (exp_tm, numLib.term_of_int n)
        val reduce_th =
            (RAND_CONV (REWR_CONV (SYM suc_th)) THENC
             REWR_CONV (CONJUNCT2 field_exp_def) THENC
             RAND_CONV (REWR_CONV (hd reduce_ths)) THENC
             with_flag (ORACLE_field_poly,true)
             (Count.apply (SIMP_CONV (field_poly_ss reduce_ths) context)))
            reduce_tm
(***
        val _ = (print ("reduce_n " ^ int_to_string n ^ ":\n");
                        print_thm reduce_th; print "\n")
***)
      in
        reduce_th :: reduce_ths
      end;

  val weakening_th = PROVE [] ``(a ==> b) ==> (a = a /\ b)``;
in
  fun curve_affine_reduce_n n =
      let
        val th = DISCH affine_tm (LIST_CONJ (tl (rev (reduce_n n))))
        val th = MATCH_MP weakening_th th
        val th = CONV_RULE (RAND_CONV (LAND_CONV (K reduce_3_eq))) th
        val th = foldl (uncurry DISCH) th (rev context_tms)
      in
        th
      end;
end;

val curve_affine_reduce = save_thm
  ("curve_affine_reduce",
   with_flag (ORACLE_algebra_dproc,true)
   (Count.apply curve_affine_reduce_n) 12);

val curve_zero_carrier = store_thm
  ("curve_zero_carrier",
   ``!e :: Curve. curve_zero e IN curve_points e``,
   RW_TAC resq_ss [curve_zero_def, curve_points_def, LET_DEF, GSPECIFICATION]
   ++ Q.EXISTS_TAC `(field_zero e.field, field_one e.field, field_zero e.field)`
   ++ RW_TAC alg_ss [nonorigin_alt, EVERY_DEF]);

val alg_context = alg_add_reduction curve_zero_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val curve_neg_carrier = Count.apply store_thm
  ("curve_neg_carrier",
   ``!e :: Curve. !p :: curve_points e. curve_neg e p IN curve_points e``,
   RW_TAC resq_ss []
   ++ ec_cases_on `e` `p`
   ++ RW_TAC resq_ss [curve_neg_def, LET_DEF]
   ++ RW_TAC alg_ss [affine_case]
   ++ Q.PAT_ASSUM `affine X Y IN Z` MP_TAC
   ++ ASM_SIMP_TAC alg_ss [curve_affine, LET_DEF]
   ++ RW_TAC alg_ss' [field_distrib, field_binomial_2]);

val alg_context = alg_add_reduction curve_neg_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val field_div_elim_ss = alg_field_div_elim_ss alg_context
and field_poly_basis_ss = alg_field_poly_basis_ss alg_context;

val curve_double_carrier = Count.apply store_thm
  ("curve_double_carrier",
   ``!e :: Curve. !p :: curve_points e. curve_double e p IN curve_points e``,
   RW_TAC resq_ss []
   ++ ec_cases_on `e` `p`
   ++ RW_TAC resq_ss [curve_double_def]
   ++ normalForms.REMOVE_ABBR_TAC
   ++ RW_TAC std_ss []
   ++ RW_TAC alg_ss [affine_case]
   ++ RW_TAC alg_ss []
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC alg_ss [field_nonzero_eq, curve_affine, LET_DEF]
   ++ match_tac field_sub_eq_zero_imp
   ++ Q.EXISTS_TAC `e.field`
   ++ RW_TAC alg_ss []
   ++ Q.UNABBREV_TAC `x'`
   ++ Q.UNABBREV_TAC `y'`
   ++ Q.UNABBREV_TAC `l`
   ++ Q.UNABBREV_TAC `m`
   ++ Count.apply (RW_TAC field_div_elim_ss [])
   ++ Q.UNABBREV_TAC `d`
   ++ POP_ASSUM (K ALL_TAC)
   ++ Q.PAT_ASSUM `affine X Y IN Z` MP_TAC
   ++ ASM_SIMP_TAC alg_ss [curve_affine_reduce]
   ++ with_flag (ORACLE_field_poly,true)
      (with_flag (ORACLE_algebra_dproc,true)
       (Count.apply (ASM_SIMP_TAC field_poly_basis_ss []))));

val alg_context = alg_add_reduction curve_double_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val curve_add_carrier = Count.apply store_thm
  ("curve_add_carrier",
   ``!e :: Curve. !p q :: curve_points e. curve_add e p q IN curve_points e``,
   RW_TAC resq_ss []
   ++ ec_cases_on `e` `p`
   ++ ec_cases_on `e` `q`
   ++ RW_TAC resq_ss [curve_add_def]
   ++ Q.UNABBREV_ALL_TAC
   ++ RW_TAC alg_ss [affine_case]
   ++ RW_TAC alg_ss []
   ++ Know `~(d = field_zero e.field)`
   >> (Q.UNABBREV_TAC `d`
       ++ RW_TAC alg_ss [field_sub_eq_zero])
   ++ RW_TAC alg_ss [field_nonzero_eq, curve_affine, LET_DEF]
   ++ match_tac field_sub_eq_zero_imp
   ++ Q.EXISTS_TAC `e.field`
   ++ RW_TAC alg_ss []
   ++ Q.UNABBREV_TAC `x''`
   ++ Q.UNABBREV_TAC `y''`
   ++ Q.UNABBREV_TAC `l`
   ++ Q.UNABBREV_TAC `m`
   ++ Count.apply (RW_TAC field_div_elim_ss [])
   ++ Q.UNABBREV_TAC `d`
   ++ POP_ASSUM (K ALL_TAC)
   ++ Q.PAT_ASSUM `affine X Y IN Z` MP_TAC
   ++ Q.PAT_ASSUM `affine X Y IN Z` MP_TAC
   ++ ASM_SIMP_TAC alg_ss [curve_affine_reduce]
   ++ SIMP_TAC bool_ss [AND_IMP_INTRO, GSYM CONJ_ASSOC]
   ++ with_flag (ORACLE_field_poly,true)
      (with_flag (ORACLE_algebra_dproc,true)
       (Count.apply (ASM_SIMP_TAC field_poly_basis_ss []))));

val alg_context = alg_add_reduction curve_add_carrier alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val curve_double_zero = store_thm
  ("curve_double_zero",
   ``!e :: Curve. curve_double e (curve_zero e) = curve_zero e``,
   RW_TAC resq_ss []
   ++ RW_TAC resq_ss [curve_double_def]
   ++ normalForms.REMOVE_ABBR_TAC
   ++ RW_TAC std_ss []
   ++ RW_TAC alg_ss [affine_case]);

val alg_context = alg_add_rewrite curve_double_zero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val curve_add_lzero = store_thm
  ("curve_add_lzero",
   ``!e :: Curve. !p :: curve_points e. curve_add e (curve_zero e) p = p``,
   RW_TAC resq_ss []
   ++ ec_cases_on `e` `p`
   ++ RW_TAC resq_ss [curve_add_def]
   ++ Q.UNABBREV_ALL_TAC
   ++ RW_TAC alg_ss [affine_case]);

val alg_context = alg_add_rewrite curve_add_lzero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val curve_add_lneg = store_thm
  ("curve_add_lneg",
   ``!e :: Curve. !p :: curve_points e.
       curve_add e (curve_neg e p) p = curve_zero e``,
   RW_TAC resq_ss []
   ++ ec_cases_on `e` `p`
   ++ RW_TAC resq_ss [curve_add_def, curve_neg_def, LET_DEF]
   ++ RW_TAC alg_ss []
   ++ Q.UNABBREV_ALL_TAC
   ++ RW_TAC alg_ss [affine_case]
   ++ Q.PAT_ASSUM `X = Y` MP_TAC
   ++ RW_TAC alg_ss [affine_case, affine_eq]
   ++ RW_TAC alg_ss [curve_double_def, LET_DEF, affine_case, curve_distinct]
   ++ Q.PAT_ASSUM `X = Y` MP_TAC
   ++ PURE_ONCE_REWRITE_TAC [EQ_SYM_EQ]
   ++ Q.PAT_ASSUM `~(X = Y)` MP_TAC
   ++ RW_TAC alg_ss' []);

val alg_context = alg_add_rewrite curve_add_lneg alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val curve_add_comm = Count.apply store_thm
  ("curve_add_comm",
   ``!e :: Curve. !p q :: curve_points e. curve_add e p q = curve_add e q p``,
   RW_TAC resq_ss []
   ++ Cases_on `p = q` >> RW_TAC alg_ss []
   ++ RW_TAC alg_ss [curve_add_def]
   ++ Q.UNABBREV_ALL_TAC
   ++ ec_cases_on `e` `p`
   ++ ec_cases_on `e` `q`
   ++ RW_TAC resq_ss []
   ++ RW_TAC alg_ss [affine_case]
   ++ RW_TAC alg_ss []
   ++ ASM_SIMP_TAC alg_ss [affine_eq]
   ++ Suff `(x''' = x'') /\ ((x''' = x'') ==> (y''' = y''))`
   >> RW_TAC std_ss []
   ++ Know `~(d = field_zero e.field)`
   >> (Q.UNABBREV_TAC `d`
       ++ RW_TAC alg_ss [field_sub_eq_zero])
   ++ Know `~(d' = field_zero e.field)`
   >> (Q.UNABBREV_TAC `d'`
       ++ RW_TAC alg_ss [field_sub_eq_zero])
   ++ RW_TAC alg_ss [field_nonzero_eq]
   ++ match_tac field_sub_eq_zero_imp
   ++ Q.EXISTS_TAC `e.field`
   ++ RW_TAC alg_ss []
   ++ Q.UNABBREV_TAC `x''`
   ++ Q.UNABBREV_TAC `y''`
   ++ Q.UNABBREV_TAC `l`
   ++ Q.UNABBREV_TAC `m`
   ++ TRY (Q.UNABBREV_TAC `x'''`)
   ++ Q.UNABBREV_TAC `y'''`
   ++ Q.UNABBREV_TAC `l'`
   ++ Q.UNABBREV_TAC `m'`
   ++ Count.apply (RW_TAC field_div_elim_ss [])
   ++ Q.UNABBREV_TAC `d`
   ++ Q.UNABBREV_TAC `d'`
   ++ with_flag (ORACLE_field_poly,true)
      (with_flag (ORACLE_algebra_dproc,true)
       (Count.apply (ASM_SIMP_TAC (alg_field_poly_ss alg_context []) []))));

val curve_add_rzero = store_thm
  ("curve_add_rzero",
   ``!e :: Curve. !p :: curve_points e. curve_add e p (curve_zero e) = p``,
   METIS_TAC [curve_add_lzero,curve_add_comm,curve_zero_carrier]);

val alg_context = alg_add_rewrite curve_add_rzero alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val curve_add_rneg = store_thm
  ("curve_add_rneg",
   ``!e :: Curve. !p :: curve_points e.
       curve_add e p (curve_neg e p) = curve_zero e``,
   METIS_TAC [curve_add_lneg,curve_add_comm,curve_neg_carrier]);

val alg_context = alg_add_rewrite curve_add_rneg alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

(***
val curve_add_assoc = store_thm
  ("curve_add_assoc",
   ``!e :: Curve. !p q r :: curve_points e.
        curve_add e p (curve_add e q r) = curve_add e (curve_add e p q) r``,
   RW_TAC resq_ss []
   ++ ec_cases_on `e` `p`
   ++ ASM_SIMP_TAC alg_ss []
   ++ STRIP_TAC >> RW_TAC alg_ss [curve_add_lzero]
   ++ ec_cases_on `e` `q`
   ++ ASM_SIMP_TAC alg_ss []
   ++ STRIP_TAC >> RW_TAC alg_ss [curve_add_lzero, curve_add_rzero]
   ++ ec_cases_on `e` `r`
   ++ ASM_SIMP_TAC alg_ss []
   ++ STRIP_TAC >> RW_TAC alg_ss [curve_add_rzero]
   ++ (Cases_on `p = q` ++ Cases_on `q = r`)
   >> (METIS_TAC [curve_add_comm,curve_add_carrier])
   ++ RW_TAC alg_ss []
   ++ clean_assumptions




   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC resq_ss []
   ++ RW_TAC alg_ss
        [curve_add_def, curve_double_def, affine_case, LET_DEF,
         affine_eq, curve_distinct]
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC alg_ss
        [curve_add_def, curve_double_def, affine_case, LET_DEF,
         affine_eq, curve_distinct]

   ++ Q.UNABBREV_ALL_TAC
   ++ ec_cases_on `e` `p`
   ++ ec_cases_on `e` `q`
   ++ RW_TAC resq_ss []

val curve_group = store_thm
  ("curve_group",
   ``!e :: Curve. curve_group e IN AbelianGroup``,
   RW_TAC resq_ss
     [curve_group_def, AbelianGroup_def, Group_def,
      GSPECIFICATION, combinTheory.K_THM]
   ++ RW_TAC alg_ss []
, curve_zero_carrier,
      curve_add_carrier, curve]
   << [


val alg_context = alg_add_reduction curve_group alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;
***)

(***
val curve_hom_field = store_thm
  ("curve_hom_field",
   ``!f1 f2 :: Field. !f :: FieldHom f1 f2. !e :: Curve.
       project_map f IN
       GroupHom (curve_group e) (curve_group (curve_map f e))``,
***)

(***
(* ------------------------------------------------------------------------- *)
(* Examples                                                                  *)
(* ------------------------------------------------------------------------- *)

(*** Testing the primality checker
val prime_65537 = Count.apply prove
  (``65537 IN Prime``,
   RW_TAC std_ss [Prime_def, GSPECIFICATION]
   ++ CONV_TAC prime_checker_conv);
***)

(* From exercise VI.2.3 of Koblitz (1987) *)

val example_prime_def = Define `example_prime = 751`;

val example_field_def = Define `example_field = GF example_prime`;

val example_curve_def = Define
  `example_curve = curve example_field 0 0 1 (example_prime - 1) 0`;

val alg_context = alg_add_rewrite example_prime_def alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val alg_context = alg_add_rewrite example_field_def alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val example_prime = lemma
  (``example_prime IN Prime``,
   RW_TAC alg_ss [Prime_def, GSPECIFICATION]
   ++ CONV_TAC prime_checker_conv);

val alg_context =
    alg_add_reduction (SIMP_RULE alg_ss [] example_prime) alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val example_field = lemma
  (``example_field IN Field``,
   RW_TAC alg_ss []);

val alg_context =
    alg_add_reduction (SIMP_RULE alg_ss [] example_field) alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val example_curve = lemma
  (``example_curve IN Curve``,
   RW_TAC alg_ss
     [example_curve_def, Curve_def, GSPECIFICATION, discriminant_def,
      non_singular_def, LET_DEF] ++
   RW_TAC alg_ss
     [LET_DEF, GF_alt, curve_b2_def, curve_b4_def,
      curve_b6_def, curve_b8_def, field_exp_small] ++
   CONV_TAC EVAL);

val alg_context = alg_add_reduction example_curve alg_context;
val {simplify = alg_ss, normalize = alg_ss'} = alg_simpsets alg_context;

val example_curve_field = lemma
  (``example_curve.field = example_field``,
   RW_TAC std_ss [curve_accessors, example_curve_def]);

fun example_curve_pt pt = lemma
  (``^pt IN curve_points example_curve``,
   RW_TAC std_ss [GSYM example_curve_field]
   ++ MP_TAC (Q.ISPEC `example_curve` (CONV_RULE RES_FORALL_CONV curve_affine))
   ++ SIMP_TAC alg_ss []
   ++ RW_TAC alg_ss [example_curve_def, LET_DEF]
   ++ POP_ASSUM (K ALL_TAC)
   ++ RW_TAC alg_ss [field_exp_small]
   ++ RW_TAC alg_ss [GF_alt]);

val execute_conv =
    SIMP_CONV
      alg_ss
      [GSYM example_curve_field, curve_neg_def, curve_add_def,
       curve_double_def, affine_case, LET_DEF] THENC
    SIMP_CONV
      alg_ss
      [example_curve_def, curve_accessors, GF_alt, affine_eq, CONS_11] THENC
    RAND_CONV EVAL;

val pt1 = ``affine example_field [361; 383]``
and pt2 = ``affine example_field [241; 605]``;

val pt1_on_example_curve = example_curve_pt pt1
and pt2_on_example_curve = example_curve_pt pt2;

Count.apply execute_conv ``curve_neg example_curve ^pt1``;
Count.apply example_curve_pt (rhs (concl it));

Count.apply execute_conv ``curve_add example_curve ^pt1 ^pt2``;
Count.apply example_curve_pt (rhs (concl it));

Count.apply execute_conv ``curve_double example_curve ^pt1``;
Count.apply example_curve_pt (rhs (concl it));

(* ------------------------------------------------------------------------- *)
(* A formalized version of random binary maps in HOL.                        *)
(* ------------------------------------------------------------------------- *)

val () = Hol_datatype
  `randomMap =
     Leaf
   | Node of num => randomMap => 'a => 'b => randomMap`;

val emptyMap_def = Define `emptyMap : ('a,'b) randomMap = Leaf`;

val singletonMap_def = Define
  `singletonMap p a b : ('a,'b) randomMap = Node p Leaf a b Leaf`;

(* ------------------------------------------------------------------------- *)
(* Compilable versions of multiword operations                               *)
(* ------------------------------------------------------------------------- *)

fun compilable_multiword_operations words bits =

(* ------------------------------------------------------------------------- *)
(* Compilable versions of elliptic curve operations                          *)
(* ------------------------------------------------------------------------- *)

fun compilable_curve_operations prime words bits =
    let
      val {inject,add,mod,...} = compilable_multiword_operations words bits
    in
    end;

val curve_add_example_def = Define
  `curve_add_example (x_1_1 : word5) x_1_2 y_1_1 y_1_2 x_2_1 x_2_2 y_2_1 y_2_2 =
     let x_1 = FCP i. if i=0 then x_1_1 else x_1_2 in
     let y_1 = FCP i. if i=0 then y_1_1 else y_1_2 in
     let x_2 = FCP i. if i=0 then x_2_1 else x_1_2 in
     let y_2 = FCP i. if i=0 then y_2_1 else y_2_2 in
     curve_add
       ec
       (affine (GF 751) [mw2n x_1; mw2n y_1])
       (affine (GF 751) [mw2n x_2; mw2n y_2])`;

val curve_add_example_compilable = 
    CONV_RULE (RAND_CONV execute_conv) curve_add_example_def;
***)

val () = export_theory ();
