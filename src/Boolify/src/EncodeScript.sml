(* Interactive mode
app load
["bossLib", "listSyntax", "combinSyntax", "rich_listTheory", "metisLib"];
*)

open HolKernel boolLib Parse bossLib pairTheory pairTools combinTheory
     arithmeticTheory listTheory rich_listTheory optionTheory metisLib;

val arith_ss = old_arith_ss

val _ = new_theory "Encode";

infixr 0 ++ || <<;
infix 1 >>;

val op ++ = op THEN;
val op >> = op THEN1;
val op << = op THENL;
val op || = op ORELSE;

val Suff = Q_TAC SUFF_TAC;
val Know = Q_TAC KNOW_TAC;

val REVERSE = Tactical.REVERSE;

(*---------------------------------------------------------------------------
        biprefix is a bi-directional version of IS_PREFIX.
 ---------------------------------------------------------------------------*)

val biprefix_def = Define `biprefix a b = IS_PREFIX a b \/ IS_PREFIX b a`;

val biprefix_refl = store_thm
  ("biprefix_refl",
   ``!x. biprefix x x``,
   RW_TAC std_ss [biprefix_def, IS_PREFIX_REFL]);

val biprefix_sym = store_thm
  ("biprefix_sym",
   ``!x y. biprefix x y ==> biprefix y x``,
   PROVE_TAC [biprefix_def]);

val biprefix_append = store_thm
  ("biprefix_append",
   ``!a b c d. biprefix (APPEND a b) (APPEND c d) ==> biprefix a c``,
   RW_TAC std_ss [biprefix_def] ++
   PROVE_TAC [IS_PREFIX_APPEND1, IS_PREFIX_APPEND2]);

val biprefix_cons = store_thm
  ("biprefix_cons",
   ``!a b c d. biprefix (a :: b) (c :: d) = (a = c) /\ biprefix b d``,
   RW_TAC std_ss [biprefix_def, IS_PREFIX] ++
   PROVE_TAC []);

val biprefix_appends = store_thm
  ("biprefix_appends",
   ``!a b c. biprefix (APPEND a b) (APPEND a c) = biprefix b c``,
   RW_TAC std_ss [biprefix_def, IS_PREFIX_APPENDS]);

(*---------------------------------------------------------------------------
        An always true predicate for total encodings.
 ---------------------------------------------------------------------------*)

(*
local
  val th =prove (``?p. !x. p x``, Q.EXISTS_TAC `\x. T` ++ RW_TAC std_ss []);
in
  val total_def = new_specification ("total_def", ["total"], th);
end;

val every_total = store_thm
  ("every_total",
   ``EVERY total = total``,
   MATCH_MP_TAC EQ_EXT ++
   Induct ++
   RW_TAC std_ss [EVERY_DEF, total_def]);

val lift_prod_total = store_thm
  ("lift_prod_total",
   ``lift_prod total total = total``,
   MATCH_MP_TAC EQ_EXT ++
   RW_TAC std_ss [lift_prod_def, total_def]);

val lift_sum_total = store_thm
  ("lift_sum_total",
   ``lift_sum total total = total``,
   MATCH_MP_TAC EQ_EXT ++
   RW_TAC std_ss [lift_sum_def, total_def] ++
   CASE_TAC);

val lift_option_total = store_thm
  ("lift_option_total",
   ``lift_option total = total``,
   MATCH_MP_TAC EQ_EXT ++
   RW_TAC std_ss [lift_option_def, total_def] ++
   CASE_TAC);

val lift_tree_total = store_thm
  ("lift_tree_total",
   ``lift_tree total = total``,
   MATCH_MP_TAC EQ_EXT ++
   HO_MATCH_MP_TAC tree_ind ++
   RW_TAC std_ss [lift_tree_def, total_def] ++
   CONV_TAC (DEPTH_CONV ETA_CONV) ++
   RW_TAC std_ss [EVERY_MEM]);
*)

(*---------------------------------------------------------------------------
        Well-formed predicates are non-empty.
 ---------------------------------------------------------------------------*)

val wf_pred_def = Define `wf_pred p = ?x. p x`;

(*---------------------------------------------------------------------------
        A well-formed encoder is prefix-free and injective.
 ---------------------------------------------------------------------------*)

val wf_encoder_def = Define
  `wf_encoder p (e : 'a -> bool list) =
   !x y. p x /\ p y /\ IS_PREFIX (e x) (e y) ==> (x = y)`;

val wf_encoder_alt = store_thm
  ("wf_encoder_alt",
   ``wf_encoder p (e : 'a -> bool list) =
     !x y. p x /\ p y /\ biprefix (e x) (e y) ==> (x = y)``,
   PROVE_TAC [wf_encoder_def, biprefix_def]);

val wf_encoder_eq = store_thm
  ("wf_encoder_eq",
   ``!p e f. wf_encoder p e /\ (!x. p x ==> (e x = f x)) ==> wf_encoder p f``,
   RW_TAC std_ss [wf_encoder_def]);

val wf_encoder_total = store_thm
  ("wf_encoder_total",
   ``!p e. wf_encoder (K T) e ==> wf_encoder p e``,
   RW_TAC std_ss [wf_encoder_def, wf_encoder_def, K_THM]);

(*---------------------------------------------------------------------------
      The unit type is cool because it consumes no space in the
      target list: the type has all the information!
 ---------------------------------------------------------------------------*)

val encode_unit_def =
  TotalDefn.Define `encode_unit (_ : one) : bool list = []`;

val wf_encode_unit = store_thm
  ("wf_encode_unit",
   ``!p. wf_encoder p encode_unit``,
   RW_TAC std_ss [wf_encoder_def, encode_unit_def, IS_PREFIX, oneTheory.one]);

(*---------------------------------------------------------------------------
        Booleans
 ---------------------------------------------------------------------------*)

val encode_bool_def = TotalDefn.Define
  `encode_bool (x : bool) = [x]`;

val wf_encode_bool = store_thm
  ("wf_encode_bool",
   ``!p. wf_encoder p encode_bool``,
   RW_TAC std_ss [wf_encoder_def, encode_bool_def, IS_PREFIX]);

(*---------------------------------------------------------------------------
        Pairs
 ---------------------------------------------------------------------------*)

val encode_prod_def =
  TotalDefn.Define
  `encode_prod xb yb (x : 'a, y : 'b) : bool list = APPEND (xb x) (yb y)`;

val lift_prod_def = Define `lift_prod p1 p2 x = p1 (FST x) /\ p2 (SND x)`;

val encode_prod_alt = store_thm
  ("encode_prod_alt",
   ``!xb yb p. encode_prod xb yb p = APPEND (xb (FST p)) (yb (SND p))``,
   GEN_TAC ++ GEN_TAC ++ Cases ++
   RW_TAC std_ss [encode_prod_def]);

val wf_encode_prod = store_thm
  ("wf_encode_prod",
   ``!p1 p2 e1 e2.
       wf_encoder p1 e1 /\ wf_encoder p2 e2 ==>
       wf_encoder (lift_prod p1 p2) (encode_prod e1 e2)``,
   RW_TAC std_ss [wf_encoder_def, encode_prod_alt, lift_prod_def] ++
   Cases_on `x` ++
   Cases_on `y` ++
   FULL_SIMP_TAC std_ss [] ++
   Suff `q = q'` >> PROVE_TAC [IS_PREFIX_APPENDS] ++
   PROVE_TAC [IS_PREFIX_APPEND1, IS_PREFIX_APPEND2]);

(*---------------------------------------------------------------------------
        Sums
 ---------------------------------------------------------------------------*)

val encode_sum_def =
  TotalDefn.Define
  `(encode_sum xb yb (INL (x : 'a)) : bool list = T :: xb x) /\
   (encode_sum xb yb (INR (y : 'b)) = F :: yb y)`;

val lift_sum_def = Define
  `lift_sum (p1 : 'a->bool) p2 x =
   case x of INL x1 -> p1 x1 || INR x2 -> p2 x2`;

val wf_encode_sum = store_thm
  ("wf_encode_sum",
   ``!p1 p2 e1 e2.
       wf_encoder p1 e1 /\ wf_encoder p2 e2 ==>
       wf_encoder (lift_sum p1 p2) (encode_sum e1 e2)``,
   RW_TAC std_ss [wf_encoder_def, lift_sum_def] ++
   Cases_on `x` ++
   Cases_on `y` ++
   FULL_SIMP_TAC std_ss [encode_sum_def, IS_PREFIX]);

(*---------------------------------------------------------------------------
        Options
 ---------------------------------------------------------------------------*)

val encode_option_def =
  TotalDefn.Define
  `(encode_option xb NONE = [F]) /\
   (encode_option xb (SOME x) = T :: xb x)`;

val lift_option_def = Define
  `lift_option p x = case x of NONE -> T || SOME y -> p y`;

val wf_encode_option = store_thm
  ("wf_encode_option",
   ``!p e. wf_encoder p e ==> wf_encoder (lift_option p) (encode_option e)``,
   RW_TAC std_ss [wf_encoder_def, lift_option_def] ++
   Cases_on `x` ++
   Cases_on `y` ++
   FULL_SIMP_TAC std_ss [encode_option_def, IS_PREFIX]);

(*---------------------------------------------------------------------------
        Lists
 ---------------------------------------------------------------------------*)

val encode_list_def =
  TotalDefn.Define
  `(encode_list xb [] = [F]) /\
   (encode_list xb (x :: xs) = T :: APPEND (xb x) (encode_list xb xs))`;

val wf_encode_list = store_thm
  ("wf_encode_list",
   ``!p e. wf_encoder p e ==> wf_encoder (EVERY p) (encode_list e)``,
   RW_TAC std_ss [wf_encoder_def] ++
   POP_ASSUM MP_TAC ++
   POP_ASSUM MP_TAC ++
   POP_ASSUM MP_TAC ++
   Q.SPEC_TAC (`y`, `y`) ++
   Q.SPEC_TAC (`x`, `x`) ++
   Induct >>
   (Cases ++
    RW_TAC std_ss [IS_PREFIX, encode_list_def]) ++
   GEN_TAC ++
   Cases >> RW_TAC std_ss [IS_PREFIX, encode_list_def] ++
   SIMP_TAC std_ss [encode_list_def, IS_PREFIX, EVERY_DEF] ++
   STRIP_TAC ++
   STRIP_TAC ++
   STRIP_TAC ++
   Suff `h = h'` >> PROVE_TAC [IS_PREFIX_APPENDS] ++
   PROVE_TAC [IS_PREFIX_APPEND1, IS_PREFIX_APPEND2]);

(* A congruence rule *)

val encode_list_cong = store_thm
 ("encode_list_cong",
  ``!l1 l2 f1 f2.
      (l1=l2) /\ (!x. MEM x l2 ==> (f1 x = f2 x))
              ==>
      (encode_list f1 l1 = encode_list f2 l2)``,
  Induct ++
  SIMP_TAC list_ss [MEM,encode_list_def] ++
  RW_TAC list_ss []);

val _ = DefnBase.write_congs (encode_list_cong::DefnBase.read_congs());

val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME(fn ppstrm =>
   let val S = PP.add_string ppstrm
       fun NL() = PP.add_newline ppstrm
   in
  S "val _ = DefnBase.write_congs (encode_list_cong::DefnBase.read_congs());";
  NL()
  end)};

(*---------------------------------------------------------------------------
        Bounded lists
 ---------------------------------------------------------------------------*)

val encode_blist_def =
  Define
  `(encode_blist 0 e l = []) /\
   (encode_blist (SUC m) e l = APPEND (e (HD l)) (encode_blist m e (TL l)))`;

val lift_blist_def = Define `lift_blist m p x = EVERY p x /\ (LENGTH x = m)`;

val lift_blist_suc = store_thm
  ("lift_blist_suc",
   ``!n p h t. lift_blist (SUC n) p (h :: t) = p h /\ lift_blist n p t``,
   RW_TAC std_ss [lift_blist_def, EVERY_DEF, LENGTH, CONJ_ASSOC]);

val wf_encode_blist = store_thm
  ("wf_encode_blist",
   ``!m p e.
       wf_encoder p e ==> wf_encoder (lift_blist m p) (encode_blist m e)``,
   RW_TAC std_ss [wf_encoder_alt, lift_blist_def]
   ++ NTAC 4 (POP_ASSUM MP_TAC)
   ++ REWRITE_TAC [AND_IMP_INTRO]
   ++ Q.SPEC_TAC (`y`, `y`)
   ++ Q.SPEC_TAC (`x`, `x`)
   ++ (Induct_on `x` ++ Cases_on `y` ++ FULL_SIMP_TAC std_ss [LENGTH, SUC_NOT])
   ++ SIMP_TAC std_ss [EVERY_DEF, prim_recTheory.INV_SUC_EQ,
                       encode_blist_def, HD, TL]
   ++ REPEAT STRIP_TAC
   ++ Suff `h = h'`
   >> (RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss [biprefix_appends])
   ++ Q.PAT_ASSUM `!y. P y` (K ALL_TAC)
   ++ Q.PAT_ASSUM `!x. P x` MATCH_MP_TAC
   ++ RW_TAC std_ss []
   ++ MATCH_MP_TAC biprefix_append
   ++ PROVE_TAC [biprefix_sym]);

(*---------------------------------------------------------------------------
        Nums (Norrish numeral encoding)
 ---------------------------------------------------------------------------*)

val (encode_num_def, encode_num_ind) =
  Defn.tprove
  (Defn.Hol_defn "encode_num"
   `encode_num (n:num) =
    if n = 0 then [T; T]
    else if EVEN n then F :: encode_num ((n - 2) DIV 2)
    else T :: F :: encode_num ((n - 1) DIV 2)`,
   TotalDefn.WF_REL_TAC `$<` ++
   REPEAT STRIP_TAC ++
   (KNOW_TAC (Term `?j. n = SUC j`) >> PROVE_TAC [num_CASES]) ++
   STRIP_TAC ++
   IMP_RES_TAC EVEN_EXISTS ++
   ASM_SIMP_TAC arith_ss
   [SUC_SUB1, MULT_DIV, DIV_LESS_EQ,
    DECIDE (Term `2n*m - 2n = (m-1n)*2n`),
    DECIDE (Term `x < SUC y = x <= y`)]);

val _ = save_thm ("encode_num_def", encode_num_def);
val _ = save_thm ("encode_num_ind", encode_num_ind);

  (*--------------------------------------------------------------------
       Termination proof can also go:
           WF_REL_TAC `$<` THEN intLib.COOPER_TAC
       but then we'd need integers.
   ----------------------------------------------------------------------*)

val wf_encode_num = store_thm
  ("wf_encode_num",
   ``!p. wf_encoder p encode_num``,
   MATCH_MP_TAC wf_encoder_total ++
   SIMP_TAC std_ss [wf_encoder_def, K_THM] ++
   recInduct encode_num_ind ++
   GEN_TAC ++
   Cases_on `n = 0` >>
   (POP_ASSUM SUBST1_TAC ++
    SIMP_TAC std_ss [REWRITE_RULE [] (Q.INST [`n` |-> `0`] encode_num_def)] ++
    ONCE_REWRITE_TAC [encode_num_def] ++
    RW_TAC std_ss [IS_PREFIX]) ++
   ASM_REWRITE_TAC [] ++
   MP_TAC encode_num_def ++
   (DISCH_THEN (fn th => RW_TAC std_ss [th]) ++
    POP_ASSUM MP_TAC ++
    Q.SPEC_TAC (`y`, `y`) ++
    recInduct encode_num_ind ++
    GEN_TAC ++
    MP_TAC (Q.INST [`n` |-> `n'`] encode_num_def) ++
    RW_TAC std_ss [IS_PREFIX] ++
    RES_TAC) <<
   [Cases_on `n` >> RW_TAC std_ss [] ++
    Cases_on `n''` >> FULL_SIMP_TAC std_ss [EVEN] ++
    FULL_SIMP_TAC arith_ss [EVEN] ++
    Q.PAT_ASSUM `EVEN n` MP_TAC ++
    RW_TAC std_ss [EVEN_EXISTS] ++
    Cases_on `n'` >> RW_TAC std_ss [] ++
    Cases_on `n` >> FULL_SIMP_TAC std_ss [EVEN] ++
    FULL_SIMP_TAC arith_ss [EVEN] ++
    Q.PAT_ASSUM `EVEN n'` MP_TAC ++
    RW_TAC std_ss [EVEN_EXISTS] ++
    POP_ASSUM MP_TAC ++
    POP_ASSUM_LIST (K ALL_TAC) ++
    Know `!m : num. SUC (SUC m) - 2 = m` >> DECIDE_TAC ++
    DISCH_THEN (fn th => REWRITE_TAC [th]) ++
    ONCE_REWRITE_TAC [MULT_COMM] ++
    RW_TAC arith_ss [MULT_DIV],
    Cases_on `n` >> RW_TAC std_ss [] ++
    FULL_SIMP_TAC arith_ss [EVEN] ++
    Q.PAT_ASSUM `EVEN n''` MP_TAC ++
    RW_TAC std_ss [EVEN_EXISTS] ++
    Cases_on `n'` >> RW_TAC std_ss [] ++
    FULL_SIMP_TAC arith_ss [EVEN] ++
    Q.PAT_ASSUM `EVEN n` MP_TAC ++
    RW_TAC std_ss [EVEN_EXISTS] ++
    POP_ASSUM MP_TAC ++
    POP_ASSUM_LIST (K ALL_TAC) ++
    ONCE_REWRITE_TAC [MULT_COMM] ++
    RW_TAC arith_ss [MULT_DIV]]);

(*---------------------------------------------------------------------------
        Bounded numbers (bit encoding)
 ---------------------------------------------------------------------------*)

val encode_bnum_def =
  Define
  `(encode_bnum 0 (n : num) = []) /\
   (encode_bnum (SUC m) n = ~(EVEN n) :: encode_bnum m (n DIV 2))`;

val collision_free_def =
  Define
  `collision_free m p =
   !x y. p x /\ p y /\ (x MOD (2 EXP m) = y MOD (2 EXP m)) ==> (x = y)`;

val wf_pred_bnum_def =
  Define `wf_pred_bnum m p = wf_pred p /\ !x. p x ==> x < 2 ** m`;

val wf_pred_bnum_total = store_thm
  ("wf_pred_bnum_total",
   ``!m. wf_pred_bnum m (\x. x < 2 ** m)``,
   RW_TAC std_ss [wf_pred_bnum_def, wf_pred_def]
   ++ Q.EXISTS_TAC `0`
   ++ REWRITE_TAC [ZERO_LESS_EXP, TWO]);

val wf_pred_bnum_collision_free = store_thm
  ("wf_pred_bnum",
   ``!m p. wf_pred_bnum m p ==> collision_free m p``,
   RW_TAC std_ss [wf_pred_bnum_def, collision_free_def]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC arith_ss [LESS_MOD]);

val encode_bnum_length = store_thm
  ("encode_bnum_length",
   ``!m n. LENGTH (encode_bnum m n) = m``,
   Induct
   ++ RW_TAC std_ss [LENGTH, encode_bnum_def]);

val encode_bnum_inj = store_thm
  ("encode_bnum_inj",
   ``!m x y.
       x < 2 ** m /\ y < 2 ** m /\ (encode_bnum m x = encode_bnum m y) ==>
       (x = y)``,
   Induct
   ++ RW_TAC std_ss
      [encode_bnum_def, DECIDE ``!n. n < 1 = (n = 0)``, GSYM EXP2_LT]
   ++ RES_TAC
   ++ Know `x DIV 2 = y DIV 2` >> RES_TAC
   ++ Q.PAT_ASSUM `EVEN x = Y` MP_TAC
   ++ POP_ASSUM_LIST (K ALL_TAC)
   ++ RW_TAC std_ss []
   ++ MP_TAC (MP (Q.SPEC `2` DIVISION) (DECIDE ``0 < 2``))
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   ++ RW_TAC std_ss [MOD_2]);

val wf_encode_bnum_collision_free = store_thm
  ("wf_encode_bnum_collision_free",
   ``!m p. wf_encoder p (encode_bnum m) = collision_free m p``,
   RW_TAC std_ss [collision_free_def, wf_encoder_def]
   ++ HO_MATCH_MP_TAC
      (PROVE []
       ``(!x y. p x /\ p y ==> (Q x y = R x y)) ==>
         ((!x y. p x /\ p y /\ Q x y ==> P x y) =
          (!x y. p x /\ p y /\ R x y ==> P x y))``)
   ++ RW_TAC std_ss []
   ++ MP_TAC
      (Q.SPECL [`encode_bnum m y`, `encode_bnum m x`]
       (INST_TYPE [alpha |-> bool] IS_PREFIX_LENGTH_ANTI))
   ++ RW_TAC std_ss [encode_bnum_length]
   ++ POP_ASSUM_LIST (K ALL_TAC)
   ++ Q.SPEC_TAC (`y`, `y`)
   ++ Q.SPEC_TAC (`x`, `x`)
   ++ Q.SPEC_TAC (`m`, `m`)
   ++ Induct
   ++ RW_TAC std_ss [encode_bnum_def, EXP, MOD_1]
   ++ POP_ASSUM (K ALL_TAC)
   ++ MP_TAC (Q.SPEC `2` DIVISION)
   ++ SIMP_TAC arith_ss []
   ++ DISCH_THEN (fn th => MP_TAC (CONJ (Q.SPEC `x` th) (Q.SPEC `y` th)))
   ++ DISCH_THEN (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
   ++ Know `!n. (n MOD 2 = 0) \/ (n MOD 2 = 1)`
   >> (STRIP_TAC
       ++ Suff `n MOD 2 < 2` >> DECIDE_TAC
       ++ RW_TAC arith_ss [DIVISION])
   ++ STRIP_TAC
   ++ Know `(EVEN y = EVEN x) = (x MOD 2 = y MOD 2)`
   >> (RW_TAC std_ss [EVEN_MOD2]
       ++ POP_ASSUM (fn th => MP_TAC (CONJ (Q.SPEC `x` th) (Q.SPEC `y` th)))
       ++ STRIP_TAC
       ++ ASM_REWRITE_TAC []
       ++ METIS_TAC [])
   ++ DISCH_THEN (fn th => REWRITE_TAC [th])
   ++ MATCH_MP_TAC (PROVE [] ``(R ==> P) /\ (P ==> (Q = R)) ==> (P /\ Q = R)``)
   ++ CONJ_TAC
   >> (RW_TAC std_ss []
       ++ Suff `?m n. (m * 2 + x MOD 2) MOD 2 = (n * 2 + y MOD 2) MOD 2`
       >> (RW_TAC std_ss []
           ++ POP_ASSUM MP_TAC
           ++ MP_TAC (Q.SPEC `2` MOD_PLUS)
           ++ SIMP_TAC arith_ss []
           ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
           ++ RW_TAC arith_ss [MOD_EQ_0, MOD_MOD])
       ++ Suff `0 < 2 /\ 0 < 2 ** m` >> PROVE_TAC [MOD_MULT_MOD, MULT_COMM]
       ++ REWRITE_TAC [ZERO_LESS_EXP, TWO]
       ++ DECIDE_TAC)
   ++ DISCH_THEN (fn th => REWRITE_TAC [th])
   ++ Suff `((x DIV 2) MOD 2 ** m = (y DIV 2) MOD 2 ** m) =
            ((x DIV 2 * 2) MOD (2 * 2 ** m) =
             (y DIV 2 * 2) MOD (2 * 2 ** m))`
   >> (POP_ASSUM (MP_TAC o Q.SPEC `y`)
       ++ STRIP_TAC
       ++ RW_TAC arith_ss [GSYM ADD1]
       ++ POP_ASSUM MP_TAC
       ++ MP_TAC (Q.SPEC `2 * 2 ** m` SUC_MOD)
       ++ Suff `0 < 2 * 2 ** m` >> RW_TAC std_ss []
       ++ REWRITE_TAC [GSYM EXP, ZERO_LESS_EXP, TWO])
   ++ REWRITE_TAC [GSYM EXP]
   ++ ONCE_REWRITE_TAC [MULT_COMM]
   ++ REWRITE_TAC [EXP, TWO]
   ++ RW_TAC arith_ss [GSYM MOD_COMMON_FACTOR, ZERO_LESS_EXP]);

val wf_encode_bnum = store_thm
  ("wf_encode_bnum",
   ``!m p. wf_pred_bnum m p ==> wf_encoder p (encode_bnum m)``,
   PROVE_TAC [wf_encode_bnum_collision_free, wf_pred_bnum_collision_free]);

(*---------------------------------------------------------------------------
        Datatype of polymorphic n-ary trees.

        A challenging example for boolification.
 ---------------------------------------------------------------------------*)

val () = Hol_datatype `tree = Node of 'a => tree list`;

val tree_size_def  = fetch "-" "tree_size_def";
val tree_induction = fetch "-" "tree_induction";

val tree_ind = store_thm
  ("tree_ind",
   ``!p. (!a ts. (!t. MEM t ts ==> p t) ==> p (Node a ts)) ==> (!t. p t)``,
   GEN_TAC
   ++ REPEAT DISCH_TAC
   ++ Suff `(!t. p t) /\ (!l : 'a tree list. EVERY p l)` >> PROVE_TAC []
   ++ HO_MATCH_MP_TAC tree_induction
   ++ RW_TAC std_ss [EVERY_DEF]
   ++ Q.PAT_ASSUM `!x. Q x` MATCH_MP_TAC
   ++ Induct_on `l`
   ++ RW_TAC std_ss [EVERY_DEF, MEM]
   ++ METIS_TAC []);

val (encode_tree_def, _) =
  Defn.tprove
  (Defn.Hol_defn "encode_tree"
   `encode_tree e (Node a ts) = APPEND (e a) (encode_list (encode_tree e) ts)`,
   TotalDefn.WF_REL_TAC `measure (tree_size (K 0) o SND)` ++
   (Induct_on `ts` ++
    RW_TAC list_ss [tree_size_def, K_THM]) >> DECIDE_TAC ++
   RES_THEN (MP_TAC o SPEC_ALL) ++
   SIMP_TAC arith_ss [K_THM]);

val encode_tree_def =
  save_thm ("encode_tree_def", CONV_RULE (DEPTH_CONV ETA_CONV) encode_tree_def);

val (lift_tree_def, _) =
  Defn.tprove
  (Defn.Hol_defn "lift_tree"
   `lift_tree p (Node a ts) = p a /\ EVERY (lift_tree p) ts`,
   TotalDefn.WF_REL_TAC `measure (tree_size (K 0) o SND)` ++
   RW_TAC list_ss [tree_size_def, K_THM] ++
   (Induct_on `ts` ++
    RW_TAC list_ss [tree_size_def, K_THM]) >> DECIDE_TAC ++
   RES_THEN (MP_TAC o SPEC_ALL) ++
   SIMP_TAC arith_ss [K_THM]);

val lift_tree_def =
  save_thm ("lift_tree_def", CONV_RULE (DEPTH_CONV ETA_CONV) lift_tree_def);

val wf_encode_tree = store_thm
  ("wf_encode_tree",
   ``!p e. wf_encoder p e ==> wf_encoder (lift_tree p) (encode_tree e)``,
   RW_TAC std_ss [] ++
   SIMP_TAC std_ss [wf_encoder_alt] ++
   HO_MATCH_MP_TAC tree_ind ++
   REPEAT GEN_TAC ++
   REPEAT DISCH_TAC ++
   Cases ++
   SIMP_TAC std_ss [lift_tree_def, encode_tree_def] ++
   REPEAT STRIP_TAC ++
   Know `a = a'` >> PROVE_TAC [biprefix_append, wf_encoder_alt] ++
   RW_TAC std_ss [] ++
   FULL_SIMP_TAC std_ss [biprefix_appends] ++
   POP_ASSUM MP_TAC ++
   POP_ASSUM MP_TAC ++
   POP_ASSUM (K ALL_TAC) ++
   POP_ASSUM MP_TAC ++
   POP_ASSUM (K ALL_TAC) ++
   CONV_TAC (DEPTH_CONV ETA_CONV) ++
   POP_ASSUM MP_TAC ++
   Q.SPEC_TAC (`ts`, `z`) ++
   Q.SPEC_TAC (`l`, `y`) ++
   Induct >>
   (Cases ++ RW_TAC std_ss [IS_PREFIX, encode_list_def, biprefix_def]) ++
   GEN_TAC ++
   Cases >> RW_TAC std_ss [IS_PREFIX, encode_list_def, biprefix_def] ++
   SIMP_TAC std_ss [encode_list_def, EVERY_DEF, biprefix_cons] ++
   REPEAT STRIP_TAC ++
   Know `h = h'` >>
   (Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `h'`) ++
    Q.PAT_ASSUM `!x. P x` (K ALL_TAC) ++
    RW_TAC std_ss [MEM] ++
    MATCH_MP_TAC EQ_SYM ++
    POP_ASSUM MATCH_MP_TAC ++
    RW_TAC std_ss [] ++
    PROVE_TAC [biprefix_append]) ++
   RW_TAC std_ss [] ++
   Q.PAT_ASSUM `!z. (!x. P x z) ==> Q z`
   (MATCH_MP_TAC o REWRITE_RULE [AND_IMP_INTRO]) ++
   PROVE_TAC [MEM, biprefix_appends]);

val _ = export_theory ();
