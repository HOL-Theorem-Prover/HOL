(* Interactive mode
app load ["listSyntax", "combinSyntax", "rich_listTheory"];
*)

open HolKernel boolLib Parse bossLib pairTheory pairTools
     arithmeticTheory listTheory rich_listTheory optionTheory;

val REVERSE = Tactical.REVERSE;

val _ = new_theory "Encode";

infixr 0 ++ || <<;
infix 1 >>;

val op ++ = op THEN;
val op >> = op THEN1;
val op << = op THENL;
val op || = op ORELSE;

val Suff = Q_TAC SUFF_TAC;
val Know = Q_TAC KNOW_TAC;

(*---------------------------------------------------------------------------
        Theorems that should be somewhere else.
 ---------------------------------------------------------------------------*)

val IS_PREFIX_APPEND1 = store_thm
  ("IS_PREFIX_APPEND1",
   ``!a b c. IS_PREFIX c (APPEND a b) ==> IS_PREFIX c a``,
   Induct >> RW_TAC std_ss [IS_PREFIX]
   ++ RW_TAC std_ss []
   ++ Cases_on `c`
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [IS_PREFIX, APPEND]
   ++ PROVE_TAC []);

val IS_PREFIX_APPEND2 = store_thm
  ("IS_PREFIX_APPEND2",
   ``!a b c. IS_PREFIX (APPEND b c) a ==> IS_PREFIX b a \/ IS_PREFIX a b``,
   Induct >> RW_TAC std_ss [IS_PREFIX]
   ++ RW_TAC std_ss []
   ++ Cases_on `b` >> RW_TAC std_ss [IS_PREFIX]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [IS_PREFIX, APPEND]
   ++ PROVE_TAC []);

val IS_PREFIX_APPENDS = store_thm
  ("IS_PREFIX_APPENDS",
   ``!a b c. IS_PREFIX (APPEND a c) (APPEND a b) = IS_PREFIX c b``,
   Induct >> RW_TAC std_ss [APPEND]
   ++ RW_TAC std_ss [APPEND, IS_PREFIX]);

(*---------------------------------------------------------------------------
        A well-formed encoder is prefix-free and injective.
 ---------------------------------------------------------------------------*)

val wf_encoder_def = Define
  `wf_encoder e = !x y. IS_PREFIX (e x) (e y) ==> (x = y)`;

(*---------------------------------------------------------------------------
      The unit type is cool because it consumes no space in the
      target list: the type has all the information!
 ---------------------------------------------------------------------------*)

val encode_unit_def =
  TotalDefn.Define `encode_unit (_ : one) : bool list = []`;

(*---------------------------------------------------------------------------
        Booleans
 ---------------------------------------------------------------------------*)

val encode_bool_def = TotalDefn.Define
  `encode_bool (x : bool) = [x]`;

(*---------------------------------------------------------------------------
        Pairs
 ---------------------------------------------------------------------------*)

val encode_prod_def =
  TotalDefn.Define
  `encode_prod xb yb (x : 'a, y : 'b) : bool list = APPEND (xb x) (yb y)`;

(*---------------------------------------------------------------------------
        Sums
 ---------------------------------------------------------------------------*)

val encode_sum_def =
  TotalDefn.Define
  `(encode_sum xb yb (INL (x : 'a)) : bool list = T :: xb x) /\
   (encode_sum xb yb (INR (y : 'b)) = F :: yb y)`;

(*---------------------------------------------------------------------------
        Options
 ---------------------------------------------------------------------------*)

val encode_option_def =
  TotalDefn.Define
  `(encode_option xb NONE = [F]) /\
   (encode_option xb (SOME x) = T :: xb x)`;

(*---------------------------------------------------------------------------
        Lists
 ---------------------------------------------------------------------------*)

val encode_list_def = 
  TotalDefn.Define
  `(encode_list xb [] = [F]) /\
   (encode_list xb (x :: xs) = T :: APPEND (xb x) (encode_list xb xs))`;

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

(*---------------------------------------------------------------------------*)
(* An alternative definition of encode_prod.                                 *)
(*---------------------------------------------------------------------------*)

val encode_prod_alt = prove
  (``!xb yb p. encode_prod xb yb p = APPEND (xb (FST p)) (yb (SND p))``,
   GEN_TAC ++ GEN_TAC ++ Cases ++
   RW_TAC std_ss [encode_prod_def]);

(*---------------------------------------------------------------------------*)
(* Proving that all our encoders are well-formed.                            *)
(*---------------------------------------------------------------------------*)

val wf_encode_unit = store_thm
  ("wf_encode_unit",
   ``wf_encoder encode_unit``,
   RW_TAC std_ss [wf_encoder_def, encode_unit_def, IS_PREFIX, oneTheory.one]);

val wf_encoder_bool = store_thm
  ("wf_encoder_bool",
   ``wf_encoder encode_bool``,
   RW_TAC std_ss [wf_encoder_def, encode_bool_def, IS_PREFIX]);
   
val wf_encoder_prod = store_thm
  ("wf_encoder_prod",
   ``!f g. wf_encoder f /\ wf_encoder g ==> wf_encoder (encode_prod f g)``,
   RW_TAC std_ss [wf_encoder_def, encode_prod_alt] ++
   Cases_on `x` ++
   Cases_on `y` ++
   FULL_SIMP_TAC std_ss [] ++
   Suff `q = q'` >> PROVE_TAC [IS_PREFIX_APPENDS] ++
   PROVE_TAC [IS_PREFIX_APPEND1, IS_PREFIX_APPEND2]);

val wf_encoder_sum = store_thm
  ("wf_encoder_sum",
   ``!f g. wf_encoder f /\ wf_encoder g ==> wf_encoder (encode_sum f g)``,
   RW_TAC std_ss [wf_encoder_def] ++
   Cases_on `x` ++
   Cases_on `y` ++
   FULL_SIMP_TAC std_ss [encode_sum_def, IS_PREFIX]);

val wf_encoder_option = store_thm
  ("wf_encoder_option",
   ``!f. wf_encoder f ==> wf_encoder (encode_option f)``,
   RW_TAC std_ss [wf_encoder_def] ++
   Cases_on `x` ++
   Cases_on `y` ++
   FULL_SIMP_TAC std_ss [encode_option_def, IS_PREFIX]);

val wf_encoder_num = store_thm
  ("wf_encoder_num",
   ``wf_encoder encode_num``,
   SIMP_TAC std_ss [wf_encoder_def] ++
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

val wf_encoder_list = store_thm
  ("wf_encoder_list",
   ``!f. wf_encoder f ==> wf_encoder (encode_list f)``,
   RW_TAC std_ss [wf_encoder_def] ++
   POP_ASSUM MP_TAC ++
   Q.SPEC_TAC (`y`, `y`) ++
   Q.SPEC_TAC (`x`, `x`) ++
   Induct >>
   (Cases ++
    RW_TAC std_ss [IS_PREFIX, encode_list_def]) ++
   GEN_TAC ++
   Cases >> RW_TAC std_ss [IS_PREFIX, encode_list_def] ++
   SIMP_TAC std_ss [encode_list_def, IS_PREFIX] ++
   STRIP_TAC ++
   Suff `h = h'` >> PROVE_TAC [IS_PREFIX_APPENDS] ++
   PROVE_TAC [IS_PREFIX_APPEND1, IS_PREFIX_APPEND2]);

(*---------------------------------------------------------------------------*)
(* A congruence rule for encode_list                                         *)
(*---------------------------------------------------------------------------*)

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


val _ = export_theory ();
