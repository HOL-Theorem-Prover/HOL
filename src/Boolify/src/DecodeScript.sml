(*===========================================================================*)
(* Mapping from `:bool list` back to the original type. Implemented by       *)
(* monadic-style parsing. There is some difficulty when the types get        *)
(* more complex, owing to the requirement to prove termination.              *)
(*===========================================================================*)

(* Interactive mode
app load ["rich_listTheory", "EncodeTheory"];
*)

open HolKernel boolLib Parse bossLib pairTheory pairTools
     arithmeticTheory listTheory rich_listTheory EncodeTheory
     mesonLib optionTheory;

val REVERSE = Tactical.REVERSE;

val _ = new_theory "Decode";

val apro = apropos o Term;

(*---------------------------------------------------------------------------
    A special-purpose case-splitting tactic.
 ---------------------------------------------------------------------------*)

fun exists_p [] _ = false
  | exists_p (p :: ps) x = p x orelse exists_p ps x;

fun strip_dom_rng ty =
  (case total dom_rng ty of NONE => ([], ty)
   | SOME (d, r) => (cons d ## I) (strip_dom_rng r));

local
  fun rator_n 0 f tm = f tm
    | rator_n n f tm = is_comb tm andalso rator_n (n - 1) f (rator tm);

  fun case_p c =
    let val (doms, _) = strip_dom_rng (type_of c)
    in rator_n (length doms) (same_const c)
    end;

  val cases_p =
    exists_p o map (case_p o TypeBasePure.case_const_of) o
    TypeBasePure.listItems o TypeBase.theTypeBase;

  fun free_cases tm =
    let val cp = cases_p ()
    in fn t => is_comb t andalso cp t andalso free_in t tm
    end;

  fun find_free_case tm = rand (find_term (free_cases tm) tm);

  fun case_rws tyi =
    List.mapPartial I
    [SOME (TypeBasePure.case_def_of tyi),
     TypeBasePure.distinct_of tyi,
     TypeBasePure.one_one_of tyi];

  val all_case_rws =
    flatten o map case_rws o TypeBasePure.listItems o TypeBase.theTypeBase;
in
  fun PURE_CASE_TAC g =
    let val t = find_free_case (snd g) in Cases_on `^t` g end;

  fun CASE_TAC g = (PURE_CASE_TAC THEN SIMP_TAC bool_ss (all_case_rws ())) g;
end;

(*---------------------------------------------------------------------------
     decode turns a decoding parser of type
       bool list -> ('a # bool list) option
     into a straight function of type
       bool list -> 'a

     domain parser identifies the set of bool lists where it is valid
     to apply decode parser (i.e., any bool list l such that parser l
     results in a successful parse with no bools remaining: SOME (t, []))
 ---------------------------------------------------------------------------*)

val decode_def = Define `decode f = FST o THE o f`;

val domain_exists = store_thm
  ("domain_exists",
   ``?d. !f x. x IN d f = ?y. f x = SOME (y, [])``,
   Q.EXISTS_TAC `\f x. ?y. f x = SOME (y, [])` THEN
   SIMP_TAC bool_ss [IN_DEF]);

val domain_def =
  Definition.new_specification
  ("domain_def", ["domain"], domain_exists);

val _ = add_const "domain";

(*---------------------------------------------------------------------------*)
(* A well-formed monadic parser is one that doesn't increase the length of   *)
(* the input by parsing it. A *strict* well-formed monadic parser decreases  *)
(* the input by parsing it.                                                  *)
(*---------------------------------------------------------------------------*)

val wf_parser_def = Define
  `wf_parser f =
   !a x b.
     (f a = SOME (x, b)) ==>
     ?c. (APPEND c b = a) /\ !d. f (APPEND c d) = SOME (x, d)`;

val swf_parser_def = Define
   `swf_parser f =
    wf_parser f /\ !a x b. (f a = SOME (x, b)) ==> LENGTH b < LENGTH a`;

val swf_imp_wf_parser = Q.store_thm
("swf_imp_wf_parser",
 `!f. swf_parser f ==> wf_parser f`,
 RW_TAC arith_ss [swf_parser_def]);

val wf_parser_alt = store_thm
  ("wf_parser_alt",
   ``!f.
       wf_parser f =
       !x a b.
         (f a = SOME (x, b)) ==>
         LENGTH b <= LENGTH a /\
         (!c. f (APPEND a c) = SOME (x, APPEND b c)) /\
         (?c. IS_PREFIX a c /\ (f c = SOME (x, [])))``,
   SIMP_TAC bool_ss [wf_parser_def] THEN
   REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
   [RES_TAC THEN
    Q.PAT_ASSUM `APPEND X Y = Z`
    (fn th => SIMP_TAC arith_ss [LENGTH_APPEND, SYM th]),
    RES_TAC THEN
    Q.PAT_ASSUM `APPEND X Y = Z` (fn th => REWRITE_TAC [SYM th]) THEN
    ASM_REWRITE_TAC [GSYM APPEND_ASSOC],
    RES_TAC THEN
    Q.EXISTS_TAC `c` THEN
    POP_ASSUM
    (fn th => REWRITE_TAC [REWRITE_RULE [APPEND_NIL] (Q.SPEC `[]` th)]) THEN
    ASM_MESON_TAC [IS_PREFIX_APPEND],
    RES_TAC THEN
    Q.EXISTS_TAC `c` THEN
    (REVERSE CONJ_TAC THEN1 ASM_MESON_TAC [APPEND_NIL]) THEN
    Q.PAT_ASSUM `IS_PREFIX X Y` MP_TAC THEN
    REWRITE_TAC [IS_PREFIX_APPEND] THEN
    STRIP_TAC THEN
    Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `[]`) THEN
    REWRITE_TAC [APPEND_NIL] THEN
    (Q_TAC KNOW_TAC `f a = SOME (x, l)` THEN1 ASM_MESON_TAC [APPEND_NIL]) THEN
    SIMP_TAC bool_ss [optionTheory.SOME_11, pairTheory.PAIR_EQ] THEN
    ASM_MESON_TAC []]);

val swf_parser_alt = store_thm
  ("swf_parser_alt",
   ``!f.
       swf_parser f =
       !x a b.
         (f a = SOME (x, b)) ==>
         LENGTH b < LENGTH a /\
         (!c. f (APPEND a c) = SOME (x, APPEND b c)) /\
         (?c. IS_PREFIX a c /\ (f c = SOME (x, [])))``,
   SIMP_TAC bool_ss [swf_parser_def, wf_parser_alt] THEN
   REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
   ASM_MESON_TAC [DECIDE ``!m n : num. m < n ==> m <= n``]);

(*---------------------------------------------------------------------------
     The definition of some decoding parsers
 ---------------------------------------------------------------------------*)

val decode_bool_def = Define
  `(decode_bool [] = NONE) /\
   (decode_bool (h::t) = SOME(h,t))`;
    
val decode_unit_def = Define
   `decode_unit l = SOME((),l)`;

val decode_prod_def = Define
   `decode_prod p1 p2 (l:bool list) = 
       case p1 l 
        of NONE -> NONE
        || SOME(x:'a,l1:bool list) ->
            (case p2 l1
              of NONE -> NONE
              || SOME(y:'b,l2:bool list) -> SOME((x,y),l2))`;

val decode_sum_def = Define
  `(decode_sum p1 p2   []   = NONE) /\
   (decode_sum p1 p2 (T::t) = 
        (case p1 t
          of NONE -> NONE
          || SOME(x:'a,rst) -> SOME(INL x,rst))) /\
   (decode_sum p1 p2 (F::t) = 
         (case p2 t
           of NONE -> NONE
           || SOME(y:'b,rst:bool list) -> SOME(INR y,rst)))`;
   
val decode_num_def = Define
  `(decode_num (T::T::t) = SOME(0:num,t))                         /\
   (decode_num (T::F::t) = (case decode_num t
                             of NONE -> NONE
                             || SOME(v,t') -> SOME(2*v + 1, t'))) /\
   (decode_num (F::t)    = (case decode_num t
                             of NONE -> NONE
                             || SOME(v,t') -> SOME(2*v + 2, t'))) /\
   (decode_num  _____    = NONE)`;

val decode_num_ind = fetch "-" "decode_num_ind";

val decode_option_def = Define
  `(decode_option f   []   = (NONE:('a option#bool list)option)) /\
   (decode_option f (F::t) = SOME(NONE,t)) /\
   (decode_option f (T::t) = case f t
                              of NONE -> NONE
                              || SOME(v,t') -> SOME(SOME v, t'))`;
  
(*---------------------------------------------------------------------------*)
(* This definition has to be schematic in f, since the termination of        *)
(* decode_list depends on the behaviour of f. Same thing happens with every  *)
(* recursive polymorphic type.                                               *)
(*                                                                           *)
(* At the same time we partially instantiate decode_list_def and             *)
(* decode_list_ind to a length measure, and require their arguments to be    *)
(* wf_parsers.                                                               *)
(*---------------------------------------------------------------------------*)

local
  val def = TotalDefn.DefineSchema
    `(decode_list [] = NONE)            /\
     (decode_list (F::t) = SOME([],t))  /\  
     (decode_list (T::t) = 
        case f t 
         of NONE -> NONE
         || SOME(h,t') ->
             (case decode_list t'
               of NONE -> NONE
               || SOME(tl, t'') -> SOME(h::tl, t'')))`;   

  val ind = fetch "-" "decode_list_ind";

  val listlemma =prove
    (``!f p.
         ((!t v v1 v2.
             (f t = SOME v) /\ (v = (v1,v2)) ==> LENGTH v2 <= LENGTH t) ==>
          p) ==>
       wf_parser f ==> p``,
     RW_TAC std_ss [wf_parser_alt]);

  val th = DISCH_ALL def;
  val th1 = Q.INST [`R` |-> `measure LENGTH`] th;
  val th2 = REWRITE_RULE [prim_recTheory.WF_measure] th1;
  val def' = 
    MATCH_MP listlemma
    (REWRITE_RULE [DECIDE (Term`x < SUC y = x <= y`),
                   prim_recTheory.measure_thm,listTheory.LENGTH] th2);

  val th = DISCH_ALL ind;
  val th1 = Q.INST [`R` |-> `measure LENGTH`] th;
  val th2 = REWRITE_RULE [prim_recTheory.WF_measure] th1;
  val ind' = 
    MATCH_MP listlemma
    (REWRITE_RULE [DECIDE (Term`x < SUC y = x <= y`),
                   prim_recTheory.measure_thm,listTheory.LENGTH] th2);
in
  val decode_list_def = save_thm ("decode_list_def", def');
  val decode_list_ind = save_thm ("decode_list_ind", ind');
end;

(*---------------------------------------------------------------------------
   Alternative definitions for decoders with lots of cases.
  ---------------------------------------------------------------------------*)

val decode_bool_alt = store_thm
  ("decode_bool_alt",
   ``decode_bool l = case l of [] -> NONE || (h :: t) -> SOME (h, t)``,
   REPEAT CASE_TAC THEN
   RW_TAC std_ss [decode_bool_def]);

val decode_sum_alt = store_thm
  ("decode_sum_alt",
   ``decode_sum p1 p2 l =
     case l of [] -> NONE
     || (T :: t) ->
        (case p1 t of NONE -> NONE
         || SOME (x:'a, t') -> SOME (INL x, t'))
     || (F :: t) ->
        (case p2 t of NONE -> NONE
         || SOME (y:'b, t':bool list) -> SOME (INR y, t'))``,
   REPEAT CASE_TAC THEN
   RW_TAC std_ss [decode_sum_def]);

val decode_num_alt = prove 
  (``decode_num l =
     case l of [] -> NONE
     || (F :: t) ->
        (case decode_num t of NONE -> NONE
         || SOME (n, t') -> SOME (2 * n + 2, t'))
     || [T] -> NONE
     || (T :: T :: t) -> SOME (0, t)
     || (T :: F :: t) ->
        (case decode_num t of NONE -> NONE
         || SOME (n, t') -> SOME (2 * n + 1, t'))``,
   REPEAT CASE_TAC THEN
   RW_TAC std_ss [decode_num_def]);

val decode_option_alt = store_thm
  ("decode_option_alt",
   ``decode_option f l =
     case l of [] -> (NONE : ('a option # bool list) option)
     || (T :: t) ->
        (case f t of NONE -> NONE
         || SOME (v, t') -> SOME (SOME v, t'))
     || (F :: t) -> SOME (NONE, t)``,
   REPEAT CASE_TAC THEN
   RW_TAC std_ss [decode_option_def]);

val decode_list_alt = store_thm
  ("decode_list_alt",
   ``wf_parser f ==>
     (decode_list f l =
      case l of [] -> NONE
      || (T :: t) ->
         (case f t of NONE -> NONE
          || SOME (x, t') ->
             (case decode_list f t' of NONE -> NONE
              || SOME (xs, t'') -> SOME (x :: xs, t'')))
      || (F :: t) -> SOME ([], t))``,
   REPEAT CASE_TAC THEN
   RW_TAC std_ss [decode_list_def]);

(*---------------------------------------------------------------------------*)
(* Proofs that our basic monadic parsers are well-formed. Decoders for       *)
(* single constructor types can only propagate well-formedness; decoders for *)
(* multi-constructor types take well-formed arguments and return strict      *)
(* well-formed results.                                                      *)
(*---------------------------------------------------------------------------*)

val wf_decode_bool = store_thm
  ("wf_decode_bool",
   ``swf_parser decode_bool``,
   REWRITE_TAC [swf_parser_alt] THEN
   REPEAT (DISCH_TAC ORELSE GEN_TAC) THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE [decode_bool_alt]) THEN
   REPEAT CASE_TAC THEN
   RW_TAC arith_ss [LENGTH, APPEND, decode_bool_def] THEN
   Q.EXISTS_TAC `[h]` THEN
   RW_TAC std_ss [IS_PREFIX, decode_bool_def]);

val wf_decode_unit = store_thm
  ("wf_decode_unit",
   ``wf_parser decode_unit``,
   RW_TAC list_ss [wf_parser_alt, decode_unit_def, IS_PREFIX]);

val wf_decode_prod = store_thm
  ("wf_decode_prod",
   ``!f g. wf_parser f /\ wf_parser g ==> wf_parser (decode_prod f g)``,
   SIMP_TAC std_ss [wf_parser_def, decode_prod_def] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   REPEAT CASE_TAC THEN
   RW_TAC std_ss [] THEN
   RES_TAC THEN
   Q.EXISTS_TAC `APPEND c' c` THEN
   RW_TAC std_ss [GSYM APPEND_ASSOC]);

val wf_decode_prod1 = store_thm
  ("wf_decode_prod1",
   ``!f g. swf_parser f /\ wf_parser g ==> swf_parser (decode_prod f g)``,
   RW_TAC std_ss [swf_parser_def, wf_decode_prod, decode_prod_def] THEN
   POP_ASSUM MP_TAC THEN
   REPEAT CASE_TAC THEN
   RW_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [wf_parser_alt] THEN
   RES_TAC THEN
   ASM_MESON_TAC [LESS_EQ_LESS_TRANS]);

val wf_decode_prod2 = store_thm
  ("wf_decode_prod2",
   ``!f g. wf_parser f /\ swf_parser g ==> swf_parser (decode_prod f g)``,
   RW_TAC std_ss [swf_parser_def, wf_decode_prod, decode_prod_def] THEN
   POP_ASSUM MP_TAC THEN
   REPEAT CASE_TAC THEN
   RW_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [wf_parser_alt] THEN
   RES_TAC THEN
   ASM_MESON_TAC [LESS_LESS_EQ_TRANS]);

val swf_decode_sum = store_thm
  ("swf_decode_sum",
   ``!f g. wf_parser f /\ wf_parser g ==> swf_parser (decode_sum f g)``,
   RW_TAC std_ss [swf_parser_def] THENL
   [REPEAT (POP_ASSUM MP_TAC) THEN
    RW_TAC std_ss [wf_parser_def] THEN
    POP_ASSUM (MP_TAC o REWRITE_RULE [decode_sum_alt]) THEN
    (REPEAT CASE_TAC THEN
     RW_TAC std_ss [] THEN
     RES_TAC) THENL
    [Q.EXISTS_TAC `T :: c` THEN
     RW_TAC std_ss [APPEND, decode_sum_def],
     Q.EXISTS_TAC `F :: c` THEN
     RW_TAC std_ss [APPEND, decode_sum_def]],
    REPEAT (POP_ASSUM MP_TAC) THEN
    RW_TAC std_ss [wf_parser_alt, decode_sum_alt] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    REPEAT CASE_TAC THEN
    RW_TAC std_ss [] THEN
    RES_TAC THEN
    RW_TAC arith_ss [LENGTH]]);

val swf_decode_option = store_thm
  ("swf_decode_option",
   ``!f. wf_parser f ==> swf_parser (decode_option f)``,
   RW_TAC std_ss [swf_parser_def] THENL
   [POP_ASSUM MP_TAC THEN
    RW_TAC std_ss [wf_parser_def] THEN
    POP_ASSUM (MP_TAC o REWRITE_RULE [decode_option_alt]) THEN
    (REPEAT CASE_TAC THEN
     RW_TAC std_ss []) THENL
    [RES_TAC THEN
     Q.EXISTS_TAC `T :: c` THEN
     RW_TAC std_ss [APPEND, decode_option_def],
     Q.EXISTS_TAC `[F]` THEN
     RW_TAC std_ss [APPEND, decode_option_def]],
    REPEAT (POP_ASSUM MP_TAC) THEN
    RW_TAC std_ss [wf_parser_alt, decode_option_alt] THEN
    POP_ASSUM MP_TAC THEN
    REPEAT CASE_TAC THEN
    RW_TAC std_ss [] THEN
    RES_TAC THEN
    RW_TAC arith_ss [LENGTH]]);

(*---------------------------------------------------------------------------*)
(* Some recursive types. Induction needed in the proofs, of course. We use   *)
(* the custom induction theorems produced at definition time.                *)
(*---------------------------------------------------------------------------*)

val wf_decode_num = store_thm
  ("wf_decode_num",
   ``swf_parser decode_num``,
   REWRITE_TAC [swf_parser_def] THEN
   MATCH_MP_TAC (DECIDE ``!a b. a /\ (a ==> b) ==> a /\ b``) THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [wf_parser_def] THEN
    recInduct decode_num_ind THEN
    RW_TAC list_ss [decode_num_def] THENL
    [Q.EXISTS_TAC `[T; T]` THEN
     RW_TAC std_ss [IS_PREFIX, decode_num_def, APPEND],
     POP_ASSUM MP_TAC THEN
     REPEAT CASE_TAC THEN
     RW_TAC std_ss [] THEN
     RES_TAC THEN
     Q.EXISTS_TAC `T::F::c` THEN
     RW_TAC std_ss [APPEND, decode_num_def],
     POP_ASSUM MP_TAC THEN
     REPEAT CASE_TAC THEN
     RW_TAC std_ss [] THEN
     RES_TAC THEN
     Q.EXISTS_TAC `F::c` THEN
     RW_TAC std_ss [APPEND, decode_num_def]],
    SIMP_TAC std_ss [wf_parser_alt] THEN
    STRIP_TAC THEN
    recInduct decode_num_ind THEN
    RW_TAC list_ss [decode_num_def] THEN
    POP_ASSUM MP_TAC THEN
    REPEAT CASE_TAC THEN
    RES_TAC THEN
    RW_TAC arith_ss [] THEN
    RW_TAC arith_ss []]);

val wf_decode_list = store_thm
 ("wf_decode_list",
  ``!f. wf_parser f ==> swf_parser (decode_list f)``,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [swf_parser_def] THEN
   MATCH_MP_TAC (DECIDE ``!a b. a /\ (a ==> b) ==> a /\ b``) THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [wf_parser_def] THEN
    recInduct (UNDISCH decode_list_ind) THEN
    RW_TAC list_ss [decode_list_def] THENL
    [Q.EXISTS_TAC `[F]` THEN
     RW_TAC std_ss [APPEND, decode_list_def],
     POP_ASSUM MP_TAC THEN
     REPEAT CASE_TAC THEN
     RW_TAC std_ss [] THEN
     Q.PAT_ASSUM `wf_parser f`
     (fn th =>
      ASSUME_TAC (REWRITE_RULE [wf_parser_def] th) THEN ASSUME_TAC th) THEN
     RES_TAC THEN
     Q.EXISTS_TAC `T :: APPEND c c'` THEN
     RW_TAC std_ss [APPEND, GSYM APPEND_ASSOC, decode_list_def]],
    SIMP_TAC std_ss [wf_parser_alt] THEN
    STRIP_TAC THEN
    recInduct (UNDISCH decode_list_ind) THEN
    RW_TAC list_ss [decode_list_def] THEN
    POP_ASSUM MP_TAC THEN
    REPEAT CASE_TAC THEN
    RW_TAC std_ss [] THEN
    Q.PAT_ASSUM `wf_parser f`
    (fn th =>
     ASSUME_TAC (REWRITE_RULE [wf_parser_alt] th) THEN ASSUME_TAC th) THEN
    RES_TAC THEN
    RW_TAC arith_ss []]);

(*---------------------------------------------------------------------------*)
(* Congruence rule for decode_list. Reflects fact that decode_list calls     *)
(* its argument on strictly smaller lists. The format of the rule is         *)
(* slightly non-standard. Usually, antecedents are conditional rewrites. In  *)
(* our case, we add the requirements wf_parser f and wf_parser g. These are  *)
(* needed to prove the theorem. When the rule is used to extract termination *)
(* conditions, the matched parser f (which will be used to instantiate g)    *)
(* will have to be proved to be a wf_parser on the fly. Therefore, the       *)
(* condition prover in the T.C. extractor will have to be augmented to       *)
(* understand how to prove wf_parser goals. Note that the wf_parser formulas *)
(* appear after the other conditions. The conditions now get separated into  *)
(* two conceptual blocks: the first, as before, finds the values for the     *)
(* variables on the rhs of the conclusion (TC trapping happens here). The    *)
(* second block is a collection of other goals, dependent on the variable    *)
(* settings found in the first block, which need other theorem proving to    *)
(* polish off. So we need a little "wf_parser" prover. It may also be        *)
(* possible to handle schematic arguments by having the wf_parser prover     *)
(* assume them.                                                              *)
(*---------------------------------------------------------------------------*)

(* This is where we're currently stuck---Joe, 12 Aug 2002
val th1 = UNDISCH (decode_list'');
val th2 = UNDISCH (Q.SPEC `g` (Q.GEN `f` decode_list''));

val decode_list_cong = store_thm
("decode_list_cong",
 ``wf_parser f /\ wf_parser g  ==>
   !l1 l2. 
      (l1=l2) /\ 
      (!l'. LENGTH l' < LENGTH l2 ==> (f l' = g l'))
               ==>
      (decode_list f l1 = decode_list g l2)``,
  STRIP_TAC 
    THEN recInduct (UNDISCH decode_list_ind'')
    THEN RW_TAC list_ss [th1] THEN RW_TAC list_ss [th2]
    THEN Cases_on `g t` THEN RW_TAC std_ss []
    THEN Cases_on `x` THEN RW_TAC std_ss []
    THEN Cases_on `decode_list f r`
    THEN Cases_on `decode_list g r` THEN RW_TAC std_ss []
    THEN `f t = g t` by PROVE_TAC [prim_recTheory.LESS_SUC_REFL]
    THEN POP_ASSUM SUBST_ALL_TAC 
    THEN `!l'. LENGTH l' < LENGTH r ==> (f l' = g l')` 
      by (GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
          MATCH_MP_TAC (DECIDE (Term `!a b c. a < b /\ b <= c ==> a < c`)) THEN
          Q.EXISTS_TAC `LENGTH r` THEN RW_TAC std_ss [] THEN
          Q.PAT_ASSUM `wf_parser g` 
               (MP_TAC o GSYM o REWRITE_RULE [wf_parser]) THEN
          PROVE_TAC [DECIDE(Term`x <= y ==> x <= SUC y`)])
    THENL [PROVE_TAC [TypeBase.distinct_of "option"],
           PROVE_TAC [TypeBase.distinct_of "option"],
           Cases_on `x` THEN Cases_on `x'` 
             THEN RW_TAC std_ss []
             THEN RES_THEN MP_TAC
             THEN RW_TAC std_ss []]);

val decode_list_cong_ideal = store_thm
("decode_list_cong_ideal",
 ``!l1 l2 f g. 
       (l1=l2) 
    /\ (!l'. LENGTH l' < LENGTH l2 ==> (f l' = g l')) 
    /\ wf_parser f 
    /\ wf_parser g
    ==>
      (decode_list f l1 = decode_list g l2)``,
 PROVE_TAC [decode_list_cong]);
*)

val _ = export_theory ();
