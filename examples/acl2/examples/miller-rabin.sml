(* ========================================================================= *)
(* miller_rabin_def theory                                                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories.                                          *)
(* (Comment out "load"s and "quietdec"s for compilation.)                    *)
(* ------------------------------------------------------------------------- *)
(*
*)

val () = loadPath := ["../../miller/ho_prover",
                      "../../miller/subtypes",
                      "../../miller/RSA",
                      "../../miller/formalize",
                      "../../miller/prob",
                      "../../miller/groups",
                      "../../miller/miller",
                      "../ml"] @ !loadPath;
val () = app load
  ["bossLib", "metisLib", "RealArith",
   "pairTheory", "combinTheory", "listTheory", "arithmeticTheory",
   "state_transformerTheory",
   "miller_rabinTheory",
   "encodeLib"];
val () = quietdec := true;

open HolKernel Parse boolLib bossLib metisLib;
open pairTheory combinTheory listTheory arithmeticTheory;
open state_transformerTheory;
open miller_rabinTheory;
open encodeLib;

(*
*)
val () = quietdec := false;

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "miller_rabin_def".                             *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "miller_rabin_def";

(* ------------------------------------------------------------------------- *)
(* Helper proof tools.                                                       *)
(* ------------------------------------------------------------------------- *)

val arith_ss = bossLib.arith_ss ++ boolSimps.LET_ss;

infixr 0 <<
infixr 1 ++ || THENC ORELSEC ORELSER ## orelse_bdd_conv
infix 2 >>

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;

(* ------------------------------------------------------------------------- *)
(* Helper theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(***
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

val DIVISION_TWO = store_thm
  ("DIVISION_TWO",
   ``!n. (n = 2 * (n DIV 2) + (n MOD 2)) /\ ((n MOD 2 = 0) \/ (n MOD 2 = 1))``,
   STRIP_TAC
   ++ MP_TAC (Q.SPEC `2` DIVISION)
   ++ Know `0:num < 2` >> DECIDE_TAC
   ++ DISCH_THEN (fn th => REWRITE_TAC [th])
   ++ DISCH_THEN (MP_TAC o Q.SPEC `n`)
   ++ RW_TAC bool_ss [] <<
   [PROVE_TAC [MULT_COMM],
    DECIDE_TAC]);

val DIV_TWO = store_thm
  ("DIV_TWO",
   ``!n. n = 2 * (n DIV 2) + (n MOD 2)``,
   PROVE_TAC [DIVISION_TWO]);

val MOD_TWO = store_thm
  ("MOD_TWO",
   ``!n. n MOD 2 = if EVEN n then 0 else 1``,
   STRIP_TAC
   ++ MP_TAC (Q.SPEC `n` DIVISION_TWO)
   ++ STRIP_TAC <<
   [Q.PAT_ASSUM `n = X` MP_TAC
    ++ RW_TAC std_ss []
    ++ PROVE_TAC [EVEN_DOUBLE, ODD_EVEN, ADD_CLAUSES],
    Q.PAT_ASSUM `n = X` MP_TAC
    ++ RW_TAC std_ss []
    ++ PROVE_TAC [ODD_DOUBLE, ODD_EVEN, ADD1]]);
***)

(* ------------------------------------------------------------------------- *)
(* Definitions to port to ACL2.                                              *)
(* ------------------------------------------------------------------------- *)

val (log2_def,log2_ind) =
    (extra_numTheory.log2_def,extra_numTheory.log2_ind);

(***
    Defn.tprove
      let
        val d =
            Hol_defn "log2"
              `(log2 0 = 0) /\
               (log2 n = SUC (log2 (n DIV 2)))`

        val g = `measure (\x. x)`
      in
        (d,
         WF_REL_TAC g
         ++ STRIP_TAC
         ++ Know `2 * (SUC v DIV 2) <= SUC v`
         >> PROVE_TAC [TWO, DIV_THEN_MULT]
         ++ DECIDE_TAC)
      end;

val _ = save_thm ("log2_def", log2_def);
val _ = save_thm ("log2_ind", log2_ind);
***)

val log2a_def = Define `
	(log2a 0 _ = 0) /\ 
	(log2a _ 0 = 0) /\ 
	(log2a (SUC a) b = SUC (log2a a (b DIV 2)))`;

val log2a_lemma = prove(``!x y. x <= y ==> (log2 x = log2a y x)``,
	GEN_TAC ++ completeInduct_on `x` ++
	Cases ++ Cases_on `x` ++ RW_TAC arith_ss [log2a_def,log2_def] ++ 
	PAT_ASSUM ``!a:num.P`` (STRIP_ASSUME_TAC o SPEC ``SUC n' DIV 2``) ++
	FULL_SIMP_TAC arith_ss [DIV_LT_X,DIV_LE_X,DECIDE ``0 < 2n``]);

val log2a_proof = store_thm("log2a_proof",``!x. log2 x = log2a x x``,RW_TAC arith_ss [log2a_lemma]);

val (factor_twos_def,factor_twos_ind) =
    (miller_rabinTheory.factor_twos_def,miller_rabinTheory.factor_twos_ind);
(***
    Defn.tprove
      let
        val d =
            Hol_defn "factor_twos"
              `factor_twos n =
               if 0 < n /\ EVEN n then
                 let (r,s) = factor_twos (n DIV 2) in (SUC r, s)
               else (0, n)`

        val g = `measure (\x. x)`
      in
        (d,
         WF_REL_TAC g
         ++ RW_TAC arith_ss []
         ++ Know `2 * (n DIV 2) <= n`
         >> PROVE_TAC [TWO, DIV_THEN_MULT]
         ++ DECIDE_TAC)
      end;

val _ = save_thm ("factor_twos_def", factor_twos_def);
val _ = save_thm ("factor_twos_ind", factor_twos_ind);
***)

val factor_twosa_def = Define `
	(factor_twosa 0 _ = (0, 0)) /\ 
	(factor_twosa (SUC a) n =
	 if 0 < n /\ EVEN n then
	   let (r,s) = factor_twosa a (n DIV 2) in (SUC r, s)
	 else (0,n))`;

val factor_twosa_lemma = prove(``!x y. x <= y ==> (factor_twos x = factor_twosa y x)``,
	GEN_TAC ++ completeInduct_on `x` ++
	Cases ++ Cases_on `x` ++ ONCE_REWRITE_TAC [factor_twos_def] ++ 
	RW_TAC arith_ss [factor_twosa_def] ++ 
	PAT_ASSUM ``!a:num.P`` (STRIP_ASSUME_TAC o SPEC ``SUC n' DIV 2``) ++
	FULL_SIMP_TAC arith_ss [DIV_LT_X,DIV_LE_X,DECIDE ``0 < 2n``] ++
	POP_ASSUM (STRIP_ASSUME_TAC o SPEC ``n:num``) ++
	FULL_SIMP_TAC arith_ss []);

val factor_twosa_proof = store_thm("factor_twosa_proof",``!x. factor_twos x = factor_twosa x x``,
	RW_TAC arith_ss [factor_twosa_lemma]);

val (modexp_def,modexp_ind) =
    (miller_rabinTheory.modexp_def,miller_rabinTheory.modexp_ind);
(***
    Defn.tprove
      let
        val d =
            Hol_defn "modexp"
              `modexp n a b =
               if b = 0 then 1
               else
                 let r = modexp n a (b DIV 2) in
                 let r2 = (r * r) MOD n in
                 if EVEN b then r2 else (r2 * a) MOD n`

        val g = `measure (\(x,y,z). z)`
      in
        (d,
         WF_REL_TAC g
         ++ RW_TAC arith_ss []
         ++ Know `2 * (b DIV 2) <= b`
         >> PROVE_TAC [TWO, DIV_THEN_MULT]
         ++ DECIDE_TAC)
      end;

val _ = save_thm ("modexp_def", modexp_def);
val _ = save_thm ("modexp_ind", modexp_ind);
***)

val modexpa_def = Define `
	(modexpa 0 n a b = 1) /\
	(modexpa _ _ _ 0 = 1) /\ 
	(modexpa (SUC v) n a b = 
               let r = modexpa v n a (b DIV 2) in
               let r2 = (r * r) MOD n in
               if EVEN b then r2 else (r2 * a) MOD n)`;

val modexpa_lemma = prove(``!x y n a. x <= y ==> (modexp n a x = modexpa y n a x)``,
	GEN_TAC ++ completeInduct_on `x` ++
	Cases ++ Cases_on `x` ++ ONCE_REWRITE_TAC [modexp_def] ++ 
	RW_TAC arith_ss [modexpa_def] ++ 
	PAT_ASSUM ``!a:num.P`` (STRIP_ASSUME_TAC o SPEC ``SUC n' DIV 2``) ++
	FULL_SIMP_TAC arith_ss [DIV_LT_X,DIV_LE_X,DECIDE ``0 < 2n``] ++
	POP_ASSUM (STRIP_ASSUME_TAC o SPEC ``n:num``) ++
	FULL_SIMP_TAC arith_ss []);

val modexpa_proof = store_thm("modexpa_proof",``!n a b. modexp n a b = modexpa b n a b``,
	RW_TAC arith_ss [modexpa_lemma]);

val witness_tail_def = miller_rabinTheory.witness_tail_def;
(***
    Define
      `(witness_tail 0 n a = ~(a = 1)) /\
       (witness_tail (SUC r) n a =
        let a2 = (a * a) MOD n in
        if a2 = 1 then ~(a = 1) /\ ~(a = n - 1)
        else witness_tail r n a2)`;
***)

val witness_def = miller_rabinTheory.witness_def;
(***
    Define
      `witness n a =
       let (r, s) = factor_twos (n - 1) in
       witness_tail r n (modexp n a s)`;
***)

val exists_witness_def = 
    Define
      `(exists_witness n [] = F) /\
       (exists_witness n (hd::tl) = witness n hd \/ exists_witness n tl)`;

val exists_witness_proof = store_thm("exists_witness_proof",
	``!n l. EXISTS (witness n) l = exists_witness n l``,
	GEN_TAC ++ Induct ++
	RW_TAC std_ss [EXISTS_DEF,exists_witness_def]);

val miller_rabin_list_def =
    Define
      `miller_rabin_list n l =
       if n = 2 then T
       else if (n = 1) \/ EVEN n then F
       else ~(EXISTS (witness n) l)`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val many_longcircuit_def = Define
  `(many_longcircuit f b 0 = UNIT b) /\
   (many_longcircuit f b (SUC n) =
    BIND f (\b'. many_longcircuit f (b /\ b') n))`;

val indep_fn_many_longcircuit = prove
  (``!f b n. f IN indep_fn ==> many_longcircuit f b n IN indep_fn``,
   Induct_on `n`
   ++ RW_TAC std_ss
        [many_longcircuit_def, probTheory.INDEP_FN_UNIT,
         probTheory.INDEP_FN_BIND]);

val many_longcircuit_f = prove
  (``!f n.
       f IN indep_fn ==>
       (prob bern { s | FST (many_longcircuit f F n s)} = 0)``,
   Induct_on `n`
   ++ RW_TAC std_ss [many_longcircuit_def, state_transformerTheory.UNIT_DEF,
                     pred_setTheory.GSPEC_F, probTheory.PROB_BERN_EMPTY]
   ++ MP_TAC
        (Q.SPECL
           [`f`, `\b'. many_longcircuit f F n`,
            `prob bern (FST o (f : (num -> bool) -> bool # (num -> bool)))`]
           probTheory.PROB_BERN_BIND_BOOL_BOOL)
   ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
   ++ CONJ_TAC >> RW_TAC std_ss [indep_fn_many_longcircuit]
   ++ Q.PAT_ASSUM `!f. P f` (MP_TAC o Q.SPEC `f`)
   ++ Know `!g : (num -> bool) -> bool # (num -> bool).
              FST o g = { s | FST (g s) }`
   >> (RW_TAC std_ss [pred_setTheory.EXTENSION]
       ++ RW_TAC std_ss [pred_setTheory.GSPECIFICATION]
       ++ RW_TAC std_ss [IN_DEF])
   ++ DISCH_THEN (fn th => RW_TAC std_ss [th])
   ++ RW_TAC std_ss [realTheory.REAL_MUL_RZERO, realTheory.REAL_ADD_RID]);

val many_longcircuit_t = prove
  (``!f n.
       f IN indep_fn ==>
       (prob bern {s | FST (many_longcircuit f T n s)} =
        prob bern {s | FST (many f n s)})``,
   Induct_on `n`
   ++ RW_TAC std_ss [probTheory.MANY, many_longcircuit_def]
   ++ MP_TAC
        (Q.SPECL
           [`f`, `\b'. many_longcircuit f b' n`,
            `prob bern (FST o (f : (num -> bool) -> bool # (num -> bool)))`]
           probTheory.PROB_BERN_BIND_BOOL_BOOL)
   ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
   ++ CONJ_TAC >> RW_TAC std_ss [indep_fn_many_longcircuit]
   ++ MP_TAC
        (Q.SPECL
           [`f`, `\b'. if b' then many f n else UNIT F`,
            `prob bern (FST o (f : (num -> bool) -> bool # (num -> bool)))`]
           probTheory.PROB_BERN_BIND_BOOL_BOOL)
   ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
   ++ CONJ_TAC >> RW_TAC std_ss [probTheory.INDEP_FN_MANY,
                                 probTheory.INDEP_FN_UNIT]
   ++ Q.PAT_ASSUM `!f. P f` (MP_TAC o Q.SPEC `f`)
   ++ Know `!g : (num -> bool) -> bool # (num -> bool).
              FST o g = { s | FST (g s) }`
   >> (RW_TAC std_ss [pred_setTheory.EXTENSION]
       ++ RW_TAC std_ss [pred_setTheory.GSPECIFICATION]
       ++ RW_TAC std_ss [IN_DEF])
   ++ DISCH_THEN (fn th => RW_TAC std_ss [th])
   ++ AP_TERM_TAC
   ++ AP_TERM_TAC
   ++ RW_TAC std_ss [many_longcircuit_f, state_transformerTheory.UNIT_DEF,
                     pred_setTheory.GSPEC_F, probTheory.PROB_BERN_EMPTY]);

val miller_rabin_uniform_def = Define
  `miller_rabin_uniform n =
   if n <= 2 then UNIT 0
   else
     BIND (prob_uniform_cut (2 * log2 (n - 1)) (n - 2)) (\a. UNIT (a + 2n))`;

val miller_rabin_uniform_list_def = Define
  `(miller_rabin_uniform_list n 0 = UNIT []) /\
   (miller_rabin_uniform_list n (SUC m) =
    BIND (miller_rabin_uniform n)
      (\a. BIND (miller_rabin_uniform_list n m) (\l. UNIT (a :: l))))`;

val miller_rabin_list_empty = prove
  (``!n.
       ~(n = 1) /\ ~EVEN n ==>
       (miller_rabin_list n [] = T)``,
   RW_TAC std_ss [miller_rabin_list_def, EXISTS_DEF]);

val miller_rabin_list_single = prove
  (``!n x.
       ~(n = 1) /\ ~EVEN n ==>
       (miller_rabin_list n [x] = ~witness n x)``,
   RW_TAC std_ss [miller_rabin_list_def, EXISTS_DEF]
   ++ Know `EVEN 2` >> RW_TAC std_ss []
   ++ METIS_TAC []);

val miller_rabin_list_append = prove
  (``!n l l'.
       ~(n = 1) /\ ~EVEN n ==>
       (miller_rabin_list n (APPEND l l') =
        miller_rabin_list n l /\ miller_rabin_list n l')``,
   RW_TAC std_ss []
   ++ Induct_on `l`
   ++ RW_TAC std_ss [APPEND, miller_rabin_list_empty]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [miller_rabin_list_def, EXISTS_DEF]
   ++ Know `EVEN 2` >> RW_TAC std_ss []
   ++ METIS_TAC []);

val indep_fn_miller_rabin_uniform = prove
  (``!n. miller_rabin_uniform n IN indep_fn``,
   RW_TAC std_ss [miller_rabin_uniform_def, probTheory.INDEP_FN_UNIT]
   ++ Cases_on `n - 2`
   >> (Suff `F` >> PROVE_TAC []
       ++ DECIDE_TAC)
   ++ RW_TAC std_ss [probTheory.INDEP_FN_UNIT,
                     probTheory.INDEP_FN_BIND,
                     prob_uniformTheory.INDEP_FN_PROB_UNIFORM_CUT]);

val indep_fn_miller_rabin_uniform_list = prove
  (``!n m. miller_rabin_uniform_list n m IN indep_fn``,
   Induct_on `m`
   ++ RW_TAC std_ss [miller_rabin_uniform_list_def,
                     probTheory.INDEP_FN_BIND,
                     probTheory.INDEP_FN_UNIT,
                     indep_fn_miller_rabin_uniform]);

val miller_rabin_list_many_longcircuit = prove
  (``!n m.
       ~(n = 1) /\ ~EVEN n ==>
       (BIND (miller_rabin_uniform_list n m)
          (\l. UNIT (miller_rabin_list n l)) =
        many_longcircuit
          (BIND (miller_rabin_uniform n) (\a. UNIT (~witness n a))) T m)``,
   RW_TAC std_ss []
   ++ Suff
      `!m q. 
         BIND (miller_rabin_uniform_list n m)
           (\l. UNIT (miller_rabin_list n (APPEND q l))) =
         many_longcircuit
           (BIND (miller_rabin_uniform n)
             (\a. UNIT (~witness n a))) (miller_rabin_list n q) m`
   >> (DISCH_THEN (MP_TAC o Q.SPECL [`m`,`[]`])
       ++ RW_TAC std_ss [APPEND, miller_rabin_list_empty])
   ++ Induct
   ++ RW_TAC std_ss [miller_rabin_uniform_list_def, many_longcircuit_def,
                     state_transformerTheory.BIND_LEFT_UNIT, APPEND_NIL]
   ++ RW_TAC std_ss [GSYM state_transformerTheory.BIND_ASSOC]
   ++ AP_TERM_TAC
   ++ ONCE_REWRITE_TAC [FUN_EQ_THM]
   ++ RW_TAC std_ss []
   ++ RW_TAC std_ss [state_transformerTheory.BIND_LEFT_UNIT]
   ++ Know `!l. q ++ (x :: l) = (q ++ [x]) ++ l`
   >> (GEN_TAC
       ++ Induct_on `q`
       ++ RW_TAC std_ss [APPEND])
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   ++ POP_ASSUM (fn th => ONCE_REWRITE_TAC [Q.SPEC `q ++ [x]` th])
   ++ RW_TAC std_ss [miller_rabin_list_append, miller_rabin_list_single]);

val miller_rabin_equivalence = prove
  (``!n m.
       ~(n = 1) /\ ~EVEN n ==>
       (many (BIND (miller_rabin_uniform n) (\a. UNIT (~witness n a))) m =
        miller_rabin$miller_rabin n m)``,
   RW_TAC std_ss [miller_rabinTheory.miller_rabin_def]
   ++ Induct_on `m`
   ++ RW_TAC std_ss [probTheory.MANY]
   ++ POP_ASSUM (K ALL_TAC)
   ++ AP_THM_TAC
   ++ ONCE_REWRITE_TAC [FUN_EQ_THM]
   ++ ONCE_REWRITE_TAC [FUN_EQ_THM]
   ++ Cases_on `n = 2`
   >> (RW_TAC std_ss []
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC std_ss [])
   ++ Cases_on `n <= 2`
   >> (Suff `F` >> DECIDE_TAC
       ++ Suff `~(n = 0)` >> DECIDE_TAC
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `~EVEN n` MP_TAC
       ++ RW_TAC std_ss [])
   ++ RW_TAC std_ss [state_transformerTheory.BIND_DEF,
                     state_transformerTheory.UNIT_DEF,
                     miller_rabinTheory.miller_rabin_1_def,
                     miller_rabin_uniform_def]
   ++ RW_TAC std_ss [UNCURRY, FST, SND]);

val MILLER_RABIN_COMPOSITE_ERROR = store_thm
  ("MILLER_RABIN_COMPOSITE_ERROR",
   ``!n m.
       ~prime n ==>
       prob bern {s | FST (BIND (miller_rabin_uniform_list n m)
                                (\l. UNIT (miller_rabin_list n l)) s)} <=
       (1 / 2) pow m``,
   RW_TAC std_ss []
   ++ Cases_on `n = 1`
   >> (RW_TAC std_ss [miller_rabin_list_def,
                      state_transformerTheory.BIND_DEF,
                      state_transformerTheory.UNIT_DEF, UNCURRY,
                      pred_setTheory.GSPEC_F, probTheory.PROB_BERN_EMPTY]
       ++ MATCH_MP_TAC realTheory.POW_POS
       ++ RW_TAC std_ss [realTheory.REAL_HALF_BETWEEN])
   ++ Cases_on `EVEN n`
   >> (Know `~(n = 2)` >> METIS_TAC [extra_arithTheory.PRIME_2]
       ++ RW_TAC std_ss [miller_rabin_list_def,
                         state_transformerTheory.BIND_DEF,
                         state_transformerTheory.UNIT_DEF, UNCURRY,
                         pred_setTheory.GSPEC_F, probTheory.PROB_BERN_EMPTY]
       ++ MATCH_MP_TAC realTheory.POW_POS
       ++ RW_TAC std_ss [realTheory.REAL_HALF_BETWEEN])
   ++ RW_TAC std_ss [miller_rabin_list_many_longcircuit]
   ++ RW_TAC std_ss [many_longcircuit_t, probTheory.INDEP_FN_BIND,
                     probTheory.INDEP_FN_UNIT, indep_fn_miller_rabin_uniform]
   ++ RW_TAC std_ss [miller_rabin_equivalence]
   ++ METIS_TAC [MILLER_RABIN_COMPOSITE_UPPER]);

(* The top-level specification when the input number n is prime: *)
(* whatever the input list l of bases, miller_rabin_list n l will always *)
(* return true. *)

val MILLER_RABIN_PRIME = store_thm
  ("MILLER_RABIN_PRIME",
   ``!n l.
       prime n /\ EVERY (\a. 0 < a /\ a < n) l ==>
       (miller_rabin_list n l = T)``,
   RW_TAC bool_ss [miller_rabin_list_def]
   ++ Cases_on `EVEN n` >> METIS_TAC [extra_arithTheory.NOT_PRIME_EVEN]
   ++ Cases_on `n = 1` >> METIS_TAC [dividesTheory.NOT_PRIME_1]
   ++ RW_TAC bool_ss []
   ++ DISJ2_TAC
   ++ Induct_on `l`
   ++ RW_TAC bool_ss [EXISTS_DEF,EVERY_DEF]
   ++ METIS_TAC [WITNESS_CORRECT]);

(* The top-level specification when the input number n is composite: *)
(* If the input list l consists of m bases chosen uniformly at random, the *)
(* probability that miller_rabin_list n l returns false is at least *)
(* 1 - (1/2)^m. *)

val MILLER_RABIN_COMPOSITE = store_thm
  ("MILLER_RABIN_COMPOSITE",
   ``!n m.
       ~prime n ==>
       1 - (1 / 2) pow m <=
       prob bern {s | FST (BIND (miller_rabin_uniform_list n m)
                                (\l. UNIT (miller_rabin_list n l)) s) = F}``,
   RW_TAC std_ss []
   ++ Know
      `{s | ~FST (BIND (miller_rabin_uniform_list n m)
                       (\l. UNIT (miller_rabin_list n l)) s)} =
       COMPL (I o FST o BIND (miller_rabin_uniform_list n m)
                             (\l. UNIT (miller_rabin_list n l)))`
   >> (ONCE_REWRITE_TAC [pred_setTheory.EXTENSION]
       ++ RW_TAC std_ss [pred_setTheory.GSPECIFICATION,
                         pred_setTheory.IN_COMPL]
       ++ RW_TAC std_ss [pred_setTheory.SPECIFICATION, o_THM, I_THM])
   ++ DISCH_THEN (fn th => REWRITE_TAC [th])
   ++ RW_TAC std_ss [probabilityTheory.PROB_COMPL,
                     probTheory.PROB_SPACE_BERN,
                     probTheory.INDEP_FN_FST_EVENTS,
                     probTheory.INDEP_FN_BIND,
                     probTheory.INDEP_FN_UNIT,
                     indep_fn_miller_rabin_uniform_list]
   ++ Know `!a b c : real. c <= b ==> a - b <= a - c`
   >> RealArith.REAL_ARITH_TAC
   ++ DISCH_THEN MATCH_MP_TAC
   ++ MATCH_MP_TAC realTheory.REAL_LE_TRANS
   ++ Q.EXISTS_TAC
        `prob bern {s | FST (BIND (miller_rabin_uniform_list n m)
                                  (\l. UNIT (miller_rabin_list n l)) s)}`
   ++ REVERSE CONJ_TAC >> METIS_TAC [MILLER_RABIN_COMPOSITE_ERROR]
   ++ Know `!a b : real. (a = b) ==> a <= b`
   >> RealArith.REAL_ARITH_TAC
   ++ DISCH_THEN MATCH_MP_TAC
   ++ AP_TERM_TAC
   ++ ONCE_REWRITE_TAC [pred_setTheory.EXTENSION]
   ++ RW_TAC std_ss [pred_setTheory.GSPECIFICATION]
   ++ RW_TAC std_ss [pred_setTheory.SPECIFICATION]);

(***
(* ------------------------------------------------------------------------- *)
(* Versions of the definitions suitable for exporting to ML                  *)
(* ------------------------------------------------------------------------- *)

val UNCURRY_ML = save_thm ("UNCURRY_ML", pairTheory.UNCURRY_DEF);

val EVEN_ML = store_thm
  ("EVEN_ML",
   ``!n. EVEN n = (n MOD 2 = 0)``,
   STRIP_TAC
   ++ RW_TAC std_ss [MOD_TWO]
   ++ DECIDE_TAC);

val ODD_ML = store_thm
  ("ODD_ML",
   ``ODD = $~ o EVEN``,
   RW_TAC std_ss [o_DEF, EVEN_ODD, FUN_EQ_THM]);

val UNIT_ML = store_thm
  ("UNIT_ML",
   ``!x. UNIT x = \s. (x, s)``,
   RW_TAC std_ss [UNIT_DEF]);

val BIND_ML = store_thm
  ("BIND_ML",
   ``!f g. BIND f g = UNCURRY g o f``,
   RW_TAC std_ss [BIND_DEF]);

val MANY_ML = store_thm
  ("MANY_ML",
   ``!f n.
       many f n =
       if n = 0 then UNIT T
       else BIND f (\x. if x then many f (n - 1) else UNIT F)``,
   STRIP_TAC
   ++ Cases
   ++ RW_TAC std_ss [MANY, SUC_SUB1]);

val LOG2_ML = store_thm
  ("LOG2_ML",
   ``!n. log2 n = if n = 0 then 0 else SUC (log2 (n DIV 2))``,
   Cases
   ++ RW_TAC std_ss [log2_def, SUC_SUB1]);

val PROB_UNIF_ML = store_thm
  ("PROB_UNIF_ML",
   ``!n s.
        prob_unif n s =
        if n = 0 then (0, s)
        else
          let (m, s') = prob_unif (n DIV 2) s
          in (if shd s' then 2 * m + 1 else 2 * m, stl s')``,
   Cases
   ++ RW_TAC std_ss [prob_unif_def, SUC_SUB1]);

val PROB_UNIFORM_CUT_ML = store_thm
  ("PROB_UNIFORM_CUT_ML",
   ``!t n.
       prob_uniform_cut t n =
       if n = 0 then prob_uniform_cut t n
       else if t = 0 then UNIT 0
       else
         BIND (prob_unif (n - 1))
         (\m. if m < n then UNIT m else prob_uniform_cut (t - 1) n)``,
   Cases
   ++ Cases
   ++ RW_TAC std_ss [PROB_UNIFORM_CUT_MONAD, SUC_SUB1]);

val FACTOR_TWOS_ML = save_thm ("FACTOR_TWOS_ML", factor_twos_def);

val MODEXP_ML = save_thm ("MODEXP_ML", modexp_def);

val WITNESS_TAIL_ML = store_thm
  ("WITNESS_TAIL_ML",
   ``!n a r.
       witness_tail r n a =
       if r = 0 then ~(a = 1)
       else
         let a2 = (a * a) MOD n
         in if a2 = 1 then ~(a = 1) /\ ~(a = n - 1)
            else witness_tail (r - 1) n a2``,
   Cases_on `r`
   ++ RW_TAC std_ss [witness_tail_def, SUC_SUB1]);

val WITNESS_ML = save_thm ("WITNESS_ML", witness_def);

val MILLER_RABIN_LIST_ML =
    save_thm ("MILLER_RABIN_LIST_ML", miller_rabin_list_def);
***)

(* ------------------------------------------------------------------------- *)
(* Converting the definitions to HOL/SEXP ... with tracing                   *)
(* ------------------------------------------------------------------------- *)

set_trace "EncodeLib.FunctionEncoding" 1;

val (list_natp_rewrite,list_natp_def) = get_recogniser ``:num list``;

(* ACL2 doesn't have this lemma, so include it for sake of termination *)
val div_terminate =  prove(``!a. 0 < a ==> a DIV 2 < a``,RW_TAC arith_ss [DIV_LT_X]);

val (_,acl2_factor_twos_def) = 		
	convert_definition_full 
		(SOME ``\a. 0 < a ==> a DIV 2 < a``) 
		[div_terminate,DECIDE ``~(2 = 0n)``] 
	factor_twos_def

val (_,acl2_modexp_def) = 		
	convert_definition_full 
		(SOME ``\a b c. ~(a = 0n) /\ (0 < c ==> c DIV 2 < c)``) 
		[div_terminate,DECIDE ``~(2 = 0n)``]  
	modexp_def;

val (_,acl2_witness_tail_def) = 	
	convert_definition_full 
		(SOME ``\a b c. ~(b = 0n)``) 
		[]
	witness_tail_def;

val (_,acl2_witness_def) = 	
	convert_definition_full 
		(SOME ``\a b.~(a = 0n)``)
		[]
	witness_def;

val (_,acl2_exists_ho_def) = 
	convert_definition 
	(INST_TYPE [``:'a`` |-> ``:num``] EXISTS_DEF);

val (miller_rabin_list_correct,acl2_miller_rabin_list_def) = 
	convert_definition_full 
		(SOME ``\a b. ~(a = 0n)``) 
		[]
	miller_rabin_list_def;

val (witness_rewrite,acl2_exists_witness_def) = 
	flatten_HO_definition "acl2_exists_witness" acl2_exists_ho_def 
		``acl2_EXISTS (\x. ite (natp x) (acl2_witness n x) (acl2_witness n (nat 0))) l``;

(* ------------------------------------------------------------------------- *)
(* Print out the definitions (removing 'andl')                               *)
(* ------------------------------------------------------------------------- *)

open TextIO sexp; 

val outs = openOut(FileSys.fullPath "../lisp/miller-rabin.lisp");

fun output_thm thm = 
let	val string = ref ""
	val _ = (print_mlsexp (fn s => string := (!string) ^ s) o 
			def_to_mlsexp_defun o REWRITE_RULE [sexpTheory.andl_def]) thm
	val _ = string := (!string) ^ "\n\n"
in
	(print (!string) ; output(outs,!string))
end;

val _ = output(outs,"(in-package \"ACL2\")\n\n");

val _ = output_thm acl2_factor_twos_def;
val _ = output_thm acl2_modexp_def;
val _ = output_thm acl2_witness_tail_def;
val _ = output_thm acl2_witness_def;
val _ = output_thm list_natp_def;
val _ = output_thm (REWRITE_RULE [list_natp_rewrite] acl2_exists_witness_def);
val _ = output_thm (REWRITE_RULE [list_natp_rewrite,witness_rewrite] acl2_miller_rabin_list_def);

val _ = closeOut outs;

(* ------------------------------------------------------------------------- *)
(* Equivalence between miller_rabin_list and the acl2 version                *)
(* ------------------------------------------------------------------------- *)

val _ = (print_thm miller_rabin_list_correct ; print "\n");

val miller_rabin_list_correct2 = 
	DISCH_ALL (REWRITE_RULE [SEXP_TO_BOOL_OF_BOOL] 
		(AP_TERM ``sexp_to_bool`` (UNDISCH (SPEC_ALL miller_rabin_list_correct))));

val miller_rabin_list_correct2 = 
	prove(``~(n = 0) ==>
	       (miller_rabin_list n =
        	sexp_to_bool o acl2_miller_rabin_list (nat n) o list nat)``,
	RW_TAC arith_ss [FUN_EQ_THM] THEN MATCH_MP_TAC miller_rabin_list_correct2
	THEN FIRST_ASSUM ACCEPT_TAC);
