(* ========================================================================= *)
(* miller_rabin_def theory                                                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories.                                          *)
(* (Comment out "load"s and "quietdec"s for compilation.)                    *)
(* ------------------------------------------------------------------------- *)
(*
*)

val () = loadPath := [] @ !loadPath;
val () = app load
  ["bossLib", "metisLib",
   "pairTheory", "combinTheory", "listTheory", "arithmeticTheory",
   "state_transformerTheory","encodeLib"];
val () = quietdec := true;

open HolKernel Parse boolLib bossLib metisLib;
open pairTheory combinTheory listTheory arithmeticTheory;
open state_transformerTheory encodeLib;

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
   ++ RW_TAC std_ss [] <<
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

(* ------------------------------------------------------------------------- *)
(* Definitions to port to ACL2.                                              *)
(* ------------------------------------------------------------------------- *)

val (log2_def,log2_ind) =
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

val _ = save_thm ("factor_twos_def", factor_twos_def);
val _ = save_thm ("factor_twos_ind", factor_twos_ind);

val (modexp_def,modexp_ind) =
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


val _ = save_thm ("modexp_def", modexp_def);
val _ = save_thm ("modexp_ind", modexp_ind);

val witness_tail_def =
    Define
      `(witness_tail 0 n a = ~(a = 1)) /\
       (witness_tail (SUC r) n a =
        let a2 = (a * a) MOD n in
        if a2 = 1 then ~(a = 1) /\ ~(a = n - 1)
        else witness_tail r n a2)`;

val witness_def =
    Define
      `witness n a =
       let (r, s) = factor_twos (n - 1) in
       witness_tail r n (modexp n a s)`;

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
(* Definitions to keep in HOL, since they involve boolean sequences.         *)
(* ------------------------------------------------------------------------- *)

val shd_def = Define `shd (f : num -> 'a) = f 0`;

val stl_def = Define `stl (f : num -> 'a) n = f (SUC n)`;

val prob_while_cut_def = Define
  `(prob_while_cut c b 0 a = UNIT a) /\
   (prob_while_cut c b (SUC n) a =
    if c a then BIND (b a) (prob_while_cut c b n) else UNIT a)`;

val many_def = Define `many f n = prob_while_cut I (K f) n T`;

val (prob_unif_def,prob_unif_ind) = Defn.tprove
  let val d = Hol_defn "prob_unif"
        `(prob_unif 0 s = (0:num, s))
         /\ (prob_unif n s = let (m, s') = prob_unif (n DIV 2) s
	                in (if shd s' then 2 * m + 1 else 2 * m, stl s'))`
      val g = `measure (\(x,y). x)`
  in (d,
      WF_REL_TAC g
      ++ STRIP_TAC
      ++ Know `2 * (SUC v2 DIV 2) <= SUC v2`
      >> PROVE_TAC [TWO, DIV_THEN_MULT]
      ++ DECIDE_TAC)
  end;

val _ = save_thm ("prob_unif_def", prob_unif_def);
val _ = save_thm ("prob_unif_ind", prob_unif_ind);
 
val prob_uniform_cut_def = Define
  `(prob_uniform_cut 0 (SUC n) s = (0, s)) /\
   (prob_uniform_cut (SUC u) (SUC n) s =
    let (res, s') = prob_unif n s
    in if res < SUC n then (res, s') else prob_uniform_cut u (SUC n) s')`;

(***
Must change this to use the new list version.

val miller_rabin_def = Define `miller_rabin n t = many (miller_rabin_1 n) t`;
***)

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val MANY = store_thm
  ("MANY",
   ``!f n.
       (many f 0 = UNIT T) /\
       (many f (SUC n) = BIND f (\s. if s then many f n else UNIT F))``,
   RW_TAC std_ss [many_def, prob_while_cut_def, K_THM, I_THM,
                  BIND_DEF, UNCURRY, o_THM, UNIT_DEF, FUN_EQ_THM]
   ++ Cases_on `n`
   ++ RW_TAC std_ss [many_def, prob_while_cut_def, K_THM, I_THM,
                     BIND_DEF, UNCURRY, o_THM, UNIT_DEF]
   ++ Cases_on `f x`
   ++ FULL_SIMP_TAC std_ss []);

val PROB_UNIFORM_CUT_MONAD = store_thm
  ("PROB_UNIFORM_CUT_MONAD",
   ``(!n. prob_uniform_cut 0 (SUC n) = UNIT 0) /\
     (!t n.
        prob_uniform_cut (SUC t) (SUC n) =
        BIND (prob_unif n)
        (\m. if m < SUC n then UNIT m else prob_uniform_cut t (SUC n)))``,
   RW_TAC std_ss [BIND_DEF, UNIT_DEF, o_DEF, prob_uniform_cut_def,
                  FUN_EQ_THM, LET_DEF, UNCURRY]
   ++ RW_TAC std_ss []);

(***
The top-level specification when the input number is prime

val MILLER_RABIN_PRIME = store_thm
  ("MILLER_RABIN_PRIME",
   ``!n t s. prime n ==> FST (miller_rabin n t s) = T``)
***)

(***
The top-level specification when the input number is composite

val MILLER_RABIN_COMPOSITE = store_thm
  ("MILLER_RABIN_COMPOSITE",
   ``!n t.
       ~prime n ==>
        1 - (1 / 2) pow t <= prob bern {s | FST (miller_rabin n t s) = F}``)
***)

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

(***
val MILLER_RABIN_ML = save_thm ("MILLER_RABIN_ML", miller_rabin_def);
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
