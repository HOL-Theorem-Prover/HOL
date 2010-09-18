structure quantHeuristicsScript =
struct


open HolKernel Parse boolLib Drule BasicProvers
     pairTheory listTheory optionTheory metisLib simpLib
     boolSimps pureSimps TotalDefn numLib ConseqConv

val _ = new_theory "quantHeuristics";

(*
quietdec := false;
*)



val GUESS_EXISTS_def = Define `
    GUESS_EXISTS i P = ((?v. P v) = (?fv. P (i fv)))`

val GUESS_FORALL_def = Define `
    GUESS_FORALL i P = ((!v. P v) = (!fv. P (i fv)))`

val GUESS_EXISTS_FORALL_REWRITES = store_thm ("GUESS_EXISTS_FORALL_REWRITES",
``(GUESS_EXISTS i P = (!v. P v ==> (?fv. P (i fv)))) /\
  (GUESS_FORALL i P = (!v. ~(P v) ==> (?fv. ~(P (i fv)))))``,
SIMP_TAC std_ss [GUESS_EXISTS_def, GUESS_FORALL_def] THEN
METIS_TAC[]);


val GUESS_TRUE_def = Define `
    GUESS_TRUE i P = (!fv. P (i fv))`

val GUESS_FALSE_def = Define `
    GUESS_FALSE i P = (!fv. ~(P (i fv)))`

val GUESS_TRUE_FALSE_THM = store_thm ("GUESS_TRUE_FALSE_THM",
``(GUESS_TRUE i P ==> ((?v. P v) = T)) /\
  (GUESS_FALSE i P ==> ((!v. P v) = F))``,
SIMP_TAC std_ss [GUESS_TRUE_def, GUESS_FALSE_def] THEN
METIS_TAC[]);


val GUESS_EXISTS_STRONG_def = Define `
    GUESS_EXISTS_STRONG i P =
       (!v. P v ==> (?fv. v = (i fv)))`;

val GUESS_FORALL_STRONG_def = Define `
    GUESS_FORALL_STRONG i P =
       (!v. ~(P v) ==> (?fv. v = (i fv)))`;


val GUESS_REWRITES = save_thm ("GUESS_REWRITES",
   LIST_CONJ [GUESS_EXISTS_FORALL_REWRITES, GUESS_TRUE_def, GUESS_FALSE_def,
      GUESS_EXISTS_STRONG_def, GUESS_FORALL_STRONG_def]);




(******************************************************************************)
(* Now the intended semantic                                                  *)
(******************************************************************************)

val GUESS_TRUE_THM = store_thm ("GUESS_TRUE_THM",
``!i P. GUESS_TRUE i P ==> ($? P = T)``,
SIMP_TAC std_ss [GUESS_TRUE_def, EXISTS_THM] THEN
METIS_TAC[]);

val GUESS_FALSE_THM = store_thm ("GUESS_FALSE_THM",
``!i P. GUESS_FALSE i P ==> (($! P) = F)``,
SIMP_TAC std_ss [GUESS_REWRITES, FORALL_THM] THEN
METIS_TAC[]);

val GUESS_EXISTS_THM = store_thm ("GUESS_EXISTS_THM",
``!i P. GUESS_EXISTS i P ==> ($? P = ?fv. P (i fv))``,
SIMP_TAC std_ss [GUESS_REWRITES, EXISTS_THM] THEN
METIS_TAC[]);

val GUESS_FORALL_THM = store_thm ("GUESS_FORALL_THM",
``!i P. GUESS_FORALL i P ==> (($! P) = !fv. P (i fv))``,
SIMP_TAC std_ss [GUESS_REWRITES, FORALL_THM] THEN
METIS_TAC[]);


val GUESSES_UEXISTS_THM1 = store_thm("GUESSES_UEXISTS_THM1",
``!i P. GUESS_EXISTS (\x. i) P ==>
        ($?! P = ((P i) /\ (!v. P v ==> (v = i))))``,
SIMP_TAC std_ss [GUESS_REWRITES, combinTheory.K_DEF] THEN
METIS_TAC[]);

val GUESSES_UEXISTS_THM2 = store_thm("GUESSES_UEXISTS_THM2",
``!i P. GUESS_EXISTS_STRONG (\x. i) P ==> ($?! P = P i)``,
SIMP_TAC std_ss [GUESS_REWRITES, combinTheory.K_DEF] THEN
METIS_TAC[]);

val GUESSES_UEXISTS_THM3 = store_thm("GUESSES_UEXISTS_THM3",
``!i P. GUESS_TRUE (\x. i) P ==>
        ($?! P = (!v. P v ==> (v = i)))``,
SIMP_TAC std_ss [GUESS_REWRITES, combinTheory.K_DEF] THEN
METIS_TAC[]);


val GUESSES_NEG_DUALITY = store_thm ("GUESSES_NEG_DUALITY",
``(GUESS_EXISTS i ($~ o P) =
   GUESS_FORALL i P) /\

  (GUESS_FORALL i ($~ o P) =
   GUESS_EXISTS i P) /\

  (GUESS_EXISTS_STRONG i ($~ o P) =
   GUESS_FORALL_STRONG i P) /\

  (GUESS_FORALL_STRONG i ($~ o P) =
   GUESS_EXISTS_STRONG i P) /\

  (GUESS_TRUE  i ($~ o P) =
   GUESS_FALSE i P) /\

  (GUESS_FALSE i ($~ o P) =
   GUESS_TRUE  i P)``,

SIMP_TAC std_ss [GUESS_REWRITES, combinTheory.o_DEF]);


val GUESSES_NEG_REWRITE = save_thm ("GUESSES_NEG_REWRITE",
SIMP_RULE std_ss [combinTheory.o_DEF]
  (INST [``P:'b -> bool`` |-> ``\x:'b. (P x):bool``] GUESSES_NEG_DUALITY));


val GUESSES_WEAKEN_THM = store_thm ("GUESSES_WEAKEN_THM",
``(GUESS_FORALL_STRONG i P ==> GUESS_FORALL i P) /\
  (GUESS_FALSE         i P ==> GUESS_FORALL i P) /\
  (GUESS_TRUE          i P ==> GUESS_EXISTS i P) /\
  (GUESS_EXISTS_STRONG i P ==> GUESS_EXISTS i P)``,

SIMP_TAC std_ss [GUESS_REWRITES] THEN
METIS_TAC[]);



(******************************************************************************)
(* Equations                                                                  *)
(******************************************************************************)

val GUESS_RULES_EQUATION_TRUE = store_thm ("GUESS_RULES_EQUATION_TRUE",
``!i P Q. 
  (P i = Q i) ==>
  GUESS_TRUE (\xxx:unit. i) (\x. P x = Q x)``,
SIMP_TAC std_ss [GUESS_REWRITES]);

val GUESS_RULES_EQUATION_FALSE = store_thm ("GUESS_RULES_EQUATION_FALSE",
``!i P Q. 
  (!fv. ~(P (i fv) = Q (i fv))) ==>
  GUESS_FALSE i (\x. P x = Q x)``,
SIMP_TAC std_ss [GUESS_REWRITES]);

val GUESS_RULES_EQUATION_EXISTS_STRONG = store_thm ("GUESS_RULES_EQUATION_EXISTS_STRONG",
``!i.
  GUESS_EXISTS_STRONG (\xxx:unit. i) (\x. x = i)``,
SIMP_TAC std_ss [GUESS_REWRITES] THEN
METIS_TAC[]);


(******************************************************************************)
(* Trivial booleans                                                           *)
(******************************************************************************)

val GUESS_RULES_BOOL = store_thm ("GUESS_RULES_BOOL",
``GUESS_TRUE (\ARB:unit. T) (\x. x) /\
  GUESS_FALSE (\ARB:unit. F) (\x. x) /\
  GUESS_EXISTS_STRONG (\ARB:unit. T) (\x. x) /\
  GUESS_FORALL_STRONG (\ARB:unit. F) (\x. x)``,
SIMP_TAC std_ss [GUESS_REWRITES]);



(******************************************************************************)
(* Cases                                                                      *)
(******************************************************************************)

val GUESS_RULES_TWO_CASES = store_thm ("GUESS_RULES_TWO_CASES",
``!y Q. ((!x. ((x = y) \/ (?fv. x = Q fv)))) ==>
  GUESS_FORALL_STRONG Q (\x. x = y)``,
SIMP_TAC std_ss [GUESS_REWRITES] THEN
METIS_TAC[]);

val GUESS_RULES_ONE_CASE___FORALL_STRONG = store_thm ("GUESS_RULES_ONE_CASE___FORALL_STRONG",
``!P Q. ((!x:'a. (?fv. x = Q fv))) ==>
  GUESS_FORALL_STRONG Q (P:'a -> bool)``,
SIMP_TAC std_ss [GUESS_REWRITES]);

val GUESS_RULES_ONE_CASE___EXISTS_STRONG = store_thm ("GUESS_RULES_ONE_CASE___EXISTS_STRONG",
``!P Q. ((!x:'a. (?fv. x = Q fv))) ==>
  GUESS_EXISTS_STRONG Q (P:'a -> bool)``,
SIMP_TAC std_ss [GUESS_REWRITES]);


(******************************************************************************)
(* Boolean operators                                                          *)
(******************************************************************************)

val GUESS_RULES_NEG = store_thm ("GUESS_RULES_NEG",
``(GUESS_EXISTS i (\x. P x) ==>
   GUESS_FORALL i (\x. ~(P x))) /\

  (GUESS_EXISTS_STRONG i (\x. P x) ==>
   GUESS_FORALL_STRONG i (\x. ~(P x))) /\

  (GUESS_TRUE  i (\x. P x) ==>
   GUESS_FALSE i (\x. ~(P x))) /\

  (GUESS_FORALL i (\x. P x) ==>
   GUESS_EXISTS i (\x. ~(P x))) /\

  (GUESS_FORALL_STRONG i (\x. P x) ==>
   GUESS_EXISTS_STRONG i (\x. ~(P x))) /\

  (GUESS_FALSE i (\x. P x) ==>
   GUESS_TRUE  i (\x. ~(P x)))``,

SIMP_TAC std_ss [GUESSES_NEG_REWRITE]);


val GUESS_RULES_CONSTANT_EXISTS = store_thm ("GUESS_RULES_CONSTANT_EXISTS",
``(GUESS_EXISTS i (\x. p)) = T``,
SIMP_TAC std_ss [GUESS_REWRITES]);

val GUESS_RULES_CONSTANT_FORALL = store_thm ("GUESS_RULES_CONSTANT_FORALL",
``(GUESS_FORALL i (\x. p)) = T``,
SIMP_TAC std_ss [GUESS_REWRITES]);


val GUESS_RULES_DISJ = store_thm ("GUESS_RULES_DISJ",
``(GUESS_TRUE i (\x. P x) ==>
   GUESS_TRUE i (\x. P x \/ Q x)) /\

  (GUESS_TRUE i (\x. Q x) ==>
   GUESS_TRUE i (\x. P x \/ Q x)) /\

  (GUESS_EXISTS i (\x. P x) /\
   GUESS_EXISTS i (\x. Q x) ==>
   GUESS_EXISTS i (\x. P x \/ Q x)) /\

  (GUESS_EXISTS_STRONG i (\x. P x) /\
   GUESS_EXISTS_STRONG i (\x. Q x) ==>
   GUESS_EXISTS_STRONG i (\x. P x \/ Q x)) /\ 

  (GUESS_FORALL (\xxx:unit. iK) (\x. P x) /\
   GUESS_FORALL (\xxx:unit. iK) (\x. Q x) ==>
   GUESS_FORALL (\xxx:unit. iK) (\x. P x \/ Q x)) /\

  (GUESS_FORALL i (\x. P x) ==>
   GUESS_FORALL i (\x. P x \/ q)) /\

  (GUESS_FORALL i (\x. Q x) ==>
   GUESS_FORALL i (\x. p \/ Q x)) /\

  (GUESS_FALSE i (\x. P x) /\
   GUESS_FALSE i (\x. Q x) ==>
   GUESS_FALSE i (\x. P x \/ Q x)) /\

  (GUESS_FORALL_STRONG i (\x. P x) ==>
   GUESS_FORALL_STRONG i (\x. P x \/ Q x)) /\

  (GUESS_FORALL_STRONG i (\x. Q x) ==>
   GUESS_FORALL_STRONG i (\x. P x \/ Q x))``,

SIMP_TAC std_ss [GUESS_REWRITES, combinTheory.K_DEF] THEN
METIS_TAC[]);



val GUESS_RULES_CONJ = save_thm ("GUESS_RULES_CONJ",
let
   val thm0 = INST [
      ``P:'b->bool`` |-> ``$~ o (P:'b->bool)``,
      ``Q:'b->bool`` |-> ``$~ o (Q:'b->bool)``,
      ``p:bool`` |-> ``~p``,
      ``q:bool`` |-> ``~q``] GUESS_RULES_DISJ
   val thm1 = SIMP_RULE std_ss [GUESSES_NEG_REWRITE] thm0
   val thm2 = REWRITE_RULE [GSYM DE_MORGAN_THM] thm1
   val thm3 = SIMP_RULE std_ss [GUESSES_NEG_REWRITE] thm2
in
   thm3 
end);



val GUESS_RULES_IMP = save_thm ("GUESS_RULES_IMP",
let
   val thm0 = INST [
      ``P:'b->bool`` |-> ``$~ o (P:'b->bool)``,
      ``p:bool`` |-> ``~p``] GUESS_RULES_DISJ
   val thm1 = SIMP_RULE std_ss [GUESSES_NEG_REWRITE] thm0
   val thm2 = REWRITE_RULE [GSYM IMP_DISJ_THM] thm1
in
   thm2
end);


(*

Code for generating theorems with rewriting using the basic ones.
This is used for comming up with ideas for the lemma for
COND and EXISTS_UNIQUE


local

(*
val thmL = [GUESS_RULES_NEG, GUESS_RULES_DISJ, GUESS_RULES_CONJ,
            GUESS_RULES_IMP, GUESSES_RULES_CONSTANT_EXISTS, 
            GUESSES_RULES_CONSTANT_FORALL, ELIM_UNLICKLY_THM]

val tmL = [``\x:'a. P x <=> Q x``, ``\x. p <=> Q x``, ``\x. P x <=> q``]
val rewr = [EQ_EXPAND]
val tm = hd tmL

val currentL = prepare_org_thms rewr tmL
val ruleL = prepare_rules thmL
*)

val ELIM_UNLICKLY_THM = prove(
``(F ==> GUESS_TRUE i (\x. p)) /\
  (F ==> GUESS_FALSE i (\x. p)) /\
  (F ==> GUESS_EXISTS_STRONG i (\x. p)) /\
  (F ==> GUESS_FORALL_STRONG i (\x. p))``,
SIMP_TAC std_ss [])


fun prepare_org_thms rewr tmL =
let
   val thmL0 = map (fn t => REWRITE_CONV rewr t handle UNCHANGED => REFL t) tmL
   fun mk_guess_terms tm =
      ([``GUESS_TRUE (i:'b -> 'a) ^tm``,
       ``GUESS_FALSE (i:'b -> 'a) ^tm``,
       ``GUESS_EXISTS (i:'b -> 'a) ^tm``,
       ``GUESS_FORALL (i:'b -> 'a) ^tm``,
       ``GUESS_EXISTS_STRONG (i:'b -> 'a) ^tm``,
       ``GUESS_FORALL_STRONG (i:'b -> 'a) ^tm``],
      [``GUESS_TRUE (K (iK:'a)) ^tm``,
       ``GUESS_FALSE (K (iK:'a)) ^tm``,
       ``GUESS_EXISTS (K (iK:'a)) ^tm``,
       ``GUESS_FORALL (K (iK:'a)) ^tm``,
       ``GUESS_EXISTS_STRONG (K (iK:'a)) ^tm``,
       ``GUESS_FORALL_STRONG (K (iK:'a)) ^tm``])

   fun basic_thms Pthm =
   let
       val (xtmL1, xtmL2) = mk_guess_terms (rhs (concl Pthm));
       val xthmL1 = map ConseqConv.REFL_CONSEQ_CONV xtmL1;
       val xthmL2 = map ConseqConv.REFL_CONSEQ_CONV xtmL2;
       val Pthm' = GSYM Pthm;
       val xthmL1' = map (CONV_RULE (RAND_CONV (RAND_CONV (K Pthm')))) xthmL1
       val xthmL2' = map (CONV_RULE (RAND_CONV (RAND_CONV (K Pthm')))) xthmL2
   in
       (xthmL1', xthmL2')
   end;
             
   val (thmL1, thmL2) = unzip (map basic_thms thmL0); 
in
   (flatten thmL1, flatten thmL2)
end;


fun prepare_rules thmL =
   let
      val thmL' = flatten (map BODY_CONJUNCTS thmL);
   in
      map (fn thm => fn thm2 => SOME (ConseqConv.STRENGTHEN_CONSEQ_CONV_RULE
             (ConseqConv.CONSEQ_HO_REWRITE_CONV ([],[thm],[])) thm2) handle UNCHANGED => NONE) thmL'
   end


fun mapPartial f = ((map valOf) o (filter isSome) o (map f));

fun apply_rules ruleL doneL [] = doneL
  | apply_rules ruleL doneL (thm::currentL) =
    let
       val xthmL = mapPartial (fn r => r thm) ruleL;
    in
       if null xthmL then apply_rules ruleL (thm::doneL) currentL
       else apply_rules ruleL doneL (xthmL @ currentL)
    end;

in
   fun test_rules thmL rewr tmL =
   let
      val (currentL1, currentL2) = prepare_org_thms rewr tmL
      val ruleL = prepare_rules thmL;

      fun doit cL = 
        filter (fn x => not (same_const ((fst o dest_imp o concl) x) F)) 
          (apply_rules ruleL [] cL);

      val thmL1 =  doit currentL1;
      val thmL2 = doit currentL2;

      val thm1' = SIMP_RULE (std_ss++boolSimps.CONJ_ss) [] (LIST_CONJ thmL1)
      val thm2' = SIMP_RULE (std_ss++boolSimps.CONJ_ss) [thm1'] (LIST_CONJ thmL2)
   in
      CONJ thm2' thm1'
   end
end


*)

val GUESS_RULES_EQUIV = store_thm ("GUESS_RULES_EQUIV",
``(GUESS_TRUE i (\x. P x) /\
   GUESS_TRUE i (\x. Q x) ==>
   GUESS_TRUE i (\x. P x <=> Q x)) /\

  (GUESS_FALSE i (\x. P x) /\
   GUESS_FALSE i (\x. Q x) ==>
   GUESS_TRUE i (\x. P x <=> Q x)) /\

  (GUESS_TRUE i (\x. P x) /\
   GUESS_FALSE i (\x. Q x) ==>
   GUESS_FALSE i (\x. P x <=> Q x)) /\

  (GUESS_FALSE i (\x. P x) /\
   GUESS_TRUE i (\x. Q x) ==>
   GUESS_FALSE i (\x. P x <=> Q x)) /\

  (GUESS_FORALL_STRONG i (\x. P1 x) /\
   GUESS_FORALL_STRONG i (\x. P2 x) ==>
   GUESS_FORALL_STRONG i (\x. P1 x <=> P2 x)) /\

  (GUESS_EXISTS_STRONG i (\x. P1 x) /\
   GUESS_EXISTS_STRONG i (\x. P2 x) ==>
   GUESS_FORALL_STRONG i (\x. P1 x <=> P2 x)) /\

  (GUESS_EXISTS_STRONG i (\x. P1 x) /\
   GUESS_FORALL_STRONG i (\x. P2 x) ==>
   GUESS_EXISTS_STRONG i (\x. P1 x <=> P2 x)) /\

  (GUESS_FORALL_STRONG i (\x. P1 x) /\
   GUESS_EXISTS_STRONG i (\x. P2 x) ==>
   GUESS_EXISTS_STRONG i (\x. P1 x <=> P2 x))
``,

SIMP_TAC std_ss [GUESS_REWRITES, combinTheory.K_DEF] THEN
METIS_TAC[]);


val GUESS_RULES_COND = store_thm ("GUESS_RULES_COND",
`` (GUESS_FALSE i (\x. P x) /\
    GUESS_FALSE i (\x. Q x) ==>
    GUESS_FALSE i (\x. if b x then P x else Q x)) /\

   (GUESS_TRUE i (\x. P x) /\
    GUESS_TRUE i (\x. Q x) ==>
    GUESS_TRUE i (\x. if b x then P x else Q x)) /\

   (GUESS_EXISTS i (\x. P x) /\
    GUESS_EXISTS i (\x. Q x) ==>
    GUESS_EXISTS i (\x. if bc then P x else Q x)) /\

   (GUESS_FORALL i (\x. P x) /\
    GUESS_FORALL i (\x. Q x) ==>
    GUESS_FORALL i (\x. if bc then P x else Q x)) /\

   (GUESS_EXISTS_STRONG i (\x. P x) /\
    GUESS_EXISTS_STRONG i (\x. Q x) ==>
    GUESS_EXISTS_STRONG i (\x. if b x then P x else Q x)) /\

   (GUESS_FORALL_STRONG i (\x. P x) /\
    GUESS_FORALL_STRONG i (\x. Q x) ==>
    GUESS_FORALL_STRONG i (\x. if b x then P x else Q x)) /\


   (GUESS_FALSE i (\x. b x) /\
    GUESS_FALSE i (\x. Q x) ==>
    GUESS_FALSE i (\x. if b x then P x else Q x)) /\
 
   (GUESS_FALSE i (\x. b x) /\
    GUESS_TRUE i (\x. Q x) ==>
    GUESS_TRUE i (\x. if b x then P x else Q x)) /\

   (GUESS_TRUE i (\x. b x) /\
    GUESS_FALSE i (\x. P x) ==>
    GUESS_FALSE i (\x. if b x then P x else Q x)) /\
 
   (GUESS_TRUE i (\x. b x) /\
    GUESS_TRUE i (\x. P x) ==>
    GUESS_TRUE i (\x. if b x then P x else Q x)) /\

   (GUESS_FORALL_STRONG i (\x. b x) /\
    GUESS_EXISTS_STRONG i (\x. P x) ==>
    GUESS_EXISTS_STRONG i (\x. if b x then P x else Q x)) /\

   (GUESS_EXISTS_STRONG i (\x. b x) /\
    GUESS_EXISTS_STRONG i (\x. Q x) ==>
    GUESS_EXISTS_STRONG i (\x. if b x then P x else Q x)) /\

   (GUESS_EXISTS_STRONG i (\x. b x) /\
    GUESS_FORALL_STRONG i (\x. Q x) ==>
    GUESS_FORALL_STRONG i (\x. if b x then P x else Q x)) /\

   (GUESS_FORALL_STRONG i (\x. b x) /\
    GUESS_FORALL_STRONG i (\x. P x) ==>
    GUESS_FORALL_STRONG i (\x. if b x then P x else Q x))``,

SIMP_TAC std_ss [GUESS_REWRITES] THEN
METIS_TAC[]);



val GUESS_RULES_FORALL___NEW_FV = store_thm ("GUESS_RULES_FORALL___NEW_FV",
``((!y. GUESS_FALSE (iy y) (\x. P x y)) ==>
   GUESS_FALSE (\fv. iy (FST fv) (SND fv)) (\x. !y. P x y)) /\
  
  ((!y. GUESS_FORALL (iy y) (\x. P x y)) ==>
   GUESS_FORALL (\fv. iy (FST fv) (SND fv)) (\x. !y. P x y)) /\

  ((!y. GUESS_FORALL_STRONG (iy y) (\x. P x y)) ==>
   GUESS_FORALL_STRONG (\fv. iy (FST fv) (SND fv)) (\x. !y. P x y)) /\

  ((!y. GUESS_EXISTS_STRONG (iy y) (\x. P x y)) ==>
    GUESS_EXISTS_STRONG (\fv. iy (FST fv) (SND fv)) (\x. !y. P x y))``,

SIMP_TAC std_ss [GUESS_REWRITES, FORALL_PROD, EXISTS_PROD] THEN
METIS_TAC[]);


val GUESS_RULES_FORALL___NEW_FV_1 = store_thm ("GUESS_RULES_FORALL___NEW_FV_1",
``((!y. GUESS_FALSE (\xxx:unit. (i y)) (\x. P (x:'c) (y:'a))) ==>
   GUESS_FALSE i (\x. !y. P x y)) /\
  
  ((!y. GUESS_FORALL (\xxx:unit. (i y)) (\x. P x y)) ==>
   GUESS_FORALL i (\x. !y. P x y)) /\

  ((!y. GUESS_FORALL_STRONG (\xxx:unit. (i y)) (\x. P x y)) ==>
   GUESS_FORALL_STRONG i (\x. !y. P x y)) /\

  ((!y. GUESS_EXISTS_STRONG (\xxx:unit. (i y)) (\x. P x y)) ==>
    GUESS_EXISTS_STRONG i (\x. !y. P x y))``,

SIMP_TAC std_ss [GUESS_REWRITES, FORALL_PROD, EXISTS_PROD] THEN
METIS_TAC[]);



val GUESS_RULES_FORALL = store_thm ("GUESS_RULES_FORALL",
``((!y. GUESS_FALSE i (\x. P x y)) ==>
   GUESS_FALSE i (\x. !y. P x y)) /\
  
  ((!y. GUESS_FORALL i (\x. P x y)) ==>
   GUESS_FORALL i (\x. !y. P x y)) /\

  ((!y. GUESS_FORALL_STRONG i (\x. P x y)) ==>
   GUESS_FORALL_STRONG i (\x. !y. P x y)) /\

  ((!y. GUESS_TRUE i (\x. P x y)) ==>
   GUESS_TRUE i (\x. !y. P x y)) /\

  ((!y. GUESS_EXISTS (\xxx:unit. iK) (\x. P x y)) ==>
   GUESS_EXISTS (\xxx:unit. iK) (\x. !y. P x y)) /\

  ((!y. GUESS_EXISTS_STRONG i (\x. P x y)) ==>
    GUESS_EXISTS_STRONG i (\x. !y. P x y))``,

SIMP_TAC std_ss [GUESS_REWRITES, FORALL_PROD, EXISTS_PROD] THEN
METIS_TAC[]);



local

fun mk_exists_thm thm =
let
   val thm0 = INST [
      ``P:'c -> 'a -> bool`` |-> ``\x y. ~((P:'c -> 'a ->bool) x y)``] thm      
   val thm1 = BETA_RULE thm0
   val thm2 = SIMP_RULE pure_ss [GSYM NOT_FORALL_THM, GSYM NOT_EXISTS_THM,
        GUESSES_NEG_REWRITE] thm1
in
   thm2
end;

in

val GUESS_RULES_EXISTS___NEW_FV = save_thm ("GUESS_RULES_EXISTS___NEW_FV",
    mk_exists_thm GUESS_RULES_FORALL___NEW_FV);

val GUESS_RULES_EXISTS___NEW_FV_1= save_thm ("GUESS_RULES_EXISTS___NEW_FV_1",
    mk_exists_thm GUESS_RULES_FORALL___NEW_FV_1);

val GUESS_RULES_EXISTS = save_thm ("GUESS_RULES_EXISTS",
    mk_exists_thm GUESS_RULES_FORALL);

end


val GUESS_RULES_EXISTS_UNIQUE = store_thm ("GUESS_RULES_EXISTS_UNIQUE",
``((!y. GUESS_FALSE i (\x. P x y)) ==>
   GUESS_FALSE i (\x. ?!y. P x y)) /\

  ((!y. GUESS_EXISTS_STRONG i (\x. P x y)) ==>
   GUESS_EXISTS_STRONG i (\x. ?!y. P x y))``,

SIMP_TAC std_ss [GUESS_REWRITES, EXISTS_UNIQUE_THM]);


val QUANT_UNIT_ELIM = prove (``
  ((!x:unit. P x) = (P ())) /\
  ((?x:unit. P x) = (P ()))``,
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
  ASM_REWRITE_TAC[],
  Cases_on `x` THEN ASM_REWRITE_TAC[],
  Cases_on `x` THEN ASM_REWRITE_TAC[],
  EXISTS_TAC ``()`` THEN ASM_REWRITE_TAC[]
]);



val GUESS_RULES_ELIM_UNIT = store_thm ("GUESS_RULES_ELIM_UNIT",
``(GUESS_FALSE (i:('a # unit) -> 'b) vt =
   GUESS_FALSE (\x:'a. i (x,())) vt) /\

  (GUESS_TRUE (i:('a # unit) -> 'b) vt =
   GUESS_TRUE (\x:'a. i (x,())) vt) /\

  (GUESS_EXISTS (i:('a # unit) -> 'b) vt =
   GUESS_EXISTS (\x:'a. i (x,())) vt) /\

  (GUESS_FORALL (i:('a # unit) -> 'b) vt =
   GUESS_FORALL (\x:'a. i (x,())) vt) /\

  (GUESS_EXISTS_STRONG (i:('a # unit) -> 'b) vt =
   GUESS_EXISTS_STRONG (\x:'a. i (x,())) vt) /\

  (GUESS_FORALL_STRONG (i:('a # unit) -> 'b) vt =
   GUESS_FORALL_STRONG (\x:'a. i (x,())) vt)``,

SIMP_TAC std_ss [GUESS_REWRITES, FORALL_PROD, 
   EXISTS_PROD, QUANT_UNIT_ELIM]);




(*Basic theorems*)

val CONJ_NOT_OR_THM = store_thm ("CONJ_NOT_OR_THM",
``!A B. A /\ B = ~(~A \/ ~B)``,
REWRITE_TAC[DE_MORGAN_THM])


val EXISTS_NOT_FORALL_THM = store_thm ("EXISTS_NOT_FORALL_THM",
``!P. ((?x. P x) = (~(!x. ~(P x))))``,
PROVE_TAC[])



val MOVE_EXISTS_IMP_THM = store_thm ("MOVE_EXISTS_IMP_THM",
``(?x. ((!y. (~(P x y)) ==> R y) ==> Q x)) =
         (((!y. (~(!x. P x y)) ==> R y)) ==> ?x. Q x)``,
         PROVE_TAC[]);


val UNWIND_EXISTS_THM = store_thm ("UNWIND_EXISTS_THM",
 ``!a P. (?x. P x) = ((!x. ~(x = a) ==> ~(P x)) ==> P a)``,
 PROVE_TAC[]);



val LEFT_IMP_AND_INTRO = store_thm ("LEFT_IMP_AND_INTRO",
 ``!x t1 t2. (t1 ==> t2) ==> ((x /\ t1) ==> (x /\ t2))``,
 PROVE_TAC[]);

val RIGHT_IMP_AND_INTRO = store_thm ("RIGHT_IMP_AND_INTRO",
 ``!x t1 t2. (t1 ==> t2) ==> ((t1 /\ x) ==> (t2 /\ x))``,
 PROVE_TAC[]);


val LEFT_IMP_OR_INTRO = store_thm ("LEFT_IMP_OR_INTRO",
 ``!x t1 t2. (t1 ==> t2) ==> ((x \/ t1) ==> (x \/ t2))``,
 PROVE_TAC[]);

val RIGHT_IMP_OR_INTRO = store_thm ("RIGHT_IMP_OR_INTRO",
 ``!x t1 t2. (t1 ==> t2) ==> ((t1 \/ x) ==> (t2 \/ x))``,
 PROVE_TAC[]);




(* Theorems for the specialised logics *)

val PAIR_EQ_EXPAND = store_thm ("PAIR_EQ_EXPAND",
``(((x:'a,y:'b) = X) = ((x = FST X) /\ (y = SND X))) /\
  ((X = (x,y)) = ((FST X = x) /\ (SND X = y)))``,
Cases_on `X` THEN
REWRITE_TAC[pairTheory.PAIR_EQ]);


val PAIR_EQ_SIMPLE_EXPAND = store_thm ("PAIR_EQ_SIMPLE_EXPAND",
``(((x:'a,y:'b) = (x, y')) = (y = y')) /\
  (((y:'b,x:'a) = (y', x)) = (y = y')) /\
  (((FST X, y) = X) = (y = SND X)) /\
  (((x, SND X) = X) = (x = FST X)) /\
  ((X = (FST X, y)) = (SND X = y)) /\
  ((X = (x, SND X)) = (FST X = x))``,
Cases_on `X` THEN
ASM_REWRITE_TAC[pairTheory.PAIR_EQ]);


val IS_SOME_EQ_NOT_NONE = store_thm ("IS_SOME_EQ_NOT_NONE",
``!x. IS_SOME x = ~(x = NONE)``,
REWRITE_TAC[GSYM optionTheory.NOT_IS_SOME_EQ_NONE]);


val _ = export_theory();


end
