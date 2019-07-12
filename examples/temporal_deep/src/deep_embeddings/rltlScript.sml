open HolKernel Parse boolLib bossLib;

(*
quietdec := true;

val home_dir = (Globals.HOLDIR ^ "/examples/temporal_deep/");
loadPath := (home_dir ^ "src/deep_embeddings") ::
            (home_dir ^ "src/tools") :: !loadPath;

map load
 ["infinite_pathTheory", "prop_logicTheory", "pred_setTheory", "arithmeticTheory", "tuerk_tacticsLib", "numLib", "symbolic_kripke_structureTheory", "set_lemmataTheory"];
*)

open pred_setTheory arithmeticTheory infinite_pathTheory prop_logicTheory tuerk_tacticsLib numLib set_lemmataTheory symbolic_kripke_structureTheory
open Sanity;

(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)

val _ = hide "S";
val _ = hide "I";


val _ = new_theory "rltl";
val _ = ParseExtras.temp_loose_equality()


(******************************************************************************
* Syntax and semantic
******************************************************************************)
val rltl_def =
 Hol_datatype
  `rltl = RLTL_PROP       of 'prop prop_logic         (* b!                       *)
      | RLTL_NOT          of rltl                     (* not f                    *)
      | RLTL_AND          of rltl # rltl              (* f1 and f2                *)
      | RLTL_NEXT         of rltl                     (* X! f                     *)
      | RLTL_SUNTIL       of rltl # rltl              (* [f1 U f2]                *)
      | RLTL_ACCEPT       of rltl # 'prop prop_logic`;          (* f abort b                *)


val rltl_induct =
 save_thm
  ("rltl_induct",
   Q.GEN
    `P`
    (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2)) ==> (A ==> B1)``)
     (SIMP_RULE
       std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P x ==> Q(x,y)) = !x. P x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P y ==> Q(x,y)) = !y. P y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P`,`\(f,b). P f`,`\(f1,f2). P f1 /\ P f2`]
         (TypeBase.induction_of ``:'a rltl``)))));


val RLTL_SEM_TIME_def =
 Define
   `(RLTL_SEM_TIME t v a r (RLTL_PROP b) =
      ((P_SEM (v t) a) \/ ((P_SEM (v t) b) /\ ~(P_SEM (v t) r))))
    /\
    (RLTL_SEM_TIME t v a r (RLTL_NOT f) =
      ~(RLTL_SEM_TIME t v r a f))
    /\
    (RLTL_SEM_TIME t v a r (RLTL_AND (f1,f2)) =
     RLTL_SEM_TIME t v a r f1 /\ RLTL_SEM_TIME t v a r f2)
    /\
    (RLTL_SEM_TIME t v a r (RLTL_NEXT f) =
     ((P_SEM (v t) a) \/ (~(P_SEM (v t) r) /\ RLTL_SEM_TIME (SUC t) v a r f)))
    /\
    (RLTL_SEM_TIME t v a r (RLTL_SUNTIL(f1,f2)) =
      ?k. (k >= t) /\ (RLTL_SEM_TIME k v a r f2) /\ (!j. (t <= j /\ j < k) ==> (RLTL_SEM_TIME j v a r f1)))
    /\
    (RLTL_SEM_TIME t v a r (RLTL_ACCEPT (f, b)) =
     RLTL_SEM_TIME t v (P_OR(a, P_AND(b, P_NOT(r)))) r f)`;


val RLTL_SEM_def =
 Define
   `RLTL_SEM v f = RLTL_SEM_TIME 0 v P_FALSE P_FALSE f`;


val RLTL_KS_SEM_def =
 Define
   `RLTL_KS_SEM M f =
      !p. IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p ==> RLTL_SEM p f`;


(******************************************************************************
* Syntactic Sugar
******************************************************************************)
val RLTL_TRUE_def =
 Define
   `RLTL_TRUE = RLTL_PROP P_TRUE`;

val RLTL_FALSE_def =
 Define
   `RLTL_FALSE = RLTL_PROP P_FALSE`;



val RLTL_OR_def =
 Define
   `RLTL_OR(f1,f2) = RLTL_NOT (RLTL_AND((RLTL_NOT f1),(RLTL_NOT f2)))`;


val RLTL_IMPL_def =
 Define
   `RLTL_IMPL(f1, f2) = RLTL_OR(RLTL_NOT f1, f2)`;


val RLTL_COND_def =
 Define
   `RLTL_COND(c, f1, f2) = RLTL_AND(RLTL_IMPL(c, f1), RLTL_IMPL(RLTL_NOT c, f2))`;


val RLTL_EQUIV_def =
 Define
   `RLTL_EQUIV(b1, b2) = RLTL_AND(RLTL_IMPL(b1, b2),RLTL_IMPL(b2, b1))`;


val RLTL_REJECT_def =
 Define
   `RLTL_REJECT(f,b) = RLTL_NOT (RLTL_ACCEPT((RLTL_NOT f),b))`;


val RLTL_EVENTUAL_def =
 Define
   `RLTL_EVENTUAL f = RLTL_SUNTIL (RLTL_PROP(P_TRUE),f)`;


val RLTL_ALWAYS_def =
 Define
   `RLTL_ALWAYS f = RLTL_NOT (RLTL_EVENTUAL (RLTL_NOT f))`;


val RLTL_UNTIL_def =
 Define
   `RLTL_UNTIL(f1,f2) = RLTL_OR(RLTL_SUNTIL(f1,f2),RLTL_ALWAYS f1)`;


val RLTL_BEFORE_def =
 Define
   `RLTL_BEFORE(f1,f2) = RLTL_NOT(RLTL_SUNTIL(RLTL_NOT f1,f2))`;


val RLTL_SBEFORE_def =
 Define
   `RLTL_SBEFORE(f1,f2) = RLTL_SUNTIL(RLTL_NOT f2,RLTL_AND(f1, RLTL_NOT f2))`;


val RLTL_WHILE_def =
 Define
   `RLTL_WHILE(f1,f2) = RLTL_NOT(RLTL_SUNTIL(RLTL_OR(RLTL_NOT f1, RLTL_NOT f2),RLTL_AND(f2, RLTL_NOT f1)))`;


val RLTL_SWHILE_def =
 Define
   `RLTL_SWHILE(f1,f2) = RLTL_SUNTIL(RLTL_NOT f2,RLTL_AND(f1, f2))`;


val RLTL_EQUIV_PATH_STRONG_def =
  Define `RLTL_EQUIV_PATH_STRONG (t:num) v1 v2 a r =
      ?k. (k >= t) /\
     (((P_SEM (v1 k) a) /\ (P_SEM (v2 k) a) /\ ~(P_SEM (v1 k) r) /\ ~(P_SEM (v2 k) r)) \/
      ((P_SEM (v1 k) r) /\ (P_SEM (v2 k) r) /\ ~(P_SEM (v1 k) a) /\ ~(P_SEM (v2 k) a))) /\
     (!l. (t <= l /\ l < k ==> ((v1 l) = (v2 l))))`;

val RLTL_EQUIV_PATH_def =
  Define `RLTL_EQUIV_PATH t v1 v2 a r =
      (EQUIV_PATH_RESTN t v1 v2) \/ (RLTL_EQUIV_PATH_STRONG t v1 v2 a r)`;






(******************************************************************************
* Classes of RLTL
******************************************************************************)

val IS_RLTL_G_def =
 Define
   `(IS_RLTL_G (RLTL_PROP p) = T) /\
    (IS_RLTL_G (RLTL_NOT f) = IS_RLTL_F f) /\
    (IS_RLTL_G (RLTL_AND (f,g)) = (IS_RLTL_G f /\ IS_RLTL_G g)) /\
    (IS_RLTL_G (RLTL_NEXT f) = IS_RLTL_G f) /\
    (IS_RLTL_G (RLTL_SUNTIL(f,g)) = F) /\
    (IS_RLTL_G (RLTL_ACCEPT (f,p)) = IS_RLTL_G f) /\

    (IS_RLTL_F (RLTL_PROP p) = T) /\
    (IS_RLTL_F (RLTL_NOT f) = IS_RLTL_G f) /\
    (IS_RLTL_F (RLTL_AND (f,g)) = (IS_RLTL_F f /\ IS_RLTL_F g)) /\
    (IS_RLTL_F (RLTL_NEXT f) = IS_RLTL_F f) /\
    (IS_RLTL_F (RLTL_SUNTIL(f,g)) = (IS_RLTL_F f /\ IS_RLTL_F g)) /\
    (IS_RLTL_F (RLTL_ACCEPT (f,p)) = IS_RLTL_F f)`;


val IS_RLTL_PREFIX_def =
  Define
   `(IS_RLTL_PREFIX (RLTL_NOT f) = IS_RLTL_PREFIX f) /\
    (IS_RLTL_PREFIX (RLTL_AND (f,g)) = (IS_RLTL_PREFIX f /\ IS_RLTL_PREFIX g)) /\
    (IS_RLTL_PREFIX (RLTL_ACCEPT (f, p)) = (IS_RLTL_PREFIX f)) /\
    (IS_RLTL_PREFIX f = (IS_RLTL_G f \/ IS_RLTL_F f))`;


val IS_RLTL_GF_def=
 Define
   `(IS_RLTL_GF (RLTL_PROP p) = T) /\
    (IS_RLTL_GF (RLTL_NOT f) = IS_RLTL_FG f) /\
    (IS_RLTL_GF (RLTL_AND (f,g)) = (IS_RLTL_GF f /\ IS_RLTL_GF g)) /\
    (IS_RLTL_GF (RLTL_NEXT f) = IS_RLTL_GF f) /\
    (IS_RLTL_GF (RLTL_SUNTIL(f,g)) = (IS_RLTL_GF f /\ IS_RLTL_F g)) /\
    (IS_RLTL_GF (RLTL_ACCEPT (f,p)) = IS_RLTL_GF f) /\

    (IS_RLTL_FG (RLTL_PROP p) = T) /\
    (IS_RLTL_FG (RLTL_NOT f) = IS_RLTL_GF f) /\
    (IS_RLTL_FG (RLTL_AND (f,g)) = (IS_RLTL_FG f /\ IS_RLTL_FG g)) /\
    (IS_RLTL_FG (RLTL_NEXT f) = IS_RLTL_FG f) /\
    (IS_RLTL_FG (RLTL_SUNTIL(f,g)) = (IS_RLTL_FG f /\ IS_RLTL_FG g)) /\
    (IS_RLTL_FG (RLTL_ACCEPT (f,p)) = IS_RLTL_FG f)`;


val IS_RLTL_STREET_def =
  Define
   `(IS_RLTL_STREET (RLTL_NOT f) = IS_RLTL_STREET f) /\
    (IS_RLTL_STREET (RLTL_AND (f,g)) = (IS_RLTL_STREET f /\ IS_RLTL_STREET g)) /\
    (IS_RLTL_STREET (RLTL_ACCEPT (f, p)) = (IS_RLTL_STREET f)) /\
    (IS_RLTL_STREET f = (IS_RLTL_GF f \/ IS_RLTL_FG f))`;


val IS_RLTL_THM = save_thm("IS_RLTL_THM",
   LIST_CONJ [IS_RLTL_G_def,
              IS_RLTL_GF_def,
              IS_RLTL_PREFIX_def,
              IS_RLTL_STREET_def]);


(******************************************************************************
 * Tautologies und Contradictions
 ******************************************************************************)
val RLTL_EQUIVALENT_def =
 Define
   `RLTL_EQUIVALENT l1 l2 = !w t a r. (RLTL_SEM_TIME t w a r l1) = (RLTL_SEM_TIME t w a r l2)`;

val RLTL_EQUIVALENT_INITIAL_def =
 Define
   `RLTL_EQUIVALENT_INITIAL l1 l2 = !w. (RLTL_SEM w l1) = (RLTL_SEM w l2)`;

val RLTL_IS_CONTRADICTION_def =
 Define
   `RLTL_IS_CONTRADICTION l = (!v. ~(RLTL_SEM v l))`;

val RLTL_IS_TAUTOLOGY_def =
 Define
   `RLTL_IS_TAUTOLOGY l = (!v. RLTL_SEM v l)`;


val RLTL_TAUTOLOGY_CONTRADICTION_DUAL =
 store_thm
  ("RLTL_TAUTOLOGY_CONTRADICTION_DUAL",

  ``(!l. RLTL_IS_CONTRADICTION (RLTL_NOT l) = RLTL_IS_TAUTOLOGY l) /\
    (!l. RLTL_IS_TAUTOLOGY (RLTL_NOT l) = RLTL_IS_CONTRADICTION l)``,

    REWRITE_TAC[RLTL_IS_TAUTOLOGY_def, RLTL_IS_CONTRADICTION_def, RLTL_SEM_def, RLTL_SEM_TIME_def]);


val RLTL_TAUTOLOGY_CONTRADICTION___TO___EQUIVALENT_INITIAL =
 store_thm
  ("RLTL_TAUTOLOGY_CONTRADICTION___TO___EQUIVALENT_INITIAL",

  ``(!l. RLTL_IS_CONTRADICTION l = RLTL_EQUIVALENT_INITIAL l RLTL_FALSE) /\
    (!l. RLTL_IS_TAUTOLOGY l = RLTL_EQUIVALENT_INITIAL l RLTL_TRUE)``,

    REWRITE_TAC[RLTL_IS_TAUTOLOGY_def, RLTL_IS_CONTRADICTION_def,
      RLTL_SEM_TIME_def, RLTL_EQUIVALENT_INITIAL_def, RLTL_FALSE_def, P_SEM_THM,
      RLTL_TRUE_def, RLTL_SEM_def] THEN
    PROVE_TAC[]);


val RLTL_EQUIVALENT_INITIAL___TO___TAUTOLOGY =
 store_thm
  ("RLTL_EQUIVALENT_INITIAL___TO___TAUTOLOGY",

  ``!l1 l2. RLTL_EQUIVALENT_INITIAL l1 l2 = RLTL_IS_TAUTOLOGY (RLTL_EQUIV(l1, l2))``,

    REWRITE_TAC[RLTL_IS_TAUTOLOGY_def, RLTL_SEM_TIME_def, RLTL_EQUIV_def,
      RLTL_IMPL_def, RLTL_OR_def,
      RLTL_EQUIVALENT_INITIAL_def, RLTL_SEM_def] THEN
    PROVE_TAC[]);


(******************************************************************************
* Some simple Lemmata
******************************************************************************)

val RLTL_SEM_PROP_RLTL_OPERATOR_EQUIV =
 store_thm
  ("RLTL_SEM_PROP_RLTL_OPERATOR_EQUIV",

   ``(!t v a r f. (~(P_SEM (v t) a) \/ ~(P_SEM (v t) r)) ==>
   (RLTL_SEM_TIME t v a r (RLTL_PROP (P_NOT f)) =
   RLTL_SEM_TIME t v a r (RLTL_NOT (RLTL_PROP f)))) /\

   (!t v a r f1 f2.
   (RLTL_SEM_TIME t v a r (RLTL_PROP (P_AND(f1, f2))) =
   RLTL_SEM_TIME t v a r (RLTL_AND (RLTL_PROP f1, RLTL_PROP f2))))``,

   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[RLTL_SEM_TIME_def, P_SEM_def] THEN
   PROVE_TAC[])


val RLTL_USED_VARS_def=
 Define
   `(RLTL_USED_VARS (RLTL_PROP p) = P_USED_VARS p) /\
    (RLTL_USED_VARS (RLTL_NOT f) = RLTL_USED_VARS f) /\
    (RLTL_USED_VARS (RLTL_AND (f,g)) = (RLTL_USED_VARS f UNION RLTL_USED_VARS g)) /\
    (RLTL_USED_VARS (RLTL_NEXT f) = RLTL_USED_VARS f) /\
    (RLTL_USED_VARS (RLTL_SUNTIL(f,g)) = (RLTL_USED_VARS f UNION RLTL_USED_VARS g)) /\
    (RLTL_USED_VARS (RLTL_ACCEPT (f, p)) = (RLTL_USED_VARS f UNION P_USED_VARS p))`;


val RLTL_USED_VARS_INTER_SUBSET_THM =
 store_thm
  ("RLTL_USED_VARS_INTER_SUBSET_THM",
   ``!f t a r v S. ((RLTL_USED_VARS f) SUBSET S /\ (P_USED_VARS a) SUBSET S /\ (P_USED_VARS r) SUBSET S) ==> (RLTL_SEM_TIME t v a r f = RLTL_SEM_TIME t (PATH_RESTRICT v S) a r f)``,

   INDUCT_THEN rltl_induct ASSUME_TAC THENL [
      SIMP_TAC std_ss [RLTL_SEM_TIME_def, RLTL_USED_VARS_def, PATH_RESTRICT_def, PATH_MAP_def] THEN
      METIS_TAC[P_USED_VARS_INTER_SUBSET_THM, UNION_SUBSET],


      REWRITE_TAC[RLTL_SEM_TIME_def, RLTL_USED_VARS_def] THEN
      FULL_SIMP_TAC std_ss [UNION_SUBSET],


      FULL_SIMP_TAC std_ss [RLTL_SEM_TIME_def, RLTL_USED_VARS_def, UNION_SUBSET] THEN
      PROVE_TAC[],


      REWRITE_TAC[RLTL_SEM_TIME_def, RLTL_USED_VARS_def] THEN
      FULL_SIMP_TAC std_ss [UNION_SUBSET] THEN
      REPEAT STRIP_TAC THEN
      BINOP_TAC THENL [
         SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def] THEN
         METIS_TAC[P_USED_VARS_INTER_SUBSET_THM],

         BINOP_TAC THENL [
            SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def] THEN
            METIS_TAC[P_USED_VARS_INTER_SUBSET_THM],

            METIS_TAC[]
         ]
      ],


      REWRITE_TAC[RLTL_SEM_TIME_def, RLTL_USED_VARS_def] THEN
      FULL_SIMP_TAC std_ss [UNION_SUBSET] THEN
      METIS_TAC[],


      REWRITE_TAC[RLTL_SEM_TIME_def, RLTL_USED_VARS_def] THEN
      FULL_SIMP_TAC std_ss [UNION_SUBSET] THEN
      REPEAT STRIP_TAC THEN
      `(P_USED_VARS (P_OR (a,P_AND (p_2,P_NOT r)))) SUBSET S` by ASM_REWRITE_TAC[P_USED_VARS_def, P_OR_def, UNION_SUBSET] THEN
      METIS_TAC[]
   ]);


val RLTL_USED_VARS_INTER_THM =
 store_thm
  ("RLTL_USED_VARS_INTER_THM",
   ``!f t a r v. (RLTL_SEM_TIME t v a r f = RLTL_SEM_TIME t (PATH_RESTRICT v (RLTL_USED_VARS f UNION P_USED_VARS a UNION P_USED_VARS r)) a r f)``,

   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC RLTL_USED_VARS_INTER_SUBSET_THM THEN
   SIMP_TAC std_ss [SUBSET_DEF, IN_UNION]);


val RLTL_RESTN_SEM =
 store_thm
  ("RLTL_RESTN_SEM",
   ``!f v a r t1 t2. ((RLTL_SEM_TIME (t1+t2) v a r f) = (RLTL_SEM_TIME t1 (PATH_RESTN v t2) a r f))``,

   INDUCT_THEN rltl_induct ASSUME_TAC THENL [
      REWRITE_TAC[RLTL_SEM_TIME_def, PATH_RESTN_def] THEN METIS_TAC[],
      REWRITE_TAC[RLTL_SEM_TIME_def] THEN METIS_TAC[],
      REWRITE_TAC[RLTL_SEM_TIME_def] THEN METIS_TAC[],

      FULL_SIMP_TAC arith_ss [RLTL_SEM_TIME_def, PATH_RESTN_def] THEN
      `!t1 t2. SUC (t1 + t2) = SUC t1 + t2` by DECIDE_TAC THEN
      METIS_TAC[],

      REWRITE_TAC[RLTL_SEM_TIME_def] THEN
      REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [

         EXISTS_TAC ``(k:num)-(t2:num)`` THEN
         REPEAT STRIP_TAC THENL [
            DECIDE_TAC,

            `((k - t2) + t2) = k` by DECIDE_TAC THEN
            METIS_TAC[],

            `(t1 + t2 <= j+t2) /\ (j+t2 < k)` by DECIDE_TAC THEN
            `RLTL_SEM_TIME (j+t2) v a r f` by METIS_TAC[] THEN
            METIS_TAC[]
         ],

         EXISTS_TAC ``(k:num)+(t2:num)`` THEN
         REPEAT STRIP_TAC THENL [
            DECIDE_TAC,
            METIS_TAC[],

            `(t1 <= j - t2) /\ (j-t2 < k)` by DECIDE_TAC THEN
            `RLTL_SEM_TIME (j-t2) (PATH_RESTN v t2) a r f` by METIS_TAC[] THEN
            `((j - t2) + t2) = j` by DECIDE_TAC THEN
            METIS_TAC[]
         ]
      ],

      REWRITE_TAC[RLTL_SEM_TIME_def] THEN METIS_TAC[]
   ]);


val RLTL_SEM_TIME___TIME_ELIM =
 store_thm
  ("RLTL_SEM_TIME___TIME_ELIM",
   ``!f v a r t. ((RLTL_SEM_TIME t v a r f) = (RLTL_SEM_TIME 0 (PATH_RESTN v t) a r f))``,

   `!t. t = 0+t` by DECIDE_TAC THEN
   METIS_TAC[RLTL_RESTN_SEM]);


val RLTL_SEM_TIME___EQUIV_PATH =
 store_thm
  ("RLTL_SEM_TIME___EQUIV_PATH",
   ``!f v1 v2 a r t. (EQUIV_PATH_RESTN t v1 v2) ==>
      ((RLTL_SEM_TIME t v1 a r f) = (RLTL_SEM_TIME t v2 a r f))``,

   ONCE_REWRITE_TAC[RLTL_SEM_TIME___TIME_ELIM] THEN
   PROVE_TAC[EQUIV_PATH_RESTN___PATH_RESTN]);


val RLTL_SEM_TIME___ACCEPT_REJECT_EQUIV =
 store_thm
  ("RLTL_SEM_TIME___ACCEPT_REJECT_EQUIV",
   ``!f v a1 a2 r t. (PROP_LOGIC_EQUIVALENT a1 a2) ==>
      (((RLTL_SEM_TIME t v a1 r f) = (RLTL_SEM_TIME t v a2 r f)) /\
       ((RLTL_SEM_TIME t v r a1 f) = (RLTL_SEM_TIME t v r a2 f)))``,

   REWRITE_TAC[PROP_LOGIC_EQUIVALENT_def] THEN
   INDUCT_THEN rltl_induct ASSUME_TAC THEN
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   RES_TAC THEN ASM_REWRITE_TAC[RLTL_SEM_TIME_def] THEN
   `(!s. P_SEM s (P_OR (a1,P_AND (p_2,P_NOT r))) = P_SEM s (P_OR (a2,P_AND (p_2,P_NOT r)))) /\
    (!s. P_SEM s (P_OR (r,P_AND (p_2,P_NOT a1))) = P_SEM s (P_OR (r,P_AND (p_2,P_NOT a2))))`
      by ASM_REWRITE_TAC[P_SEM_THM] THEN
   RES_TAC THEN ASM_REWRITE_TAC[]);



val RLTL_SEM_TIME___ACCEPT_REJECT_EQUIV___BOTH =
 store_thm
  ("RLTL_SEM_TIME___ACCEPT_REJECT_EQUIV___BOTH",
   ``!f v a1 a2 r1 r2 t. (PROP_LOGIC_EQUIVALENT a1 a2) ==>
                         (PROP_LOGIC_EQUIVALENT r1 r2) ==>
      ((RLTL_SEM_TIME t v a1 r1 f) = (RLTL_SEM_TIME t v a2 r2 f))``,

   PROVE_TAC[RLTL_SEM_TIME___ACCEPT_REJECT_EQUIV]);


val RLTL_REJECT_SEM =
 store_thm
  ("RLTL_REJECT_SEM",
   ``!v a r f b t.((RLTL_SEM_TIME t v a r (RLTL_REJECT(f,b))) =
   RLTL_SEM_TIME t v a (P_OR(r, P_AND(b, P_NOT(a)))) f)``,
   REWRITE_TAC[RLTL_REJECT_def, RLTL_SEM_TIME_def]);


val RLTL_OR_SEM =
 store_thm
  ("RLTL_OR_SEM",
   ``!v a r f1 f2 t.((RLTL_SEM_TIME t v a r (RLTL_OR(f1,f2))) = ((RLTL_SEM_TIME t v a r f1) \/ (RLTL_SEM_TIME t v a r f2)))``,
   REWRITE_TAC[RLTL_OR_def, RLTL_SEM_TIME_def] THEN SIMP_TAC std_ss []);


val RLTL_IMPL_SEM =
 store_thm
  ("RLTL_IMPL_SEM",
   ``!v a r f1 f2 t.((RLTL_SEM_TIME t v a r (RLTL_IMPL(f1,f2))) = ((RLTL_SEM_TIME t v r a f1) ==> (RLTL_SEM_TIME t v a r f2)))``,
   REWRITE_TAC[RLTL_IMPL_def, RLTL_OR_SEM,RLTL_SEM_TIME_def] THEN METIS_TAC[]);


val RLTL_EVENTUAL_SEM =
 store_thm
  ("RLTL_EVENTUAL_SEM",
   ``!v a r f t. ((RLTL_SEM_TIME t v a r (RLTL_EVENTUAL f)) =
      (?k. (k >= t) /\ (RLTL_SEM_TIME k v a r f) /\ (!j. t <= j /\ j < k ==>
        P_SEM (v j) a \/ ~P_SEM (v j) r)))``,

   REWRITE_TAC[RLTL_EVENTUAL_def,RLTL_SEM_TIME_def, P_SEM_def]);


val RLTL_ALWAYS_SEM =
 store_thm
  ("RLTL_ALWAYS_SEM",
   ``!v a r f t. (RLTL_SEM_TIME t v a r (RLTL_ALWAYS f)) =
      (!k. ((k >= t) /\ (!j. (t <= j /\ j < k) ==> (P_SEM (v j) r \/ ~P_SEM (v j) a))) ==> (RLTL_SEM_TIME k v a r f))``,

   SIMP_TAC std_ss [RLTL_ALWAYS_def, RLTL_EVENTUAL_def,RLTL_SEM_TIME_def, P_SEM_def] THEN
   PROVE_TAC[]);


val RLTL_SEM_THM = LIST_CONJ [RLTL_SEM_def,
                             RLTL_SEM_TIME_def,
                             RLTL_OR_SEM,
                             RLTL_IMPL_SEM,
                             RLTL_ALWAYS_SEM,
                             RLTL_EVENTUAL_SEM];
val _ = save_thm("RLTL_SEM_THM",RLTL_SEM_THM);


val RLTL_EQUIV_PATH_STRONG___SYM_PATH =
 store_thm
  ("RLTL_EQUIV_PATH_STRONG___SYM_PATH",
   ``!v1 v2 a r t. RLTL_EQUIV_PATH_STRONG t v1 v2 a r = RLTL_EQUIV_PATH_STRONG t v2 v1 a r``,

   REWRITE_TAC[RLTL_EQUIV_PATH_STRONG_def] THEN
   METIS_TAC[]);


val RLTL_EQUIV_PATH_STRONG___SYM_ACCEPT_REJECT =
 store_thm
  ("RLTL_EQUIV_PATH_STRONG___SYM_ACCEPT_REJECT",
   ``!v1 v2 a r t. RLTL_EQUIV_PATH_STRONG t v1 v2 a r = RLTL_EQUIV_PATH_STRONG t v1 v2 r a``,

   REWRITE_TAC[RLTL_EQUIV_PATH_STRONG_def] THEN
   METIS_TAC[]);


val RLTL_EQUIV_PATH___SYM_PATH =
 store_thm
  ("RLTL_EQUIV_PATH___SYM_PATH",
   ``!v1 v2 a r t. RLTL_EQUIV_PATH t v1 v2 a r = RLTL_EQUIV_PATH t v2 v1 a r``,

   REWRITE_TAC[RLTL_EQUIV_PATH_def] THEN
   PROVE_TAC[EQUIV_PATH_RESTN_SYM, RLTL_EQUIV_PATH_STRONG___SYM_PATH]);


val RLTL_EQUIV_PATH___SYM_ACCEPT_REJECT =
 store_thm
  ("RLTL_EQUIV_PATH___SYM_ACCEPT_REJECT",
   ``!v1 v2 a r t. RLTL_EQUIV_PATH t v1 v2 a r = RLTL_EQUIV_PATH t v1 v2 r a``,
   REWRITE_TAC[RLTL_EQUIV_PATH_def] THEN
   PROVE_TAC[RLTL_EQUIV_PATH_STRONG___SYM_ACCEPT_REJECT]);


val RLTL_EQUIV_PATH_STRONG___GREATER_IMPL =
 store_thm
  ("RLTL_EQUIV_PATH_STRONG___GREATER_IMPL",
   ``!v1 v2 t t2 a r. (t2 >= t /\ (RLTL_EQUIV_PATH_STRONG t v1 v2 a r) /\ (!j. (t <= j /\ j < t2) ==> ((~(P_SEM (v1 j) a) \/ ~(P_SEM (v2 j) a)) /\
   (~(P_SEM (v1 j) r) \/ ~(P_SEM (v2 j) r))))) ==> (RLTL_EQUIV_PATH_STRONG t2 v1 v2 a r)``,

   REWRITE_TAC [RLTL_EQUIV_PATH_STRONG_def] THEN
   REPEAT STRIP_TAC THEN (
      `~(k < t2)` by PROVE_TAC[GREATER_EQ] THEN
      EXISTS_TAC ``k:num`` THEN
      ASM_SIMP_TAC arith_ss []
   ));


val RLTL_EQUIV_PATH___GREATER_IMPL =
 store_thm
  ("RLTL_EQUIV_PATH___GREATER_IMPL",
   ``!v1 v2 t t2 a r. (t2 >= t /\ (RLTL_EQUIV_PATH t v1 v2 a r) /\ (!j. (t <= j /\ j < t2) ==> ((~(P_SEM (v1 j) a) \/ ~(P_SEM (v2 j) a)) /\
   (~(P_SEM (v1 j) r) \/ ~(P_SEM (v2 j) r))))) ==> (RLTL_EQUIV_PATH t2 v1 v2 a r)``,

   REWRITE_TAC[RLTL_EQUIV_PATH_def] THEN
   REPEAT STRIP_TAC THENL [
      PROVE_TAC[EQUIV_PATH_RESTN___GREATER_IMPL],

      ASSUME_TAC RLTL_EQUIV_PATH_STRONG___GREATER_IMPL THEN
      RES_TAC THEN ASM_REWRITE_TAC[]
   ]);


val RLTL_EQUIV_PATH_STRONG___SUC =
 store_thm
  ("RLTL_EQUIV_PATH_STRONG___SUC",
   ``!v1 v2 t a r. ((RLTL_EQUIV_PATH_STRONG t v1 v2 a r) /\ (~(P_SEM (v1 t) a) \/ ~(P_SEM (v2 t) a)) /\
   (~(P_SEM (v1 t) r) \/ ~(P_SEM (v2 t) r))) ==> (RLTL_EQUIV_PATH_STRONG (SUC t) v1 v2 a r)``,

   `!t. SUC t >= t /\ (!j. (t <= j /\ j < SUC t) ==> (j = t))` by DECIDE_TAC THEN
   METIS_TAC[RLTL_EQUIV_PATH_STRONG___GREATER_IMPL]);


val RLTL_EQUIV_PATH___SUC =
 store_thm
  ("RLTL_EQUIV_PATH___SUC",
   ``!v1 v2 t a r. ((RLTL_EQUIV_PATH t v1 v2 a r) /\ (~(P_SEM (v1 t) a) \/ ~(P_SEM (v2 t) a)) /\
   (~(P_SEM (v1 t) r) \/ ~(P_SEM (v2 t) r))) ==> (RLTL_EQUIV_PATH (SUC t) v1 v2 a r)``,

   `!t. SUC t >= t /\ (!j. (t <= j /\ j < SUC t) ==> (j = t))` by DECIDE_TAC THEN
   METIS_TAC[RLTL_EQUIV_PATH___GREATER_IMPL]);



val RLTL_EQUIV_PATH_STRONG___INITIAL =
 store_thm
  ("RLTL_EQUIV_PATH_STRONG___INITIAL",
   ``!v1 v2 t a r. (RLTL_EQUIV_PATH_STRONG t v1 v2 a r) ==>
      (((P_SEM (v1 t) a) = (P_SEM (v2 t) a)) /\
       ((P_SEM (v1 t) r) = (P_SEM (v2 t) r)))``,

   REWRITE_TAC [RLTL_EQUIV_PATH_STRONG_def] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN (
     Cases_on `k = t` THENL [
       PROVE_TAC[],

       `t < k` by DECIDE_TAC THEN
       PROVE_TAC[LESS_EQ_REFL]
     ]
   ));


val RLTL_EQUIV_PATH___INITIAL =
 store_thm
  ("RLTL_EQUIV_PATH___INITIAL",
   ``!v1 v2 t a r. (RLTL_EQUIV_PATH t v1 v2 a r) ==>
      (((P_SEM (v1 t) a) = (P_SEM (v2 t) a)) /\
       ((P_SEM (v1 t) r) = (P_SEM (v2 t) r)))``,

   REWRITE_TAC [RLTL_EQUIV_PATH_def] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THENL [
     FULL_SIMP_TAC std_ss [EQUIV_PATH_RESTN_def],
     PROVE_TAC[RLTL_EQUIV_PATH_STRONG___INITIAL]
   ]
  );



val RLTL_ACCEPT_REJECT_THM =
 store_thm
  ("RLTL_ACCEPT_REJECT_THM",
   ``!f v a r t. (((P_SEM (v t) a) /\ ~(P_SEM (v t) r)) ==> RLTL_SEM_TIME t v a r f) /\
                 ((~(P_SEM (v t) a) /\ (P_SEM (v t) r)) ==> ~(RLTL_SEM_TIME t v a r f))``,


INDUCT_THEN rltl_induct ASSUME_TAC THENL [
   REWRITE_TAC[RLTL_SEM_TIME_def] THEN METIS_TAC[],
   REWRITE_TAC[RLTL_SEM_TIME_def] THEN METIS_TAC[],
   REWRITE_TAC[RLTL_SEM_TIME_def] THEN METIS_TAC[],
   REWRITE_TAC[RLTL_SEM_TIME_def] THEN METIS_TAC[],

   REWRITE_TAC[RLTL_SEM_TIME_def] THEN
   REPEAT STRIP_TAC THENL [
      EXISTS_TAC ``t:num`` THEN
      ASM_SIMP_TAC arith_ss [],

      `(t <= t) /\ ((t < k) \/ (t = k))` by DECIDE_TAC THEN
      METIS_TAC[]
   ],

   REWRITE_TAC[RLTL_SEM_TIME_def] THEN METIS_TAC[P_SEM_THM]
]);


val RLTL_SEM_TIME___STRANGE_NEGATION_EXAMPLE =
 store_thm
  ("RLTL_SEM_TIME___STRANGE_NEGATION_EXAMPLE",

   ``!v a r p1 p2 t. (P_SEM (v t) a /\ P_SEM (v t) r /\ (!j:num. j > t ==> (
   ~(P_SEM (v j) p1) /\ ~(P_SEM (v j) p2) /\ ~(P_SEM (v j) r))) /\ (!j:num. (P_SEM (v j) a = (j <= SUC t)))) ==>

   ((RLTL_SEM_TIME t v a r (RLTL_SUNTIL(RLTL_PROP p1, RLTL_NOT(RLTL_PROP p2)))) /\
   (RLTL_SEM_TIME t v a r (RLTL_NOT(RLTL_SUNTIL(RLTL_PROP p1, RLTL_NOT(RLTL_PROP p2))))))``,

   REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC std_ss [RLTL_SEM_THM] THENL [
      EXISTS_TAC ``SUC t`` THEN
      ASM_SIMP_TAC arith_ss [],

      REPEAT STRIP_TAC THEN
      Cases_on `k >= t` THEN ASM_REWRITE_TAC[] THEN
      Cases_on `k <= SUC t` THEN ASM_REWRITE_TAC[] THEN
      `k > SUC t` by DECIDE_TAC THEN
      DISJ2_TAC THEN
      EXISTS_TAC ``SUC t`` THEN
      ASM_SIMP_TAC arith_ss []
   ]);



val RLTL_SEM_TIME___ACCEPT_REJECT_IMP_ON_PATH =
 store_thm
  ("RLTL_SEM_TIME___ACCEPT_REJECT_IMP_ON_PATH",
   ``!f t v a1 a2 r. (IMP_ON_PATH_RESTN t v a1 a2) ==>
     ((RLTL_SEM_TIME t v a1 r f ==> RLTL_SEM_TIME t v a2 r f) /\
      (RLTL_SEM_TIME t v r a2 f ==> RLTL_SEM_TIME t v r a1 f))``,

   INDUCT_THEN rltl_induct ASSUME_TAC THENL [
      REWRITE_TAC[RLTL_SEM_TIME_def, IMP_ON_PATH_RESTN_def] THEN METIS_TAC[LESS_EQ_REFL, GREATER_EQ],
      REWRITE_TAC[RLTL_SEM_TIME_def] THEN METIS_TAC[],
      REWRITE_TAC[RLTL_SEM_TIME_def] THEN METIS_TAC[],

      REWRITE_TAC[RLTL_SEM_TIME_def] THEN
      REPEAT STRIP_TAC THENL [
         METIS_TAC[IMP_ON_PATH_RESTN_def, LESS_EQ_REFL, GREATER_EQ],

         `SUC t >= t` by DECIDE_TAC THEN
         `IMP_ON_PATH_RESTN (SUC t) v a1 a2` by   METIS_TAC[IMP_ON_PATH_RESTN___GREATER_IMPL] THEN
         METIS_TAC[],

         ASM_REWRITE_TAC[],

         `~ P_SEM (v t) a1` by METIS_TAC[IMP_ON_PATH_RESTN_def, LESS_EQ_REFL, GREATER_EQ] THEN
         `SUC t >= t` by DECIDE_TAC THEN
         `IMP_ON_PATH_RESTN (SUC t) v a1 a2` by   METIS_TAC[IMP_ON_PATH_RESTN___GREATER_IMPL] THEN
         METIS_TAC[]
      ],


      ONCE_REWRITE_TAC[RLTL_SEM_TIME_def, IMP_ON_PATH_RESTN___GREATER_IMPL] THEN
      REPEAT STRIP_TAC THEN
      EXISTS_TAC ``k:num`` THEN
      METIS_TAC[GREATER_EQ],



      REWRITE_TAC[RLTL_SEM_TIME_def] THEN
      REPEAT GEN_TAC THEN DISCH_TAC THEN
      REPEAT STRIP_TAC THENL[
         `IMP_ON_PATH_RESTN t v (P_OR (a1,P_AND (p_2,P_NOT r))) (P_OR (a2,P_AND (p_2,P_NOT r)))` by
         (FULL_SIMP_TAC std_ss [P_SEM_def, P_SEM_THM, IMP_ON_PATH_RESTN_def] THEN METIS_TAC[]) THEN
         METIS_TAC[],


         `IMP_ON_PATH_RESTN t v (P_OR (r,P_AND (p_2,P_NOT a2))) (P_OR (r,P_AND (p_2,P_NOT a1)))` by
         (FULL_SIMP_TAC std_ss [P_SEM_def, P_SEM_THM, IMP_ON_PATH_RESTN_def] THEN METIS_TAC[]) THEN
         METIS_TAC[]
      ]
   ]);


val RLTL_SEM_TIME___ACCEPT_REJECT_EQUIV_ON_PATH =
 store_thm
  ("RLTL_SEM_TIME___ACCEPT_REJECT_EQUIV_ON_PATH",
   ``!f t v a1 a2 r. (EQUIV_ON_PATH_RESTN t v a1 a2) ==>
     ((RLTL_SEM_TIME t v a1 r f = RLTL_SEM_TIME t v a2 r f) /\
      (RLTL_SEM_TIME t v r a1 f = RLTL_SEM_TIME t v r a2 f))``,

   METIS_TAC[EQUIV_ON_PATH_RESTN___IMP_ON_PATH_RESTN, RLTL_SEM_TIME___ACCEPT_REJECT_IMP_ON_PATH]);


val RLTL_SEM_TIME___ACCEPT_REJECT_EQUIV_ON_PATH___BOTH =
 store_thm
  ("RLTL_SEM_TIME___ACCEPT_REJECT_EQUIV_ON_PATH___BOTH",
   ``!f t v a1 a2 r1 r2. (EQUIV_ON_PATH_RESTN t v a1 a2) ==>
                     (EQUIV_ON_PATH_RESTN t v r1 r2) ==>
     (RLTL_SEM_TIME t v a1 r1 f = RLTL_SEM_TIME t v a2 r2 f)``,

   METIS_TAC[EQUIV_ON_PATH_RESTN___IMP_ON_PATH_RESTN, RLTL_SEM_TIME___ACCEPT_REJECT_IMP_ON_PATH]);


val RLTL_SEM_TIME___ACCEPT_REJECT_IMPL_EQUIV =
 store_thm
  ("RLTL_SEM_TIME___ACCEPT_REJECT_IMPL_EQUIV",

   ``!t v r a1 a2.
   (!f. (RLTL_SEM_TIME t v r a2 f ==> RLTL_SEM_TIME t v r a1 f)) =
   (!f. (RLTL_SEM_TIME t v a1 r f ==> RLTL_SEM_TIME t v a2 r f))``,

   METIS_TAC[RLTL_SEM_TIME_def]);



val RLTL_EQUIV_PATH_STRONG_THM =
 store_thm
  ("RLTL_EQUIV_PATH_STRONG_THM",
     ``!f t a r v1 v2. (RLTL_EQUIV_PATH_STRONG t v1 v2 a r) ==> (RLTL_SEM_TIME t v1 a r f = RLTL_SEM_TIME
      t v2 a r f)``,

   INDUCT_THEN rltl_induct ASSUME_TAC THEN REPEAT STRIP_TAC THENL [

      FULL_SIMP_TAC std_ss [RLTL_SEM_TIME_def, RLTL_EQUIV_PATH_STRONG_def] THEN
      (Cases_on `k = t` THENL [
         METIS_TAC[],

         `t <= t /\ t < k` by DECIDE_TAC THEN
         METIS_TAC[]
      ]),

      ASM_SIMP_TAC std_ss [RLTL_SEM_TIME_def, RLTL_EQUIV_PATH_STRONG___SYM_ACCEPT_REJECT],
      ASM_SIMP_TAC std_ss [RLTL_SEM_TIME_def] THEN METIS_TAC[],


      REWRITE_TAC [RLTL_SEM_TIME_def] THEN
      METIS_TAC [RLTL_EQUIV_PATH_STRONG___SUC, RLTL_EQUIV_PATH_STRONG___INITIAL],

      REMAINS_TAC `!v1 v2. RLTL_EQUIV_PATH_STRONG t v1 v2 a r /\ RLTL_SEM_TIME t v1 a r (RLTL_SUNTIL (f,f')) ==> RLTL_SEM_TIME t v2 a r (RLTL_SUNTIL (f,f'))` THEN1 (
        METIS_TAC[RLTL_EQUIV_PATH_STRONG___SYM_PATH]
      ) THEN
      WEAKEN_HD_TAC THEN
      SIMP_TAC arith_ss [RLTL_EQUIV_PATH_STRONG_def, RLTL_SEM_TIME_def] THEN
      REPEAT STRIP_TAC THEN (
        `?l. MIN k k' = l` by METIS_TAC[] THEN
        SUBGOAL_TAC `l <= k /\ l <= k' /\ l >= t` THEN1 (
          REWRITE_TAC[GSYM (ASSUME ``MIN k k' = l``), MIN_DEF] THEN
          Cases_on `k < k'` THEN
          ASM_REWRITE_TAC[] THEN
          DECIDE_TAC
        ) THEN
        SUBGOAL_TAC `!j. (t <= j /\ j <= l) ==> (RLTL_EQUIV_PATH_STRONG j v1 v2 a r)` THEN1 (
              REWRITE_TAC[RLTL_EQUIV_PATH_STRONG_def] THEN
              REPEAT STRIP_TAC THEN
              `k >= j /\ !j':num. (j <= j') ==> (t <= j')` by DECIDE_TAC THEN
              EXISTS_TAC ``k:num`` THEN
              METIS_TAC[]
        ) THEN
        EXISTS_TAC ``l:num`` THEN
        `l >= t` by DECIDE_TAC THEN
        ASM_REWRITE_TAC [] THEN
        REPEAT STRIP_TAC
      ) THENL [
        `(l = k) \/ (l = k')` by METIS_TAC[MIN_DEF] THENL [
            METIS_TAC[RLTL_ACCEPT_REJECT_THM],
            METIS_TAC[GREATER_EQ, LESS_EQ_REFL]
        ],

        `t <= j /\ j < k' /\ j <= l` by DECIDE_TAC THEN
        METIS_TAC[],

        `(k < k') \/ (l = k')` by METIS_TAC[MIN_DEF] THENL [
            METIS_TAC[RLTL_ACCEPT_REJECT_THM, GREATER_EQ],
            METIS_TAC[GREATER_EQ, LESS_EQ_REFL]
        ],

        `t <= j /\ j < k' /\ j <= l` by DECIDE_TAC THEN
        METIS_TAC[]
      ],


      SIMP_TAC std_ss [RLTL_SEM_TIME_def] THEN
      SUBGOAL_TAC `RLTL_EQUIV_PATH_STRONG t v1 v2 (P_OR (a,P_AND (p_2,P_NOT r))) r` THEN1 (
         REWRITE_ALL_TAC[RLTL_EQUIV_PATH_STRONG_def, P_SEM_THM] THEN
         EXISTS_TAC ``k:num`` THEN
         ASM_REWRITE_TAC[]
      ) THEN
      METIS_TAC[]
   ]);




val RLTL_EQUIV_PATH_THM =
 store_thm
  ("RLTL_EQUIV_PATH_THM",
     ``!f t a r v1 v2. (RLTL_EQUIV_PATH t v1 v2 a r) ==> (RLTL_SEM_TIME t v1 a r f = RLTL_SEM_TIME
      t v2 a r f)``,

      METIS_TAC[RLTL_EQUIV_PATH_def, RLTL_SEM_TIME___EQUIV_PATH, RLTL_EQUIV_PATH_STRONG_THM]);



val RLTL_SEM_TIME___ACCEPT_BEFORE_ON_PATH =
 store_thm
  ("RLTL_SEM_TIME___ACCEPT_BEFORE_ON_PATH",

  ``!t v a1 a2 r f. (NAND_ON_PATH_RESTN t v a1 r /\ BEFORE_ON_PATH_RESTN t v a1 a2) ==>
    ((RLTL_SEM_TIME t v a2 r f ==> RLTL_SEM_TIME t v a1 r f))``,

   REPEAT GEN_TAC THEN
   REPEAT DISCH_TAC THEN
   CLEAN_ASSUMPTIONS_TAC THEN
   Cases_on `NOT_ON_PATH_RESTN t v a2` THENL [
      `IMP_ON_PATH_RESTN t v a2 a1` by
         (REWRITE_ALL_TAC [IMP_ON_PATH_RESTN_def, NOT_ON_PATH_RESTN_def, GREATER_EQ] THEN
         METIS_TAC[]) THEN
      METIS_TAC[RLTL_SEM_TIME___ACCEPT_REJECT_IMP_ON_PATH],


      SUBGOAL_TAC `?u. (t <= u /\ P_SEM (v u) a1) /\ (!u'. (t <= u' /\ u' < u) ==>
         (~P_SEM (v u') a1) /\ ~P_SEM (v u') a2)` THEN1 (

         SIMP_ALL_TAC std_ss [NOT_ON_PATH_RESTN_def] THEN
         SUBGOAL_TAC `?k. (P_SEM (v k) a2 /\ t <= k) /\ !k'. (t <= k' /\ k' < k) ==> ~(P_SEM (v k') a2)` THEN1 (
            ASSUME_TAC (EXISTS_LEAST_CONV ``?k. (P_SEM (v k) a2) /\  t <= k``) THEN
            METIS_TAC[]
         ) THEN
         REWRITE_ALL_TAC [BEFORE_ON_PATH_RESTN_def] THEN
         `?k'. t <= k' /\ k' <= k /\ P_SEM (v k') a1` by METIS_TAC[] THEN

         SUBGOAL_TAC `?u. (P_SEM (v u) a1 /\ t <= u) /\ !l'. (t <= l' /\ l' < u) ==> ~(P_SEM (v l') a1)` THEN1 (
            ASSUME_TAC (EXISTS_LEAST_CONV ``?u. (P_SEM (v u) a1) /\  t <= u``) THEN
            METIS_TAC[]
         ) THEN

         EXISTS_TAC ``u:num`` THEN
         ASM_REWRITE_TAC[] THEN
         `~(k' < u)` by METIS_TAC[] THEN
         `!u'. u' < u ==> u' < k` by DECIDE_TAC THEN
         METIS_TAC[]
      ) THEN



      `~P_SEM (v u) r` by
            (SIMP_ALL_TAC arith_ss [NAND_ON_PATH_RESTN_def] THEN
            METIS_TAC[GREATER_EQ, LESS_EQ_REFL]) THEN
      Cases_on `t = u` THEN1 (METIS_TAC[RLTL_ACCEPT_REJECT_THM]) THEN
      `t < u` by DECIDE_TAC THEN
      `?w. (\n. if (u < n) then (v t) else v n) = w` by METIS_TAC[] THEN


      SUBGOAL_TAC `RLTL_SEM_TIME t v (P_OR(a1, a2)) r f` THEN1 (
         SUBGOAL_TAC `IMP_ON_PATH_RESTN t v a2 (P_OR (a1,a2))` THEN1 (
           SIMP_TAC std_ss [IMP_ON_PATH_RESTN_def, P_SEM_THM]
         ) THEN
         METIS_TAC[RLTL_SEM_TIME___ACCEPT_REJECT_IMP_ON_PATH]
      ) THEN

      SUBGOAL_TAC `(RLTL_EQUIV_PATH_STRONG t v w a1 r) /\ (RLTL_EQUIV_PATH_STRONG t v w (P_OR(a1, a2)) r)` THEN1 (
         REWRITE_TAC[RLTL_EQUIV_PATH_STRONG_def, GREATER_EQ, P_SEM_THM] THEN
         REPEAT STRIP_TAC THEN
         EXISTS_TAC ``u:num`` THEN
         `w u = v u` by METIS_TAC[] THEN
         ASM_REWRITE_TAC[] THEN
         REPEAT STRIP_TAC THEN
         `~(u < l)` by DECIDE_TAC THEN
         METIS_TAC[]
      ) THEN

      SUBGOAL_TAC `IMP_ON_PATH_RESTN t w (P_OR(a1,a2)) a1` THEN1 (
         REWRITE_TAC [IMP_ON_PATH_RESTN_def, GREATER_EQ, P_SEM_THM] THEN
         REPEAT STRIP_TAC THEN
         Cases_on `u < t'` THENL [
            `w t' = v t` by METIS_TAC[] THEN
            METIS_TAC[LESS_EQ_REFL],

            `w t' = v t'` by METIS_TAC[] THEN
            Cases_on `t' = u` THENL [
               METIS_TAC[],

               `t' < u` by DECIDE_TAC THEN
               METIS_TAC[]
            ]
         ]) THEN

      PROVE_TAC[RLTL_EQUIV_PATH_STRONG_THM, RLTL_SEM_TIME___ACCEPT_REJECT_IMP_ON_PATH]
   ]);


val RLTL_SEM_TIME___REJECT_BEFORE_ON_PATH =
 store_thm
  ("RLTL_SEM_TIME___REJECT_BEFORE_ON_PATH",

  ``!t v a1 a2 r f. (NAND_ON_PATH_RESTN t v a1 r /\ BEFORE_ON_PATH_RESTN t v a1 a2) ==>
    ((RLTL_SEM_TIME t v r a1 f ==> RLTL_SEM_TIME t v r a2 f))``,

   REPEAT GEN_TAC THEN DISCH_TAC THEN
   `!f. RLTL_SEM_TIME t v a2 r f ==> RLTL_SEM_TIME t v a1 r f` by PROVE_TAC[RLTL_SEM_TIME___ACCEPT_BEFORE_ON_PATH] THEN
   PROVE_TAC[RLTL_SEM_TIME___ACCEPT_REJECT_IMPL_EQUIV]);



val RLTL_SEM_TIME___ACCEPT_OR_THM =
 store_thm
  ("RLTL_SEM_TIME___ACCEPT_OR_THM",
   ``!t v a1 a2 r f. (NAND_ON_PATH_RESTN t v a1 r /\ NAND_ON_PATH_RESTN t v a2 r) ==>
    ((RLTL_SEM_TIME t v (P_OR (a1, a2)) r f = (RLTL_SEM_TIME t v a1 r f \/ RLTL_SEM_TIME t v a2 r f)))``,

   REPEAT STRIP_TAC THEN
   EQ_TAC THENL [
      DISJ_CASES_TAC (SPECL [``v:num->'a set``, ``t:num``, ``a1:'a prop_logic``, ``a2:'a prop_logic``] BEFORE_ON_PATH_CASES) THENL [
         SUBGOAL_TAC `BEFORE_ON_PATH_RESTN t v a1 (P_OR (a1,a2))` THEN1 (
            REWRITE_ALL_TAC [BEFORE_ON_PATH_RESTN_def, P_SEM_THM] THEN
            PROVE_TAC[LESS_EQ_REFL]
         ) THEN
         PROVE_TAC[RLTL_SEM_TIME___ACCEPT_BEFORE_ON_PATH],

         SUBGOAL_TAC `BEFORE_ON_PATH_RESTN t v a2 (P_OR (a1,a2))` THEN1 (
            REWRITE_ALL_TAC [BEFORE_ON_PATH_RESTN_def, P_SEM_THM] THEN
            PROVE_TAC[LESS_EQ_REFL]
         ) THEN
         PROVE_TAC[RLTL_SEM_TIME___ACCEPT_BEFORE_ON_PATH]
      ],

      REPEAT STRIP_TAC THENL [
         `IMP_ON_PATH_RESTN t v a1 (P_OR(a1, a2))` by PROVE_TAC[IMP_ON_PATH_RESTN_def, P_SEM_THM, LESS_EQ_REFL],
         `IMP_ON_PATH_RESTN t v a2 (P_OR(a1, a2))` by PROVE_TAC[IMP_ON_PATH_RESTN_def, P_SEM_THM, LESS_EQ_REFL]
      ] THEN
      PROVE_TAC[RLTL_SEM_TIME___ACCEPT_REJECT_IMP_ON_PATH]
   ]);



val RLTL_SEM_TIME___REJECT_OR_THM =
 store_thm
  ("RLTL_SEM_TIME___REJECT_OR_THM",
   ``!t v a r1 r2 f. (NAND_ON_PATH_RESTN t v r1 a /\ NAND_ON_PATH_RESTN t v r2 a) ==>
    ((RLTL_SEM_TIME t v a (P_OR (r1, r2)) f = (RLTL_SEM_TIME t v a r1 f /\ RLTL_SEM_TIME t v a r2 f)))``,

   REPEAT STRIP_TAC THEN
   `RLTL_SEM_TIME t v a (P_OR (r1,r2)) f = ~(RLTL_SEM_TIME t v (P_OR (r1,r2)) a (RLTL_NOT f))` by
      REWRITE_TAC[RLTL_SEM_TIME_def] THEN
   ASM_REWRITE_TAC[] THEN
   `(RLTL_SEM_TIME t v (P_OR (r1,r2)) a (RLTL_NOT f)) =
   (RLTL_SEM_TIME t v r1 a (RLTL_NOT f) \/ RLTL_SEM_TIME t v r2 a (RLTL_NOT f))` by
      METIS_TAC[RLTL_SEM_TIME___ACCEPT_OR_THM] THEN
   ASM_REWRITE_TAC[RLTL_SEM_TIME_def] THEN
   PROVE_TAC[]);




val RLTL_SEM_TIME___ACCEPT_REJECT_IS_ON_PATH =
 store_thm
  ("RLTL_SEM_TIME___ACCEPT_REJECT_IS_ON_PATH",
   ``!v t a b r f. ((RLTL_SEM_TIME t v a r f /\ ~RLTL_SEM_TIME t v b r f) \/
                    (RLTL_SEM_TIME t v r b f /\ ~RLTL_SEM_TIME t v r a f)) ==>
                    IS_ON_PATH_RESTN t v a``,

   REPEAT STRIP_TAC THEN
   CCONTR_TAC THEN
   `IMP_ON_PATH_RESTN t v a b` by PROVE_TAC[IS_ON_PATH_RESTN_def, NOT_ON_PATH___IMP_ON_PATH] THEN
   PROVE_TAC [RLTL_SEM_TIME___ACCEPT_REJECT_IMP_ON_PATH]);






val RLTL_SEM_TIME___ACCEPT_REJECT_BEFORE_ON_PATH_STRONG =
 store_thm
  ("RLTL_SEM_TIME___ACCEPT_REJECT_BEFORE_ON_PATH_STRONG",
   ``!v t a1 a2 r f. (NAND_ON_PATH_RESTN t v a2 r /\
   ((RLTL_SEM_TIME t v a1 r f /\ ~RLTL_SEM_TIME t v a2 r f) \/
    (~RLTL_SEM_TIME t v r a1 f /\ RLTL_SEM_TIME t v r a2 f))) ==> BEFORE_ON_PATH_RESTN_STRONG t v a1 a2``,

   REPEAT STRIP_TAC THEN
   CCONTR_TAC THEN
   `BEFORE_ON_PATH_RESTN t v a2 a1` by METIS_TAC[BEFORE_ON_PATH_RESTN___NEGATION_IMPL] THENL [
      METIS_TAC[RLTL_SEM_TIME___ACCEPT_BEFORE_ON_PATH],
      METIS_TAC[RLTL_SEM_TIME___REJECT_BEFORE_ON_PATH]
   ]);



val RLTL_WEAK_UNTIL___ALTERNATIVE_DEF =
 store_thm
  ("RLTL_WEAK_UNTIL___ALTERNATIVE_DEF",
   ``!v a r t f1 f2.
                     (RLTL_SEM_TIME t v a r (RLTL_UNTIL(f1,f2)) =
                      RLTL_SEM_TIME t v a r (RLTL_NOT (RLTL_SUNTIL(RLTL_NOT f2, RLTL_AND(RLTL_NOT f1, RLTL_NOT f2)))))``,

   SIMP_TAC std_ss [RLTL_UNTIL_def, RLTL_SEM_THM] THEN
   REPEAT STRIP_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Cases_on `k < k'` THENL [
         `t <= k` by DECIDE_TAC THEN
         METIS_TAC[],

         Cases_on `~(k' >= t)` THEN1 ASM_REWRITE_TAC[] THEN
         Cases_on `k' = k`  THEN1 ASM_REWRITE_TAC[] THEN
         `t <= k' /\ k' < k` by DECIDE_TAC THEN
         METIS_TAC[]
      ],


      Cases_on `(!j. t <= j /\ j < k ==> P_SEM (v j) r \/ ~P_SEM (v j) a)` THENL [
         PROVE_TAC[],
         PROVE_TAC[RLTL_ACCEPT_REJECT_THM]
      ],


      Cases_on `!k. k >= t ==> RLTL_SEM_TIME k v a r f1` THENL [
         PROVE_TAC[],

         DISJ1_TAC THEN
         SIMP_ASSUMPTIONS_TAC std_ss [] THEN
         SUBGOAL_TAC `?k. (k >= (t:num) /\ ~RLTL_SEM_TIME k v a r f1) /\ !k'. k' < k ==> ~(k' >= t /\ ~RLTL_SEM_TIME k' v a r f1)` THEN1 (
            ASSUME_TAC (EXISTS_LEAST_CONV ``?k. k >= (t:num) /\ ~RLTL_SEM_TIME k (v:num -> 'a set) a r f1``) THEN
            RES_TAC THEN
            PROVE_TAC[]
         ) THEN
         SUBGOAL_TAC `?l:num. l >= (t:num) /\ l <= (k':num) /\ RLTL_SEM_TIME l v a r f2` THEN1 (
            Cases_on `RLTL_SEM_TIME k' v a r f2` THENL [
               EXISTS_TAC ``k':num`` THEN
               ASM_SIMP_TAC arith_ss [],

               `?j. t <= j /\ j < k' /\ RLTL_SEM_TIME j v a r f2` by METIS_TAC[] THEN
               EXISTS_TAC ``j:num`` THEN
               ASM_SIMP_TAC arith_ss []
            ]
         ) THEN
         EXISTS_TAC ``l:num`` THEN
         ASM_SIMP_TAC arith_ss [] THEN
         REPEAT STRIP_TAC THEN
         `j < k' /\ j >= t` by DECIDE_TAC THEN
         PROVE_TAC[]
      ]
   ]);





val RLTL_NEGATION_NORMAL_FORM =
 store_thm
  ("RLTL_NEGATION_NORMAL_FORM",

   ``!v t a r f f1 f2 b p. (~(P_SEM (v t) a /\ P_SEM (v t) r) ==>
         ((RLTL_SEM_TIME t v a r (RLTL_NOT(RLTL_PROP p)) = RLTL_SEM_TIME t v a r (RLTL_PROP (P_NOT p))) /\
          (RLTL_SEM_TIME t v a r (RLTL_NOT(RLTL_NEXT f)) = RLTL_SEM_TIME t v a r (RLTL_NEXT(RLTL_NOT f))))) /\

         (RLTL_SEM_TIME t v a r (RLTL_NOT(RLTL_NOT f)) = RLTL_SEM_TIME t v a r f) /\
         (RLTL_SEM_TIME t v a r (RLTL_NOT(RLTL_AND(f1, f2))) = RLTL_SEM_TIME t v a r (RLTL_OR (RLTL_NOT f1, RLTL_NOT f2))) /\
         (RLTL_SEM_TIME t v a r (RLTL_NOT(RLTL_SUNTIL(f1,f2))) = RLTL_SEM_TIME t v a r (RLTL_BEFORE(RLTL_NOT f1, f2))) /\
         (RLTL_SEM_TIME t v a r (RLTL_NOT(RLTL_ACCEPT(f,b))) = RLTL_SEM_TIME t v a r (RLTL_REJECT (RLTL_NOT f, b)))``,

   SIMP_TAC std_ss [RLTL_BEFORE_def, RLTL_SEM_TIME_def, P_SEM_def, RLTL_OR_def, RLTL_REJECT_def] THEN
   PROVE_TAC[]);



val IS_RLTL_RELATIONS =
 store_thm
  ("IS_RLTL_RELATIONS",
   ``!f. ((IS_RLTL_F f = IS_RLTL_G (RLTL_NOT f)) /\ (IS_RLTL_G f = IS_RLTL_F (RLTL_NOT f)) /\
          (IS_RLTL_FG f = IS_RLTL_GF (RLTL_NOT f)) /\ (IS_RLTL_GF f = IS_RLTL_FG (RLTL_NOT f)) /\
          (IS_RLTL_F f ==> IS_RLTL_FG f) /\ (IS_RLTL_G f ==> IS_RLTL_GF f) /\
          (IS_RLTL_G f ==> IS_RLTL_FG f) /\ (IS_RLTL_F f ==> IS_RLTL_GF f) /\
          (IS_RLTL_PREFIX f ==> (IS_RLTL_FG f /\ IS_RLTL_GF f)))``,

      INDUCT_THEN rltl_induct ASSUME_TAC THEN
      REWRITE_TAC[IS_RLTL_G_def, IS_RLTL_PREFIX_def, IS_RLTL_GF_def] THEN
      METIS_TAC[]
  );



val RLTL_VAR_RENAMING_def=
 Define
   `(RLTL_VAR_RENAMING f (RLTL_PROP p) = RLTL_PROP (P_VAR_RENAMING f p)) /\
    (RLTL_VAR_RENAMING f (RLTL_NOT r) = RLTL_NOT (RLTL_VAR_RENAMING f r)) /\
    (RLTL_VAR_RENAMING f (RLTL_AND (r1,r2)) = RLTL_AND(RLTL_VAR_RENAMING f r1, RLTL_VAR_RENAMING f r2)) /\
    (RLTL_VAR_RENAMING f (RLTL_NEXT r) = RLTL_NEXT (RLTL_VAR_RENAMING f r)) /\
    (RLTL_VAR_RENAMING f (RLTL_SUNTIL(r1,r2)) = RLTL_SUNTIL(RLTL_VAR_RENAMING f r1, RLTL_VAR_RENAMING f r2)) /\
    (RLTL_VAR_RENAMING f (RLTL_ACCEPT (r, p)) = RLTL_ACCEPT(RLTL_VAR_RENAMING f r, P_VAR_RENAMING f p))`;



val RLTL_SEM_TIME___VAR_RENAMING =
 store_thm
  ("RLTL_SEM_TIME___VAR_RENAMING",
   ``!f' t v a r f.
       (INJ f (PATH_USED_VARS v UNION RLTL_USED_VARS f' UNION P_USED_VARS a UNION P_USED_VARS r) UNIV) ==>
       ((RLTL_SEM_TIME t v a r f') =
        (RLTL_SEM_TIME t (PATH_VAR_RENAMING f v) (P_VAR_RENAMING f a) (P_VAR_RENAMING f r) (RLTL_VAR_RENAMING f f')))``,


   INDUCT_THEN rltl_induct ASSUME_TAC THENL [
      SIMP_TAC std_ss [RLTL_SEM_TIME_def,
        RLTL_VAR_RENAMING_def, PATH_VAR_RENAMING_def,
        PATH_MAP_def] THEN
      REPEAT STRIP_TAC THEN
      REMAINS_TAC `INJ f ((v t) UNION P_USED_VARS a) UNIV /\
                   INJ f ((v t) UNION P_USED_VARS p) UNIV /\
                   INJ f ((v t) UNION P_USED_VARS r) UNIV` THEN1 (
        ASM_SIMP_TAC std_ss [GSYM P_SEM___VAR_RENAMING]
      ) THEN STRIP_TAC THEN
      REPEAT STRIP_TAC THEN
      UNDISCH_HD_TAC THEN
      MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
      REWRITE_TAC [SUBSET_DEF, IN_UNION, RLTL_USED_VARS_def,
        GSYM PATH_USED_VARS_THM] THEN
      PROVE_TAC[],


      SIMP_TAC std_ss [RLTL_SEM_TIME_def, RLTL_USED_VARS_def,
        RLTL_VAR_RENAMING_def] THEN
      REPEAT STRIP_TAC THEN
      POP_NO_ASSUM 1 MATCH_MP_TAC THEN
      PROVE_TAC[UNION_COMM, UNION_ASSOC],


      SIMP_TAC std_ss [RLTL_SEM_TIME_def, RLTL_USED_VARS_def,
        RLTL_VAR_RENAMING_def] THEN
      REPEAT STRIP_TAC THEN
      REMAINS_TAC `INJ f (PATH_USED_VARS v UNION RLTL_USED_VARS f'' UNION
                          P_USED_VARS a UNION P_USED_VARS r) UNIV /\
                   INJ f (PATH_USED_VARS v UNION RLTL_USED_VARS f' UNION
                          P_USED_VARS a UNION P_USED_VARS r) UNIV` THEN1 (
        RES_TAC THEN
        ASM_REWRITE_TAC[]
      ) THEN
      NTAC 2 (WEAKEN_NO_TAC 1) THEN
      STRIP_TAC THEN
      UNDISCH_HD_TAC THEN
      MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
      PROVE_TAC[],


      SIMP_TAC std_ss [RLTL_SEM_TIME_def, RLTL_USED_VARS_def,
        RLTL_VAR_RENAMING_def] THEN
      REPEAT STRIP_TAC THEN
      Q_SPECL_NO_ASSUM 1 [`SUC t`, `v`, `a`, `r`, `f`] THEN
      UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      WEAKEN_HD_TAC THEN
      REMAINS_TAC `INJ f ((v t) UNION P_USED_VARS a) UNIV /\
                   INJ f ((v t) UNION P_USED_VARS r) UNIV` THEN1 (
        ASM_SIMP_TAC std_ss [GSYM P_SEM___VAR_RENAMING, PATH_VAR_RENAMING_def,
          PATH_MAP_def]
      ) THEN
      STRIP_TAC THEN UNDISCH_HD_TAC THEN
      MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, GSYM PATH_USED_VARS_THM] THEN
      PROVE_TAC[],


      SIMP_TAC std_ss [RLTL_SEM_TIME_def, RLTL_USED_VARS_def,
        RLTL_VAR_RENAMING_def] THEN
      REPEAT STRIP_TAC THEN
      REMAINS_TAC `INJ f (PATH_USED_VARS v UNION RLTL_USED_VARS f'' UNION
                          P_USED_VARS a UNION P_USED_VARS r) UNIV /\
                   INJ f (PATH_USED_VARS v UNION RLTL_USED_VARS f' UNION
                          P_USED_VARS a UNION P_USED_VARS r) UNIV` THEN1 (
        RES_TAC THEN
        ASM_REWRITE_TAC[]
      ) THEN
      NTAC 2 (WEAKEN_NO_TAC 1) THEN
      STRIP_TAC THEN
      UNDISCH_HD_TAC THEN
      MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
      PROVE_TAC[],



      SIMP_TAC std_ss [RLTL_SEM_TIME_def, RLTL_USED_VARS_def,
        RLTL_VAR_RENAMING_def, GSYM P_VAR_RENAMING_def, P_OR_def] THEN
      REPEAT STRIP_TAC THEN
      REMAINS_TAC `INJ f (PATH_USED_VARS v UNION RLTL_USED_VARS f' UNION
                          P_USED_VARS (P_NOT (P_AND (P_NOT a,P_NOT (P_AND (p_2,P_NOT r))))) UNION P_USED_VARS r) UNIV` THEN1 (
        RES_TAC THEN
        ASM_REWRITE_TAC[]
      ) THEN
      UNDISCH_HD_TAC THEN
      MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, P_USED_VARS_def] THEN
      PROVE_TAC[]
   ]);




val RLTL_SEM_TIME___VAR_RENAMING___PATH_RESTRICT =
 store_thm
  ("RLTL_SEM_TIME___VAR_RENAMING___PATH_RESTRICT",
   ``!f' t v a r f. (INJ f (RLTL_USED_VARS f' UNION P_USED_VARS a UNION P_USED_VARS r) UNIV) ==> ((RLTL_SEM_TIME t v a r f') = (RLTL_SEM_TIME t
    (PATH_VAR_RENAMING f (PATH_RESTRICT v (RLTL_USED_VARS f' UNION P_USED_VARS a UNION P_USED_VARS r))) (P_VAR_RENAMING f a) (P_VAR_RENAMING f r) (RLTL_VAR_RENAMING f f')))``,

   REPEAT STRIP_TAC THEN
   CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [RLTL_USED_VARS_INTER_THM])) THEN
   MATCH_MP_TAC RLTL_SEM_TIME___VAR_RENAMING THEN
   UNDISCH_HD_TAC THEN
   MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
   SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, GSYM PATH_USED_VARS_THM,
    PATH_RESTRICT_def, PATH_MAP_def, IN_INTER] THEN
   PROVE_TAC[]);


val RLTL_SEM___VAR_RENAMING___PATH_RESTRICT =
 store_thm
  ("RLTL_SEM___VAR_RENAMING___PATH_RESTRICT",
   ``!f' v f. (INJ f (RLTL_USED_VARS f') UNIV) ==> ((RLTL_SEM v f') = (RLTL_SEM
    (PATH_VAR_RENAMING f (PATH_RESTRICT v (RLTL_USED_VARS f'))) (RLTL_VAR_RENAMING f f')))``,

   REPEAT STRIP_TAC THEN
   REWRITE_TAC[RLTL_SEM_def] THEN
   SUBGOAL_TAC `P_FALSE = P_VAR_RENAMING f P_FALSE` THEN1 (
      SIMP_TAC std_ss [P_FALSE_def, P_VAR_RENAMING_def]
   ) THEN
   ASM_REWRITE_TAC[] THEN
   ASSUME_TAC RLTL_SEM_TIME___VAR_RENAMING___PATH_RESTRICT THEN
   Q_SPECL_NO_ASSUM 0 [`f'`, `0:num`, `v`, `P_FALSE`, `P_FALSE`, `f`] THEN
   UNDISCH_HD_TAC THEN
   ASM_SIMP_TAC std_ss [P_USED_VARS_EVAL, UNION_EMPTY]);



val _ = export_theory();
