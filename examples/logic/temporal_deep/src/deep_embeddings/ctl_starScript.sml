open HolKernel Parse boolLib bossLib;

(*
quietdec := true;

val home_dir = (concat Globals.HOLDIR "/examples/temporal_deep/");
loadPath := (concat home_dir "src/deep_embeddings") ::
            (concat home_dir "src/tools") :: !loadPath;

map load
 ["tuerk_tacticsLib", "res_quanTools", "prop_logicTheory",
  "infinite_pathTheory", "symbolic_kripke_structureTheory", "numLib",
  "full_ltlTheory", "pred_setTheory",
  "symbolic_semi_automatonTheory", "automaton_formulaTheory",
  "temporal_deep_mixedTheory", "pairTheory", "set_lemmataTheory"];
*)

open tuerk_tacticsLib res_quanTools prop_logicTheory infinite_pathTheory
     symbolic_kripke_structureTheory numLib full_ltlTheory pred_setTheory
     symbolic_semi_automatonTheory automaton_formulaTheory
     temporal_deep_mixedTheory pairTheory set_lemmataTheory;
open Sanity;

val _ = hide "S";
val _ = hide "I";

(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)

val _ = new_theory "ctl_star";
val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj"]
val _ = ParseExtras.temp_loose_equality()


val ctl_star_def =
 Hol_datatype
  `ctl_star = CTL_STAR_PROP       of 'a prop_logic               (* boolean expression      *)
            | CTL_STAR_NOT        of ctl_star                    (* \neg f                  *)
            | CTL_STAR_AND        of ctl_star # ctl_star         (* f1 \wedge f2            *)
            | CTL_STAR_PSNEXT     of ctl_star                    (* X f                     *)
            | CTL_STAR_PSUNTIL    of ctl_star # ctl_star         (* f1 U f2                 *)
            | CTL_STAR_NEXT       of ctl_star                    (* X f                     *)
            | CTL_STAR_SUNTIL     of ctl_star # ctl_star         (* f1 U f2                 *)
            | CTL_STAR_E          of ctl_star`;                  (* E f                     *)


val ctl_star_induct =
 save_thm
  ("ctl_star_induct",
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
         [`P`,`\(f1,f2). P f1 /\ P f2`]
         (TypeBase.induction_of ``:'a ctl_star``)))));


val CTL_STAR_SEM_PATH_TIME_def =
 Define `
   (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_PROP b) p = (P_SEM (p t) b)) /\
   (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_NOT f) p = ~(CTL_STAR_SEM_PATH_TIME t M f p)) /\
   (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_AND(f1,f2)) p = CTL_STAR_SEM_PATH_TIME t M f1 p /\ CTL_STAR_SEM_PATH_TIME t M f2 p) /\
   (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_NEXT f) p = CTL_STAR_SEM_PATH_TIME (SUC t) M f p) /\
   (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_PSNEXT f) p = (t > 0 /\ CTL_STAR_SEM_PATH_TIME (PRE t) M f p)) /\
   (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_E f) p = (?p'. (p' 0 = p t) /\
    IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p' /\ CTL_STAR_SEM_PATH_TIME 0 M f p')) /\
   (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_SUNTIL(f1,f2)) p = (?k. k >= t /\ CTL_STAR_SEM_PATH_TIME k M f2 p /\
      (!j. (t <= j /\ j < k) ==> CTL_STAR_SEM_PATH_TIME j M f1 p ))) /\
   (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_PSUNTIL(f1,f2)) p = (?k. k <= t /\ CTL_STAR_SEM_PATH_TIME k M f2 p /\
      (!j. (k < j /\ j <= t) ==> CTL_STAR_SEM_PATH_TIME j M f1 p )))`;


val CTL_STAR_SEM_PATH_def =
 Define `
   CTL_STAR_SEM_PATH M f p = CTL_STAR_SEM_PATH_TIME 0 M f p`;



val CTL_STAR_SEM_STATE_def =
 Define
  `(CTL_STAR_SEM_STATE M (CTL_STAR_PROP b) s = P_SEM s b) /\
   (CTL_STAR_SEM_STATE M (CTL_STAR_NOT f) s = ~(CTL_STAR_SEM_STATE M f s)) /\
   (CTL_STAR_SEM_STATE M (CTL_STAR_AND(f1,f2)) s = CTL_STAR_SEM_STATE M f1 s /\ CTL_STAR_SEM_STATE M f2 s) /\
   (CTL_STAR_SEM_STATE M (CTL_STAR_E f) s = (?p'. (p' 0 = s) /\
    IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p' /\ CTL_STAR_SEM_PATH M f p'))`;


val CTL_STAR_KS_SEM_def =
 Define
  `CTL_STAR_KS_SEM M f = (!s. P_SEM s M.S0 ==> CTL_STAR_SEM_STATE M f s)`;


val IS_CTL_STAR_PATH_FORMULA_def =
 Define `
   (IS_CTL_STAR_PATH_FORMULA (CTL_STAR_PROP b) = T) /\
   (IS_CTL_STAR_PATH_FORMULA (CTL_STAR_NOT f) = IS_CTL_STAR_PATH_FORMULA f) /\
   (IS_CTL_STAR_PATH_FORMULA (CTL_STAR_AND(f1,f2)) = IS_CTL_STAR_PATH_FORMULA f1 /\ IS_CTL_STAR_PATH_FORMULA f2) /\
   (IS_CTL_STAR_PATH_FORMULA (CTL_STAR_NEXT f) = IS_CTL_STAR_PATH_FORMULA f) /\
   (IS_CTL_STAR_PATH_FORMULA (CTL_STAR_PSNEXT f) = IS_CTL_STAR_PATH_FORMULA f) /\
   (IS_CTL_STAR_PATH_FORMULA (CTL_STAR_E f) = F) /\
   (IS_CTL_STAR_PATH_FORMULA (CTL_STAR_SUNTIL(f1,f2)) = IS_CTL_STAR_PATH_FORMULA f1 /\ IS_CTL_STAR_PATH_FORMULA f2) /\
   (IS_CTL_STAR_PATH_FORMULA (CTL_STAR_PSUNTIL(f1,f2)) = IS_CTL_STAR_PATH_FORMULA f1 /\ IS_CTL_STAR_PATH_FORMULA f2)`;


val IS_CTL_STAR_STATE_FORMULA_def =
 Define `
   (IS_CTL_STAR_STATE_FORMULA (CTL_STAR_PROP b) = T) /\
   (IS_CTL_STAR_STATE_FORMULA (CTL_STAR_NOT f) = IS_CTL_STAR_STATE_FORMULA f) /\
   (IS_CTL_STAR_STATE_FORMULA (CTL_STAR_AND(f1,f2)) = IS_CTL_STAR_STATE_FORMULA f1 /\ IS_CTL_STAR_STATE_FORMULA f2) /\
   (IS_CTL_STAR_STATE_FORMULA (CTL_STAR_NEXT f) = F) /\
   (IS_CTL_STAR_STATE_FORMULA (CTL_STAR_PSNEXT f) = F) /\
   (IS_CTL_STAR_STATE_FORMULA (CTL_STAR_E f) = T) /\
   (IS_CTL_STAR_STATE_FORMULA (CTL_STAR_SUNTIL(f1,f2)) = F) /\
   (IS_CTL_STAR_STATE_FORMULA (CTL_STAR_PSUNTIL(f1,f2)) = F)`;


val IS_CTL_STAR_PROP_FORMULA_def =
 Define `
   (IS_CTL_STAR_PROP_FORMULA (CTL_STAR_PROP b) = T) /\
   (IS_CTL_STAR_PROP_FORMULA (CTL_STAR_NOT f) = IS_CTL_STAR_PROP_FORMULA f) /\
   (IS_CTL_STAR_PROP_FORMULA (CTL_STAR_AND(f1,f2)) = IS_CTL_STAR_PROP_FORMULA f1 /\ IS_CTL_STAR_PROP_FORMULA f2) /\
   (IS_CTL_STAR_PROP_FORMULA (CTL_STAR_NEXT f) = F) /\
   (IS_CTL_STAR_PROP_FORMULA (CTL_STAR_PSNEXT f) = F) /\
   (IS_CTL_STAR_PROP_FORMULA (CTL_STAR_E f) = F) /\
   (IS_CTL_STAR_PROP_FORMULA (CTL_STAR_SUNTIL(f1,f2)) = F) /\
   (IS_CTL_STAR_PROP_FORMULA (CTL_STAR_PSUNTIL(f1,f2)) = F)`;


val CTL_STAR_USED_VARS_def =
 Define `
   (CTL_STAR_USED_VARS (CTL_STAR_PROP b) = P_USED_VARS b) /\
   (CTL_STAR_USED_VARS (CTL_STAR_NOT f) = CTL_STAR_USED_VARS f) /\
   (CTL_STAR_USED_VARS (CTL_STAR_AND(f1,f2)) = CTL_STAR_USED_VARS f1 UNION CTL_STAR_USED_VARS f2) /\
   (CTL_STAR_USED_VARS (CTL_STAR_NEXT f) = CTL_STAR_USED_VARS f) /\
   (CTL_STAR_USED_VARS (CTL_STAR_PSNEXT f) = CTL_STAR_USED_VARS f) /\
   (CTL_STAR_USED_VARS (CTL_STAR_E f) = CTL_STAR_USED_VARS f) /\
   (CTL_STAR_USED_VARS (CTL_STAR_SUNTIL(f1,f2)) = CTL_STAR_USED_VARS f1 UNION CTL_STAR_USED_VARS f2) /\
   (CTL_STAR_USED_VARS (CTL_STAR_PSUNTIL(f1,f2)) = CTL_STAR_USED_VARS f1 UNION CTL_STAR_USED_VARS f2)`;


val FINITE___CTL_STAR_USED_VARS =
 store_thm
  ("FINITE___CTL_STAR_USED_VARS",

  ``!p. FINITE(CTL_STAR_USED_VARS p)``,

  INDUCT_THEN ctl_star_induct ASSUME_TAC THEN (
      ASM_REWRITE_TAC[CTL_STAR_USED_VARS_def, FINITE___P_USED_VARS,
                      FINITE_UNION]
  ));


val IS_CTL_STAR_PROP_FORMULA___IS_PATH_STATE_FORMULA =
  store_thm
    ("IS_CTL_STAR_PROP_FORMULA___IS_PATH_STATE_FORMULA",

     ``!f. IS_CTL_STAR_PROP_FORMULA f = (IS_CTL_STAR_STATE_FORMULA f /\ IS_CTL_STAR_PATH_FORMULA f)``,

    INDUCT_THEN ctl_star_induct ASSUME_TAC THEN
    FULL_SIMP_TAC std_ss [IS_CTL_STAR_STATE_FORMULA_def,
      IS_CTL_STAR_PATH_FORMULA_def, IS_CTL_STAR_PROP_FORMULA_def] THEN
    METIS_TAC[]);


(*For state formulas just the first element of a path matters*)
val IS_CTL_STAR_STATE_FORMULA___SEM =
  store_thm
    ("IS_CTL_STAR_STATE_FORMULA___SEM",

     ``!f t M p s. (IS_CTL_STAR_STATE_FORMULA f /\ (p t = s)) ==>
                 (CTL_STAR_SEM_STATE M f s = CTL_STAR_SEM_PATH_TIME t M f p)``,

    INDUCT_THEN ctl_star_induct ASSUME_TAC THEN
    FULL_SIMP_TAC std_ss [IS_CTL_STAR_STATE_FORMULA_def,
      CTL_STAR_SEM_STATE_def, CTL_STAR_SEM_PATH_def,
      CTL_STAR_SEM_PATH_TIME_def]);


(*This inspieres the following definitions*)
val CTL_STAR_SEM_NO_MODEL_PATH_TIME_def =
 Define `
   (CTL_STAR_SEM_NO_MODEL_PATH_TIME t (CTL_STAR_PROP b) p = (P_SEM (p t) b)) /\
   (CTL_STAR_SEM_NO_MODEL_PATH_TIME t (CTL_STAR_NOT f) p = ~(CTL_STAR_SEM_NO_MODEL_PATH_TIME t f p)) /\
   (CTL_STAR_SEM_NO_MODEL_PATH_TIME t (CTL_STAR_AND(f1,f2)) p = CTL_STAR_SEM_NO_MODEL_PATH_TIME t f1 p /\ CTL_STAR_SEM_NO_MODEL_PATH_TIME t f2 p) /\
   (CTL_STAR_SEM_NO_MODEL_PATH_TIME t (CTL_STAR_NEXT f) p = CTL_STAR_SEM_NO_MODEL_PATH_TIME (SUC t) f p) /\
   (CTL_STAR_SEM_NO_MODEL_PATH_TIME t (CTL_STAR_PSNEXT f) p = (t > 0 /\ CTL_STAR_SEM_NO_MODEL_PATH_TIME (PRE t) f p)) /\
   (CTL_STAR_SEM_NO_MODEL_PATH_TIME t (CTL_STAR_SUNTIL(f1,f2)) p = (?k. k >= t /\ CTL_STAR_SEM_NO_MODEL_PATH_TIME k f2 p /\
      (!j. (t <= j /\ j < k) ==> CTL_STAR_SEM_NO_MODEL_PATH_TIME j f1 p ))) /\
   (CTL_STAR_SEM_NO_MODEL_PATH_TIME t (CTL_STAR_PSUNTIL(f1,f2)) p = (?k. k <= t /\ CTL_STAR_SEM_NO_MODEL_PATH_TIME k f2 p /\
      (!j. (k < j /\ j <= t) ==> CTL_STAR_SEM_NO_MODEL_PATH_TIME j f1 p)))`;

val CTL_STAR_SEM_NO_MODEL_PATH_def =
 Define `
   CTL_STAR_SEM_NO_MODEL_PATH f p = CTL_STAR_SEM_NO_MODEL_PATH_TIME 0 f p`;


val IS_CTL_STAR_PATH_FORMULA___NO_MODEL_SEM =
  store_thm
    ("IS_CTL_STAR_PATH_FORMULA___NO_MODEL_SEM",

     ``!f t M p. IS_CTL_STAR_PATH_FORMULA f ==>
                 (CTL_STAR_SEM_PATH_TIME t M f p =
                  CTL_STAR_SEM_NO_MODEL_PATH_TIME t f p)``,

    INDUCT_THEN ctl_star_induct ASSUME_TAC THEN
    FULL_SIMP_TAC std_ss [IS_CTL_STAR_PATH_FORMULA_def,
      CTL_STAR_SEM_PATH_TIME_def, CTL_STAR_SEM_NO_MODEL_PATH_TIME_def] THEN
    METIS_TAC[]);



val CTL_STAR_USED_VARS_LABEL_RESTRICT_THM___NO_MODEL_SEM_PATH_TIME =
  store_thm
    ("CTL_STAR_USED_VARS_LABEL_RESTRICT_THM___NO_MODEL_SEM_PATH_TIME",
     ``!f t p S. (CTL_STAR_USED_VARS f SUBSET S /\
                    IS_CTL_STAR_PATH_FORMULA f) ==>
                (CTL_STAR_SEM_NO_MODEL_PATH_TIME t f p =
                 CTL_STAR_SEM_NO_MODEL_PATH_TIME t f (PATH_RESTRICT p S))``,

      INDUCT_THEN ctl_star_induct ASSUME_TAC THEN1 (
        (*Case PROP*)
        SIMP_TAC std_ss [CTL_STAR_USED_VARS_def, CTL_STAR_SEM_NO_MODEL_PATH_TIME_def,
                         PATH_RESTRICT_def, PATH_MAP_def] THEN
        PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM]
      ) THEN
      ASM_SIMP_TAC std_ss [CTL_STAR_USED_VARS_def, CTL_STAR_SEM_NO_MODEL_PATH_TIME_def, UNION_SUBSET, IS_CTL_STAR_PATH_FORMULA_def] THEN
      PROVE_TAC[]);


val CTL_STAR_USED_VARS_NO_MODEL_SEM_PATH_TIME___PATH_RESTRICT_THM =
  store_thm
    ("CTL_STAR_USED_VARS_NO_MODEL_SEM_PATH_TIME___PATH_RESTRICT_THM",
     ``!f t p. IS_CTL_STAR_PATH_FORMULA f ==>
                (CTL_STAR_SEM_NO_MODEL_PATH_TIME t f p =
                 CTL_STAR_SEM_NO_MODEL_PATH_TIME t f (PATH_RESTRICT p (CTL_STAR_USED_VARS f)))``,

     PROVE_TAC[SUBSET_REFL, CTL_STAR_USED_VARS_LABEL_RESTRICT_THM___NO_MODEL_SEM_PATH_TIME]);




(******************************************************************************
* Syntactic Sugar
******************************************************************************)
val CTL_STAR_A_def = Define `CTL_STAR_A f = CTL_STAR_NOT (CTL_STAR_E(CTL_STAR_NOT f))`;
val CTL_STAR_OR_def = Define `CTL_STAR_OR(f1,f2) = CTL_STAR_NOT (CTL_STAR_AND((CTL_STAR_NOT f1),(CTL_STAR_NOT f2)))`;
val CTL_STAR_IMPL_def = Define `CTL_STAR_IMPL(f1, f2) = CTL_STAR_OR(CTL_STAR_NOT f1, f2)`;
val CTL_STAR_COND_def = Define `CTL_STAR_COND(c, f1, f2) = CTL_STAR_AND(CTL_STAR_IMPL(c, f1), CTL_STAR_IMPL(CTL_STAR_NOT c, f2))`;
val CTL_STAR_EQUIV_def = Define `CTL_STAR_EQUIV(b1, b2) = CTL_STAR_AND(CTL_STAR_IMPL(b1, b2),CTL_STAR_IMPL(b2, b1))`;
val CTL_STAR_EVENTUAL_def = Define `CTL_STAR_EVENTUAL f = CTL_STAR_SUNTIL (CTL_STAR_PROP(P_TRUE),f)`;
val CTL_STAR_ALWAYS_def = Define `CTL_STAR_ALWAYS f = CTL_STAR_NOT (CTL_STAR_EVENTUAL (CTL_STAR_NOT f))`;
val CTL_STAR_UNTIL_def = Define `CTL_STAR_UNTIL(f1,f2) = CTL_STAR_OR(CTL_STAR_SUNTIL(f1,f2),CTL_STAR_ALWAYS f1)`;
val CTL_STAR_BEFORE_def = Define `CTL_STAR_BEFORE(f1,f2) = CTL_STAR_NOT(CTL_STAR_SUNTIL(CTL_STAR_NOT f1,f2))`;
val CTL_STAR_SBEFORE_def = Define `CTL_STAR_SBEFORE(f1,f2) = CTL_STAR_SUNTIL(CTL_STAR_NOT f2,CTL_STAR_AND(f1, CTL_STAR_NOT f2))`;
val CTL_STAR_WHILE_def = Define `CTL_STAR_WHILE(f1,f2) = CTL_STAR_NOT(CTL_STAR_SUNTIL(CTL_STAR_OR(CTL_STAR_NOT f1, CTL_STAR_NOT f2),CTL_STAR_AND(f2, CTL_STAR_NOT f1)))`;
val CTL_STAR_SWHILE_def = Define `CTL_STAR_SWHILE(f1,f2) = CTL_STAR_SUNTIL(CTL_STAR_NOT f2,CTL_STAR_AND(f1, f2))`;
val CTL_STAR_PEVENTUAL_def = Define `CTL_STAR_PEVENTUAL f = CTL_STAR_PSUNTIL (CTL_STAR_PROP(P_TRUE),f)`;
val CTL_STAR_PALWAYS_def = Define `CTL_STAR_PALWAYS f = CTL_STAR_NOT (CTL_STAR_PEVENTUAL (CTL_STAR_NOT f))`;
val CTL_STAR_PUNTIL_def = Define `CTL_STAR_PUNTIL(f1,f2) = CTL_STAR_OR(CTL_STAR_PSUNTIL(f1,f2),CTL_STAR_PALWAYS f1)`;
val CTL_STAR_PNEXT_def = Define `CTL_STAR_PNEXT f = CTL_STAR_NOT(CTL_STAR_PSNEXT (CTL_STAR_NOT f))`;
val CTL_STAR_PBEFORE_def = Define `CTL_STAR_PBEFORE(f1,f2) = CTL_STAR_NOT(CTL_STAR_PSUNTIL(CTL_STAR_NOT f1,f2))`;
val CTL_STAR_PSBEFORE_def = Define `CTL_STAR_PSBEFORE(f1,f2) = CTL_STAR_PSUNTIL(CTL_STAR_NOT f2,CTL_STAR_AND(f1, CTL_STAR_NOT f2))`;
val CTL_STAR_PWHILE_def = Define `CTL_STAR_PWHILE(f1,f2) = CTL_STAR_NOT(CTL_STAR_PSUNTIL(CTL_STAR_OR(CTL_STAR_NOT f1, CTL_STAR_NOT f2),CTL_STAR_AND(f2, CTL_STAR_NOT f1)))`;
val CTL_STAR_PSWHILE_def = Define `CTL_STAR_PSWHILE(f1,f2) = CTL_STAR_PSUNTIL(CTL_STAR_NOT f2,CTL_STAR_AND(f1, f2))`;

val CTL_STAR_FAIRNESS_def =
 Define
  `(CTL_STAR_FAIRNESS [] = (CTL_STAR_PROP (P_TRUE))) /\
   (CTL_STAR_FAIRNESS (f::FC) = (CTL_STAR_AND (CTL_STAR_ALWAYS(CTL_STAR_EVENTUAL (CTL_STAR_PROP f)), CTL_STAR_FAIRNESS FC)))`;

val CTL_STAR_FAIR_E_def = Define `CTL_STAR_FAIR_E FC f = (CTL_STAR_E (CTL_STAR_AND(f, CTL_STAR_FAIRNESS FC)))`;
val CTL_STAR_FAIR_A_def = Define `CTL_STAR_FAIR_A FC f = (CTL_STAR_A (CTL_STAR_IMPL(CTL_STAR_FAIRNESS FC, f)))`;


val CTL_STAR_SEM___PROP_CASES =
    prove (``!M f1 f2 p s t.
      (CTL_STAR_SEM_PATH M (CTL_STAR_OR(f1, f2)) p =
       (CTL_STAR_SEM_PATH M f1 p \/ CTL_STAR_SEM_PATH M f2 p)) /\
      (CTL_STAR_SEM_PATH M (CTL_STAR_IMPL(f1, f2)) p =
       (CTL_STAR_SEM_PATH M f1 p ==> CTL_STAR_SEM_PATH M f2 p)) /\
      (CTL_STAR_SEM_PATH M (CTL_STAR_EQUIV(f1, f2)) p =
       (CTL_STAR_SEM_PATH M f1 p = CTL_STAR_SEM_PATH M f2 p)) /\
      (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_OR(f1, f2)) p =
       (CTL_STAR_SEM_PATH_TIME t M f1 p \/ CTL_STAR_SEM_PATH_TIME t M f2 p)) /\
      (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_IMPL(f1, f2)) p =
       (CTL_STAR_SEM_PATH_TIME t M f1 p ==> CTL_STAR_SEM_PATH_TIME t M f2 p)) /\
      (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_EQUIV(f1, f2)) p =
       (CTL_STAR_SEM_PATH_TIME t M f1 p = CTL_STAR_SEM_PATH_TIME t M f2 p)) /\
      (CTL_STAR_SEM_STATE M (CTL_STAR_OR(f1, f2)) s =
       (CTL_STAR_SEM_STATE M f1 s \/ CTL_STAR_SEM_STATE M f2 s)) /\
      (CTL_STAR_SEM_STATE M (CTL_STAR_IMPL(f1, f2)) s =
       (CTL_STAR_SEM_STATE M f1 s ==> CTL_STAR_SEM_STATE M f2 s)) /\
      (CTL_STAR_SEM_STATE M (CTL_STAR_EQUIV(f1, f2)) s =
       (CTL_STAR_SEM_STATE M f1 s = CTL_STAR_SEM_STATE M f2 s))``,

    REPEAT GEN_TAC THEN
    SIMP_TAC std_ss [CTL_STAR_SEM_PATH_def, CTL_STAR_SEM_PATH_TIME_def, CTL_STAR_SEM_STATE_def,
      CTL_STAR_OR_def, CTL_STAR_IMPL_def, CTL_STAR_EQUIV_def,
      CTL_STAR_SEM_STATE_def] THEN
    METIS_TAC[]);


val CTL_STAR_SEM___EVENTUAL_ALWAYS =
    prove (``!M t f p.
      (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_EVENTUAL f) p =
       (?k. k >= t /\ CTL_STAR_SEM_PATH_TIME k M f p)) /\
      (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_ALWAYS f) p =
       (!k. k >= t ==> CTL_STAR_SEM_PATH_TIME k M f p)) /\
      (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_PEVENTUAL f) p =
       (?k. k <= t /\ CTL_STAR_SEM_PATH_TIME k M f p)) /\
      (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_PALWAYS f) p =
       (!k. k <= t ==> CTL_STAR_SEM_PATH_TIME k M f p))``,

    SIMP_TAC std_ss [CTL_STAR_SEM_PATH_TIME_def, CTL_STAR_EVENTUAL_def,
      CTL_STAR_ALWAYS_def, P_SEM_THM, CTL_STAR_PALWAYS_def, CTL_STAR_PEVENTUAL_def] THEN
    PROVE_TAC[]);



val CTL_STAR_SEM___CTL_STAR_A =
    prove (``!M f p s t.
   (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_A f) p = (!p'. ((p' 0 = p t) /\
    IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p') ==> CTL_STAR_SEM_PATH M f p')) /\
   (CTL_STAR_SEM_STATE M (CTL_STAR_A f) s = (!p'. ((p' 0 = s) /\
    IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p') ==> CTL_STAR_SEM_PATH M f p'))``,

   SIMP_TAC std_ss [CTL_STAR_SEM_PATH_def, CTL_STAR_SEM_PATH_TIME_def, CTL_STAR_SEM_STATE_def,
      CTL_STAR_A_def] THEN
   METIS_TAC[]);



val CTL_STAR_SEM___FAIRNESS =
  store_thm ("CTL_STAR_SEM___FAIRNESS",
    ``!M FC p t.
      (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_FAIRNESS FC) p =
       (!b. MEM b FC ==> !t0. ?t. t >= t0 /\ P_SEM (p t) b))``,

    Induct_on `FC` THENL [
      SIMP_TAC list_ss [CTL_STAR_FAIRNESS_def, CTL_STAR_SEM_PATH_TIME_def, P_SEM_THM],

      SIMP_TAC list_ss [CTL_STAR_FAIRNESS_def, CTL_STAR_SEM_PATH_TIME_def,
        CTL_STAR_SEM___EVENTUAL_ALWAYS, P_SEM_THM,
        DISJ_IMP_THM, FORALL_AND_THM, PATH_RESTN_def] THEN
      REPEAT GEN_TAC THEN
      Tactical.REVERSE (BINOP_TAC) THEN1 ASM_REWRITE_TAC[] THEN
      REPEAT WEAKEN_HD_TAC THEN
      EQ_TAC THEN REPEAT STRIP_TAC THENL [
        SUBGOAL_TAC `?t1. t1 >= t /\ t1 > t0` THEN1 (
          Cases_on `t > t0` THENL [
            EXISTS_TAC ``t:num`` THEN
            ASM_SIMP_TAC arith_ss [],

            EXISTS_TAC ``SUC t0`` THEN
            FULL_SIMP_TAC arith_ss []
          ]
        ) THEN
        SPECL_NO_ASSUM 2 [``t1:num``] THEN
        UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
        EXISTS_TAC ``k':num`` THEN
        ASM_SIMP_TAC arith_ss [],

        SPECL_NO_ASSUM 1 [``k:num``] THEN
        FULL_SIMP_TAC std_ss [] THEN
        EXISTS_TAC ``t':num`` THEN
        ASM_SIMP_TAC arith_ss []
      ]
    ]);


val CTL_STAR_SEM___FAIR_E_FAIR_A =
    prove (``!M f t FC p s.
   (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_FAIR_E FC f) p = (?p'. (p' 0 = p t) /\
    IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M FC p' /\ CTL_STAR_SEM_PATH M f p')) /\
   (CTL_STAR_SEM_STATE M (CTL_STAR_FAIR_E FC f) s = (?p'. (p' 0 = s) /\
    IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M FC p' /\ CTL_STAR_SEM_PATH M f p')) /\
   (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_FAIR_A FC f) p = (!p'. ((p' 0 = p t) /\
    IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M FC p') ==> CTL_STAR_SEM_PATH M f p')) /\
   (CTL_STAR_SEM_STATE M (CTL_STAR_FAIR_A FC f) s = (!p'. ((p' 0 = s) /\
    IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M FC p') ==> CTL_STAR_SEM_PATH M f p'))``,

   SIMP_TAC std_ss [CTL_STAR_FAIR_E_def, CTL_STAR_FAIR_A_def,
     CTL_STAR_SEM_STATE_def, CTL_STAR_SEM_PATH_def, CTL_STAR_SEM_PATH_TIME_def,
     IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def, CTL_STAR_SEM___FAIRNESS,
     CTL_STAR_SEM___CTL_STAR_A, CTL_STAR_SEM___PROP_CASES] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC arith_ss [] THEN
   METIS_TAC[]);



val CTL_STAR_SEM___EMPTY_FAIRNESS =
    prove (``!M t f p s.
   (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_FAIR_E [] f) p = CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_E f) p) /\
   (CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_FAIR_A [] f) p = CTL_STAR_SEM_PATH_TIME t M (CTL_STAR_A f) p) /\
   (CTL_STAR_SEM_STATE M (CTL_STAR_FAIR_E [] f) s = CTL_STAR_SEM_STATE M (CTL_STAR_E f) s) /\
   (CTL_STAR_SEM_STATE M (CTL_STAR_FAIR_A [] f) s = CTL_STAR_SEM_STATE M (CTL_STAR_A f) s)``,

   SIMP_TAC std_ss [CTL_STAR_SEM_PATH_def, CTL_STAR_SEM_PATH_TIME_def, CTL_STAR_SEM_STATE_def,
    CTL_STAR_FAIR_E_def, CTL_STAR_FAIRNESS_def, P_SEM_THM,
    CTL_STAR_FAIR_A_def, CTL_STAR_SEM___CTL_STAR_A,
    CTL_STAR_SEM___PROP_CASES]);


val CTL_STAR_SEM_THM = save_thm ("CTL_STAR_SEM_THM",
    SIMP_RULE std_ss [FORALL_AND_THM] (
      LIST_CONJ [CTL_STAR_SEM_PATH_def,
                 CTL_STAR_SEM_PATH_TIME_def,
                CTL_STAR_SEM_STATE_def,
                CTL_STAR_SEM___PROP_CASES,
                CTL_STAR_SEM___EVENTUAL_ALWAYS,
                CTL_STAR_SEM___CTL_STAR_A,
                CTL_STAR_SEM___EMPTY_FAIRNESS,
                CTL_STAR_SEM___FAIR_E_FAIR_A]));




(******************************************************************************
* SUBLANGUAGE LTL
******************************************************************************)

val LTL_TO_CTL_STAR_def =
 Define
  `(LTL_TO_CTL_STAR (LTL_PROP b) = (CTL_STAR_PROP b)) /\
   (LTL_TO_CTL_STAR (LTL_NOT f) = (CTL_STAR_NOT (LTL_TO_CTL_STAR f))) /\
   (LTL_TO_CTL_STAR (LTL_AND (f1, f2)) = (CTL_STAR_AND (LTL_TO_CTL_STAR f1, LTL_TO_CTL_STAR f2))) /\
   (LTL_TO_CTL_STAR (LTL_NEXT f) = (CTL_STAR_NEXT (LTL_TO_CTL_STAR f))) /\
   (LTL_TO_CTL_STAR (LTL_SUNTIL (f1, f2)) = (CTL_STAR_SUNTIL (LTL_TO_CTL_STAR f1, LTL_TO_CTL_STAR f2))) /\
   (LTL_TO_CTL_STAR (LTL_PSNEXT f) = (CTL_STAR_PSNEXT (LTL_TO_CTL_STAR f))) /\
   (LTL_TO_CTL_STAR (LTL_PSUNTIL (f1, f2)) = (CTL_STAR_PSUNTIL (LTL_TO_CTL_STAR f1, LTL_TO_CTL_STAR f2)))`;


val LTL_FORMULAS_ARE_PATH_FORMULAS =
  store_thm (
    "LTL_FORMULAS_ARE_PATH_FORMULAS",
    ``!f. IS_CTL_STAR_PATH_FORMULA (LTL_TO_CTL_STAR f)``,

      INDUCT_THEN ltl_induct ASSUME_TAC THEN
      ASM_SIMP_TAC std_ss [IS_CTL_STAR_PATH_FORMULA_def,
        LTL_TO_CTL_STAR_def]);


val LTL_TO_CTL_STAR_THM =
  store_thm ("LTL_TO_CTL_STAR_THM",
    ``!l p M t.
        CTL_STAR_SEM_PATH_TIME t M (LTL_TO_CTL_STAR l) p = (LTL_SEM_TIME t p l)``,

    INDUCT_THEN ltl_induct ASSUME_TAC THEN
    FULL_SIMP_TAC arith_ss [LTL_TO_CTL_STAR_def,
      LTL_SEM_THM, CTL_STAR_SEM_THM] THEN
    PROVE_TAC[]);


val LTL_TO_CTL_STAR_NO_MODEL_THM =
  store_thm ("LTL_TO_CTL_STAR_NO_MODEL_THM",
    ``!l p t.
        CTL_STAR_SEM_NO_MODEL_PATH_TIME t (LTL_TO_CTL_STAR l) p =
        LTL_SEM_TIME t p l``,

    REPEAT STRIP_TAC THEN
    `IS_CTL_STAR_PATH_FORMULA (LTL_TO_CTL_STAR l)` by
      PROVE_TAC[LTL_FORMULAS_ARE_PATH_FORMULAS] THEN
    PROVE_TAC [IS_CTL_STAR_PATH_FORMULA___NO_MODEL_SEM,
               LTL_TO_CTL_STAR_THM]);



val LTL_KS_SEM___TO___CTL_STAR_KS_SEM =
  store_thm ("LTL_KS_SEM___TO___CTL_STAR_KS_SEM",
    ``!M f. CTL_STAR_KS_SEM M (CTL_STAR_A (LTL_TO_CTL_STAR f)) = LTL_KS_SEM M f``,

    SIMP_TAC std_ss [LTL_KS_SEM_def, CTL_STAR_KS_SEM_def,
      LTL_TO_CTL_STAR_THM, CTL_STAR_SEM_THM, LTL_SEM_def,
      IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def] THEN
    PROVE_TAC[]);



(******************************************************************************
 *  Fair CTL
 ******************************************************************************)

val fair_ctl_def =
 Hol_datatype
  `fair_ctl =   FAIR_CTL_PROP     of 'a prop_logic                     (* boolean expression      *)
         | FAIR_CTL_NOT      of fair_ctl                                    (* \neg f                  *)
         | FAIR_CTL_AND      of fair_ctl # fair_ctl                              (* f1 \wedge f2            *)
         | FAIR_CTL_E_NEXT   of ('a prop_logic list) => fair_ctl            (* X f                     *)
         | FAIR_CTL_E_SUNTIL of ('a prop_logic list) => (fair_ctl # fair_ctl)    (* strong_until            *)
         | FAIR_CTL_E_UNTIL  of ('a prop_logic list) => (fair_ctl # fair_ctl)`;  (* weak until              *)

val fair_ctl_induct =
 save_thm
  ("fair_ctl_induct",
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
         [`P`,`\(f1,f2). P f1 /\ P f2`]
         (TypeBase.induction_of ``:'a fair_ctl``)))));


(*Since FAIR_CTL is a subset of CTL_STAR we can easily translate it to FAIR_CTL_STAR*)
val FAIR_CTL_TO_CTL_STAR_def =
 Define
  `(FAIR_CTL_TO_CTL_STAR (FAIR_CTL_PROP b) = (CTL_STAR_PROP b)) /\
   (FAIR_CTL_TO_CTL_STAR (FAIR_CTL_NOT f) = (CTL_STAR_NOT (FAIR_CTL_TO_CTL_STAR f))) /\
   (FAIR_CTL_TO_CTL_STAR (FAIR_CTL_AND (f1, f2)) = (CTL_STAR_AND (FAIR_CTL_TO_CTL_STAR f1, FAIR_CTL_TO_CTL_STAR f2))) /\
   (FAIR_CTL_TO_CTL_STAR (FAIR_CTL_E_NEXT FC f) = (CTL_STAR_FAIR_E FC (CTL_STAR_NEXT (FAIR_CTL_TO_CTL_STAR f)))) /\
   (FAIR_CTL_TO_CTL_STAR (FAIR_CTL_E_SUNTIL FC (f1, f2)) = (CTL_STAR_FAIR_E FC (CTL_STAR_SUNTIL (FAIR_CTL_TO_CTL_STAR f1, FAIR_CTL_TO_CTL_STAR f2)))) /\
   (FAIR_CTL_TO_CTL_STAR (FAIR_CTL_E_UNTIL FC (f1, f2)) = (CTL_STAR_FAIR_E FC (CTL_STAR_UNTIL (FAIR_CTL_TO_CTL_STAR f1, FAIR_CTL_TO_CTL_STAR f2))))`;


val FAIR_CTL_SEM_def =
 Define `
   FAIR_CTL_SEM M f s = CTL_STAR_SEM_STATE M (FAIR_CTL_TO_CTL_STAR f) s`;

val FAIR_CTL_KS_SEM_def =
 Define
  `FAIR_CTL_KS_SEM M f = (!s. P_SEM s M.S0 ==> FAIR_CTL_SEM M f s)`;


val FAIR_CTL_KS_SEM___TO___CTL_STAR_KS_SEM =
  store_thm ("FAIR_CTL_KS_SEM___TO___CTL_STAR_KS_SEM",
    ``!M f. FAIR_CTL_KS_SEM M f = CTL_STAR_KS_SEM M (FAIR_CTL_TO_CTL_STAR f)``,

    SIMP_TAC std_ss [FAIR_CTL_KS_SEM_def, CTL_STAR_KS_SEM_def,
      FAIR_CTL_SEM_def]);


val FAIR_CTL_FORMULAS_ARE_STATE_FORMULAS =
  store_thm (
    "FAIR_CTL_FORMULAS_ARE_STATE_FORMULAS",
    ``!f. IS_CTL_STAR_STATE_FORMULA (FAIR_CTL_TO_CTL_STAR f)``,

      INDUCT_THEN fair_ctl_induct ASSUME_TAC THEN
      ASM_SIMP_TAC std_ss [IS_CTL_STAR_STATE_FORMULA_def,
          FAIR_CTL_TO_CTL_STAR_def, CTL_STAR_FAIR_E_def]);


val FAIR_CTL_USED_VARS_def =
 Define `
   (FAIR_CTL_USED_VARS f = CTL_STAR_USED_VARS (FAIR_CTL_TO_CTL_STAR f))`;



(*Syntactic Sugaring*)
val FAIR_CTL_OR_def = Define `FAIR_CTL_OR(f1,f2) = FAIR_CTL_NOT (FAIR_CTL_AND((FAIR_CTL_NOT f1),(FAIR_CTL_NOT f2)))`;
val FAIR_CTL_IMPL_def = Define `FAIR_CTL_IMPL(f1, f2) = FAIR_CTL_OR(FAIR_CTL_NOT f1, f2)`;
val FAIR_CTL_COND_def = Define `FAIR_CTL_COND(c, f1, f2) = FAIR_CTL_AND(FAIR_CTL_IMPL(c, f1), FAIR_CTL_IMPL(FAIR_CTL_NOT c, f2))`;
val FAIR_CTL_EQUIV_def = Define `FAIR_CTL_EQUIV(b1, b2) = FAIR_CTL_AND(FAIR_CTL_IMPL(b1, b2),FAIR_CTL_IMPL(b2, b1))`;
val FAIR_CTL_A_NEXT_def = Define `FAIR_CTL_A_NEXT FC f = FAIR_CTL_NOT(FAIR_CTL_E_NEXT FC (FAIR_CTL_NOT f))`;
val FAIR_CTL_E_EVENTUAL_def = Define `FAIR_CTL_E_EVENTUAL FC f = FAIR_CTL_E_SUNTIL FC (FAIR_CTL_PROP(P_TRUE),f)`;
val FAIR_CTL_E_ALWAYS_def = Define `FAIR_CTL_E_ALWAYS FC f = FAIR_CTL_E_UNTIL FC (f, FAIR_CTL_PROP(P_FALSE))`;
val FAIR_CTL_A_EVENTUAL_def = Define `FAIR_CTL_A_EVENTUAL FC f = FAIR_CTL_NOT (FAIR_CTL_E_ALWAYS FC (FAIR_CTL_NOT f))`;
val FAIR_CTL_A_ALWAYS_def = Define `FAIR_CTL_A_ALWAYS FC f = FAIR_CTL_NOT (FAIR_CTL_E_EVENTUAL FC (FAIR_CTL_NOT f))`;
val FAIR_CTL_A_UNTIL_def = Define `FAIR_CTL_A_UNTIL FC (f1,f2) = FAIR_CTL_NOT(FAIR_CTL_E_SUNTIL FC (FAIR_CTL_NOT f2, (FAIR_CTL_AND(FAIR_CTL_NOT f1, FAIR_CTL_NOT f2))))`;
val FAIR_CTL_A_SUNTIL_def = Define `FAIR_CTL_A_SUNTIL FC (f1,f2) = FAIR_CTL_NOT(FAIR_CTL_E_UNTIL FC (FAIR_CTL_NOT f2, (FAIR_CTL_AND(FAIR_CTL_NOT f1, FAIR_CTL_NOT f2))))`;
val FAIR_CTL_E_BEFORE_def = Define `FAIR_CTL_E_BEFORE FC (f1,f2) = FAIR_CTL_E_UNTIL FC (FAIR_CTL_NOT f2, FAIR_CTL_AND(f1, FAIR_CTL_NOT f2))`;
val FAIR_CTL_E_SBEFORE_def = Define `FAIR_CTL_E_SBEFORE FC (f1,f2) = FAIR_CTL_E_SUNTIL FC (FAIR_CTL_NOT f2, FAIR_CTL_AND(f1, FAIR_CTL_NOT f2))`;
val FAIR_CTL_A_BEFORE_def = Define `FAIR_CTL_A_BEFORE FC (f1,f2) = FAIR_CTL_NOT(FAIR_CTL_E_SUNTIL FC (FAIR_CTL_NOT f1, f2))`;
val FAIR_CTL_A_SBEFORE_def = Define `FAIR_CTL_A_SBEFORE FC (f1,f2) = FAIR_CTL_NOT(FAIR_CTL_E_UNTIL FC (FAIR_CTL_NOT f1, f2))`;
val FAIR_CTL_E_WHILE_def = Define `FAIR_CTL_E_WHILE FC (f1,f2) = FAIR_CTL_E_UNTIL FC (FAIR_CTL_NOT f2, FAIR_CTL_AND(f1, f2))`;
val FAIR_CTL_E_SWHILE_def = Define `FAIR_CTL_E_SWHILE FC (f1,f2) = FAIR_CTL_E_SUNTIL FC (FAIR_CTL_NOT f2, FAIR_CTL_AND(f1, f2))`;
val FAIR_CTL_A_WHILE_def = Define `FAIR_CTL_A_WHILE FC (f1,f2) = FAIR_CTL_NOT(FAIR_CTL_E_SUNTIL FC (FAIR_CTL_NOT f2, FAIR_CTL_AND(FAIR_CTL_NOT f1, f2)))`;
val FAIR_CTL_A_SWHILE_def = Define `FAIR_CTL_A_SWHILE FC (f1,f2) = FAIR_CTL_NOT(FAIR_CTL_E_UNTIL FC (FAIR_CTL_NOT f2, FAIR_CTL_AND(FAIR_CTL_NOT f1, f2)))`;



val FAIR_CTL_SEM_THM___BASIC_CASES = prove(
    ``!M b FC f f1 f2 s.

   (FAIR_CTL_SEM M (FAIR_CTL_PROP b) s = (P_SEM s b)) /\

   (FAIR_CTL_SEM M (FAIR_CTL_NOT f) s = ~(FAIR_CTL_SEM M f s)) /\

   (FAIR_CTL_SEM M (FAIR_CTL_AND(f1,f2)) s = FAIR_CTL_SEM M f1 s /\ FAIR_CTL_SEM M f2 s) /\

   (FAIR_CTL_SEM M (FAIR_CTL_OR(f1,f2)) s = FAIR_CTL_SEM M f1 s \/ FAIR_CTL_SEM M f2 s) /\

   (FAIR_CTL_SEM M (FAIR_CTL_IMPL(f1,f2)) s = FAIR_CTL_SEM M f1 s ==> FAIR_CTL_SEM M f2 s) /\

   (FAIR_CTL_SEM M (FAIR_CTL_E_NEXT FC f) s = (?p. IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M FC p /\
      (p 0 = s) /\ FAIR_CTL_SEM M f (p 1))) /\

   (FAIR_CTL_SEM M (FAIR_CTL_E_SUNTIL FC (f1, f2)) s = (?p. IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M FC p /\
      (p 0 = s) /\ (?k. FAIR_CTL_SEM M f2 (p k) /\ (!j. j < k ==> FAIR_CTL_SEM M f1 (p j))))) /\

   (FAIR_CTL_SEM M (FAIR_CTL_E_UNTIL FC (f1, f2)) s = (?p. IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M FC p /\
      (p 0 = s) /\
      ((?k. FAIR_CTL_SEM M f2 (p k) /\ (!j. j < k ==> FAIR_CTL_SEM M f1 (p j))) \/
       (!j. FAIR_CTL_SEM M f1 (p j)))))``,

    SIMP_TAC std_ss [FAIR_CTL_SEM_def, FAIR_CTL_TO_CTL_STAR_def,
      CTL_STAR_SEM_THM, PATH_REST_def,
      CTL_STAR_UNTIL_def, FAIR_CTL_OR_def, FAIR_CTL_IMPL_def] THEN
    METIS_TAC[IS_CTL_STAR_STATE_FORMULA___SEM, FAIR_CTL_FORMULAS_ARE_STATE_FORMULAS]
  );



val FAIR_CTL_SEM_THM___A_NEXT = prove(
    ``!M f FC s.
      FAIR_CTL_SEM M (FAIR_CTL_A_NEXT FC f) s = (!p. (IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M FC p /\
                                    (p 0 = s)) ==> FAIR_CTL_SEM M f (p 1))``,

    SIMP_TAC std_ss [FAIR_CTL_SEM_THM___BASIC_CASES, FAIR_CTL_TO_CTL_STAR_def,
      FAIR_CTL_A_NEXT_def] THEN
    PROVE_TAC[]
  );


val FAIR_CTL_SEM_THM___E_EVENTUAL_ALWAYS = prove(
    ``!M f FC s.

   (FAIR_CTL_SEM M (FAIR_CTL_E_EVENTUAL FC f) s = (?p. IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M FC p /\
                                    (p 0 = s) /\ ?k. FAIR_CTL_SEM M f (p k))) /\
   (FAIR_CTL_SEM M (FAIR_CTL_E_ALWAYS FC f) s = (?p. IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M FC p /\
                                    (p 0 = s) /\ !k. FAIR_CTL_SEM M f (p k)))``,

    SIMP_TAC std_ss [FAIR_CTL_SEM_def, FAIR_CTL_TO_CTL_STAR_def,
      CTL_STAR_SEM_THM, FAIR_CTL_E_EVENTUAL_def, FAIR_CTL_E_ALWAYS_def, P_SEM_THM,
      CTL_STAR_UNTIL_def] THEN
    `!n (p:num->'b). (PATH_RESTN p n 0) = (p n)` by (EVAL_TAC THEN PROVE_TAC[]) THEN
    METIS_TAC[IS_CTL_STAR_STATE_FORMULA___SEM, FAIR_CTL_FORMULAS_ARE_STATE_FORMULAS]
  );



val FAIR_CTL_SEM_THM___A_EVENTUAL_ALWAYS = prove(
    ``!M f FC s.

   (FAIR_CTL_SEM M (FAIR_CTL_A_EVENTUAL FC f) s = (!p. (IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M FC p /\
                                    (p 0 = s)) ==> ?k. FAIR_CTL_SEM M f (p k))) /\
   (FAIR_CTL_SEM M (FAIR_CTL_A_ALWAYS FC f) s = (!p. (IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M FC p /\
                                    (p 0 = s)) ==> (!k. FAIR_CTL_SEM M f (p k))))``,

    SIMP_TAC std_ss [FAIR_CTL_SEM_THM___BASIC_CASES, FAIR_CTL_A_EVENTUAL_def, FAIR_CTL_A_ALWAYS_def,
      FAIR_CTL_TO_CTL_STAR_def, FAIR_CTL_SEM_THM___E_EVENTUAL_ALWAYS] THEN
    PROVE_TAC[]);


val FAIR_CTL_SEM_THM___A_SUNTIL = prove(
    ``!M f1 f2 FC s.
   (FAIR_CTL_SEM M (FAIR_CTL_A_SUNTIL FC (f1, f2)) s = (!p. (IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M FC p /\
      (p 0 = s)) ==> (?k. FAIR_CTL_SEM M f2 (p k) /\ (!j. j < k ==> FAIR_CTL_SEM M f1 (p j)))))``,


    SIMP_TAC std_ss [FAIR_CTL_SEM_THM___BASIC_CASES, FAIR_CTL_TO_CTL_STAR_def,
      FAIR_CTL_A_SUNTIL_def] THEN
    REPEAT STRIP_TAC THEN
    FORALL_EQ_STRIP_TAC THEN
    SIMP_TAC std_ss [IMP_DISJ_THM] THEN
    REPEAT BOOL_EQ_STRIP_TAC THEN
    Cases_on `?k. FAIR_CTL_SEM M f2 (p k)` THENL [
      POP_NO_ASSUM 0 (fn x=> (ASSUME_TAC (CONV_RULE EXISTS_LEAST_CONV x))),
      METIS_TAC[]
    ] THEN
    CLEAN_ASSUMPTIONS_TAC THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL [
      EXISTS_TAC ``k:num`` THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      rename1 `k' < k` THEN
      RIGHT_DISJ_TAC THEN
      SPECL_NO_ASSUM 2 [``k':num``] THEN
      FULL_SIMP_TAC std_ss [] THENL [
        METIS_TAC[],
        rename1 `j' < k'` THEN
        `j' < k` by DECIDE_TAC THEN PROVE_TAC[]
      ],


      rename1 `FAIR_CTL_SEM M f1 (p j)` THEN
      Cases_on `j < k'` THENL [
        PROVE_TAC[],

        Cases_on `k' = j` THENL [
          FULL_SIMP_TAC std_ss [],

          `k' < j` by DECIDE_TAC THEN
          PROVE_TAC[]
        ]
      ],

      PROVE_TAC[]
    ]);


val FAIR_CTL_SEM_THM___A_UNTIL = prove(
    ``!M f1 f2 FC s.
   (FAIR_CTL_SEM M (FAIR_CTL_A_UNTIL FC (f1, f2)) s = (!p. (IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M FC p /\
      (p 0 = s)) ==> ((?k. FAIR_CTL_SEM M f2 (p k) /\ (!j. j < k ==> FAIR_CTL_SEM M f1 (p j))) \/
                      (!j. FAIR_CTL_SEM M f1 (p j)))))``,


    SIMP_TAC std_ss [FAIR_CTL_SEM_THM___BASIC_CASES, FAIR_CTL_TO_CTL_STAR_def,
      FAIR_CTL_A_UNTIL_def] THEN
    REPEAT STRIP_TAC THEN
    FORALL_EQ_STRIP_TAC THEN
    SIMP_TAC std_ss [IMP_DISJ_THM] THEN
    REPEAT BOOL_EQ_STRIP_TAC THEN
    Cases_on `?j. ~FAIR_CTL_SEM M f1 (p j)` THENL [
      POP_NO_ASSUM 0 (fn x=> (ASSUME_TAC (CONV_RULE EXISTS_LEAST_CONV x))),
      PROVE_TAC[]
    ] THEN
    CLEAN_ASSUMPTIONS_TAC THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL [
      DISJ1_TAC THEN
      SPECL_NO_ASSUM 0 [``j:num``] THEN
      FULL_SIMP_TAC std_ss [] THENL [
        PROVE_TAC[],

        EXISTS_TAC ``j:num`` THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THEN
        RIGHT_DISJ_TAC THEN
        FULL_SIMP_TAC std_ss [],

        EXISTS_TAC ``j':num`` THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THEN
        RIGHT_DISJ_TAC THEN
        `j'' < j` by DECIDE_TAC THEN
        FULL_SIMP_TAC std_ss []
      ],


      Cases_on `k < k'` THENL [
        PROVE_TAC[],

        Cases_on `k' = k` THENL [
          PROVE_TAC[],

          `k' < k` by DECIDE_TAC THEN
          PROVE_TAC[]
        ]
      ],

      PROVE_TAC[]
    ]);




val FAIR_CTL_SEM_THM =
  save_thm
    ("FAIR_CTL_SEM_THM",
    SIMP_RULE std_ss [FORALL_AND_THM]
    (LIST_CONJ [FAIR_CTL_SEM_THM___BASIC_CASES,
               FAIR_CTL_SEM_THM___A_NEXT,
               FAIR_CTL_SEM_THM___E_EVENTUAL_ALWAYS,
               FAIR_CTL_SEM_THM___A_EVENTUAL_ALWAYS,
               FAIR_CTL_SEM_THM___A_SUNTIL,
               FAIR_CTL_SEM_THM___A_UNTIL]));



(******************************************************************************
 *  CTL
 ******************************************************************************)

val ctl_def =
 Hol_datatype
  `ctl =   CTL_PROP     of 'a prop_logic     (* boolean expression      *)
         | CTL_NOT      of ctl               (* \neg f                  *)
         | CTL_AND      of ctl # ctl         (* f1 \wedge f2            *)
         | CTL_E_NEXT   of ctl               (* X f                     *)
         | CTL_E_SUNTIL of ctl # ctl         (* strong_until            *)
         | CTL_E_UNTIL  of ctl # ctl`;       (* weak until              *)


val ctl_induct =
 save_thm
  ("ctl_induct",
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
         [`P`,`\(f1,f2). P f1 /\ P f2`]
         (TypeBase.induction_of ``:'a ctl``)))));


(*Since CTL is a subset of CTL_STAR we can easily translate it to CTL_STAR*)
val CTL_TO_FAIR_CTL_def =
 Define
  `(CTL_TO_FAIR_CTL fc (CTL_PROP b) = (FAIR_CTL_PROP b)) /\
   (CTL_TO_FAIR_CTL fc (CTL_NOT f) = (FAIR_CTL_NOT (CTL_TO_FAIR_CTL fc f))) /\
   (CTL_TO_FAIR_CTL fc (CTL_AND (f1, f2)) = (FAIR_CTL_AND (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
   (CTL_TO_FAIR_CTL fc (CTL_E_NEXT f) = (FAIR_CTL_E_NEXT fc (CTL_TO_FAIR_CTL fc f))) /\
   (CTL_TO_FAIR_CTL fc (CTL_E_SUNTIL (f1, f2)) = (FAIR_CTL_E_SUNTIL fc (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
   (CTL_TO_FAIR_CTL fc (CTL_E_UNTIL (f1, f2)) = (FAIR_CTL_E_UNTIL fc (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2)))`;


val CTL_SEM_def =
 Define `
   CTL_SEM M f s = FAIR_CTL_SEM M (CTL_TO_FAIR_CTL [] f) s`;


val CTL_FAIR_SEM_def =
 Define `
   CTL_FAIR_SEM M f fc s = FAIR_CTL_SEM M (CTL_TO_FAIR_CTL fc f) s`;

val CTL_KS_SEM_def =
 Define
  `CTL_KS_SEM M f = (!s. P_SEM s M.S0 ==> CTL_SEM M f s)`;

val CTL_KS_FAIR_SEM_def =
 Define
  `CTL_KS_FAIR_SEM M f fc = (!s. P_SEM s M.S0 ==> CTL_FAIR_SEM M f fc s)`;


val CTL_KS_SEM___TO___FAIR_CTL_KS_SEM =
  store_thm ("CTL_KS_SEM___TO___FAIR_CTL_KS_SEM",
    ``!M f. CTL_KS_SEM M f = FAIR_CTL_KS_SEM M (CTL_TO_FAIR_CTL [] f)``,

    SIMP_TAC std_ss [CTL_KS_SEM_def, FAIR_CTL_KS_SEM_def,
      CTL_SEM_def]);


val CTL_KS_FAIR_SEM___TO___FAIR_CTL_KS_SEM =
  store_thm ("CTL_KS_FAIR_SEM___TO___FAIR_CTL_KS_SEM",
    ``!M f fc. CTL_KS_FAIR_SEM M f fc = FAIR_CTL_KS_SEM M (CTL_TO_FAIR_CTL fc f)``,

    SIMP_TAC std_ss [CTL_KS_FAIR_SEM_def, FAIR_CTL_KS_SEM_def,
      CTL_FAIR_SEM_def]);


val CTL_USED_VARS_def =
 Define `
   (CTL_USED_VARS f = FAIR_CTL_USED_VARS (CTL_TO_FAIR_CTL [] f))`;



(*translation of the important FAIR_CTL definitions and lemmata*)
val CTL_FALSE_def = Define `CTL_FALSE = CTL_PROP P_FALSE`;
val CTL_TRUE_def = Define `CTL_TRUE = CTL_PROP P_TRUE`;
val CTL_OR_def = Define `CTL_OR(f1,f2) = CTL_NOT (CTL_AND((CTL_NOT f1),(CTL_NOT f2)))`;
val CTL_IMPL_def = Define `CTL_IMPL(f1, f2) = CTL_OR(CTL_NOT f1, f2)`;
val CTL_COND_def = Define `CTL_COND(c, f1, f2) = CTL_AND(CTL_IMPL(c, f1), CTL_IMPL(CTL_NOT c, f2))`;
val CTL_EQUIV_def = Define `CTL_EQUIV(b1, b2) = CTL_AND(CTL_IMPL(b1, b2),CTL_IMPL(b2, b1))`;
val CTL_A_NEXT_def = Define `CTL_A_NEXT f = CTL_NOT(CTL_E_NEXT (CTL_NOT f))`;
val CTL_E_EVENTUAL_def = Define `CTL_E_EVENTUAL f = CTL_E_SUNTIL (CTL_PROP(P_TRUE),f)`;
val CTL_E_ALWAYS_def = Define `CTL_E_ALWAYS f = CTL_E_UNTIL (f, CTL_PROP(P_FALSE))`;
val CTL_A_EVENTUAL_def = Define `CTL_A_EVENTUAL f = CTL_NOT (CTL_E_ALWAYS (CTL_NOT f))`;
val CTL_A_ALWAYS_def = Define `CTL_A_ALWAYS f = CTL_NOT (CTL_E_EVENTUAL (CTL_NOT f))`;
val CTL_A_UNTIL_def = Define `CTL_A_UNTIL(f1,f2) = CTL_NOT(CTL_E_SUNTIL(CTL_NOT f2, (CTL_AND(CTL_NOT f1, CTL_NOT f2))))`;
val CTL_A_SUNTIL_def = Define `CTL_A_SUNTIL(f1,f2) = CTL_NOT(CTL_E_UNTIL(CTL_NOT f2, (CTL_AND(CTL_NOT f1, CTL_NOT f2))))`;
val CTL_E_BEFORE_def = Define `CTL_E_BEFORE(f1,f2) = CTL_E_UNTIL(CTL_NOT f2, CTL_AND(f1, CTL_NOT f2))`;
val CTL_E_SBEFORE_def = Define `CTL_E_SBEFORE(f1,f2) = CTL_E_SUNTIL(CTL_NOT f2, CTL_AND(f1, CTL_NOT f2))`;
val CTL_A_BEFORE_def = Define `CTL_A_BEFORE(f1,f2) = CTL_NOT(CTL_E_SUNTIL(CTL_NOT f1, f2))`;
val CTL_A_SBEFORE_def = Define `CTL_A_SBEFORE(f1,f2) = CTL_NOT(CTL_E_UNTIL(CTL_NOT f1, f2))`;
val CTL_E_WHILE_def = Define `CTL_E_WHILE(f1,f2) = CTL_E_UNTIL(CTL_NOT f2, CTL_AND(f1, f2))`;
val CTL_E_SWHILE_def = Define `CTL_E_SWHILE(f1,f2) = CTL_E_SUNTIL(CTL_NOT f2, CTL_AND(f1, f2))`;
val CTL_A_WHILE_def = Define `CTL_A_WHILE(f1,f2) = CTL_NOT(CTL_E_SUNTIL(CTL_NOT f2, CTL_AND(CTL_NOT f1, f2)))`;
val CTL_A_SWHILE_def = Define `CTL_A_SWHILE(f1,f2) = CTL_NOT(CTL_E_UNTIL(CTL_NOT f2, CTL_AND(CTL_NOT f1, f2)))`;



val CTL_TO_FAIR_CTL_THM =
  store_thm ("CTL_TO_FAIR_CTL_THM",
    ``!b f f1 f2 c fc.
        (CTL_TO_FAIR_CTL fc (CTL_PROP b) = (FAIR_CTL_PROP b)) /\
        (CTL_TO_FAIR_CTL fc (CTL_NOT f) = (FAIR_CTL_NOT (CTL_TO_FAIR_CTL fc f))) /\
        (CTL_TO_FAIR_CTL fc (CTL_AND (f1, f2)) = (FAIR_CTL_AND (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_OR (f1, f2)) = (FAIR_CTL_OR (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_IMPL (f1, f2)) = (FAIR_CTL_IMPL (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_COND (c, f1, f2)) = (FAIR_CTL_COND (CTL_TO_FAIR_CTL fc c, CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_EQUIV (f1, f2)) = (FAIR_CTL_EQUIV (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_E_NEXT f) = (FAIR_CTL_E_NEXT fc (CTL_TO_FAIR_CTL fc f))) /\
        (CTL_TO_FAIR_CTL fc (CTL_A_NEXT f) = (FAIR_CTL_A_NEXT fc (CTL_TO_FAIR_CTL fc f))) /\
        (CTL_TO_FAIR_CTL fc (CTL_E_ALWAYS f) = (FAIR_CTL_E_ALWAYS fc (CTL_TO_FAIR_CTL fc f))) /\
        (CTL_TO_FAIR_CTL fc (CTL_A_ALWAYS f) = (FAIR_CTL_A_ALWAYS fc (CTL_TO_FAIR_CTL fc f))) /\
        (CTL_TO_FAIR_CTL fc (CTL_E_EVENTUAL f) = (FAIR_CTL_E_EVENTUAL fc (CTL_TO_FAIR_CTL fc f))) /\
        (CTL_TO_FAIR_CTL fc (CTL_A_EVENTUAL f) = (FAIR_CTL_A_EVENTUAL fc (CTL_TO_FAIR_CTL fc f))) /\
        (CTL_TO_FAIR_CTL fc (CTL_E_SUNTIL (f1, f2)) = (FAIR_CTL_E_SUNTIL fc (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_A_SUNTIL (f1, f2)) = (FAIR_CTL_A_SUNTIL fc (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_E_UNTIL (f1, f2)) = (FAIR_CTL_E_UNTIL fc (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_A_UNTIL (f1, f2)) = (FAIR_CTL_A_UNTIL fc (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_E_BEFORE (f1, f2)) = (FAIR_CTL_E_BEFORE fc (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_A_BEFORE (f1, f2)) = (FAIR_CTL_A_BEFORE fc (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_E_SBEFORE (f1, f2)) = (FAIR_CTL_E_SBEFORE fc (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_A_SBEFORE (f1, f2)) = (FAIR_CTL_A_SBEFORE fc (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_E_WHILE (f1, f2)) = (FAIR_CTL_E_WHILE fc (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_A_WHILE (f1, f2)) = (FAIR_CTL_A_WHILE fc (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_E_SWHILE (f1, f2)) = (FAIR_CTL_E_SWHILE fc (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2))) /\
        (CTL_TO_FAIR_CTL fc (CTL_A_SWHILE (f1, f2)) = (FAIR_CTL_A_SWHILE fc (CTL_TO_FAIR_CTL fc f1, CTL_TO_FAIR_CTL fc f2)))``,

    EVAL_TAC THEN PROVE_TAC[]);



val CTL_SEM_THM = store_thm ("CTL_SEM_THM",
    ``!M b f f1 f2 s.

   (CTL_SEM M CTL_TRUE s) /\ ~(CTL_SEM M CTL_FALSE s) /\

   (CTL_SEM M (CTL_PROP b) s = (P_SEM s b)) /\

   (CTL_SEM M (CTL_NOT f) s = ~(CTL_SEM M f s)) /\

   (CTL_SEM M (CTL_AND(f1,f2)) s = CTL_SEM M f1 s /\ CTL_SEM M f2 s) /\

   (CTL_SEM M (CTL_E_NEXT f) s = (?p. IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p /\
      (p 0 = s) /\ CTL_SEM M f (p 1))) /\

   (CTL_SEM M (CTL_E_SUNTIL(f1, f2)) s = (?p. IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p /\
      (p 0 = s) /\ (?k. CTL_SEM M f2 (p k) /\ (!j. j < k ==> CTL_SEM M f1 (p j))))) /\

   (CTL_SEM M (CTL_E_UNTIL(f1, f2)) s = (?p. IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p /\
      (p 0 = s) /\
      ((?k. CTL_SEM M f2 (p k) /\ (!j. j < k ==> CTL_SEM M f1 (p j))) \/
       (!j. CTL_SEM M f1 (p j))))) /\

   (CTL_SEM M (CTL_A_NEXT f) s = (!p. (IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p /\
                                    (p 0 = s)) ==> CTL_SEM M f (p 1))) /\

   (CTL_SEM M (CTL_E_EVENTUAL f) s = (?p. IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p /\
                                    (p 0 = s) /\ ?k. CTL_SEM M f (p k))) /\
   (CTL_SEM M (CTL_E_ALWAYS f) s = (?p. IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p /\
                                    (p 0 = s) /\ !k. CTL_SEM M f (p k))) /\

   (CTL_SEM M (CTL_A_EVENTUAL f) s = (!p. (IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p /\
                                    (p 0 = s)) ==> ?k. CTL_SEM M f (p k))) /\
   (CTL_SEM M (CTL_A_ALWAYS f) s = (!p. (IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p /\
                                    (p 0 = s)) ==> (!k. CTL_SEM M f (p k)))) /\

   (CTL_SEM M (CTL_A_SUNTIL(f1, f2)) s = (!p. (IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p /\
      (p 0 = s)) ==> (?k. CTL_SEM M f2 (p k) /\ (!j. j < k ==> CTL_SEM M f1 (p j))))) /\

   (CTL_SEM M (CTL_A_UNTIL(f1, f2)) s = (!p. (IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p /\
      (p 0 = s)) ==> ((?k. CTL_SEM M f2 (p k) /\ (!j. j < k ==> CTL_SEM M f1 (p j))) \/
                      (!j. CTL_SEM M f1 (p j)))))``,


   SIMP_TAC std_ss [CTL_SEM_def, CTL_TO_FAIR_CTL_THM, FAIR_CTL_SEM_THM,
    IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE___EMPTY_FAIRNESS,
    CTL_TRUE_def, CTL_FALSE_def, P_SEM_THM]);


val IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE___TO___CTL_KS_FAIR_SEM =
  store_thm ("IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE___TO___CTL_KS_FAIR_SEM",
    ``!M fc. IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE M fc =
             CTL_KS_FAIR_SEM M (CTL_A_EVENTUAL CTL_FALSE) fc``,

  SIMP_TAC std_ss [CTL_KS_FAIR_SEM_def, CTL_FAIR_SEM_def,
    CTL_TO_FAIR_CTL_THM, CTL_FALSE_def, FAIR_CTL_SEM_THM, P_SEM_THM,
    IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE_def,
    IS_FAIR_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def] THEN
  METIS_TAC[]);



val _ = export_theory();
