open HolKernel Parse boolLib bossLib stringLib pred_setLib pred_setTheory PairRules

val _ = new_theory "ks";

(* make the first argument to the KS type operator be the state one by
   using 'State and 'prop as the type arguments: the standard ASCII ordering
   puts uppercase letters before lowercase ones, so the 'State argument comes
   before the 'prop one. *)
val _ = Hol_datatype `KS = <|
                                S : 'state -> bool;
                                S0 : 'state -> bool;
                                T : string -> ('state # 'state) -> bool ; (* fn from R rel on S x S to bool *)
                                ap: 'prop -> bool;
                                L : 'state -> ('prop -> bool) (* returns only the true atoms *)
                        |>`;

(* environment : relvars -> 2^(ks.states) ; can be thought of as an assignment to the free vars of a formula*)

(* well formed ks. *)
val wfKS_def = Define `
  wfKS ks = (ks.S0 SUBSET ks.S) /\  (ks.S = UNIV)
`;

(* toy example of ks
val dks_def4 = Define `dks4 = <|
                     S := (UNIV:((bool # bool # bool # bool) -> bool));
                     S0:= {}; (* should be \(p1,p2,p3,p4). p1 \/ p2 \/ p3 \/ p4 but empty for the moment for convenience *)
                     T := \t. if t="t" then (\((p1,p2:bool,p3:bool,p4:bool),(p1',p2',p3',p4')).
                                                p1 \/ p1' /\ (p2=p2') /\ (p3=p3') /\ (p4=p4'))
                                       else (\((p1:bool,p2:bool,p3:bool,p4:bool),(p1':bool,p2':bool,p3':bool,p4':bool)).F);
                     ap := {"p1";"p2";"p3";"p4"};
                     L :=  \(p1,p2,p3,p4). {p|((p="p1")/\p1) \/ ((p="p2")/\p2) \/ ((p="p3") /\ p3) \/ ((p="p4") /\ p4)}  |>`;
*)

val KS_TRANSITION_def = Define`
  KS_TRANSITION (p:'state) ks a (q:'state) = (ks.T a)(p,q)
`;

val _ = add_rule {term_name = "KS_TRANSITION", fixity = Infixl 2502,
     pp_elements = [TOK ">--", TM, TOK "/",TM, TOK "-->"],
     paren_style = OnlyIfNecessary,
     block_style = (AroundSamePrec, (PP.INCONSISTENT, 0))};

val wfKS_UNIV = store_thm(
  "wfKS_UNIV",
  ``!ks. (ks.S0 SUBSET UNIV) /\ (ks.S = UNIV) ==> wfKS ks``,
  PROVE_TAC [wfKS_def])

val DECIDE_AP_EQ_LEM = save_thm("DECIDE_AP_EQ_LEM",prove (``!x y. ~(x=y) = (((\s. x) = (\s. y))=F)``,metisLib.METIS_TAC []))

val TOTAL_def = Define `TOTAL R = !s. ?s'. R(s,s')`;

(* show that the totalisation in ctlTools works *)
val TOTAL_THM = save_thm("TOTAL_THM",prove(``!R. TOTAL \(s,s').(R(s,s') \/ ((~?s'.R(s,s')) /\ (s'=s)))``,
REWRITE_TAC [TOTAL_def] THEN PBETA_TAC
THEN REPEAT GEN_TAC
THEN CONV_TAC (EXISTS_OR_CONV)
THEN CONV_TAC (RAND_CONV EXISTS_AND_CONV)
THEN Cases_on `(?s'. R (s,s'))` THENL [
DISJ1_TAC THEN ASM_REWRITE_TAC [],
DISJ2_TAC THEN ASM_REWRITE_TAC []
THEN Q.EXISTS_TAC `s` THEN REFL_TAC]))

val _ = export_theory();
