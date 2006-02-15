open HolKernel Parse boolLib bossLib

val _ = new_theory("muSyntax")


open bossLib
open pairTheory
open pairLib
open pairTools
open pairSyntax
open pred_setTheory
open pred_setLib
open listTheory
open stringTheory
open sumTheory
open simpLib
open stringLib
open numLib
open metisLib
open ksTheory
open setLemmasTheory
open reachTheory

infix && infix 8 by

fun tsimps ty = let val {convs,rewrs} = TypeBase.simpls_of ty in rewrs end


(* ======================propositional mu calculus: types,syntax,semantics etc =======================*)

(* note to self: using string rather than mu (in RV,<>,[]) because the terms denoted are not themselves mu-calc formulae *)
(*       even though this approach clutters up the syntax with double quotes, it is the right way to do things       *)
(*      however, using strings for bound vars of mu an nu is a hack because it is a pain getting general support for binders *)

val _ = bossLib.Hol_datatype `
	mu = TR
	| FL
	| Not of mu
	| And of mu => mu
	| Or of mu => mu
	| RV of string (* relational var *)
	| AP of 'prop (* atomic proposition *)
        | DIAMOND of string => mu (* diamond *)
        | BOX of string => mu (* box *)
        | mu of string => mu   (* lfp *)
        | nu of string => mu` (* mfp *)

val tsimps_mu = tsimps ``:'prop mu``;


val mu_size_def = snd (TypeBase.size_of ``:'prop mu``)
val mu_size2_def = Define `mu_size2 (f: 'prop mu) = mu_size (\(a:('prop)).0) f`

val _ = add_rule
    {term_name = "AP", fixity = TruePrefix 950, (* 950 is tighter than ~ *)
     pp_elements = [TOK "AP", HardSpace 1],
     paren_style = OnlyIfNecessary,
     block_style = (AroundSamePrec, (PP.INCONSISTENT, 0))}

(* overload ~,/\,\/,T and F give priority to the boolean versions *)

val _ = overload_on ("~", mk_const("~",``:bool -> bool``))
val _ = overload_on ("~", (``$Not``))
val _ = overload_on ("~", mk_const("~",``:bool -> bool``))
fun prepOverload s = overload_on (s, mk_const(s,``:bool -> bool -> bool``))
val _ = app prepOverload ["/\\", "\\/"]
val _ = overload_on ("/\\", (``$And``)) val _ = prepOverload "/\\"
val _ = overload_on ("\\/", (``$Or``)) val _ = prepOverload "\\/"
val _ = overload_on ("T",T) val _ = overload_on ("T",``TR``) val _ = overload_on ("T",T)
val _ = overload_on ("F",F) val _ = overload_on ("F",``FL``) val _ = overload_on ("F",F)

(* make syntax for DIAMOND, BOX, lfp and mfp (somewhat) resemble standard notation *)
(* Need to use << and >> because of precedence conflicts with < and > *)

(* prec 2501 is higher fixity than any thing in default term grammar WIP: does this make sense...not really, should be lower *)
val _ = add_rule {term_name = "DIAMOND", fixity = TruePrefix 2501,
     pp_elements = [TOK "<<", TM, TOK ">>", HardSpace 1],
     paren_style = OnlyIfNecessary,
     block_style = (AroundSamePrec, (PP.INCONSISTENT, 0))}
(* Could actually use [ and ] here by declaring CloseFix fixity. But this is for consistency with lfp *)
val _ = add_rule {term_name = "BOX", fixity = TruePrefix 2501,
     pp_elements = [TOK "[[", TM, TOK "]]",HardSpace 1],
     paren_style = OnlyIfNecessary,
     block_style = (AroundSamePrec, (PP.INCONSISTENT, 0))}
val _ = add_rule {term_name = "mu", fixity = TruePrefix 2,
     pp_elements = [TOK "mu",HardSpace 1, TM, TOK "..",HardSpace 1],
     paren_style = OnlyIfNecessary,
     block_style = (AroundSamePrec, (PP.INCONSISTENT, 0))}
val _ = add_rule {term_name = "nu", fixity = TruePrefix 2,
     pp_elements = [TOK "nu", HardSpace 1, TM, TOK "..",HardSpace 1],
     paren_style = OnlyIfNecessary,
     block_style = (AroundSamePrec, (PP.INCONSISTENT, 0))}

(* defns for checking well-formedness of a mu-formula (bound vars must occur +vely within its scope) *)

(* RVNEG(f,Q) == in f, all free ocurrances of Q are negated *)
val RVNEG_def = save_thm("RVNEG_def",Define`
(RVNEG rv (T:'prop mu) = (T:'prop mu)) /\
(RVNEG rv F = F) /\
(RVNEG rv (f /\ g) = (RVNEG rv f) /\ (RVNEG rv g)) /\
(RVNEG rv (f \/ g) = (RVNEG rv f) \/ (RVNEG rv g)) /\
(RVNEG rv (AP p) = AP p) /\
(RVNEG rv (RV Q) = if (rv=Q) then (~(RV Q)) else (RV Q)) /\
(RVNEG rv (<<a>> f) = <<a>> (RVNEG rv f)) /\
(RVNEG rv ([[a]] f) = [[a]] (RVNEG rv f)) /\
(RVNEG rv (mu Q .. f) = if (rv=Q) then (mu Q .. f) else (mu Q .. (RVNEG rv f))) /\
(RVNEG rv (nu Q .. f) = if (rv=Q) then (nu Q .. f) else (nu Q .. (RVNEG rv f))) /\
(RVNEG rv (~f) = ~(RVNEG rv f))`)

val mu_pnf = Hol_defn "NNF"  `
(NNF (T:'prop mu) = (T:'prop mu)) /\
(NNF F = F) /\
(NNF (f /\ g) = NNF f /\ NNF g) /\
(NNF (f \/ g) = NNF f \/ NNF g) /\
(NNF (AP p) = AP p) /\
(NNF (RV Q) = RV Q) /\
(NNF (<<a>> f) = <<a>> (NNF f)) /\
(NNF ([[a]] f) = [[a]] (NNF f)) /\
(NNF (mu Q .. f) = mu Q .. (NNF f)) /\
(NNF (nu Q .. f) = nu Q .. (NNF f)) /\
(NNF (~T) = F) /\
(NNF (~F) = T) /\
(NNF (~(f /\ g)) = ((NNF ~f)) \/ ((NNF ~g))) /\
(NNF (~(f \/ g)) = ((NNF ~f)) /\ ((NNF ~g))) /\
(NNF (~(AP p)) = ~(AP p)) /\
(NNF (~(RV Q)) = ~(RV Q)) /\
(NNF (~(<<a>> f)) = [[a]] (NNF ~f)) /\
(NNF (~([[a]] f)) = <<a>> (NNF ~f)) /\
(NNF (~~f) = NNF f) /\
(NNF (~(mu Q.. f)) = nu Q.. (NNF(RVNEG Q (~f)))) /\
(NNF (~(nu Q.. f)) = mu Q.. (NNF(RVNEG Q (~f))))`

val mu_pstv_size_def = Define`
(mu_pstv_size (T:'prop mu) = mu_size2 (T: 'prop mu)) /\
(mu_pstv_size (F:'prop mu) = mu_size2 (F: 'prop mu)) /\
(mu_pstv_size (f /\ g) = 1+ (mu_pstv_size f + mu_pstv_size g)) /\
(mu_pstv_size (f \/ g) = 1+ (mu_pstv_size f + mu_pstv_size g)) /\
(mu_pstv_size ((AP (p:'prop)):'prop mu) = mu_size2 ((AP (p:'prop)):'prop mu)) /\
(mu_pstv_size ((RV (Q:string)):'prop mu) = mu_size2 ((RV (Q:string)):'prop mu)) /\
(mu_pstv_size (<<(a:string)>> f) = 1 + (mu_pstv_size f)) /\
(mu_pstv_size ([[(a:string)]] f) = 1+ (mu_pstv_size f)) /\
(mu_pstv_size (mu (Q:string) .. f) = 1+ (STRLEN Q + mu_pstv_size f)) /\
(mu_pstv_size (nu (Q:string) .. f) = 1+ (STRLEN Q + mu_pstv_size f)) /\
(mu_pstv_size (~f) = mu_pstv_size f)`

val mu_pstv_size_lemma1 = prove(``!f Q. mu_pstv_size (RVNEG Q f) = mu_pstv_size f``,
  Induct_on `f` THEN RW_TAC std_ss [mu_pstv_size_def,RVNEG_def] THEN RW_TAC arith_ss [mu_pstv_size_def,RVNEG_def])

val mu_pstv_size_lemma2 = prove(``!f Q. mu_pstv_size (RVNEG Q (~f)) = mu_pstv_size f``,
  Induct_on `f` THEN RW_TAC std_ss [mu_pstv_size_def,RVNEG_def]
                   THEN RW_TAC arith_ss [mu_pstv_size_def,RVNEG_def,mu_pstv_size_lemma1])

val (NNF_def,NNF_IND_def) = Defn.tprove(mu_pnf,WF_REL_TAC `inv_image ($< LEX $<) (\f. (mu_pstv_size f,mu_size2 f))` THEN RW_TAC std_ss [mu_size_def,mu_size2_def,mu_pstv_size_def] THEN RW_TAC arith_ss [mu_pstv_size_lemma2])
val _ = save_thm("NNF_def",NNF_def)
val _ = save_thm("NNF_IND_def",NNF_IND_def)

val MU_SUB_def = save_thm("MU_SUB_def",Define `
(SUBFORMULA (g:'prop mu) (T:'prop mu) = (g = T)) /\
(SUBFORMULA g F = (g = F)) /\
(SUBFORMULA g (~f) = (SUBFORMULA g f) \/ (g=~f)) /\
(SUBFORMULA g (f1 /\ f2) = (SUBFORMULA g f1) \/ (SUBFORMULA g f2) \/ (g = f1 /\ f2)) /\
(SUBFORMULA g (f1 \/ f2) = (SUBFORMULA g f1) \/ (SUBFORMULA g f2) \/ (g = f1 \/ f2)) /\
(SUBFORMULA g (RV Q) = (g = RV Q)) /\
(SUBFORMULA g (AP p) = (g = AP p)) /\
(SUBFORMULA g (<<a>> f) = (SUBFORMULA g f) \/ (g = <<a>> f)) /\
(SUBFORMULA g ([[a]] f) = (SUBFORMULA g f) \/ (g = [[a]] f)) /\
(SUBFORMULA g (mu Q.. f) = (SUBFORMULA g f) \/ (g = mu Q.. f)) /\
(SUBFORMULA g (nu Q.. f) = (SUBFORMULA g f) \/ (g = nu Q.. f))`)

val _ = add_rule {term_name = "SUBFORMULA", fixity = Infix (HOLgrammars.RIGHT,450),
     pp_elements = [HardSpace 1,TOK "SUBF",HardSpace 1],
     paren_style = OnlyIfNecessary,
     block_style = (AroundSamePrec, (PP.INCONSISTENT, 0))}

val IMF_def = save_thm("IMF_def",Define `
(IMF (T:'prop mu) = T) /\
(IMF F = T) /\
(IMF (~f) = IMF f) /\
(IMF (f1 /\ f2) = (IMF f1) /\ (IMF f2)) /\
(IMF (f1 \/ f2) = (IMF f1) /\ (IMF f2)) /\
(IMF (RV Q) = T) /\
(IMF (AP p) = T) /\
(IMF (<<a>> f) = IMF f) /\
(IMF ([[a]] f) = IMF f) /\
(IMF (mu Q.. f) = ~(SUBFORMULA (~RV Q) (NNF f)) /\ (IMF f))  /\
(IMF (nu Q.. f) = ~(SUBFORMULA (~RV Q) (NNF f)) /\ (IMF f))`)

val FV_def = save_thm("FV_def",Define `
(FV (T:'prop mu) = {}) /\
(FV F = {}) /\
(FV (~f) = FV f) /\
(FV (f1 /\ f2) = (FV f1) UNION (FV f2)) /\
(FV (f1 \/ f2) = (FV f1) UNION (FV f2)) /\
(FV (RV Q) = {Q}) /\
(FV (AP p) = {}) /\
(FV (<<a>> f) = FV f) /\
(FV ([[a]] f) = FV f) /\
(FV (mu Q.. f) =  (FV f) DELETE Q)  /\
(FV (nu Q.. f) =  (FV f) DELETE Q)`)

val ALLV_def = save_thm("ALLV_def",Define `
(ALLV (T:'prop mu) = {}) /\
(ALLV F = {}) /\
(ALLV (~f) = ALLV f) /\
(ALLV (f1 /\ f2) = (ALLV f1) UNION (ALLV f2)) /\
(ALLV (f1 \/ f2) = (ALLV f1) UNION (ALLV f2)) /\
(ALLV (RV Q) = {Q}) /\
(ALLV (AP p) = {}) /\
(ALLV (<<a>> f) = ALLV f) /\
(ALLV ([[a]] f) = ALLV f) /\
(ALLV (mu Q.. f) =  (ALLV f))  /\
(ALLV (nu Q.. f) =  (ALLV f))`)

val CLOSED_def = save_thm("CLOSED_def",Define `CLOSED (f:'prop mu) = (FV f = {})`)

val IS_PROP_def = Define `
(IS_PROP (T:'prop mu) = T) /\
(IS_PROP F = T) /\
(IS_PROP (~f) = IS_PROP f) /\
(IS_PROP (f1 /\ f2) = (IS_PROP f1) /\ (IS_PROP f2)) /\
(IS_PROP (f1 \/ f2) = (IS_PROP f1) /\ (IS_PROP f2)) /\
(IS_PROP (RV Q) = F) /\
(IS_PROP (AP p) = T) /\
(IS_PROP (<<a>> f) = F) /\
(IS_PROP ([[a]] f) = F) /\
(IS_PROP (mu Q.. f) =  F)  /\
(IS_PROP (nu Q.. f) =  F)`

val AP_SUBST_def = Define `
(AP_SUBST g ap (T:'prop mu) = (T:'prop mu)) /\
(AP_SUBST g ap F = F) /\
(AP_SUBST g ap (~f) = ~(AP_SUBST g ap f)) /\
(AP_SUBST g ap (f1 /\ f2) = (AP_SUBST g ap f1) /\ (AP_SUBST g ap f2)) /\
(AP_SUBST g ap (f1 \/ f2) = (AP_SUBST g ap f1) \/ (AP_SUBST g ap f2)) /\
(AP_SUBST g ap (RV Q) = (RV Q)) /\
(AP_SUBST g ap (AP p) = if (p=ap) then g else AP p) /\
(AP_SUBST g ap (<<a>> f) = <<a>> (AP_SUBST g ap f)) /\
(AP_SUBST g ap ([[a]] f) = [[a]] (AP_SUBST g ap f)) /\
(AP_SUBST g ap (mu Q.. f) = (mu Q.. (AP_SUBST g ap f)))  /\
(AP_SUBST g ap (nu Q.. f) =  (nu Q.. (AP_SUBST g ap f)))`

val RVNEG_SYM = save_thm("RVNEG_SYM",prove(``!Q Q' (f:'prop mu). RVNEG Q (RVNEG Q' f) = RVNEG Q' (RVNEG Q f)``,
REPEAT GEN_TAC
THEN Induct_on `f` THEN SIMP_TAC std_ss (RVNEG_def::tsimps ``:'prop mu``) THEN
FULL_SIMP_TAC std_ss [] THENL [
ASSUM_LIST PROVE_TAC,
ASSUM_LIST PROVE_TAC,
REPEAT GEN_TAC
THEN Cases_on `Q=Q'` THEN REPEAT (Cases_on `Q'=s` THEN REPEAT (Cases_on `Q=s` THEN FULL_SIMP_TAC std_ss [RVNEG_def])),(*RV*)
GEN_TAC
THEN Cases_on `Q=Q'` THENL [
  Cases_on `Q'=s` THEN REPEAT (Cases_on `Q=s` THEN
				    (FULL_SIMP_TAC std_ss [RVNEG_def] ORELSE ASSUM_LIST PROVE_TAC)),
  Cases_on `Q'=s` THENL [
   Cases_on `Q=s` THENL [
    FULL_SIMP_TAC std_ss [RVNEG_def],
    FULL_SIMP_TAC std_ss [RVNEG_def]],
   Cases_on `Q=s` THENL [
    FULL_SIMP_TAC std_ss [RVNEG_def],
    FULL_SIMP_TAC std_ss [RVNEG_def]
    THEN ASSUM_LIST PROVE_TAC]]], (* mu *)
GEN_TAC
THEN Cases_on `Q=Q'` THENL [
  Cases_on `Q'=s` THEN REPEAT (Cases_on `Q=s` THEN
				    (FULL_SIMP_TAC std_ss [RVNEG_def] ORELSE ASSUM_LIST PROVE_TAC)),
  Cases_on `Q'=s` THENL [
   Cases_on `Q=s` THENL [
    FULL_SIMP_TAC std_ss [RVNEG_def],
    FULL_SIMP_TAC std_ss [RVNEG_def]],
   Cases_on `Q=s` THENL [
    FULL_SIMP_TAC std_ss [RVNEG_def],
    FULL_SIMP_TAC std_ss [RVNEG_def]
    THEN ASSUM_LIST PROVE_TAC]]]])) (* nu *)

val IMF_NEG_NEG_LEM1 = save_thm("IMF_NEG_NEG_LEM1",prove(``!(f:'prop mu) Q Q'. ~(Q'=Q) ==> (~SUBFORMULA (~RV Q) (NNF (RVNEG Q' f)) = ~SUBFORMULA (~RV Q) (NNF f))``,
recInduct NNF_IND_def THEN REPEAT CONJ_TAC THEN BETA_TAC THEN SIMP_TAC std_ss ([NNF_def,RVNEG_def,IMF_def,MU_SUB_def]@tsimps_mu) THENL [
REPEAT GEN_TAC THEN DISCH_TAC
THEN FULL_SIMP_TAC std_ss ([NNF_def,RVNEG_def,IMF_def,MU_SUB_def]@tsimps_mu)
THEN Cases_on `Q''=Q` THENL [
FULL_SIMP_TAC std_ss ([NNF_def,RVNEG_def,IMF_def,MU_SUB_def]@tsimps_mu),
FULL_SIMP_TAC std_ss ([NNF_def,RVNEG_def,IMF_def,MU_SUB_def]@tsimps_mu)],
REPEAT STRIP_TAC THEN Cases_on `Q''=Q` THENL [
FULL_SIMP_TAC std_ss ([NNF_def,RVNEG_def,IMF_def,MU_SUB_def]@tsimps_mu),
FULL_SIMP_TAC std_ss ([NNF_def,RVNEG_def,IMF_def,MU_SUB_def]@tsimps_mu)],
REPEAT STRIP_TAC THEN Cases_on `Q''=Q` THENL [
FULL_SIMP_TAC std_ss ([NNF_def,RVNEG_def,IMF_def,MU_SUB_def]@tsimps_mu),
FULL_SIMP_TAC std_ss ([NNF_def,RVNEG_def,IMF_def,MU_SUB_def]@tsimps_mu)],
REPEAT GEN_TAC THEN DISCH_TAC
THEN FULL_SIMP_TAC std_ss ([NNF_def,RVNEG_def,IMF_def,MU_SUB_def]@tsimps_mu)
THEN Cases_on `Q''=Q` THENL [
FULL_SIMP_TAC std_ss ([NNF_def,RVNEG_def,IMF_def,MU_SUB_def]@tsimps_mu),
FULL_SIMP_TAC std_ss ([NNF_def,RVNEG_def,IMF_def,MU_SUB_def]@tsimps_mu)],
REPEAT STRIP_TAC THEN Cases_on `Q''=Q` THENL [
FULL_SIMP_TAC std_ss ([NNF_def,RVNEG_def,IMF_def,MU_SUB_def]@tsimps_mu),
FULL_SIMP_TAC std_ss ([NNF_def,RVNEG_def,IMF_def,MU_SUB_def]@tsimps_mu)
THEN FULL_SIMP_TAC std_ss [RVNEG_SYM]], (* mu *)
REPEAT STRIP_TAC THEN Cases_on `Q''=Q` THENL [
FULL_SIMP_TAC std_ss ([NNF_def,RVNEG_def,IMF_def,MU_SUB_def]@tsimps_mu),
FULL_SIMP_TAC std_ss ([NNF_def,RVNEG_def,IMF_def,MU_SUB_def]@tsimps_mu)
THEN FULL_SIMP_TAC std_ss [RVNEG_SYM]]])) (* nu *)

val IMF_INV_RVNEG = save_thm("IMF_INV_RVNEG",prove(``!(f: 'prop mu) Q. IMF (RVNEG Q f) = IMF f``,
Induct_on `f` THEN FULL_SIMP_TAC std_ss ([IMF_def,MU_SUB_def,RVNEG_def]@tsimps_mu) THENL [
REPEAT GEN_TAC THEN Cases_on `Q=s` THENL [
 FULL_SIMP_TAC std_ss ([IMF_def]),
 FULL_SIMP_TAC std_ss ([IMF_def])], (* RV *)
REPEAT STRIP_TAC THEN Cases_on `Q=s` THENL [
 FULL_SIMP_TAC std_ss ([IMF_def,MU_SUB_def]),
 FULL_SIMP_TAC std_ss ([IMF_def,MU_SUB_def])
 THEN FULL_SIMP_TAC std_ss [IMF_NEG_NEG_LEM1]], (* mu *)
REPEAT STRIP_TAC THEN Cases_on `Q=s` THENL [
 FULL_SIMP_TAC std_ss ([IMF_def,MU_SUB_def]),
 FULL_SIMP_TAC std_ss ([IMF_def,MU_SUB_def])
 THEN FULL_SIMP_TAC std_ss [IMF_NEG_NEG_LEM1]]])) (* nu *)

val IMF_INV_NEG_RVNEG = save_thm("IMF_INV_NEG_RVNEG",prove (``!f Q. IMF (f:'prop mu) = IMF (RVNEG Q ~f)``,
SIMP_TAC std_ss [RVNEG_def,GSYM IMF_INV_RVNEG,IMF_def]))

val STATES_MONO_NEG_MU_LEM1 =  save_thm("STATES_MONO_NEG_MU_LEM1",prove(``!Q' Q (f:'prop mu) . SUBFORMULA (~RV Q') (NNF ~mu Q.. f) = SUBFORMULA (~RV Q') (NNF (RVNEG Q ~f))``,SIMP_TAC std_ss ([NNF_def,MU_SUB_def]@tsimps_mu)))

val STATES_MONO_LEM2 = save_thm("STATES_MONO_LEM2",prove (``!(f:'prop mu) Q Q'. ~(Q'=Q) ==> (SUBFORMULA (~RV Q') (NNF f) = SUBFORMULA (~RV Q') (NNF (RVNEG Q f)))``,
recInduct NNF_IND_def THEN REPEAT CONJ_TAC THEN BETA_TAC THEN (SIMP_TAC std_ss ([NNF_def,MU_SUB_def,RVNEG_def]@tsimps_mu)) THENL [
PROVE_TAC [], (* /\ *)
PROVE_TAC [], (* \/ *)
REPEAT GEN_TAC THEN DISCH_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@tsimps_mu),
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@tsimps_mu)], (* RV *)
REPEAT STRIP_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@tsimps_mu),
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@tsimps_mu)], (* mu *)
REPEAT STRIP_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@tsimps_mu),
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@tsimps_mu)], (* nu *)
PROVE_TAC [], (* ~/\ *)
PROVE_TAC [], (* ~\/ *)
REPEAT GEN_TAC THEN DISCH_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@tsimps_mu),
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@tsimps_mu)], (* ~RV *)
REPEAT STRIP_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@tsimps_mu),
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@tsimps_mu)
 THEN FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def,RVNEG_SYM]@tsimps_mu)], (* ~ mu *)
REPEAT STRIP_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@tsimps_mu),
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@tsimps_mu)
 THEN FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def,RVNEG_SYM]@tsimps_mu)]])) (* ~ nu *)

val NNF_RVNEG_DUALITY = save_thm("NNF_RVNEG_DUALITY",prove(``!(f:'prop mu) Q. NNF (RVNEG Q (RVNEG Q f)) = NNF f``,
recInduct NNF_IND_def THEN REPEAT CONJ_TAC THEN BETA_TAC THEN FULL_SIMP_TAC std_ss (NNF_def::MU_SUB_def::RVNEG_def::tsimps_mu) THENL [
REPEAT GEN_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss (RVNEG_def::NNF_def::tsimps_mu),
 FULL_SIMP_TAC std_ss (RVNEG_def::NNF_def::tsimps_mu)], (* RV *)
REPEAT STRIP_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss (RVNEG_def::NNF_def::tsimps_mu),
 FULL_SIMP_TAC std_ss (RVNEG_def::NNF_def::tsimps_mu)], (* mu *)
REPEAT STRIP_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss (RVNEG_def::NNF_def::tsimps_mu),
 FULL_SIMP_TAC std_ss (RVNEG_def::NNF_def::tsimps_mu)], (* nu *)
REPEAT GEN_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss (RVNEG_def::NNF_def::tsimps_mu),
 FULL_SIMP_TAC std_ss (RVNEG_def::NNF_def::tsimps_mu)], (* ~RV *)
REPEAT STRIP_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss (RVNEG_def::NNF_def::tsimps_mu),
 FULL_SIMP_TAC std_ss (RVNEG_SYM::RVNEG_def::NNF_def::tsimps_mu)], (* ~mu *)
REPEAT STRIP_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss (RVNEG_def::NNF_def::tsimps_mu),
 FULL_SIMP_TAC std_ss (RVNEG_SYM::RVNEG_def::NNF_def::tsimps_mu)]])) (* ~nu *)

val IMF_MU_IFF_IMF_NU=save_thm("IMF_MU_IFF_IMF_NU",prove(``!(f:'prop mu) Q. IMF (mu Q..f) = IMF (nu Q..f)``,SIMP_TAC std_ss [IMF_def]))

val ALLV_RVNEG = prove(``!f Q. ALLV f = ALLV (RVNEG Q f)``,
Induct_on `f` THEN FULL_SIMP_TAC std_ss ([UNION_DEF,SET_SPEC,RVNEG_def,ALLV_def]@tsimps_mu) THENL [
 ONCE_REWRITE_TAC [EXTENSION]
 THEN FULL_SIMP_TAC std_ss [SET_SPEC]
 THEN METIS_TAC [],
 ONCE_REWRITE_TAC [EXTENSION]
 THEN FULL_SIMP_TAC std_ss [SET_SPEC]
 THEN METIS_TAC [],
 REPEAT GEN_TAC THEN Cases_on `Q=s` THEN FULL_SIMP_TAC std_ss [ALLV_def],
 REPEAT GEN_TAC THEN Cases_on `Q=s` THEN FULL_SIMP_TAC std_ss [ALLV_def],
 REPEAT GEN_TAC THEN Cases_on `Q=s` THEN FULL_SIMP_TAC std_ss [ALLV_def]
])

val ALLV_NNF = prove(``!f. ALLV f = ALLV (NNF f)``,
recInduct NNF_IND_def THEN REPEAT CONJ_TAC THEN BETA_TAC
THEN FULL_SIMP_TAC std_ss ([GSYM ALLV_RVNEG,NNF_def,RVNEG_def,NOT_IN_EMPTY,MU_SUB_def,ALLV_def]@tsimps_mu))

val ALLV_SUBF = prove(``!f Q. (RV Q) SUBF f = Q IN ALLV f``,
Induct_on `f` THEN FULL_SIMP_TAC std_ss ([IN_SING,UNION_DEF,SET_SPEC,NOT_IN_EMPTY,MU_SUB_def,ALLV_def]@tsimps_mu))

val ALLV_FINITE = prove(``!f. FINITE (ALLV f)``,
Induct_on `f` THEN FULL_SIMP_TAC std_ss [FINITE_EMPTY,FINITE_UNION,ALLV_def,FINITE_SING])

val CLOSED_NEG = save_thm("CLOSED_NEG",prove(``!f. CLOSED (~f) = CLOSED f``,Induct_on `f` THEN FULL_SIMP_TAC std_ss ([CLOSED_def,FV_def]@tsimps_mu)))

val CLOSED_AND = save_thm("CLOSED_AND",prove(``!f g. CLOSED (f /\ g) = CLOSED f /\ CLOSED g``,Induct_on `f` THEN FULL_SIMP_TAC std_ss ([CLOSED_def,FV_def,UNION_EMPTY,EMPTY_UNION]@tsimps_mu)))

val CLOSED_OR = save_thm("CLOSED_OR",prove(``!f g. CLOSED (f \/ g) = CLOSED f /\ CLOSED g``,Induct_on `f` THEN FULL_SIMP_TAC std_ss ([CLOSED_def,FV_def,UNION_EMPTY,EMPTY_UNION]@tsimps_mu)))

val CLOSED_AP = save_thm("CLOSED_AP",prove(``!p. CLOSED (AP p)``,FULL_SIMP_TAC std_ss ([CLOSED_def,FV_def,UNION_EMPTY,EMPTY_UNION]@tsimps_mu)))

val CLOSED_BOX = save_thm("CLOSED_BOX",prove(``!f a. CLOSED ([[a]] f) = CLOSED f``,Induct_on `f` THEN FULL_SIMP_TAC std_ss ([CLOSED_def,FV_def,UNION_EMPTY,EMPTY_UNION]@tsimps_mu)))

val CLOSED_DMD = save_thm("CLOSED_DMD",prove(``!f a. CLOSED (<<a>> f) = CLOSED f``,Induct_on `f` THEN FULL_SIMP_TAC std_ss ([CLOSED_def,FV_def,UNION_EMPTY,EMPTY_UNION]@tsimps_mu)))

(* thms about subformulas *)

val SUBF_REFL = save_thm("SUBF_REFL",prove(``!f. f SUBF f``,Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUBF_NEG = prove(``!f g. ~(g SUBF f) ==> ~(~g SUBF f)``,
Induct_on `f` THEN Induct_on `g` THEN FULL_SIMP_TAC std_ss ([MU_SUB_def]@tsimps_mu)
THEN TRY (METIS_TAC (MU_SUB_def::tsimps_mu)))

val SUBF_NEG2 = prove(``!f g. (~g SUBF f) ==> (g SUBF f)``, PROVE_TAC [SUBF_NEG])

val SUBF_CONJ =  save_thm("SUBF_CONJ",prove(``!f g h. (f /\ g) SUBF h ==> f SUBF h /\ g SUBF h``,
Induct_on `h` THEN REPEAT CONJ_TAC THEN FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def]@tsimps_mu)
THEN REPEAT STRIP_TAC THEN (FIRST_PROVE [DISJ1_TAC THEN RES_TAC,DISJ2_TAC THEN RES_TAC, DISJ2_TAC THEN DISJ1_TAC THEN RES_TAC] ORELSE ASM_REWRITE_TAC [SUBF_REFL])))

val SUBF_DISJ =  save_thm("SUBF_DISJ",prove(``!f g h. (f \/ g) SUBF h ==> f SUBF h /\ g SUBF h``,
Induct_on `h` THEN REPEAT CONJ_TAC THEN FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def]@tsimps_mu)
THEN REPEAT STRIP_TAC THEN (FIRST_PROVE [DISJ1_TAC THEN RES_TAC,DISJ2_TAC THEN RES_TAC, DISJ2_TAC THEN DISJ1_TAC THEN RES_TAC] ORELSE ASM_REWRITE_TAC [SUBF_REFL])))

val SUBF_DMD = save_thm("SUBF_DMD",prove(``!a f h. <<a>> f SUBF h ==> f SUBF h``,
Induct_on `h` THEN REPEAT CONJ_TAC THEN FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def]@tsimps_mu)
THEN REPEAT STRIP_TAC THEN (FIRST_PROVE [DISJ1_TAC THEN RES_TAC,DISJ2_TAC THEN RES_TAC, DISJ2_TAC THEN DISJ1_TAC THEN RES_TAC] ORELSE ASM_REWRITE_TAC [SUBF_REFL])))

val SUBF_BOX = save_thm("SUBF_BOX",prove(``!a f h. [[a]] f SUBF h ==> f SUBF h``,
Induct_on `h` THEN REPEAT CONJ_TAC THEN FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def]@tsimps_mu)
THEN REPEAT STRIP_TAC THEN (FIRST_PROVE [DISJ1_TAC THEN RES_TAC,DISJ2_TAC THEN RES_TAC, DISJ2_TAC THEN DISJ1_TAC THEN RES_TAC] ORELSE ASM_REWRITE_TAC [SUBF_REFL])))

val SUBF_MU = save_thm("SUBF_MU",prove(``!Q f h. (mu Q .. f) SUBF h ==> f SUBF h``,
Induct_on `h` THEN REPEAT CONJ_TAC THEN FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def]@tsimps_mu)
THEN REPEAT STRIP_TAC THEN (FIRST_PROVE [DISJ1_TAC THEN RES_TAC,DISJ2_TAC THEN RES_TAC, DISJ2_TAC THEN DISJ1_TAC THEN RES_TAC] ORELSE ASM_REWRITE_TAC [SUBF_REFL])))

val SUBF_NU = save_thm("SUBF_NU",prove(``!Q f h. (nu Q .. f) SUBF h ==> f SUBF h``,
Induct_on `h` THEN REPEAT CONJ_TAC THEN FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def]@tsimps_mu)
THEN REPEAT STRIP_TAC THEN (FIRST_PROVE [DISJ1_TAC THEN RES_TAC,DISJ2_TAC THEN RES_TAC, DISJ2_TAC THEN DISJ1_TAC THEN RES_TAC] ORELSE ASM_REWRITE_TAC [SUBF_REFL])))

val SUB_RV_BOX  = save_thm("SUB_RV_BOX",prove(``!f a Q. ~SUBFORMULA (~RV Q) ([[a]] f) = ~SUBFORMULA (~RV Q) f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)));

val SUB_RV_MU  = save_thm("SUB_RV_MU",prove(``!f Q Q'. ~SUBFORMULA (~RV Q') (mu Q .. f) = ~SUBFORMULA (~RV Q') f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)));

val SUB_RV_NU  = save_thm("SUB_RV_NU",prove(``!f Q Q'. ~SUBFORMULA (~RV Q') (nu Q .. f) = ~SUBFORMULA (~RV Q') f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)));

val SUB_AP_RVNEG = save_thm("SUB_AP_RVNEG",prove(``!f p Q . SUBFORMULA (AP p) f = SUBFORMULA (AP p) (RVNEG Q ~f)``,
Induct_on `f` THEN FULL_SIMP_TAC std_ss (RVNEG_def::MU_SUB_def::tsimps_mu)
THEN REPEAT GEN_TAC THEN (TRY EQ_TAC) THEN RW_TAC std_ss []
THEN FULL_SIMP_TAC std_ss (RVNEG_def::MU_SUB_def::tsimps_mu) THEN ASSUM_LIST PROVE_TAC));

val SUB_AP_NEG_MU = save_thm("SUB_AP_NEG_MU",prove(``!f p Q . SUBFORMULA (AP p) ~(mu Q.. f) = SUBFORMULA (AP p) (RVNEG Q ~f)``,
Induct_on `f` THEN FULL_SIMP_TAC std_ss ([SUB_AP_RVNEG,NNF_def,RVNEG_def,MU_SUB_def]@tsimps_mu)
THEN REPEAT GEN_TAC THEN (TRY EQ_TAC) THEN RW_TAC std_ss []
THEN FULL_SIMP_TAC std_ss (RVNEG_def::MU_SUB_def::tsimps_mu) THEN ASSUM_LIST PROVE_TAC
));

val SUB_AP_NEG_NU = save_thm("SUB_AP_NEG_NU",prove(``!f p Q . SUBFORMULA (AP p) ~(nu Q.. f) = SUBFORMULA (AP p) (RVNEG Q ~f)``,
Induct_on `f` THEN FULL_SIMP_TAC std_ss ([SUB_AP_RVNEG,NNF_def,RVNEG_def,MU_SUB_def]@tsimps_mu)
THEN REPEAT GEN_TAC THEN (TRY EQ_TAC) THEN RW_TAC std_ss []
THEN FULL_SIMP_TAC std_ss (RVNEG_def::MU_SUB_def::tsimps_mu) THEN ASSUM_LIST PROVE_TAC
));

val SUB_AP_NEG  = save_thm("SUB_AP_NEG",prove(``!f p. SUBFORMULA (AP p) (~f) = SUBFORMULA (AP p) f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_AP_CONJ  = save_thm("SUB_AP_CONJ",prove(``!f g p. SUBFORMULA (AP p) (f /\ g) = SUBFORMULA (AP p) f \/ SUBFORMULA (AP p) g``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_AP_DISJ  = save_thm("SUB_AP_DISJ",prove(``!f g p. SUBFORMULA (AP p) (f \/ g) = SUBFORMULA (AP p) f \/ SUBFORMULA (AP p) g``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_AP_BOX = save_thm("SUB_AP_BOX",prove(``!f p a. SUBFORMULA (AP p) ([[a]]f) = SUBFORMULA (AP p) f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_AP_DMD = save_thm("SUB_AP_DMD",prove(``!f p a. SUBFORMULA (AP p) (<<a>>f) = SUBFORMULA (AP p) f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_AP_MU = save_thm("SUB_AP_MU",prove(``!f p Q. SUBFORMULA (AP p) (mu Q .. f) = SUBFORMULA (AP p) f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_AP_NU = save_thm("SUB_AP_NU",prove(``!f p Q. SUBFORMULA (AP p) (nu Q .. f) = SUBFORMULA (AP p) f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val NNF_NEG = save_thm("NNF_NEG",prove (``!f. IMF f ==> !g. SUBFORMULA (~g) (NNF f) ==> (?p. (g = AP p) \/ ?Q. (g = RV Q))``,
recInduct NNF_IND_def THEN REPEAT CONJ_TAC THEN BETA_TAC
THEN REPEAT (RW_TAC std_ss ([IMF_def,MU_SUB_def,NNF_def,RVNEG_def,IMF_INV_RVNEG]@tsimps_mu))))

val SUB_DMD_NEG  = save_thm("SUB_DMD_NEG",prove(``!f g a. ~SUBFORMULA (<<a>> g) (~f) = ~SUBFORMULA (<<a>> g) f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_DMD_CONJ  = save_thm("SUB_DMD_CONJ",prove(``!f f1 g a. ~SUBFORMULA (<<a>> g) (f /\ f1) = (~SUBFORMULA (<<a>> g) f) /\ (~SUBFORMULA (<<a>> g) f1)``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_DMD_DISJ  = save_thm("SUB_DMD_DISJ",prove(``!f f1 g a. ~SUBFORMULA (<<a>> g) (f \/ f1) = (~SUBFORMULA (<<a>> g) f) /\ (~SUBFORMULA (<<a>> g) f1)``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_DMD_DMD = save_thm("SUB_DMD_DMD",prove (``!f a. ~(!a' g . ~SUBFORMULA <<a'>> g <<a>> f)``,SIMP_TAC std_ss [] THEN REPEAT GEN_TAC THEN MAP_EVERY Q.EXISTS_TAC [`a`,`f`] THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_DMD_BOX  = save_thm("SUB_DMD_BOX",prove(``!f g a a'. ~SUBFORMULA (<<a>> g) ([[a']]f) = ~SUBFORMULA (<<a>> g) f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_DMD_MU  = save_thm("SUB_DMD_MU",prove(``!f g a Q. ~SUBFORMULA (<<a>> g) (mu Q .. f) = ~SUBFORMULA (<<a>> g) f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_DMD_NU  = save_thm("SUB_DMD_NU",prove(``!f g a Q. ~SUBFORMULA (<<a>> g) (nu Q .. f) = ~SUBFORMULA (<<a>> g) f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_AP_NEG_CONJ  = save_thm("SUB_AP_NEG_CONJ",prove(``!f g p. SUBFORMULA (AP p) ~(f /\ g) = SUBFORMULA (AP p) ~f \/ SUBFORMULA (AP p) ~g``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_AP_NEG_DISJ  = save_thm("SUB_AP_NEG_DISJ",prove(``!f g p. SUBFORMULA (AP p) ~(f \/ g) = SUBFORMULA (AP p) ~f \/ SUBFORMULA (AP p) ~g``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_AP_NEG_DMD = save_thm("SUB_AP_NEG_DMD",prove(``!f p a. SUBFORMULA (AP p) ~(<<a>>f) = SUBFORMULA (AP p) ~f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_AP_NEG_NEG  = save_thm("SUB_AP_NEG_NEG",prove(``!f p. SUBFORMULA (AP p) (~~f) = SUBFORMULA (AP p) f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_DMD_NEG_CONJ  = save_thm("SUB_DMD_NEG_CONJ",prove(``!f f1 g a. ~SUBFORMULA (<<a>> g) ~(f /\ f1) = (~SUBFORMULA (<<a>> g) ~f) /\ (~SUBFORMULA (<<a>> g) ~f1)``,Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_DMD_NEG_DISJ  = save_thm("SUB_DMD_NEG_DISJ",prove(``!f f1 g a. ~SUBFORMULA (<<a>> g) ~(f \/ f1) = (~SUBFORMULA (<<a>> g) ~f) /\ (~SUBFORMULA (<<a>> g) ~f1)``,Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_DMD_NEG_DMD  = save_thm("SUB_DMD_NEG_DMD",prove(``!f a. (!a' g. ~SUBFORMULA (<<a'>> g) ~(<<a>>f)) ==> !a' g. ~SUBFORMULA (<<a'>> g) ~f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))

val SUB_DMD_NEG_NEG  = save_thm("SUB_DMD_NEG_NEG",prove(``!f g a. ~SUBFORMULA (<<a>> g) (~~f) = ~SUBFORMULA (<<a>> g) f``,
Induct_on `f` THEN SIMP_TAC std_ss (MU_SUB_def::tsimps_mu)))


val STATES_MONO_LEM3 = save_thm("STATES_MONO_LEM3",prove(``!(f:'prop mu) Q. ~SUBFORMULA (~RV Q) (NNF f) = ~SUBFORMULA (~RV Q) (NNF (RVNEG Q ~f))``,
recInduct NNF_IND_def THEN REPEAT CONJ_TAC THEN BETA_TAC THEN SIMP_TAC std_ss ([NNF_def,MU_SUB_def,RVNEG_def]@tsimps_mu) THENL [
REPEAT GEN_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss [MU_SUB_def,NNF_def]
 THEN FULL_SIMP_TAC std_ss tsimps_mu,
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def]@ tsimps_mu)], (* RV *)
REPEAT STRIP_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@ tsimps_mu),
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@ tsimps_mu)
 THEN FULL_SIMP_TAC std_ss [SIMP_RULE std_ss [RVNEG_def] (SPECL[``~RVNEG Q' (f:'prop mu)``,``Q:string``,``Q':string``]
								      STATES_MONO_LEM2)]], (* mu *)
REPEAT STRIP_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@ tsimps_mu),
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@ tsimps_mu)
 THEN FULL_SIMP_TAC std_ss [SIMP_RULE std_ss [RVNEG_def] (SPECL[``~RVNEG Q' (f:'prop mu)``,``Q:string``,``Q':string``]
								      STATES_MONO_LEM2)]], (* nu *)
REPEAT GEN_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss [MU_SUB_def,NNF_def]
 THEN FULL_SIMP_TAC std_ss tsimps_mu,
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def]@ tsimps_mu)], (* ~RV *)
REPEAT STRIP_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss ([NNF_RVNEG_DUALITY,MU_SUB_def,NNF_def,RVNEG_def]@ tsimps_mu),
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@ tsimps_mu)
 THEN SIMP_TAC std_ss [RVNEG_SYM]
 THEN PROVE_TAC [SIMP_RULE std_ss [RVNEG_def] (SPECL[``RVNEG Q' (f:'prop mu)``,``Q:string``,``Q':string``]
								      STATES_MONO_LEM2)]], (* ~mu *)
REPEAT STRIP_TAC THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss ([NNF_RVNEG_DUALITY,MU_SUB_def,NNF_def,RVNEG_def]@ tsimps_mu),
 FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def]@ tsimps_mu)
 THEN SIMP_TAC std_ss [RVNEG_SYM]
 THEN PROVE_TAC [SIMP_RULE std_ss [RVNEG_def] (SPECL[``RVNEG Q' (f:'prop mu)``,``Q:string``,``Q':string``]
								      STATES_MONO_LEM2)]]])) (* ~nu *)

val STATES_MONO_LEM6 = save_thm("STATES_MONO_LEM6",prove (``!Q Q' (f:'prop mu). SUBFORMULA (~RV Q') (NNF mu Q.. f) = SUBFORMULA (~RV Q') (NNF f)``,FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def]@ tsimps_mu)))

val STATES_MONO_LEM11 = save_thm("STATES_MONO_LEM11",prove(``!Q Q' (f:'prop mu). SUBFORMULA (~RV Q') (NNF nu Q.. f) = SUBFORMULA (~RV Q') (NNF f)``,FULL_SIMP_TAC std_ss ([MU_SUB_def,NNF_def]@ tsimps_mu)))


val STATES_MONO_LEM8 = save_thm("STATES_MONO_LEM8",prove(``!Q. ~SUBFORMULA (~RV Q) (NNF (RV:(string -> 'prop mu) Q))``,SIMP_TAC std_ss ([MU_SUB_def,NNF_def]@tsimps_mu)))

val STATES_MONO_LEM9 = save_thm("STATES_MONO_LEM9",prove(``!Q. SUBFORMULA (~RV Q) (NNF (~(RV:(string -> 'prop mu)) Q))``,SIMP_TAC std_ss ([MU_SUB_def,NNF_def]@tsimps_mu)))

(* thms about IMF *)

val NNF_IDEM = save_thm("NNF_IDEM",prove(``!f. NNF (NNF f) = NNF f``,recInduct NNF_IND_def THEN REPEAT CONJ_TAC THEN SIMP_TAC std_ss (NNF_def::MU_SUB_def::tsimps_mu) THEN ASSUM_LIST (fn l => TRY (PROVE_TAC l))))

val IMF_NNF = save_thm("IMF_NNF",prove(``!f. IMF f = IMF (NNF f)``,
recInduct NNF_IND_def THEN REPEAT CONJ_TAC THEN SIMP_TAC std_ss (NNF_IDEM::IMF_def::MU_SUB_def::NNF_def::tsimps_mu) THEN
RW_TAC std_ss [] THEN PROVE_TAC [STATES_MONO_LEM3,IMF_INV_NEG_RVNEG]))

val IMF_MU_NNF = save_thm("IMF_MU_NNF",prove(``!f Q. IMF (mu Q .. f) = IMF (mu Q .. NNF f)``,
REWRITE_TAC [IMF_def] THEN PROVE_TAC [NNF_IDEM,IMF_NNF]))


val IMF_MU_CONJ = save_thm("IMF_MU_CONJ",prove(``!f g Q. IMF (mu Q.. f /\ g) = IMF (mu Q .. f) /\ IMF (mu Q .. g)``,SIMP_TAC std_ss [IMF_def] THEN Induct_on `f` THEN SIMP_TAC std_ss (IMF_def::MU_SUB_def::NNF_def::tsimps_mu) THEN ASSUM_LIST PROVE_TAC))

val IMF_MU_NEG_CONJ = save_thm("IMF_MU_NEG_CONJ",prove(``!f g Q. IMF (mu Q.. ~(f /\ g)) = IMF (mu Q .. ~f) /\ IMF (mu Q .. ~g)``,SIMP_TAC std_ss [IMF_def] THEN Induct_on `f` THEN SIMP_TAC std_ss (IMF_def::MU_SUB_def::NNF_def::tsimps_mu) THEN ASSUM_LIST PROVE_TAC))

val IMF_MU_DISJ = save_thm("IMF_MU_DISJ",prove(``!f g Q. IMF (mu Q.. f \/ g) = IMF (mu Q .. f) /\ IMF (mu Q .. g)``,SIMP_TAC std_ss [IMF_def] THEN Induct_on `f` THEN SIMP_TAC std_ss (IMF_def::MU_SUB_def::NNF_def::tsimps_mu) THEN ASSUM_LIST PROVE_TAC))

val IMF_MU_NEG_DISJ = save_thm("IMF_MU_NEG_DISJ",prove(``!f g Q. IMF (mu Q.. ~(f \/ g)) = IMF (mu Q .. ~f) /\ IMF (mu Q .. ~g)``,SIMP_TAC std_ss [IMF_def] THEN Induct_on `f` THEN SIMP_TAC std_ss (IMF_def::MU_SUB_def::NNF_def::tsimps_mu) THEN ASSUM_LIST PROVE_TAC))

val IMF_MU_DMD = save_thm("IMF_MU_DMD",prove(``!f a Q. IMF (mu Q.. <<a>> f ) = IMF (mu Q .. f)``,SIMP_TAC std_ss [IMF_def] THEN Induct_on `f` THEN SIMP_TAC std_ss (IMF_def::MU_SUB_def::NNF_def::tsimps_mu) THEN ASSUM_LIST PROVE_TAC))

val IMF_MU_NEG_DMD = save_thm("IMF_MU_NEG_DMD",prove(``!f a Q. IMF (mu Q.. ~<<a>> f ) = IMF (mu Q .. ~f)``,SIMP_TAC std_ss [IMF_def] THEN Induct_on `f` THEN SIMP_TAC std_ss (IMF_def::MU_SUB_def::NNF_def::tsimps_mu) THEN ASSUM_LIST PROVE_TAC))

val IMF_MU_BOX = save_thm("IMF_MU_BOX",prove(``!f a Q. IMF (mu Q.. [[a]] f) = IMF (mu Q .. f)``,SIMP_TAC std_ss [IMF_def] THEN Induct_on `f` THEN SIMP_TAC std_ss (IMF_def::MU_SUB_def::NNF_def::tsimps_mu) THEN ASSUM_LIST PROVE_TAC))

val IMF_MU_NEG_BOX = save_thm("IMF_MU_NEG_BOX",prove(``!f a Q. IMF (mu Q.. ~[[a]] f) = IMF (mu Q .. ~f)``,SIMP_TAC std_ss [IMF_def] THEN Induct_on `f` THEN SIMP_TAC std_ss (IMF_def::MU_SUB_def::NNF_def::tsimps_mu) THEN ASSUM_LIST PROVE_TAC))

val IMF_MU_MU = save_thm("IMF_MU_MU",prove(``!f Q Q'. IMF (mu Q.. mu Q' .. f) ==> IMF (mu Q' .. f)``,SIMP_TAC std_ss [IMF_def] THEN recInduct NNF_IND_def THEN REPEAT CONJ_TAC THEN SIMP_TAC std_ss (IMF_def::MU_SUB_def::NNF_def::tsimps_mu) THEN ASSUM_LIST (fn l => TRY (PROVE_TAC l))))

val IMF_MU_NEG_MU = save_thm("IMF_MU_NEG_MU",prove(``!f Q Q'. IMF (mu Q.. ~mu Q' .. f) ==> IMF (mu Q' .. f)``,SIMP_TAC std_ss [IMF_def] THEN recInduct NNF_IND_def THEN REPEAT CONJ_TAC THEN SIMP_TAC std_ss (IMF_def::MU_SUB_def::NNF_def::tsimps_mu) THEN ASSUM_LIST (fn l => TRY (PROVE_TAC l))))

val IMF_MU_NU = save_thm("IMF_MU_NU",prove(``!f Q Q'. IMF (mu Q.. nu Q' .. f) ==> IMF (mu Q' .. f)``,SIMP_TAC std_ss [IMF_def] THEN recInduct NNF_IND_def THEN REPEAT CONJ_TAC THEN SIMP_TAC std_ss (IMF_def::MU_SUB_def::NNF_def::tsimps_mu) THEN ASSUM_LIST (fn l => TRY (PROVE_TAC l))))

val IMF_MU_NEG_NU = save_thm("IMF_MU_NEG_NU",prove(``!f Q Q'. IMF (mu Q.. ~nu Q' .. f) ==> IMF (mu Q' .. f)``,SIMP_TAC std_ss [IMF_def] THEN recInduct NNF_IND_def THEN REPEAT CONJ_TAC THEN SIMP_TAC std_ss (IMF_def::MU_SUB_def::NNF_def::tsimps_mu) THEN ASSUM_LIST (fn l => TRY (PROVE_TAC l))))

val IMF_MU_NEG_NEG = save_thm("IMF_MU_NEG_NEG",prove(``!f a Q. IMF (mu Q.. ~~f) = IMF (mu Q .. f)``,SIMP_TAC std_ss [IMF_def] THEN Induct_on `f` THEN SIMP_TAC std_ss (IMF_def::MU_SUB_def::NNF_def::tsimps_mu) THEN ASSUM_LIST PROVE_TAC))

val IMF_MU_INV_RVNEG = save_thm("IMF_MU_INV_RVNEG",prove(``!f Q. IMF (mu Q.. f) = IMF mu Q.. RVNEG Q ~f``, REWRITE_TAC [IMF_def] THEN PROVE_TAC[STATES_MONO_LEM3,IMF_INV_NEG_RVNEG]))

val IMF_MU_EXT = save_thm("IMF_MU_EXT",prove(``!f. IMF f ==> ?Q. IMF (mu Q..f)``,
REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [IMF_def]
THEN Q.EXISTS_TAC `@Q. ~(Q IN ALLV (NNF f))`
THEN SELECT_ELIM_TAC
THEN CONJ_TAC THENL [
 POP_ASSUM (K ALL_TAC)
 THEN REWRITE_TAC [GSYM ALLV_NNF]
 THEN METIS_TAC [NOT_IN_FIN_STRING_SET,ALLV_FINITE],
 REPEAT STRIP_TAC
 THEN IMP_RES_TAC SUBF_NEG2
 THEN METIS_TAC [ALLV_SUBF,ALLV_NNF]
]))

val _ = export_theory()
