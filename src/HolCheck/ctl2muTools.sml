structure ctl2muTools =
struct

local 

open Globals HolKernel Parse goalstackLib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;
open Psyntax;

open boolSyntax;
open pairSyntax;
open pairTools;
open PairRules;
open bossLib;
open muTheory
open muCheck
open ctlTheory
open ctl2muTheory;
open Tactical;
open Tactic;
open Drule;
open Rewrite;
open cearTheory;
open ksTheory;
open setLemmasTheory;
open pred_setTheory;
open boolTheory;
open Conv;
open PrimitiveBddRules

fun mk_bool_var v = mk_var(v,``:bool``);
fun mk_primed_bool_var v = mk_bool_var (v^"'");
fun term_to_string2 t = with_flag (show_types,false) term_to_string t;

in

(* normalise ctl formula to only use constructors from the minimal set *)
fun ctl_norm_CONV f = Rewrite.REWRITE_CONV [C_IMP2_def,B_IMP2_def,B_AND2_def,B_OR2_def,C_AND2_def,C_OR2_def,C_AX_def,C_AG_def,C_AU_def,C_EF_def,C_IMP_def,C_IFF_def,C_AF_def,B_IMP_def,B_IFF_def,C_OR_def,B_OR_def] f handle ex => (REFL f);

(* convert ctl formula to mu formula *)
fun ctl2mu_CONV f = REWRITE_CONV [CTL2MU_def,BEXP2MU_def,C_IMP2_def,B_IMP2_def,B_AND2_def,B_OR2_def,C_AND2_def,C_OR2_def,C_AX_def,C_AG_def,C_AU_def,C_EF_def,C_IMP_def,C_IFF_def,C_AF_def,B_IMP_def,B_IFF_def,C_OR_def,B_OR_def,B_FALSE_def] ``CTL2MU ^f``

(* convert ctl model to mu model *)
fun ctl2muks_CONV Rthm cks_def = PURE_REWRITE_RULE [SYM Rthm] (PURE_REWRITE_RULE [SYM cks_def,combinTheory.K_THM,kripke_structure_accfupds] (ISPEC (rhs(concl cks_def)) ctl2muks_def)) 

end
end
