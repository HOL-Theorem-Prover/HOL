(* =====================================================================*)
(* FILE		: set_ind.ml						*)
(* DESCRIPTION  : Induction principle for finite sets.			*)
(*								        *)
(* AUTHOR	: Philippe Leveilley					*)
(*									*)
(* REWRITTEN    : T Melham						*)
(* DATE		: 90.03.14 (adapted for pred_sets: January 1992)	*)
(*									*)
(* REMARKS	: Dependence on taut library removed. Use of rewriting  *)
(*		  eliminated.  Optimized for speed.  Simplified. 	*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(*                                                                      *)
(*    `!s. FINITE s ==>  P s`                          		        *)
(*   ==========================     SET_INDUCT_TAC 			*)
(*    P EMPTY     P (x INSERT t)                         		*)
(*                [ `FINITE t` ]                       		        *)
(*		  [ `P s`						*)
(*                [ `~x IN t`]                           	        *)
(*									*)
(* ---------------------------------------------------------------------*)

structure PSet_ind :> PSet_ind =
struct

open HolKernel Parse basicHol90Lib;
infix THEN THENL |->;

type tactic = Abbrev.tactic;

local val check = assert (fn tm => #Name(dest_const(rator tm)) = "FINITE")
      val IMP = (--`==>`--) 
      val CONJ = (--`/\`--)
      fun MK_IMP1 tm = AP_TERM (mk_comb{Rator=IMP,Rand=tm})
      and MK_IMP2 th1 th2 = MK_COMB(AP_TERM IMP th1,th2) 
      fun dest tm = 
            let val {Bvar,Body} = dest_forall tm
                val {ant,conseq} = dest_imp Body
            in (Bvar,ant,conseq) end
      fun sconv tm =
            let val (s,a,balt) = dest tm
                val (e,h,c) =  dest balt
                val th1 = RAND_CONV BETA_CONV a 
                and th2 = BETA_CONV c 
            in FORALL_EQ s (MK_IMP2 th1 (FORALL_EQ e (MK_IMP1 h th2))) end
      fun conv tm = 
            let val {conj1,conj2} = dest_conj tm 
            in MK_COMB(AP_TERM CONJ (BETA_CONV conj1), sconv conj2) end
      val STAC = GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
                 GEN_TAC THEN DISCH_THEN ASSUME_TAC 
in
fun SET_INDUCT_TAC FINITE_INDUCT (A,g) =
   let val {Bvar,Body} = dest_forall g
       val {ant,conseq} = dest_imp Body
       val _ = check ant
       val (s,conc) = (Bvar,conseq)
       val {Args=[ty,_],...} = dest_type(type_of s)
       val inst = INST_TYPE [==`:'a`== |-> ty] FINITE_INDUCT
       val sv = genvar (type_of s)
       val pred = mk_abs{Bvar=sv,Body=subst [s |-> sv] conc}
       val spec = SPEC s (UNDISCH (SPEC pred inst))
       val beta = GEN s (CONV_RULE (RAND_CONV BETA_CONV) spec)
       val disc = DISCH (hd(hyp beta)) beta
       val ithm = CONV_RULE (RATOR_CONV(RAND_CONV conv)) disc
   in (MATCH_MP_TAC ithm THEN CONJ_TAC THENL [ALL_TAC, STAC]) (A,g)
   end 
   handle _ => raise HOL_ERR {origin_structure="Set_ind",
                              origin_function = "SET_INDUCT_TAC", message = ""}
end;

end; (* Set_ind *)
