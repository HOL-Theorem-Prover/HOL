(* ===================================================================== *)
(* FILE          : Num_induct.sml                                        *)
(* DESCRIPTION   : Provides a forward inference rule and a tactic for    *)
(*                 induction over numbers. Translated from hol88.        *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon and                                   *)
(*                     Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


structure Num_induct :> Num_induct =
struct


open HolKernel Rsyntax Parse Drule Tactic Prim_rec;

infix |->;

fun NUM_INDUCT_ERR f m =
   HOL_ERR
     {origin_structure = "Num_induct",
      origin_function = f, message = m};

val INDUCTION = numTheory.INDUCTION;

(* --------------------------------------------------------------------- *)
(* INDUCT: (thm * thm) -> thm                                            *)
(*                                                                       *)
(*   A1 |- t[0]      A2 |- !n. t[n] ==> t[SUC n]                         *)
(* -----------------------------------------------                       *)
(*             A1 u A2 |- !n. t[n]                                       *)
(* --------------------------------------------------------------------- *)

local val v1 = genvar Type.bool
      and v2 = genvar Type.bool
      and zero = mk_const{Name="0",Ty= Type`:num`}
      and SUC = mk_const{Name="SUC",Ty= Type`:num->num`}
in
fun INDUCT (base,step) =
   let val {Bvar,Body} = dest_forall(concl step)
       val {ant,...} = dest_imp Body
       val P  = mk_abs{Bvar = Bvar, Body = ant}
       val P0 = mk_comb{Rator = P, Rand = zero}
       val Pv = mk_comb{Rator = P, Rand = Bvar}
       val PSUC = mk_comb{Rator=P, Rand=mk_comb{Rator=SUC, Rand=Bvar}}
       val base' = EQ_MP (SYM(BETA_CONV P0)) base
       and step'  = SPEC Bvar step
       and hypth  = SYM(RIGHT_BETA(REFL Pv))
       and concth = SYM(RIGHT_BETA(REFL PSUC))
       and IND    = SPEC P INDUCTION
       val template = mk_eq{lhs = concl step',
                            rhs = mk_imp{ant = v1, conseq = v2}}
       val th1 = SUBST[v1|->hypth, v2|->concth] template (REFL (concl step'))
       val th2 = GEN Bvar (EQ_MP th1 step')
       val th3 = SPEC Bvar (MP IND (CONJ base' th2))
   in
     GEN Bvar (EQ_MP (BETA_CONV(concl th3)) th3)
   end
   handle _ => raise NUM_INDUCT_ERR "INDUCT" ""
end;

(* --------------------------------------------------------------------- *)
(*             [A] !n.t[n]                                               *)
(*  ================================                                     *)
(*   [A] t[0]  ,  [A,t[n]] t[SUC x]                                      *)
(* --------------------------------------------------------------------- *)

fun INDUCT_TAC g =
  INDUCT_THEN INDUCTION ASSUME_TAC g
   handle _ => raise NUM_INDUCT_ERR "INDUCT_TAC" "";

end; (* Num_induction *)
