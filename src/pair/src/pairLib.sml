(*---------------------------------------------------------------------------*
 * Theory of pairs and associated support.                                   *
 *---------------------------------------------------------------------------*)

structure pairLib :> pairLib =
struct

local open pairTheory pairSimps pairTools PairRules in end;

open boolLib pairSyntax PairedLambda pairTools simpLib;

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;

val LET_INTRO_TAC = 
 let open pairTheory
 in (* first move lets as far out as possible *)
   SIMP_TAC pureSimps.pure_ss
               [GEN_LET_RAND, GEN_LET_RATOR,
                C_UNCURRY_L, pairTheory.C_ABS_L,
                combinTheory.o_THM, o_ABS_R, o_UNCURRY_R]
   THEN (* turn lets into foralls *)
      SIMP_TAC pureSimps.pure_ss [LET_FORALL_ELIM, S_ABS_R,
                                  S_UNCURRY_R, combinTheory.o_THM,
                                  FORALL_UNCURRY, o_ABS_R]
   THEN REPEAT GEN_TAC 
   THEN REPEAT STRIP_TAC
 end;

end
