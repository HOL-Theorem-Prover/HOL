(*---------------------------------------------------------------------------*
 * The "boss" library. This provides a collection of proof routines.         *
 * They provide                                                              *
 *                                                                           *
 *    1. Automatic maintenance of the usual products of a datatype           *
 *       definition.                                                         *
 *                                                                           *
 *    2. Some tools that work using that information.                        *
 *                                                                           *
 *    3. Some basic automation support.                                      *
 *                                                                           *
 *---------------------------------------------------------------------------*)

structure bossLib :> bossLib =
struct

open HolKernel Parse basicHol90Lib;

  type term = Term.term
  type fixity = Parse.fixity
  type thm = Thm.thm
  type tactic = Abbrev.tactic
  type simpset = simpLib.simpset
  type defn = Defn.defn
  type 'a quotation = 'a Portable.frag list


infix ORELSE;

fun BOSS_ERR func mesg =
     HOL_ERR{origin_structure = "bossLib",
             origin_function = func,
             message = mesg};

(*---------------------------------------------------------------------------*
            Datatype definition
 *---------------------------------------------------------------------------*)

fun type_rws tyn = TypeBase.simpls_of (valOf (TypeBase.read tyn));

val Hol_datatype = Datatype.Hol_datatype;


(*---------------------------------------------------------------------------
            Function definition
 ---------------------------------------------------------------------------*)

val xDefine    = TotalDefn.xDefine
val Define     = TotalDefn.Define
val Hol_defn   = Defn.Hol_defn;
val WF_REL_TAC = TotalDefn.WF_REL_TAC;

val ind_suffix = TotalDefn.ind_suffix
val def_suffix = TotalDefn.def_suffix;


(*---------------------------------------------------------------------------
     Support for higher-order recursion. There should be a better
     place for this. Probably listTheory would be right, but then
     Context would have to be known earlier.
 ---------------------------------------------------------------------------*)

local open listTheory
     val hocongs = [EXISTS_CONG,EVERY_CONG,MAP_CONG,
                    FOLDL_CONG, FOLDR_CONG,list_size_cong]
in
  val _ = Tfl.write_context (hocongs@Tfl.read_context())
end;

(*---------------------------------------------------------------------------
            Automated proof operations
 ---------------------------------------------------------------------------*)

fun PROVE thl q = BasicProvers.PROVE thl (Parse.Term q);
val PROVE_TAC   = BasicProvers.PROVE_TAC
val RW_TAC      = BasicProvers.RW_TAC

val && = BasicProvers.&&;
infix &&;

(*---------------------------------------------------------------------------
     The following simplification sets will be applied in a context
     that extends that loaded by bossLib. They are intended to be used
     by RW_TAC. The choice of which simpset to use depends on factors
     such as running time.  For example, RW_TAC with arith_ss (and thus
     with list_ss) may take a long time on some goals featuring arithmetic
     terms (since the arithmetic decision procedure may be invoked). In
     such cases, it may be worth dropping down to use std_ss,
     supplying whatever arithmetic theorems are required, so that
     simplification is quick.
 ---------------------------------------------------------------------------*)

(* val bool_ss = boolSimps.bool_ss *)

local open simpLib sumTheory
      infix ++
in
val std_ss =
     (boolSimps.bool_ss ++ pairSimps.PAIR_ss ++ optionSimps.OPTION_ss) 
       && (type_rws "sum" @ [ISL,ISR,OUTL,OUTR,INL,INR])

val arith_ss = std_ss ++ arithSimps.ARITH_ss
val list_ss  = arith_ss ++ listSimps.list_ss
end


val DECIDE     = decisionLib.DECIDE o Parse.Term
val DECIDE_TAC = decisionLib.DECIDE_TAC

fun ZAP_TAC ss thl =
   BasicProvers.STP_TAC ss
      (tautLib.TAUT_TAC
          ORELSE DECIDE_TAC
          ORELSE BasicProvers.GEN_PROVE_TAC 0 12 1 thl);



(*---------------------------------------------------------------------------
   The following is a function creating a new simplification set to be used
   with computeLib.CBV_CONV. It contains basic definitions about arithmetic
   operations (those of reduceLib), and several others:
   LET, pairs, curryfication, options and lists.
 ---------------------------------------------------------------------------*)

local
fun iter_add []      rws = ()
  | iter_add (f::fs) rws = (f rws : unit ; iter_add fs rws);

open computeLib
val added_theories =
  [ add_thms [strictify_thm LET_DEF],
    add_thms [lazyfy_thm arithmeticTheory.num_case_compute],
    pairSimps.PAIR_rws, sumSimps.SUM_rws, optionLib.OPTION_rws,
    listSimps.list_rws ]

in
fun initial_rws () =
  let val rws = reduceLib.reduce_rws ()
      val () = iter_add added_theories rws
  in rws end;
end;

(*---------------------------------------------------------------------------
            Single step interactive proof operations
 ---------------------------------------------------------------------------*)


val Cases     = SingleStep.Cases
val Induct    = SingleStep.Induct
val recInduct = SingleStep.recInduct

val Cases_on          = SingleStep.Cases_on
val Induct_on         = SingleStep.Induct_on
val completeInduct_on = SingleStep.completeInduct_on
val measureInduct_on  = SingleStep.measureInduct_on;

val SPOSE_NOT_THEN    = SingleStep.SPOSE_NOT_THEN

val by                = SingleStep.by; (* infix 8 by *)

end;
