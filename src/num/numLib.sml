(* ===================================================================== *)
(* FILE          : numLib.sml  (Formerly num_lib.sml, num.sml)           *)
(* DESCRIPTION   : Proof support for :num. Translated from hol88.        *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon and                                   *)
(*                     Tom Melham, University of Cambridge               *)
(* DATE          : 88.04.04                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* UPDATE        : October'94 bugfix to num_EQ_CONV (KLS;bugfix from tfm)*)
(* UPDATE        : January'99 fix to use "Norrish" numerals (MN)         *)
(* UPDATE        : August'99 to incorporate num_CONV and INDUCT_TAC      *)
(* UPDATE        : Nov'99 to incorporate main entrypoints from           *)
(*                 reduceLib and arithLib. Also, ADD_CONV and            *)
(*                 num_EQ_CONV are banished: use the stuff in reduceLib  *)
(*                 instead.                                              *)
(* ===================================================================== *)


structure numLib :> numLib =
struct

local open numeralTheory in end;

open HolKernel boolLib Rsyntax Num_conv Parse;
infix THEN THENC THENL;

type conv = Abbrev.conv
type tactic = Abbrev.tactic

fun ERR function message =
    HOL_ERR{origin_structure = "numLib",
            origin_function = function,
            message = message};

infix 5 |->
infix ##;

val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars
fun -- q x = Term q

val N = Type`:num`

(* --------------------------------------------------------------------- *)
(* EXISTS_LEAST_CONV: applies the well-ordering property to non-empty    *)
(* sets of numbers specified by predicates.                              *)
(*                                                                       *)
(* A call to EXISTS_LEAST_CONV `?n:num. P[n]` returns:                   *)
(*                                                                       *)
(*   |- (?n. P[n]) = ?n. P[n] /\ !n'. (n' < n) ==> ~P[n']                *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)

local val wop = arithmeticTheory.WOP
      val wth = CONV_RULE (ONCE_DEPTH_CONV ETA_CONV) wop
      val check = assert (fn tm => type_of tm = N)
      val acnv = RAND_CONV o ABS_CONV
in
fun EXISTS_LEAST_CONV tm =
   let val {Bvar,Body = P} = dest_exists tm
       val n = check Bvar
       val thm1 = UNDISCH (SPEC (rand tm) wth)
       val thm2 = CONV_RULE (GEN_ALPHA_CONV n) thm1
       val {Rator=c1,Rand=c2} = dest_comb (#Body(dest_exists(concl thm2)))
       val bth1 = RAND_CONV BETA_CONV c1
       val bth2 = acnv (RAND_CONV (RAND_CONV BETA_CONV)) c2
       val n' = variant (n :: free_vars tm) n
       val abth2 = CONV_RULE (RAND_CONV (GEN_ALPHA_CONV n')) bth2
       val thm3 = EXISTS_EQ n (MK_COMB(bth1,abth2))
       val imp1 = DISCH tm (EQ_MP thm3 thm2)
       val eltm = rand(concl thm3)
       val thm4 = CONJUNCT1 (ASSUME (#Body(dest_exists eltm)))
       val thm5 = CHOOSE (n,ASSUME eltm) (EXISTS (tm,n) thm4)
   in
   IMP_ANTISYM_RULE imp1 (DISCH eltm thm5)
   end
   handle _ => raise ERR "EXISTS_LEAST_CONV" ""
end;

(*---------------------------------------------------------------------------*)
(* EXISTS_GREATEST_CONV - Proves existence of greatest element satisfying P. *)
(*                                                                           *)
(* EXISTS_GREATEST_CONV `(?x. P[x]) /\ (?y. !z. z > y ==> ~(P[z]))` =        *)
(*    |- (?x. P[x]) /\ (?y. !z. z > y ==> ~(P[z])) =                         *)
(*        ?x. P[x] /\ !z. z > x ==> ~(P[z])                                  *)
(*                                                                           *)
(* If the variables x and z are the same, the `z` instance will be primed.   *)
(* [JRH 91.07.17]                                                            *)
(*---------------------------------------------------------------------------*)

local val EXISTS_GREATEST = arithmeticTheory.EXISTS_GREATEST
      val t = RATOR_CONV
      and n = RAND_CONV
      and b = ABS_CONV
      val red1 = t o n o t o n o n o b
      and red2 = t o n o n o n o b o n o b o n o n
      and red3 = n o n o b o t o n
      and red4 = n o n o b o n o n o b o n o n
in
fun EXISTS_GREATEST_CONV tm =
   let val {conj1=lc,conj2=rc} = dest_conj tm
       val pred = rand lc
       val {Bvar=xv,Body=xb} = dest_exists lc
       val {Bvar=yv,Body=yb} = dest_exists rc
       val zv = #Bvar (dest_forall yb)
       val prealpha = CONV_RULE
         (red1 BETA_CONV THENC red2 BETA_CONV THENC
          red3 BETA_CONV THENC red4 BETA_CONV) (SPEC pred EXISTS_GREATEST)
       val rqd = mk_eq {lhs = tm, rhs =
            mk_exists{Bvar=xv,Body=mk_conj{conj1=xb, conj2=subst[yv|->xv] yb}}}
   in
   Lib.S (Lib.C EQ_MP) (Lib.C ALPHA rqd o concl) prealpha
   end
   handle _ => raise ERR "EXISTS_GREATEST_CONV" ""
end;


local open Psyntax
      val SUC = mk_const("SUC", mk_type("fun", [N, N]))
      fun mk_SUC t = mk_comb(SUC, t)
      fun SEC_ERR m = ERR "SUC_ELIM_CONV" m
      fun assert f x = f x orelse raise SEC_ERR "assertion failed"
in
fun SUC_ELIM_CONV tm =
   let val (v,bod) = dest_forall tm
       val _ = assert (fn x => type_of x = N) v
       val (sn,n) = (genvar N, genvar N)
       val suck_suc = Rsyntax.subst [mk_SUC v |-> sn] bod
       val suck_n = Rsyntax.subst [v |-> n] suck_suc
       val _ = assert (fn x => x <> tm) suck_n
       val th1 = ISPEC (list_mk_abs ([sn,n],suck_n))
                     arithmeticTheory.SUC_ELIM_THM
       val BETA2_CONV = (RATOR_CONV BETA_CONV) THENC BETA_CONV
       val th2 = CONV_RULE (LHS_CONV (QUANT_CONV BETA2_CONV)) th1
       val th3 = CONV_RULE (RHS_CONV (QUANT_CONV
                    (FORK_CONV (ALL_CONV, BETA2_CONV)))) th2
   in th3
   end
end;

val num_CONV   = Num_conv.num_CONV
val INDUCT_TAC = Num_induct.INDUCT_TAC

val REDUCE_CONV = reduceLib.REDUCE_CONV
val REDUCE_RULE = reduceLib.REDUCE_RULE
val REDUCE_TAC  = reduceLib.REDUCE_TAC

val ARITH_CONV  = arithLib.ARITH_CONV
val ARITH_PROVE = arithLib.ARITH_PROVE
val ARITH_TAC   = CONV_TAC ARITH_CONV;

end; (* numLib *)
