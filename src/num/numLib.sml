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
(* ===================================================================== *)


structure numLib :> numLib =
struct

local open arithmeticTheory numeralTheory in end;

open HolKernel basicHol90Lib Num_conv Parse;
infix THEN THENC THENL;

fun NUM_ERR{function,message} =
    HOL_ERR{origin_structure = "Num",
            origin_function = function,
            message = message};

infix 5 |->
infix ##;

val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars
fun -- q x = Term q

val N = Type`:num`

(* --------------------------------------------------------------------- *)
(* ADD_CONV: addition of natural number constants (numerals).            *)
(*                                                                       *)
(* If n and m are numerals (i.e 0,1,2,3,...) then:                       *)
(*                                                                       *)
(*      ADD_CONV `n + m`                                                 *)
(*                                                                       *)
(* returns                                                               *)
(*                                                                       *)
(*      |- n + m = s                                                     *)
(*                                                                       *)
(* where s is the numeral denoting the sum of n and m.                   *)
(*                                                                       *)
(* NOTE: binary numerals allow this to be done with rewriting            *)
(* --------------------------------------------------------------------- *)

local open numeralTheory
      val RW = REWRITE_CONV
         [numeral_add, numeral_distrib, numeral_suc, numeral_iisuc]
in
fun ADD_CONV tm =
 let val (f, args) = strip_comb tm
     val _ = assert (fn t => #Name(dest_const t) = "+") f
     val _ = assert (fn l => length l = 2) args
     val _ = assert is_numeral (hd args)
     val _ = assert is_numeral (hd (tl args))
 in
    RW tm
 end handle HOL_ERR _ => raise NUM_ERR{function = "ADD_CONV",message = ""}
end;


(* --------------------------------------------------------------------- *)
(* num_EQ_CONV: equality of natural number constants.                    *)
(*                                                                       *)
(* If n and m are numerals (i.e 0,1,2,3,...) or sucessors of numerals    *)
(* (e.g. SUC 0, SUC(SUC 2), etc), then:                                  *)
(*                                                                       *)
(*      num_EQ_CONV `n = m`                                              *)
(*                                                                       *)
(* returns                                                               *)
(*                                                                       *)
(*      |- (n = m) = T           if n=m                                  *)
(*      |- (n = m) = F           if ~(n=m)                               *)
(*                                                                       *)
(* and if n and m are syntactically identical terms of type :num, then   *)
(*                                                                       *)
(*      num_EQ_CONV `n = m`  returns |- (n = m) = T                      *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)

local open numeralTheory
      val RW = REWRITE_CONV [numeral_eq, numeral_distrib]
in
fun num_EQ_CONV tm =
 let val {lhs=n, rhs=m} = dest_eq tm
     val _ = assert (fn t => type_of t = N) n
 in
   if n=m then EQT_INTRO (REFL n) else
   if is_numeral n andalso is_numeral m then RW tm
   else raise NUM_ERR{function = "num_EQ_CONV",
               message = "Terms are neither identical nor numerals"}
 end
 handle HOL_ERR _ => raise NUM_ERR{function="num_EQ_CONV",message = ""}
end;


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
   handle _ => raise NUM_ERR{function = "EXISTS_LEAST_CONV",message = ""}
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
   handle _ => raise NUM_ERR{function = "EXISTS_GREATEST_CONV",message = ""}
end;


val num_CONV   = Num_conv.num_CONV
val INDUCT_TAC = Num_induct.INDUCT_TAC

end; (* numLib *)
