(*===========================================================================
== LIBRARY:     reduce (Part I)                                            ==
==                                                                         ==
== DESCRIPTION: Conversions for reducing boolean expressions.              ==
==                                                                         ==
== AUTHOR:      John Harrison                                              ==
==              University of Cambridge Computer Laboratory                ==
==              New Museums Site                                           ==
==              Pembroke Street                                            ==
==              Cambridge CB2 3QG                                          ==
==              England.                                                   ==
==                                                                         ==
==              jrh@cl.cam.ac.uk                                           ==
==                                                                         ==
== DATE:        18th May 1991                                              ==
==                                                                         ==
== TRANSLATOR:  Kim Dam Petersen (kimdam@tfl.dk)                           ==
============================================================================*)

structure Boolconv :> Boolconv =
struct

open HolKernel boolTheory Drule Rewrite Parse
infix |->;

val (Type,Term) = parse_from_grammars boolTheory.bool_grammars
fun -- q x = Term q
fun == q x = Type q

val type_of = Term.type_of;
val aconv = Term.aconv;
val rator = Term.rator;

val T = Term`T`
and F = Term`F`
and alpha = Type`:'a`
and notop = Term`$~`
and andop = Term`$/\`
and orop  = Term`$\/`
and impop = Term`$==>`
and zv    = Term`z:bool`
and beqop = Term`$= :bool->bool->bool`;


fun failwith function =
 raise Feedback.HOL_ERR{origin_structure = "Boolconv",
                         origin_function = function,
                         message = ""};

(*-----------------------------------------------------------------------*)
(* dest_op - Split application down spine, checking head operator        *)
(*-----------------------------------------------------------------------*)

fun dest_op opr tm =
    let val (opr',arg) = boolLib.strip_comb tm
    in
	if (opr=opr') then arg else failwith "dest_op"
    end;

(*-----------------------------------------------------------------------*)
(* NOT_CONV "~F"  = |-  ~F = T                                           *)
(* NOT_CONV "~T"  = |-  ~T = F                                           *)
(* NOT_CONV "~~t" = |- ~~t = t                                           *)
(*-----------------------------------------------------------------------*)

val NOT_CONV =
  let val [c1,c2,c3] = CONJUNCTS
	(Tactical.prove((--`(~T = F) /\ (~F = T) /\ (!t. ~~t = t)`--),
	       REWRITE_TAC[NOT_CLAUSES]))
  in
   fn tm =>
    case (dest_op notop tm)
     of [xn] =>
	(if xn = T then c1 else
         if xn = F then c2
         else case (dest_op notop xn)
               of [xn] => SPEC xn c3
		|    _ => failwith "NOT_CONV")
      | _ => failwith "NOT_CONV"
    end;

(*-----------------------------------------------------------------------*)
(* AND_CONV "T /\ t" = |- T /\ t = t                                     *)
(* AND_CONV "t /\ T" = |- t /\ T = t                                     *)
(* AND_CONV "F /\ t" = |- F /\ t = F                                     *)
(* AND_CONV "t /\ F" = |- t /\ F = F                                     *)
(* AND_CONV "t /\ t" = |- t /\ t = t                                     *)
(*-----------------------------------------------------------------------*)

val AND_CONV =
 let val [c1,c2,c3,c4,c5] = CONJUNCTS
       (Tactical.prove
        (Term`(!t. T /\ t = t) /\ (!t. t /\ T = t) /\
              (!t. F /\ t = F) /\ (!t. t /\ F = F) /\ (!t. t /\ t = t)`,
	       REWRITE_TAC[AND_CLAUSES]))
 in
  fn tm =>
   case (dest_op andop tm)
    of [xn,yn] =>
       (if xn = T then SPEC yn c1 else
        if yn = T then SPEC xn c2 else
        if xn = F then SPEC yn c3 else
        if yn = F then SPEC xn c4 else
        if xn = yn then SPEC xn c5 else
        if aconv xn yn
        then SUBST [zv |-> ALPHA xn yn]
		 (mk_comb{Rator=mk_comb{Rator=beqop,
                    Rand=mk_comb{Rator=
                     mk_comb{Rator=andop,Rand=xn}, Rand=zv}}, Rand=xn})
		 (SPEC xn c5)
	else failwith "AND_CONV")
     | _ => failwith "AND_CONV"
 end;

(*-----------------------------------------------------------------------*)
(* OR_CONV "T \/ t" = |- T \/ t = T                                      *)
(* OR_CONV "t \/ T" = |- t \/ T = T                                      *)
(* OR_CONV "F \/ t" = |- F \/ t = t                                      *)
(* OR_CONV "t \/ F" = |- t \/ F = t                                      *)
(* OR_CONV "t \/ t" = |- t \/ t = t                                      *)
(*-----------------------------------------------------------------------*)

val OR_CONV =
 let val [c1,c2,c3,c4,c5] = CONJUNCTS
	(Tactical.prove
         (Term`(!t. T \/ t = T) /\ (!t. t \/ T = T) /\ (!t. F \/ t = t) /\
		   (!t. t \/ F = t) /\ (!t. t \/ t = t)`,
	  REWRITE_TAC[OR_CLAUSES]))
 in
 fn tm =>
   case (dest_op orop tm)
    of [xn,yn] =>
       (if xn = T then SPEC yn c1 else
        if yn = T then SPEC xn c2 else
        if xn = F then SPEC yn c3 else
        if yn = F then SPEC xn c4 else
        if xn = yn then SPEC xn c5 else
        if aconv xn yn
        then SUBST [zv |-> ALPHA xn yn]
                   (mk_comb{Rator=mk_comb{Rator= beqop,
                    Rand=mk_comb{Rator= mk_comb{Rator= orop,Rand= xn},
			Rand= zv}}, Rand= xn})
		   (SPEC xn c5)
       else failwith "OR_CONV")
    | _ => failwith "OR_CONV"
 end;

(*-----------------------------------------------------------------------*)
(* IMP_CONV "T ==> t" = |- T ==> t = t                                   *)
(* IMP_CONV "t ==> T" = |- t ==> T = T                                   *)
(* IMP_CONV "F ==> t" = |- F ==> t = T                                   *)
(* IMP_CONV "t ==> F" = |- t ==> F = ~t                                  *)
(* IMP_CONV "t ==> t" = |- t ==> t = T                                   *)
(*-----------------------------------------------------------------------*)

val IMP_CONV =
 let val [c1,c2,c3,c4,c5] = CONJUNCTS
	(Tactical.prove(
          Term`(!t. (T ==> t) = t) /\ (!t. (t ==> T) = T) /\
               (!t. (F ==> t) = T) /\ (!t. (t ==> F) = ~t) /\
               (!t. (t ==> t) = T)`, REWRITE_TAC[IMP_CLAUSES]))
 in
 fn tm =>
  case (dest_op impop tm)
   of [xn,yn] =>
      (if xn = T then SPEC yn c1 else
       if yn = T then SPEC xn c2 else
       if xn = F then SPEC yn c3 else
       if yn = F then SPEC xn c4 else
       if xn = yn then SPEC xn c5 else
       if aconv xn yn
       then SUBST [zv |-> ALPHA xn yn]
		   (mk_comb{Rator= mk_comb{Rator= beqop,
                     Rand=mk_comb{Rator= mk_comb{Rator= impop, Rand= xn},
		                  Rand= zv}}, Rand= T})
		  (SPEC xn c5)
       else failwith "IMP_CONV")
   | _ => failwith "IMP_CONV"
 end;

(*-----------------------------------------------------------------------*)
(* BEQ_CONV "T = t" = |- T = t = t                                       *)
(* BEQ_CONV "t = T" = |- t = T = t                                       *)
(* BEQ_CONV "F = t" = |- F = t = ~t                                      *)
(* BEQ_CONV "t = F" = |- t = F = ~t                                      *)
(* BEQ_CONV "t = t" = |- t = t = T                                       *)
(*-----------------------------------------------------------------------*)

val BEQ_CONV =
 let val [c1,c2,c3,c4,c5] = CONJUNCTS
       (Tactical.prove
        (Term`(!t. (T = t) = t) /\ (!t. (t = T) = t) /\ (!t. (F = t) = ~t) /\
		   (!t. (t = F) = ~t) /\ (!t:bool. (t = t) = T)`,
	       REWRITE_TAC[EQ_CLAUSES]))
 in
 fn tm =>
  case (dest_op beqop tm)
   of [xn,yn] =>
      (if xn = T then SPEC yn c1 else
       if yn = T then SPEC xn c2 else
       if xn = F then SPEC yn c3 else
       if yn = F then SPEC xn c4 else
       if xn = yn then SPEC xn c5 else
       if aconv xn yn then EQT_INTRO (ALPHA xn yn) else failwith "BEQ_CONV")
   | _ => failwith "BEQ_CONV"
 end;

(*-----------------------------------------------------------------------*)
(* COND_CONV "F => t1 | t2" = |- (T => t1 | t2) = t2                     *)
(* COND_CONV "T => t1 | t2" = |- (T => t1 | t2) = t1                     *)
(* COND_CONV "b => t  | t"  = |- (b => t | t)   = t                      *)
(*-----------------------------------------------------------------------*)

val COND_CONV =
 let val [c1,c2,c3] = CONJUNCTS
	(Tactical.prove(Term`(!t1 t2. (if T then t1 else t2) = (t1:'a)) /\
	                     (!t1 t2. (if F then t1 else t2) = (t2:'a)) /\
		             (!b t.   (if b then t else t) = (t:'a))`,
	       REWRITE_TAC[COND_CLAUSES, COND_ID]))
 in
 fn tm =>
  case (Rsyntax.dest_cond tm handle HOL_ERR _ => failwith "COND_CONV")
   of {cond=b, larm=t1, rarm=t2} =>
      if b = T then SPECL [t1,t2] (INST_TYPE[alpha |-> type_of t1] c1) else
      if b = F then SPECL [t1,t2] (INST_TYPE[alpha |-> type_of t1] c2) else
      if t1=t2 then SPECL [b,t1]  (INST_TYPE[alpha |-> type_of t1] c3) else
      if aconv t1 t2
      then TRANS (AP_TERM (rator tm) (ALPHA t2 t1))
                 (SPECL [b, t1] (INST_TYPE [alpha |-> type_of t1] c3))
      else failwith "BEQ_CONV"

 end;

end
