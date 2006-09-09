(* =====================================================================*)
(* FILE		: monosetScript.sml                                     *)
(* DESCRIPTION  : Creates a new monoset including the EVERY operator, 	*)
(*                 and uses it to define a relation and its strong	*)
(*                 induction theorem.					*)
(*									*)
(* AUTHOR	: Peter Vincent Homeier					*)
(* DATE		: 2006.09.08						*)
(* =====================================================================*)

(*
  app load ["IndDefLib", "Datatype", "clTheory"] ;
*)

structure monosetScript =
struct

open HolKernel Parse boolLib listLib listTheory IndDefLib IndDefRules;

infix ## |-> THEN THENL THENC ORELSE; infixr 3 -->;


(* --------------------------------------------------------------------- *)
(* Open a new theory.							 *)
(* --------------------------------------------------------------------- *)

val _ = new_theory"monoset";

(* --------------------------------------------------------------------- *)
(* We intend to add a new monotonic operator to the standard monoset	 *)
(* provided as 'InductiveDefinition.bool_monoset'.  A monotonic operator *)
(* is a (possibly curried) operator which yields a boolean result, some  *)
(* of whose operands also yield boolean results, and where the set of    *)
(* operand values for which the operator yields true only increases      *)
(* ("monotonically") when the operands (considered as sets) increase.    *)
(*									 *)
(* The standard monoset supports the following monotonic operators:      *)
(* 	/\   \/   ?   !   ==>   ~   <abstraction, or "lambda">		 *)
(*									 *)
(* The following script illustrates how to add a new monotonic operator, *)
(* in this case the EVERY operator from the list theory, including the   *)
(* ability to handle tupled abstractions as arguments to EVERY.		 *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* The following theorem states that EVERY is monotonic.		 *)
(* --------------------------------------------------------------------- *)

val MONO_EVERY = store_thm
  ("MONO_EVERY",
    ``(!x:'a. MEM x l ==> (P x ==> Q x)) ==>
      (EVERY P l ==> EVERY Q l)``,
    Induct_on `l`
    THEN REWRITE_TAC[EVERY_DEF,MEM,DISJ_IMP_THM]
    THEN GEN_TAC
    THEN CONV_TAC (ONCE_DEPTH_CONV FORALL_AND_CONV)
    THEN ONCE_REWRITE_TAC[CONJ_SYM]
    THEN STRIP_TAC
    THEN HO_MATCH_MP_TAC MONO_AND
    THEN CONJ_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THENL [ FIRST_ASSUM MATCH_ACCEPT_TAC, REFL_TAC ]
   );

(* --------------------------------------------------------------------- *)
(* We will use this theorem in constructing a tactic to prove that	 *)
(* EVERY expressions are monotonic.					 *)
(* --------------------------------------------------------------------- *)

val PBETA_CONV = PairRules.PBETA_CONV;

fun GEN_CONV conv :conv = fn tm =>
   let val (v,bdy) = dest_forall tm
   in RAND_CONV (ABS_CONV conv) tm
   end;

fun REPEAT_GEN_CONV (conv:conv) :conv = fn tm =>
   if is_forall tm then GEN_CONV (REPEAT_GEN_CONV conv) tm
   else conv tm;

val TUPLE_GEN_TAC :tactic = fn (asl,gl) =>
   let val (v,bdy) = (dest_forall) gl
       val Q = (rator o rand o rand) bdy
       val (tpl,bdy) = pairLib.dest_pabs Q handle HOL_ERR _ => (v,bdy)
   in pairLib.TUPLE_TAC tpl
      THEN CONV_TAC (REPEAT_GEN_CONV (RAND_CONV
              (RAND_CONV (TRY_CONV PBETA_CONV) THENC
               RATOR_CONV(RAND_CONV (TRY_CONV PBETA_CONV)))))
   end (asl,gl);

val MONO_EVERY_TAC =
    HO_MATCH_MP_TAC MONO_EVERY
    THEN TUPLE_GEN_TAC
    THEN CONV_TAC (REPEAT_GEN_CONV (RAND_CONV
           (RAND_CONV(TRY_CONV PBETA_CONV) THENC
            RATOR_CONV(RAND_CONV(TRY_CONV PBETA_CONV)))));

(* --------------------------------------------------------------------- *)
(* To create the new monoset, we add a pair to the front of the		 *)
(* standard list.  The pair contains the name of the constant as a	 *)
(* string, and also the tactic to prove monotonicity.			 *)
(* --------------------------------------------------------------------- *)

val every_monoset = ("EVERY", MONO_EVERY_TAC)
                     :: InductiveDefinition.bool_monoset;

(* --------------------------------------------------------------------- *)
(* Now we apply the new monoset to an example definition.		 *)
(* --------------------------------------------------------------------- *)

val _ = print "Testing inductive definitions - extended monoset\n"

val (EC_rules, EC_ind, EC_cases) = prim_Hol_reln every_monoset ``
  (EC r []) /\
  (!a ps. EC r ps ==> EC r ((a,a)::ps)) /\
  (!ps. EVERY (\(a:'a,b). r a b) ps ==> EC r ps)
``;

val strongEC = prim_derive_strong_induction every_monoset (EC_rules, EC_ind);


(* --------------------------------------------------------------------- *)
(* End of example.							 *)
(* --------------------------------------------------------------------- *)

val _ = export_theory();

end;
