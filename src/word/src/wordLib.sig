(* =====================================================================*)
(* FILE          : word_convs.sig                                       *)
(* DESCRIPTION   : Signature for word conversions and tactics           *)
(* AUTHOR	 : P Curzon 					        *)
(* DATE		 : June 1993						*)
(*                                                                      *)
(* =====================================================================*)

signature wordLib =
sig
  include Abbrev

  val word_CASES_TAC      :  term -> tactic
  val word_INDUCT_TAC     : tactic
  val RESQ_WORDLEN_TAC    : tactic
  val BIT_CONV            : conv
  val WSEG_CONV           : conv
  val PWORDLEN_CONV       : term list -> conv	
  val PWORDLEN_bitop_CONV : conv	
  val WSEG_WSEG_CONV      : term -> conv	
  val PWORDLEN_TAC        : term list -> tactic
end
