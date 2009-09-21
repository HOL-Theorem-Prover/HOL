(* ===================================================================== *)
(* FILE          : hol88Lib.sig                                          *)
(* DESCRIPTION   : Signature for routines that provide a limited amount  *)
(*                 of hol88 compatibility. (To operate much as in hol88, *)
(*                 one would open Psyntax and hol88Lib.)                 *)
(*                                                                       *)
(* This interface is deprecated; please DO NOT USE in new code.          *)
(* ===================================================================== *)

signature hol88Lib =
sig
  include Abbrev

  type ('a,'b)hol88subst = ('b * 'a) list

  val match : term -> term -> (term * term) list * (hol_type * hol_type) list
  val assoc : ''a -> (''a * 'b) list -> ''a * 'b
  val rev_assoc : ''a -> ('b * ''a) list -> 'b * ''a
  val frees : term -> term list
  val GEN_ALL : thm -> thm
  val GEN_REWRITE_RULE : (conv -> conv) -> thm list -> thm list -> thm -> thm
  val GEN_REWRITE_TAC : (conv -> conv) -> thm list -> thm list -> tactic
  val variant : term list -> term -> term

  (*-------------------------------------------------------------------------
     Functions that generate and use Hol88 style substitutions. A Hol88
     substitution is a list of pairs

        [(M1,v1), ..., (Mk,vk)]

     which maps to the Hol98 substitution

        [{redex=v1, residue=M1}, ..., {redex=vk, residue=Mk}]
   -------------------------------------------------------------------------*)

  val match_type    : hol_type -> hol_type -> (hol_type,hol_type)hol88subst
  val subst         : (term,term)hol88subst -> term -> term
  val inst          : (hol_type,hol_type)hol88subst -> term -> term
  val match_term    : term -> term
                        -> (term,term)hol88subst * (hol_type,hol_type)hol88subst
  val SUBST         : (term,thm)hol88subst -> term -> thm -> thm
  val INST          : (term,term)hol88subst -> thm -> thm
  val INST_TYPE     : (hol_type,hol_type)hol88subst -> thm -> thm
  val INST_TY_TERM  : (term,term)hol88subst * (hol_type,hol_type)hol88subst
                        -> thm -> thm

end
