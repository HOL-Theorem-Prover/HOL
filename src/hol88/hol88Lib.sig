(* ===================================================================== *)
(* FILE          : hol88Lib.sig                                          *)
(* DESCRIPTION   : Signature for routines that provide hol88             *)
(*                 compatibility.                                        *)
(*                                                                       *)
(* ===================================================================== *)

signature hol88Lib =
sig
  include Abbrev

  type ('a,'b)hol88subst = ('b * 'a) list

  val setify : ''a list -> ''a list
  val find : ('a -> bool) -> 'a list -> 'a
  val match : term -> term -> (term * term) list * (hol_type * hol_type) list
  val prove_thm : string * term * tactic -> thm
  val PROVE : term * tactic -> thm
  val string_of_int : int -> string
  val int_of_string : string -> int
  val save : string -> bool
  val assoc : ''a -> (''a * 'b) list -> ''a * 'b
  val rev_assoc : ''a -> ('b * ''a) list -> 'b * ''a
  val inst_type : (hol_type * hol_type) list -> hol_type -> hol_type
  val frees : term -> term list
  val freesl : term list -> term list
  val tyvars : term -> hol_type list
  val tyvarsl : term list -> hol_type list
  val conjuncts : term -> term list
  val disjuncts : term -> term list
  val GEN_ALL : thm -> thm
  val new_axiom : (string*term) -> thm
  val new_prim_rec_definition : string * term -> thm
  val new_infix_prim_rec_definition : string * term * int -> thm
  val flat : 'a list list -> 'a list
  val forall : ('a -> bool) -> 'a list -> bool
  val ancestry : unit -> string list
  val CB :('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
  val KI :'a -> 'b -> 'b
  val oo :('a * 'b -> 'c) * (('d -> 'a) * ('d -> 'b)) -> 'd -> 'c
  val Co : ('a -> 'b -> 'c) * ('d -> 'a) -> 'b -> 'd -> 'c
  val replicate :'a -> int -> 'a list
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

  val pair2recd     : 'b * 'a -> {redex:'a,residue:'b}
  val recd2pair     : {redex:'a,residue:'b} -> 'b * 'a
  val hol88subst_of : ('a,'b)subst -> ('a,'b)hol88subst
  val subst_of      : ('a,'b)hol88subst -> ('a,'b)subst

  val type_subst    : (hol_type,hol_type)hol88subst -> hol_type -> hol_type
  val match_type    : hol_type -> hol_type -> (hol_type,hol_type)hol88subst
  val subst         : (term,term)hol88subst -> term -> term
  val inst          : (hol_type,hol_type)hol88subst -> term -> term
  val subst_occs    : int list list -> (term,term)hol88subst -> term -> term
  val match_term    : term -> term 
                       -> (term,term)hol88subst * (hol_type,hol_type)hol88subst
  val SUBST         : (term,thm)hol88subst ->term -> thm -> thm
  val INST          : (term,term)hol88subst -> thm -> thm
  val INST_TYPE     : (hol_type,hol_type)hol88subst -> thm -> thm
  val SUBST_CONV    : (term,thm)hol88subst -> term -> term -> thm
  val INST_TY_TERM  : (term,term)hol88subst * (hol_type,hol_type)hol88subst
                        -> thm -> thm

end;
