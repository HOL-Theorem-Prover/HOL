(* =====================================================================*)
(* FILE          : gen_funs.sig                                         *)
(* DESCRIPTION   : This is the signature for the structure GenFuns.     *)
(*                                                                      *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories               *)
(* DATE          : 94.03.13                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1994 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

signature GenFuns =
  sig
   type hol_type = Type.hol_type
   type term = Term.term
   type thm = Thm.thm
   type conv = Abbrev.conv

    val CURRY_LEMMA : thm
    val LEFT_IMP_LIST_FORALL_CONV : conv
    val LIST_EXISTS_IMP_CONV : conv
    val REPEAT_UNDISCH : thm -> {hyps:term list, thm:thm}
    val UNCURRY_LEMMA : thm
    val abslist : term list -> term -> term
    val applist : term list -> term -> term
    val conj_map : (thm -> thm) -> thm -> thm
    val conj_map_term : (term -> 'a) -> term -> 'a list
    val curry_to_list : hol_type
                        -> {arg_types:hol_type list, cod_type:hol_type}
    val dest_appln : term -> {args:term list, func:term}
    val dest_exists_unique : term -> {Body:term, Bvar:term}
    val disj_map : (thm -> thm) -> thm -> thm
    val dom_cod : term -> {cod:hol_type, dom:hol_type}
    val dom_cod_ty : hol_type -> {cod:hol_type, dom:hol_type}
    val forall_map : (thm -> thm) -> thm -> thm
    val get_exists_term : term -> {base_t:term, vars:term list}
    val get_exists_unique_term : term -> {base_t:term, vars:term list}
    val get_forall_term : term -> {base_t:term, vars:term list}
    val get_quant_term : ('a -> {Body:'a, Bvar:'b})
                         -> 'a -> {base_t:'a, vars:'b list}
    val list_to_curry : {arg_types:hol_type list, cod_type:hol_type}
                        -> hol_type
    val mk_poly_comb : {Rand:term, Rator:term} -> term
    val one_one_lemma : thm
    val present_strings : string list -> string
  end;
