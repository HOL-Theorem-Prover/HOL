(* ===================================================================== *)
(* FILE          : term.sig                                              *)
(* DESCRIPTION   : Simply typed lambda terms.                            *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* UPDATE        : October 94. Term signature implementation moved from  *)
(*                 symtab.sml, which is now gone.                        *)
(* Modified      : September 22, 1997, Ken Larsen                        *)
(* ===================================================================== *)

signature Term =
sig
  eqtype term

  val type_of      : term -> Type.hol_type
  val free_vars    : term -> term list
  val free_vars_lr : term -> term list
  val free_in      : term -> term -> bool
  val all_vars     : term -> term list
  val free_varsl   : term list -> term list
  val all_varsl    : term list -> term list
  val type_vars_in_term : term -> Type.hol_type list

  val term_lt      : term -> term -> bool
  val term_compare : term -> term -> order
  val genvar       : Type.hol_type -> term
  val genvars      : Type.hol_type -> int -> term list
  val variant      : term list -> term -> term

  (* Constructors and destructors *)
  val mk_var         : {Name : string, Ty : Type.hol_type} -> term
  val mk_primed_var  : {Name : string, Ty : Type.hol_type} -> term
  val mk_const       : {Name : string, Ty : Type.hol_type} -> term
  val list_mk_comb   : term * term list -> term
  val mk_comb        : {Rator : term, Rand : term} -> term
  val mk_abs         : {Bvar : term, Body : term} -> term
  val ty_antiq       : Type.hol_type -> term
  val dest_var       : term -> {Name : string, Ty : Type.hol_type}
  val dest_const     : term -> {Name : string, Ty : Type.hol_type}
  val dest_comb      : term -> {Rator : term, Rand : term}
  val dest_abs       : term -> {Bvar : term, Body : term}
  val dest_ty_antiq  : term -> Type.hol_type
  val is_var         : term -> bool
  val is_const       : term -> bool
  val is_comb        : term -> bool
  val is_abs         : term -> bool
  val is_ty_antiq    : term -> bool

  val rator : term -> term
  val rand  : term -> term
  val bvar  : term -> term
  val body  : term -> term
  val is_bvar : term -> bool

  (* Prelogic *)
  val aconv : term -> term -> bool
  val subst : (term,term) Lib.subst -> term -> term
  val inst  : (Type.hol_type,Type.hol_type) Lib.subst -> term -> term
  val beta_conv  : term -> term
  val match_term : term -> term ->
                  (term,term)Lib.subst * (Type.hol_type,Type.hol_type)Lib.subst

  (* Miscellaneous *)
  datatype lambda = VAR of {Name : string, Ty : Type.hol_type}
                  | CONST of {Name : string, Ty : Type.hol_type}
                  | COMB of {Rator : term, Rand : term}
                  | LAMB of {Bvar : term, Body : term};

  val dest_term : term -> lambda

  datatype fixity = Infix of int | Prefix | Binder

  val fixity_to_string : fixity -> string
  val const_decl : string -> {const:term, theory:string, place:fixity}

  (* Pretty printing *)
  type gravity = Portable_PrettyPrint.gravity
  type ppstream = Portable_PrettyPrint.ppstream
  type pparg = {boundvars:term list,depth:int,gravity:gravity}
                 -> term -> ppstream -> unit
  val pp_term : ppstream -> term -> unit
  val extend_pp_term : (pparg -> pparg) -> unit
  val reset_pp_term : unit -> unit
  val pp_raw_term : (term -> int) -> ppstream -> term -> unit

  (* Functor avoidance technique, via "one-time" references. *)
  val init : (string -> bool) ->
             ({Name:string, Ty:Type.hol_type} -> term) ->
             (string -> {const:term, theory:string, place:fixity})
             -> unit

  val pair_ops : (term -> {varstruct:term, body:term}) ->   (* dest_pabs *)
                 (term -> {fst:term, snd:term}) ->          (* dest_pair *)
                 (term -> term list) ->                    (* strip_pair *)
                 (unit -> (string * string) list) (* binder_restrictions *)
                 -> unit

  val Net_init : ((term -> {Bvar:term, Body:term}) ref) -> unit
  val Preterm_init : ({Name:string, Ty:Type.hol_type} -> term) ref (* Const *)
                      -> ({Rator:term, Rand:term} -> term) ref     (* Comb *)
                       -> unit

  val Theory_init : (string ref * Type.hol_type -> term) ref       (* Const *)
                 -> (term -> string ref * Type.hol_type) ref (* break_const *)
                    -> unit
  val TheoryPP_init : ((term -> unit) -> (term -> unit)) ref -> unit

  val Thm_init : (Type.hol_type -> term -> term -> term) ref
                 -> ({Rator:term, Rand:term} -> term) ref      (* Comb *)
                  -> ({Bvar:term, Body:term} -> term) ref      (* Abs *)
                   -> (int -> term) ref                        (* Bv *)
                    -> unit
  val minTheory_init: term -> unit

  (* Numeral treatment *)
  val is_numeral      : term -> bool
  val mk_numeral      : arbnum.num -> term
  val dest_numeral    : term -> arbnum.num
  val prim_mk_numeral : {mkCOMB       : {Rator:'a, Rand:'a} -> 'a,
                         mkNUM_CONST  : string -> 'a,
                         mkNUM2_CONST : string -> 'a} -> arbnum.num -> 'a
end;
