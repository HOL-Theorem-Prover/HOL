(*---------------------------------------------------------------------------
       Internal interfaces to HOL kernel structures.
 ---------------------------------------------------------------------------*)

signature RawThm =
sig
  type thm
  type tag      = Tag.tag
  type term     = KernelTypes.term
  type hol_type = KernelTypes.hol_type
  type 'a set   = 'a HOLset.set

  val tag           : thm -> tag
  val hyp           : thm -> term list
  val hypset        : thm -> term set
  val concl         : thm -> term
  val dest_thm      : thm -> term list * term
  val thm_frees     : thm -> term list
  val hyp_frees     : thm -> term set
  val hyp_tyvars    : thm -> hol_type set
  val ASSUME        : term -> thm
  val REFL          : term -> thm
  val BETA_CONV     : term -> thm
  val ABS           : term -> thm -> thm
  val DISCH         : term -> thm -> thm
  val MP            : thm -> thm -> thm
  val SUBST         : (term,thm)Lib.subst -> term -> thm -> thm
  val INST_TYPE     : (hol_type,hol_type)Lib.subst -> thm -> thm
  val ALPHA         : term -> term -> thm
  val MK_COMB       : thm * thm -> thm
  val AP_TERM       : term -> thm -> thm
  val AP_THM        : thm -> term -> thm
  val ETA_CONV      : term -> thm
  val SYM           : thm -> thm
  val TRANS         : thm -> thm -> thm
  val EQ_MP         : thm -> thm -> thm
  val EQ_IMP_RULE   : thm -> thm * thm
  val INST          : (term,term)Lib.subst -> thm -> thm
  val SPEC          : term -> thm -> thm
  val GEN           : term -> thm -> thm
  val GENL          : term list -> thm -> thm
  val EXISTS        : term * term -> thm -> thm
  val CHOOSE        : term * thm -> thm -> thm
  val CONJ          : thm -> thm -> thm
  val CONJUNCT1     : thm -> thm
  val CONJUNCT2     : thm -> thm
  val DISJ1         : thm -> term -> thm
  val DISJ2         : term -> thm -> thm
  val DISJ_CASES    : thm -> thm -> thm -> thm
  val NOT_INTRO     : thm -> thm
  val NOT_ELIM      : thm -> thm
  val CCONTR        : term -> thm -> thm
  val Beta          : thm -> thm
  val Eta           : thm -> thm
  val Mk_comb       : thm -> thm * thm * (thm -> thm -> thm)
  val Mk_abs        : thm -> term * thm * (thm -> thm)
  val Specialize    : term -> thm -> thm
  val GEN_ABS       : term option -> term list -> thm -> thm
  val mk_oracle_thm : string -> term list * term -> thm
  val add_tag       : tag * thm -> thm
  val mk_thm        : term list * term -> thm
  val mk_axiom_thm  : string ref * term -> thm
  val mk_defn_thm   : tag * term -> thm
  val disk_thm      : term vector
                       -> string list * 'a Portable.frag list list
                                      * 'a Portable.frag list -> thm
end;

signature RawTheoryPP =
sig
 type thm      = KernelTypes.thm
 type hol_type = KernelTypes.hol_type
 type ppstream = Portable.ppstream
 type num = Arbnum.num

 val pp_type : string -> string -> ppstream -> hol_type -> unit
 val pp_sig :
   (ppstream -> thm -> unit)
    -> {name        : string,
        parents     : string list,
        axioms      : (string * thm) list,
        definitions : (string * thm) list,
        theorems    : (string * thm) list,
        sig_ps      : (ppstream -> unit) option list}
    -> ppstream
    -> unit

 val pp_struct :
   {theory      : string*num*num,
    parents     : (string*num*num) list,
    types       : (string*int) list,
    constants   : (string*hol_type) list,
    axioms      : (string * thm) list,
    definitions : (string * thm) list,
    theorems    : (string * thm) list,
    struct_ps   : (ppstream -> unit) option list}
  -> ppstream
  -> unit
end


signature RawTheory =
sig
  type hol_type = KernelTypes.hol_type
  type term     = KernelTypes.term
  type thm      = KernelTypes.thm
  type witness  = KernelTypes.witness
  type ppstream = Portable.ppstream
  type thy_addon = {sig_ps    : (ppstream -> unit) option,
                    struct_ps : (ppstream -> unit) option}
  type num = Arbnum.num

  val new_type       : string * int -> unit
  val new_constant   : string * hol_type -> unit
  val new_axiom      : string * term -> thm
  val save_thm       : string * thm -> thm
  val delete_type    : string -> unit
  val delete_const   : string -> unit
  val delete_binding : string -> unit
  val current_theory : unit -> string
  val stamp          : string -> Time.time
  val parents        : string -> string list
  val ancestry       : string -> string list
  val types          : string -> (string * int) list
  val constants      : string -> term list
  val current_axioms : unit -> (string * thm) list
  val current_definitions : unit -> (string * thm) list
  val current_theorems : unit -> (string * thm) list
  val new_theory       : string -> unit
  val after_new_theory : (string * string -> unit) -> unit
  val adjoin_to_theory : thy_addon -> unit
  val export_theory    : unit -> unit
  val pp_thm           : (ppstream -> thm -> unit) ref
  val link_parents     : string*num*num -> (string*num*num)list -> unit
  val incorporate_types  : string -> (string*int) list -> unit
  val incorporate_consts : string -> (string*hol_type)list -> unit
  val uptodate_type      : hol_type -> bool
  val uptodate_term      : term -> bool
  val uptodate_thm       : thm -> bool
  val scrub              : unit -> unit
  val set_MLname         : string -> string -> unit
  val store_definition   : string * string list * witness * thm -> thm
  val store_type_definition : string * string * witness * thm -> thm
  val try_theory_extension : ('a->'b) -> 'a -> 'b
end


signature RawDefinition =
sig
  type term = KernelTypes.term
  type thm  = KernelTypes.thm

  val new_type_definition : string * thm -> thm
  val new_specification   : string * string list * thm -> thm
  val new_definition      : string * term -> thm
  val new_definition_hook : ((term -> term list * term) *
                             (term list * thm -> thm)) ref
  val new_specification_hook : (string list -> unit) ref
end

signature RawNet =
sig
  type 'a net
  type term = KernelTypes.term

  val empty     : 'a net
  val insert    : term * 'a -> 'a net -> 'a net
  val match     : term -> 'a net -> 'a list
  val index     : term -> 'a net -> 'a list
  val delete    : term * ('a -> bool) -> 'a net -> 'a net
  val filter    : ('a -> bool) -> 'a net -> 'a net
  val union     : 'a net -> 'a net -> 'a net
  val map       : ('a -> 'b) -> 'a net -> 'b net
  val itnet     : ('a -> 'b -> 'b) -> 'a net -> 'b -> 'b
  val size      : 'a net -> int
  val listItems : 'a net -> 'a list
  val enter     : term * 'a -> 'a net -> 'a net  (* for compatibility *)
  val lookup    : term -> 'a net -> 'a list      (* for compatibility *)
end
