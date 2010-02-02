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

  include TheoryPP where type thm = KernelTypes.thm
                     and type hol_type = KernelTypes.hol_type
end


signature RawTheory =
sig

  include FinalTheory
          where type hol_type = KernelTypes.hol_type
            and type term     = KernelTypes.term
            and type thm      = KernelTypes.thm
  type witness  = KernelTypes.witness

  val incorporate_consts : string -> (string*hol_type)list -> unit
  val store_definition   : string * string list * witness * thm -> thm
  val store_type_definition : string * string * witness * thm -> thm

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
