signature TotalDefn =
sig

  include Abbrev
  type defn = DefnBase.defn

   (* Support for automated termination proofs *)

   val guessR        : defn -> term list
   val proveTotal    : tactic -> defn -> defn * thm option


   (* Support for interactive termination proofs *)
   val WF_thms : unit -> thm list
   val export_WF_thm : string -> unit

   val termination_simps : unit -> thm list
   val termination_simpdb : unit -> (string,thm) Binarymap.dict
   val temp_exclude_termsimp  : string -> unit
   val exclude_termsimp  : string -> unit
   val temp_export_termsimp : string -> unit
   val export_termsimp : string -> unit
   val with_termsimps : thm list -> ('a -> 'b) -> ('a -> 'b)
   val termination_solve_simps : thm list ref


   val PRIM_WF_TAC        : thm list -> tactic
   val PRIM_TC_SIMP_CONV  : thm list -> conv
   val PRIM_TC_SIMP_TAC   : thm list -> thm list -> tactic
   val PRIM_WF_REL_TAC    : term quotation -> thm list -> thm list -> thm list -> tactic

   val size_eq_conv : conv
   val WF_TAC       : tactic
   val TC_SIMP_CONV : conv
   val TC_SIMP_TAC  : tactic
   val STD_TERM_TAC : tactic
   val WF_REL_TAC   : term quotation -> tactic

   (* Definitions with automated termination proof support *)

   val defnDefine  : tactic -> defn -> thm * thm option * thm option
   val primDefine  : defn -> thm * thm option * thm option
   val tailrecDefine: DB.thm_src_location -> string -> term quotation -> thm
   val located_tDefine : DB.thm_src_location -> string -> term quotation ->
                         tactic -> thm * thm option
   val tDefine     : string -> term quotation -> tactic -> thm * thm option
   val xDefine     : string -> term quotation -> thm * thm option
   val Define      : term quotation -> thm
   val multiDefine : term quotation -> thm list
   val qDefine     : string -> term quotation -> tactic option -> thm
   val located_qDefine : DB.thm_src_location -> string -> term quotation ->
                         tactic option -> thm
   datatype phase
        = PARSE of term quotation
        | BUILD of term
        | TERMINATION of defn

   type apidefn = (defn * thm option, phase * exn) Lib.verdict

   val apiDefine      : (defn->term list) -> tactic -> string * term -> apidefn
   val apiDefineq     : (defn->term list) -> tactic -> term quotation -> apidefn
   val std_apiDefine  : string * term -> apidefn
   val std_apiDefineq : term quotation -> apidefn

   val xDefineSchema  : string -> term quotation -> thm * thm option
   val DefineSchema   : term quotation -> thm

end
