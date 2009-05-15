signature TotalDefn =
sig

  include Abbrev

   (* Support for automated termination proofs *)

   val guessR        : defn -> term list
   val proveTotal    : tactic -> defn -> defn * thm option


   (* Support for interactive termination proofs *)

   val WF_thms : thm list ref
   val termination_simps : thm list ref

   val PRIM_WF_TAC        : thm list -> tactic
   val PRIM_TC_SIMP_CONV  : thm list -> conv
   val PRIM_TC_SIMP_TAC   : thm list -> tactic
   val PRIM_WF_REL_TAC    : term quotation -> thm list -> thm list -> tactic

   val WF_TAC       : tactic
   val TC_SIMP_CONV : conv
   val TC_SIMP_TAC  : tactic
   val STD_TERM_TAC : tactic
   val WF_REL_TAC   : term quotation -> tactic

   (* Definitions with automated termination proof support *)

   val defnDefine  : tactic -> defn -> thm * thm option * thm option
   val primDefine  : defn -> thm * thm option * thm option
   val tDefine     : string -> term quotation -> tactic -> thm
   val xDefine     : string -> term quotation -> thm
   val Define      : term quotation -> thm
   val multiDefine : term quotation -> thm list
   datatype phase 
        = PARSE of term quotation
        | BUILD of term
        | TERMINATION of defn

   type apidefn = (defn * thm option, phase * exn) Lib.verdict

   val apiDefine      : (defn->term list) -> tactic -> string * term -> apidefn
   val apiDefineq     : (defn->term list) -> tactic -> term quotation -> apidefn
   val std_apiDefine  : string * term -> apidefn
   val std_apiDefineq : term quotation -> apidefn

   val xDefineSchema  : string -> term quotation -> thm
   val DefineSchema   : term quotation -> thm

end
