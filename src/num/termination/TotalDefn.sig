signature TotalDefn =
sig

  include Abbrev
  type defn = DefnBase.defn
  type simpset = simpLib.simpset

   (* Support for automated termination proofs *)

   val guessR        : defn -> term list
   val proveTotal    : tactic -> defn -> defn * thm option


   (* Support for interactive termination proofs *)
   val WF_thms       : unit -> thm list
   val export_WF_thm : string -> unit
   val PRIM_WF_TAC   : thm list -> tactic
   val WF_TAC        : tactic

   val termination_simps : unit -> thm list
   val termination_simpdb : unit -> thm Symtab.table
   val temp_exclude_termsimp  : string -> unit
   val exclude_termsimp  : string -> unit
   val with_termsimps : thm list -> ('a -> 'b) -> ('a -> 'b)
   val export_termsimp : string -> unit
   val temp_export_termsimp : string -> unit

   val termination_solve_simps : unit -> thm list
   val export_termsolve_simp : string -> unit

   val termination_ss  : unit -> simpset
   val TC_SIMP_TAC     : simpset -> thm list -> tactic
   val WF_REL_TAC      : term quotation -> tactic

   (* Definitions with automated termination proof support *)

   val defnDefine  : defn -> thm * thm option * thm option
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
                         tactic option -> Context.t -> thm

   (* Staged explicit termination proofs. The handle and proof state can
      be saved in a heap; no source expansion or preparation is repeated.
      The caller owns the theory until finish/abort: do not interleave
      unrelated theory changes or another preparation in that context. *)
   type prepared_definition
   val prepare_tDefine : DB.thm_src_location -> string -> term quotation ->
                         prepared_definition
   val prepare_qDefine : DB.thm_src_location -> string -> term quotation ->
                         prepared_definition
   val termination_goal : prepared_definition -> (string * goal) option
   val with_prepared_definition :
       prepared_definition -> ('a -> 'b) -> 'a -> 'b
   val finish_definition : prepared_definition -> thm option ->
                           thm * thm option
   val abort_definition : prepared_definition -> unit
   (* Override explicit termination execution while retaining the native
      definition entry point, quotation expansion and SML bindings. The
      driver returns a proof of termination_goal (NONE for a trivial
      definition); the entry point finishes the definition afterwards. *)
   val with_termination_driver :
       (prepared_definition -> tactic -> thm option) ->
       ('a -> 'b) -> 'a -> 'b
   datatype phase
        = PARSE of term quotation
        | BUILD of term
        | TERMINATION of defn

   type apidefn = (defn * thm option, phase * exn) Lib.verdict

   val apiDefine      : (defn->term list) -> (unit -> tactic) ->
                        string * term -> apidefn
   val apiDefineq     : (defn->term list) -> (unit -> tactic) ->
                        term quotation -> apidefn
   val std_apiDefine  : string * term -> apidefn
   val std_apiDefineq : term quotation -> apidefn

   val xDefineSchema  : string -> term quotation -> thm * thm option
   val DefineSchema   : term quotation -> thm

end
