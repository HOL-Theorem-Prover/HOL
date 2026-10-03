signature Refute_ModelFinder_Model = sig
  type term = Term.term
  type hol_type = Type.hol_type
  type nut = Refute_ModelFinder_Nut.nut
  type scope = Refute_ModelFinder_Scope.scope
  type raw_bound = Refute_Forl.raw_bound

  type replay_hint =
    {value : term,
     provenance : Refute_Cert_Model.provenance option}

  datatype replay_hole_display =
      DisplayUnknown
    | DisplayIrrelevant
    | DisplayUnrepresented
    | DisplayFunctionFallback

  datatype replay_hole_origin =
      AnyRepresentation
    | OptionalAbsent
    | IncompleteFunctionFallback
    | UnknownFunctionPoint
    | PartialSetMembership
    | UnrepresentedSetElement
    | FunctionDefault

  type replay_hole =
    {id : int,
     variable : term,
     display : replay_hole_display,
     origin : replay_hole_origin}

  type replay_sidecar = {holes : replay_hole list}

  type reconstruction =
    {bindings : (term * term) list,
     evals : (term * term) list,
     skolems : (string * term) list,
     consts : (term * string * term) list,
     types : (hol_type * term list * bool) list,
     codatatypes_ok : bool}

  datatype verdict = Keep of Refute_Core.counterexample | Drop

  type term_postprocessor = term -> term
  type term_postprocessor_snapshot
  val register_term_postprocessor :
    hol_type -> term_postprocessor -> unit
  val lookup_term_postprocessor :
    hol_type -> term_postprocessor option
  val snapshot_term_postprocessors : unit -> term_postprocessor_snapshot
  val postprocess_term : term_postprocessor_snapshot -> term -> term
  val register_frac_type_rat : unit -> unit
  (* Installed by default (see Refute.sml).  Idempotent, like
     [register_frac_type_rat]. *)
  val register_frac_type_real : unit -> unit
  (* Installed by default (see Refute.sml).  Idempotent, like
     [register_frac_type_rat]; unlike the frac registrations there is
     only one fmap display, valid at every [:'a |-> 'b] instance. *)
  val register_fmap_display : unit -> unit
  (* Installed by default (see Refute.sml).  Idempotent, like
     [register_fmap_display]; valid at every function type. *)
  val register_function_display : unit -> unit

  val reconstruct_both :
    {context : Refute_ModelFinder_HOL.mf_context,
     formats : (term option * int list) list,
     scope : scope,
     atoms : (hol_type option * string list) list,
     special_funs : Refute_ModelFinder_HOL.special_fun list,
     real_frees : term list,
     eval_terms : term list,
     free_names : nut list,
     sel_names : nut list,
     nonsel_names : nut list,
     rel_table : nut Refute_ModelFinder_Nut.NameTable.table,
     bounds : raw_bound list} ->
    {raw : reconstruction,
     certification : reconstruction,
     displayed : reconstruction,
     replay_hints : replay_hint list,
     replay_sidecar : replay_sidecar,
     postprocessors : term_postprocessor_snapshot}

  val model_report : reconstruction -> Refute_Core.model_report
  val display_counterexample :
    term_postprocessor_snapshot -> reconstruction ->
    Refute_Core.counterexample -> Refute_Core.counterexample
  val certification_env_with_holes :
    replay_sidecar -> (term * term) list -> (term * term) list option
  val genuine_means_genuine :
    {got_all_mono_user_axioms : bool,
     no_poly_user_axioms : bool,
     wfs : bool list,
     sound_finitizes : bool,
     total_consts : bool option} -> bool
  val try_again_reasons : string list -> string list
  val certify :
    {executable : bool,
     original : term,
     eval_terms : term list,
     reconstruction : reconstruction,
     certification : reconstruction,
     replay_sidecar : replay_sidecar,
     replay_hints : replay_hint list,
     cex : Refute_Core.counterexample,
     sound : bool,
     genuine_means_genuine : bool,
     reasons : string list,
     deadline : Time.time option} -> verdict
end
