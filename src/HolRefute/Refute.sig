signature Refute = sig
  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type
  type goal = term list * term

  datatype certainty = datatype Refute_Core.certainty
  type model_report = Refute_Core.model_report
  type counterexample = Refute_Core.counterexample
  (* [NoCounterexample] says that the whole relevant space was covered and
     no counterexample is possible.  A clean search limited to non-covering
     bounds is [Unknown] and includes its frontier in the reasons.
     [Model] and [NoModel] are the distinct results of Kodkod model search;
     backend choice never changes the meaning of another constructor. *)
  datatype outcome = datatype Refute_Core.outcome
  include Refute_Config
    where type expectation = Refute_Core.expectation
      and type substrate_choice = Refute_Core.substrate_choice
      and type bound_mode = Refute_Core.bound_mode
  datatype requirement = datatype Refute_Core.requirement
  datatype goal_form = datatype Refute_Core.goal_form
  type instance = Refute_Core.instance
  type certainty_ceiling = Refute_Core.certainty_ceiling
  datatype backend_family = datatype Refute_Core.backend_family
  type witness_text = Refute_Core.witness_text
  type backend = Refute_Core.backend
  type custom_gen = Refute_Gen.custom_gen
  type rng = Refute_Gen.rng
  type term_postprocessor = term -> term

  datatype backend_choice =
      Exhaustive
    | Random
    | Narrowing
    | ModelFinder
    | RegisteredBackend of string

  datatype search =
      AllBackends
    | QuickcheckBackends
    | Only of backend_choice list

  type config_update = config -> config

  val refute        : config -> term -> outcome
  val refute_def    : term -> outcome
  val refute_with   : config_update list -> term -> outcome
  val refute_goal   : config -> goal -> outcome
  val refute_goal_with : config_update list -> goal -> outcome
  val refute_top    : unit -> outcome
  val try_refute    : config -> goal -> (string * outcome) option
  (* [NONE] derives a QC-only configuration from the stored one.  [SOME cfg]
     supplies the base configuration and preserves its backend selection.
     Every probe forces a sequential, quiet, abort-potential,
     expectation-free profile. *)
  val check_unused_assms :
    config option -> string * thm -> string * int list list option
  val find_unused_assms :
    config option -> string -> (string * int list list option) list
  val print_unused_assms : config option -> string option -> unit
  val quickcheck    : term -> outcome
  val model_refute  : term -> outcome
  (* Diagnostic tactics return the original goal unchanged.  The exact-config
     form honours every field.  The update form reads the stored configuration
     from the context the tactic is applied in, then applies its updates
     from left to right. *)
  val REFUTE_CONFIG_TAC : config -> Abbrev.tactic
  val REFUTE_TAC_WITH   : config_update list -> Abbrev.tactic
  val REFUTE_TAC        : Abbrev.tactic
  val QUICKCHECK_TAC    : Abbrev.tactic
  val NARROWING_TAC     : Abbrev.tactic
  val MODEL_REFUTE_TAC  : Abbrev.tactic

  (* Replaces a backend of the same name.  [certainty_ceiling] must bound
     what [run] can return: a search stops once a result reaches the best
     ceiling among the selected backends.  A nested Refute call from
     [run] raises, so the backend yields [Unknown]. *)
  val register_backend : backend -> unit
  val register_generator : hol_type -> custom_gen -> unit
  (* Registers a QC generator for every concrete instance of a type
     operator, built from constructor constants whose declared result type
     is [tyop] applied to distinct type variables (e.g. FEMPTY/FUPDATE for
     [:'a |-> 'b]).  Unlike [register_generator], nothing is stored per
     instance: [tyop] is matched on demand, so this fires for a type never
     previously seen.  The resulting generator always has
     [exhaustive = false].  [canonical], if present, rewrites a generated
     candidate for display by removing structure that a later part of the
     same candidate has overwritten; it never affects the term used for
     testing or certification, and need not identify every pair of terms
     that denote the same value. *)
  val register_generator_family :
    {tyop : {Thy : string, Tyop : string}, constructors : term list,
     canonical : term_postprocessor option} -> unit
  val register_term_postprocessor :
    hol_type -> term_postprocessor -> unit
  (* [witness = SOME thm] rules out generic shape defeats: [thm] must be
     [?x. x = C ... x ...] for a registered constructor [C], showing some
     value is cyclic.  For a type the datatype database already knows,
     the constructor list is separately cross-checked against it; beyond
     that it remains the caller's assertion.  See [README] for the exact
     shape. *)
  val register_codatatype :
    {tyop : {Thy : string, Tyop : string},
     case_const : term, constructors : term list, witness : thm option} ->
    unit
  val register_quotient :
    {qty : hol_type, rty : hol_type, abs : term, rep : term,
     equiv_thm : thm} -> unit
  val register_typedef :
    {ty : hol_type, abs : term, rep : term, absrep_thms : thm list} -> unit
  (* Validated structural descriptions stored in the current theory and
     inherited on import.  Export is rejected under a context pin or during
     a Refute call; register_* remains session-local.  Same-kind exports
     replace in ancestry delta order; incompatible kinds are rejected.
     A description whose symbols retire is dropped. *)
  val export_codatatype :
    {tyop : {Thy : string, Tyop : string},
     case_const : term, constructors : term list, witness : thm option} ->
    unit
  val export_quotient :
    {qty : hol_type, rty : hol_type, abs : term, rep : term,
     equiv_thm : thm} -> unit
  val export_typedef :
    {ty : hol_type, abs : term, rep : term, absrep_thms : thm list} -> unit
  (* Export exactly these generic operators, retaining earlier harvested
     proofs or discovering only the selected operators.  Deduplicates in
     input order; [] is a no-op.  Failure exports none of the selection.
     Frac and fmap are unsupported.  Built-in codata without retained
     inputs needs an explicit export_codatatype description. *)
  val export_registrations : hol_type list -> unit
  (* Sweeps every theory in [Theory.ancestry] once, in a canonical
     deterministic order, attempting typedef and quotient harvesting for
     every type operator those theories declare.  The lazy, demand-driven
     harvest remains the default; this is an opt-in alternative for a
     caller who would rather pay the scan upfront.  Returns only what this
     call newly registered - a type already registered, explicitly or by
     an earlier harvest, is not listed - so an immediate second call
     returns empty lists.  [theories_scanned] is this whole ancestry, not
     the (much narrower, per-operator) set of theories whose theorems were
     actually inspected. *)
  val harvest_registrations : unit ->
    {typedefs : hol_type list, quotients : hol_type list,
     theories_scanned : string list}
  (* Model-finder constant replacements; a [register_frac_type] row
     takes precedence over a [register_ersatz] one.  [rat] and [real] are
     registered already. *)
  val register_frac_type :
    {tyop : {Thy : string, Tyop : string},
     ersatz :
       {original : {Thy : string, Name : string},
        replacement : {Thy : string, Name : string}} list} -> unit
  val register_ersatz :
    {original : {Thy : string, Name : string},
     replacement : {Thy : string, Name : string}} -> unit
  val abstract_generator :
    {ty : hol_type, constructors : term list, pred : term option} -> unit
  (* The theorem attributes of the same names. *)
  val export_refute_simp : string -> unit
  val export_refute_psimp : string -> unit
  val export_refute_unfold : string -> unit

  val show_config : unit -> unit
  val upd_search : search -> config_update
  val apply_updates : config_update list -> config -> config
  (* Applies its updates to the stored configuration. *)
  val current_config : config_update list -> config
end
