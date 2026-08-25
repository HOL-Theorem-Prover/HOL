signature LSPExtension = sig

val markServerStarted: unit -> unit
val serverRunning: unit -> bool

type posLC = int * int
type rangeLC = posLC * posLC
type range = int * int

type lines
val mkLineCounter: string -> lines
val getLineCol: lines -> int -> posLC
val fromLineCol: lines -> posLC -> int

type 'a tag
type plugin_data
val emptyPluginData: plugin_data
val getPluginData: plugin_data * 'a tag -> 'a option
val setPluginData: plugin_data * 'a tag * 'a option -> plugin_data

type 'a plugin = {
  name: string,
  init: 'a tag -> unit,
  beforeCompile: unit -> unit,
  afterCompile: range * 'a option -> 'a option }

type uplugin = {
  name: string,
  init: unit -> unit,
  beforeCompile: unit -> unit,
  afterCompile: range * plugin_data -> plugin_data }

exception DuplicatePlugin
val registerPlugin: bool -> 'a plugin -> 'a tag
val getPlugins: unit -> uplugin list
val registerInit: bool -> string -> (unit -> unit) -> unit

type location_link = {
  origin: rangeLC option,
  range: rangeLC,
  selRange: rangeLC,
  uri: string option }

type goto_def_context = {
  uri: string, lines: lines, plugins: plugin_data,
  fromFileLine: {file: string, line: int, origin: rangeLC option} -> location_link }

val gotoDefinition: (goto_def_context * int -> location_link list) ref

type hover = {markdown: string, range: rangeLC option}

type hover_context = {
  uri: string, lines: lines, plugins: plugin_data,
  ppToString: PrettyImpl.pretty -> string }

val hover: (hover_context * (int * int) -> hover list) ref

(* Hover inside a HOL quotation.  server.ML calls this after the
   default (SML) hover returns nothing and the cursor sits inside a
   PQuote span.  `quote` is the raw quotation body (no backticks);
   `quoteStart` is its file byte offset; `target` is the cursor's
   file byte offset (inside the quote).  Default no-op; the LSP
   runtime init installs a Preterm-based implementation. *)
val hoverQuotation:
  (hover_context *
   {quote: string, quoteStart: int, target: int} -> hover list) ref

(* Goal-state at cursor for `$/hol/goalState`.  Server locates the
   enclosing `Theorem NAME: … Proof … QED` block by scanning the file
   text and calls this hook with the raw statement quote and cursor
   position; the hook parses the quote (against the live HOL Context)
   and returns the goal-state to render.  Returns NONE if the cursor
   isn't inside a proof body or the quote can't be parsed. *)
type goal_state = {asms: string list, goal: string}
type goal_state_response = {
  theorem: string, step: int, goals: goal_state list,
  (* Rendered form of the whole state — HOL's own `pp_goalstate`
     pretty-print, matching the REPL's "N subgoals: … ⊨ …" layout
     (no turnstile, blank-line-separated assumptions, `----`
     separator).  Clients that just want to display the state
     verbatim should prefer this; `goals` remains for clients that
     want to render individual subgoals structurally. *)
  pretty: string,
  (* SOME msg when the walker gave up (e.g. wall-clock budget
     exceeded) or halted at a failed tactic.  On timeout `goals`
     and `pretty` are empty; on a failed tactic they hold the
     pre-fail state so the client can render both the failure
     signal and the state the walker halted at. *)
  error: string option,
  (* SOME (fileStart, fileEnd) when a specific leaf tactic
     failed — the file byte range the client should surface as a
     runtime diagnostic (LSP squiggle).  NONE when there is no
     failure or the failure has no natural byte range (e.g. a
     structural marker, or a timeout). *)
  failedRange: (int * int) option}
type theorem_context = {
  name: string,           (* theorem name, e.g. "foo" *)
  quote: string,          (* raw text of the theorem statement *)
  quoteStart: int,        (* file byte offset of the quote's start *)
  tacText: string,        (* raw text between `Proof` and `QED` *)
  tacStart: int,          (* file byte offset of `tacText` start *)
  cursor: int             (* cursor byte offset (file coords) *)
}
val goalStateAtPos:
  (hover_context * theorem_context -> goal_state_response option) ref

val fixupTheoremLink:
  ({start: int, stop: int, text: string, uri: string} ->
   {file: string, line: int} option) ref

val helpLookup: (string * (string -> bool) -> string list) ref

(* Given an SML identifier name (possibly dotted, e.g.
   "arithmeticTheory.ADD_COMM" or bare "plus_comm"), return a
   pretty-printed theorem statement if the name resolves to a theorem
   in the current DB.  Default no-op; the LSP runtime init installs a
   version that calls DB.lookup + Parse.thm_to_string. *)
val thmLookup: (string -> string option) ref

(* Called at the start of each LSP compile pass.  Intended to restore
   the HOL Context to a snapshot taken at LSP startup, so recompiles
   run against a clean state (no accumulated theorems / retired
   constants / stale DB entries).  Default is a no-op; installed by
   the LSP runtime init in tools-poly/hol.ML. *)
val resetForCompile: (unit -> unit) ref

(* Called at the start of each LSP compile pass, alongside
   `resetForCompile`.  The int-option argument is the buffer's
   current `minEditOffset` — the minimum byte offset of any pending
   edit — or NONE if no edit is pending.  Consumers use this to
   invalidate downstream cached state without discarding entries
   whose byte position is before the edit. *)
val notifyCompileStart: (int option -> unit) ref

(* Snapshot / restore of the per-compile state channels needed for
   mid-file recompile resume: the HOL Context, the Poly/ML loaded-
   modules set, and the LSP file-namespace layer (see
   `lsp/lsp_namespace.ML`).  `captureCompileSnap ()` runs at a dec
   boundary and returns a thunk that restores each channel when
   applied; the parsers and printers derived from the grammars travel
   in the Context, so nothing else needs resetting.
   `restoreCompileSnap` is
   a small indirection so callers can apply it uniformly.  Defaults
   are no-ops; installed by the LSP runtime init in tools-poly/hol.ML.
   Concrete type is exposed (rather than opaque) because the runtime
   wiring in `hol.ML` needs to construct one via `evalString`, which
   sees the compilation-environment view of the sig. *)
type compileSnap = unit -> unit
val captureCompileSnap: (unit -> compileSnap) ref
val restoreCompileSnap: (compileSnap -> unit) ref

(* ----------------------------------------------------------------------
   Deferred proofs — Phase A of the LSP's proof replay.

   Instead of running a tactic during elaboration, the prover hook
   enqueues a self-contained item and returns an oracle-tagged theorem,
   so elaboration stays fast and something else runs the proofs later.

   An item's `run` is opaque — `unit -> string option`, SOME on failure
   — because this structure sits below the kernel and cannot name
   `Context.t`, `goal` or `tactic`.  The hook closes over all three, so
   an item is independent of every other: the context is an immutable
   value and the tactic is already elaborated.  In particular a worker
   replaying one of these does *not* need the LSP namespace layer; that
   is only for compiling tactic *text*, which Phase A has already done.

   `deferProofs` is off by default, in which case the hook behaves
   exactly as it does today and skips the proof outright.
   ---------------------------------------------------------------------- *)
(* `run` replays the proof and reports what it established: `Proved`,
   `Failed` or `Diverged` (see proof_status below -- it cannot return the
   other two, which are statements about declarations the pool was never
   given). *)
(* ----------------------------------------------------------------------
   Status of a proof, for reporting back to the user.

   Two of these the pool cannot produce, because they say something
   about declarations the pool has never been given:

     Unseen   the text has not been elaborated at all, so we do not even
              know that its statement and tactic type-check.  This is
              everything past the compile frontier.
     Cheated  elaborated -- statement and tactic both type-check, in HOL
              and in SML respectively -- but no pool entry exists, so the
              theorem is being taken on trust.  This covers "never
              submitted" and "we stopped checking it" alike: from the
              user's point of view those are the same thing.  A cancelled
              proof therefore reverts to Cheated by having its entry
              dropped, which is right, because an edit above it means its
              recorded position is about to be stale.

   The remaining three are the pool's own:

     Checking a worker is on it
     Proved   the replay went through
     Failed   the replay ran and the proof did not go through.  Really a
              diagnostic rather than a resting state, carried here so
              status and diagnostic can be reported together.
     Diverged the replay went through, but produced a theorem the
              placeholder did not match -- see proof_outcome.  Everything
              elaborated below this declaration is suspect.

   So a caller assembling a display walks its own list of declarations
   and consults the pool: an entry gives one of the last three, and
   absence means Unseen or Cheated according to whether elaboration has
   reached that declaration.
   ---------------------------------------------------------------------- *)
datatype proof_status =
         Unseen | Cheated | Checking | Proved
       | Failed of string | Diverged of string
type proof_state = {site: string, offset: int, status: proof_status}

type deferred = {site: string, offset: int, run: unit -> proof_status}
val deferProofs: bool ref
val enqueueDeferred: deferred -> unit
val pendingDeferred: unit -> int
val clearDeferred: unit -> unit
(* Runs every queued item on this thread and returns those that failed,
   in the order they were enqueued.  Empties the queue first, so a
   failure part-way through cannot leave items to be run twice.  This is
   the sequential drain; the worker pool below is the parallel one. *)
val drainDeferred: unit -> {site: string, error: string} list
(* Empties the queue and hands back what was in it, for a caller that
   wants to run the items itself -- the worker pool does. *)
val takeDeferred: unit -> deferred list

(* The byte offset of the declaration currently being elaborated, set by
   the compile driver before each one.  The prover hook reads it when
   enqueueing, so a deferred proof knows where in the file it came from
   and the pool can decide whether an edit invalidates it.  A plain ref
   is enough: elaboration is single-threaded. *)
val currentProofOffset: int ref


(* Hooks installed by the LSP runtime (tools-poly/lsp/deferred_proofs.ML);
   defaults are inert so a non-LSP session behaves as before.

   - checkDeferred: hand the queued proofs to the worker pool.
   - proofStates: current status of everything the pool knows about.
   - cancelProofsAtOrAfter n: give up on any proof whose declaration
     starts at or after byte n.  An edit invalidates the proofs below
     it in the file and leaves the ones above alone, so this is what a
     compile pass calls with its minimum edit offset.
   - cancelAllProofs: give up on all of them. *)
val checkDeferred: (unit -> unit) ref
val proofStates: (unit -> proof_state list) ref
val cancelProofsAtOrAfter: (int -> unit) ref
(* Give up on just this declaration's proof, for an edit inside a
   Proof...QED body: the tactic is not run during the cheating pass,
   so what the declaration contributes downstream is unchanged and the
   proofs below it need not be disturbed. *)
val cancelProofAt: (int -> unit) ref
val cancelAllProofs: (unit -> unit) ref
(* The declaration the user is working on, by byte offset, or NONE.
   Its proof is held back rather than checked, since the goal-state
   walker is already replaying that tactic on every keystroke; it is
   checked at raised priority once the user moves on. *)
val setProofFocus: (int option -> unit) ref

end;
