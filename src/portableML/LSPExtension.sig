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
   boundary and returns a thunk that restores each channel and forces
   `Parse.invalidate_caches` when applied.  `restoreCompileSnap` is
   a small indirection so callers can apply it uniformly.  Defaults
   are no-ops; installed by the LSP runtime init in tools-poly/hol.ML.
   Concrete type is exposed (rather than opaque) because the runtime
   wiring in `hol.ML` needs to construct one via `evalString`, which
   sees the compilation-environment view of the sig. *)
type compileSnap = unit -> unit
val captureCompileSnap: (unit -> compileSnap) ref
val restoreCompileSnap: (compileSnap -> unit) ref

end;
