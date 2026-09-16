structure LSPExtension :> LSPExtension =
struct

val running = ref false
fun serverRunning () = !running

type posLC = int * int
type rangeLC = posLC * posLC
type range = int * int

(* Which unit a `character' on the wire counts in.  The server's own
   offsets are bytes, so utf-8 is what it would rather speak, but the
   client picks: LSP has the server choose from the client's
   `general.positionEncodings', and one that cannot take utf-8 gets
   utf-16 code units.  Set once, from the initialize request, before any
   position crosses the wire; `false' is bytes. *)
val utf16 = ref false
fun setUTF16Positions b = utf16 := b
fun utf16Positions () = !utf16

(* Line starts, kept with the text they index: converting a byte offset
   to a utf-16 column means counting the characters in between, so the
   text has to be here rather than at each of the ~40 call sites. *)
type lines = {starts: int vector, text: string}
fun mkLineCounter str = let
  fun loop i ls =
    if i >= String.size str then Vector.fromList (List.rev ls)
    else
      let val c = String.sub (str, i)
      in loop (i+1) (if c = #"\n" then i+1::ls else ls) end
  in {starts = loop 0 [], text = str} end

(* How many bytes the UTF-8 sequence starting at `c' occupies, and how
   many utf-16 code units it encodes to -- two for anything outside the
   BMP, which is a surrogate pair.  A continuation byte or an invalid
   leading byte counts as one of each, so malformed input advances and
   cannot loop.

   Deliberately not `UTF8.getChar', which decodes properly: it raises
   `BadUTF8' on malformed input, and this runs on buffer text that is
   mid-edit, where a half-typed character must not cost the whole
   answer.  `UTF8' is in any case out of reach here -- it is
   Holmake-built in src/portableML, and this file is compiled into
   bin/hol at bootstrap. *)
fun seqLen c = let val b = Char.ord c in
    if b < 0x80 then (1, 1)
    else if b < 0xC0 then (1, 1)
    else if b < 0xE0 then (2, 1)
    else if b < 0xF0 then (3, 1)
    else if b < 0xF8 then (4, 2)
    else (1, 1)
  end

(* utf-16 code units in text[bol..stop). *)
fun utf16Col (text, bol, stop) = let
  val n = String.size text
  fun go (i, acc) =
    if i >= stop orelse i >= n then acc
    else let val (bs, us) = seqLen (String.sub (text, i))
         in go (i + bs, acc + us) end
  in go (bol, 0) end

(* Byte offset of the `col'-th utf-16 code unit after `bol'.  Stops at
   the end of the line: a client counting in the wrong unit, or a
   position past the last character, then lands at the line end rather
   than somewhere in the next line. *)
fun utf16Byte (text, bol, col) = let
  val n = String.size text
  fun go (i, seen) =
    if seen >= col orelse i >= n orelse String.sub (text, i) = #"\n" then i
    else let val (bs, us) = seqLen (String.sub (text, i))
         in go (i + bs, seen + us) end
  in go (bol, 0) end

fun partitionPoint len pred = let
  fun loop start len =
    if len = 0 then start
    else let
      val half = len div 2
      val middle = start + half
      in
        if pred middle
        then loop (middle + 1) (len - (half + 1))
        else loop start half
      end
  in loop 0 len end

fun lineOf starts index =
  partitionPoint (Vector.length starts)
                 (fn i => Vector.sub (starts, i) <= index)
fun bolOf starts line = if line = 0 then 0 else Vector.sub (starts, line - 1)

fun getLineCol {starts, text} index = let
  val line = lineOf starts index
  val bol = bolOf starts line
  in (line, if !utf16 then utf16Col (text, bol, index) else index - bol) end

fun fromLineCol {starts, text} (line, col) = let
  val bol = bolOf starts line
  in if !utf16 then utf16Byte (text, bol, col) else bol + col end

fun getLineColBytes {starts, text} index = let
  val line = lineOf starts index
  in (line, index - bolOf starts line) end

fun fromLineColBytes {starts, text} (line, col) = bolOf starts line + col

(* Binarymap (rather than Symtab/Table) here because LSPExtension is
   `use`d directly by tools-poly/poly/poly-init2.ML at bootstrap, before
   any of src/portableML's Holmake-built modules (Symtab, Table, ...)
   are available. *)
type plugin_data = (string, UniversalType.t) Binarymap.dict
val emptyPluginData = Binarymap.mkDict String.compare

type 'a tag = string * ('a -> UniversalType.t) * (UniversalType.t -> 'a)

fun getPluginData (map, (name, _, proj)) =
    Option.map proj (Binarymap.peek (map, name))
fun setPluginData (map, (name, inj, _), SOME v) =
    Binarymap.insert (map, name, inj v)
  | setPluginData (map, (name, _, _), NONE) =
    #1 (Binarymap.remove (map, name)) handle NotFound => map

type reuse = {fromByte: int, bytes: int, lines: int}

type 'a plugin = {
  name: string,
  init: 'a tag -> unit,
  beforeCompile: unit -> unit,
  afterCompile: range * 'a option -> 'a option,
  reuseFrom: reuse -> 'a option -> 'a option -> 'a option }

type uplugin = {
  name: string,
  init: unit -> unit,
  beforeCompile: unit -> unit,
  afterCompile: range * plugin_data -> plugin_data,
  reuseFrom: reuse -> plugin_data -> plugin_data -> plugin_data }

val plugins = ref []

fun inject (proj, inj)
           {name, init, beforeCompile, afterCompile, reuseFrom} = let
  val tag = (name, proj, inj)
  in {
    name = name, init = fn () => init tag,
    beforeCompile = beforeCompile,
    afterCompile = fn (r, map) =>
      setPluginData (map, tag, afterCompile (r, getPluginData (map, tag))),
    reuseFrom = fn r => fn old => fn new =>
      setPluginData (new, tag,
        reuseFrom r (getPluginData (old, tag)) (getPluginData (new, tag))) }
  end

exception DuplicatePlugin
fun registerPlugin quiet (p as {name, init, ...}) = let
  val ps = !plugins
  val (proj, inj) = UniversalType.embed ()
  val inj = Option.valOf o inj
  val ps = if List.exists (fn p' => #name p' = name) ps then
    if quiet then List.filter (fn p' => #name p' <> name) ps
    else raise DuplicatePlugin
  else ps
  val _ = plugins := inject (proj, inj) p :: ps
  val _ = if serverRunning () then init (name, proj, inj) else ()
  in (name, proj, inj) end

fun registerInit quiet name init = let
  val ps = !plugins
  val ps = if List.exists (fn p' => #name p' = name) ps then
    if quiet then List.filter (fn p' => #name p' <> name) ps
    else raise DuplicatePlugin
  else ps
  val p = {name = name, init = init, beforeCompile = fn () => (),
           afterCompile = #2, reuseFrom = fn _ => fn _ => fn x => x}
  val _ = plugins := p :: ps
  in if serverRunning () then init () else () end

fun markServerStarted () = (running := true; app (fn {init, ...} => init ()) (!plugins))

fun getPlugins () = !plugins

fun reusePluginData r old new =
    List.foldl (fn ({reuseFrom, ...}: uplugin, m) => reuseFrom r old m)
               new (!plugins)

type location_link = {
  origin: rangeLC option,
  range: rangeLC,
  selRange: rangeLC,
  uri: string option}

type goto_def_context = {
  uri: string, lines: lines, plugins: plugin_data,
  fromFileLine: {file: string, line: int, origin: rangeLC option} -> location_link }

type hover = {markdown: string, range: rangeLC option}

type hover_context = {
  uri: string, lines: lines, plugins: plugin_data,
  ppToString: PrettyImpl.pretty -> string,
  (* Column width to wrap a rendered goal state at: the width of the
     pane the client is going to put it in, so its line breaking is the
     one the reader sees. *)
  width: int }

type goal_state = {asms: string list, goal: string}
type pp_segment = {text: string, kind: string, name: string, ty: string}
type goal_state_response = {
  theorem: string, step: int, goals: goal_state list, pretty: string,
  context: string list, status: string,
  error: string option, failedRange: (int * int) option,
  segments: pp_segment list}
type theorem_context = {
  name: string, quote: string, quoteStart: int,
  tacText: string, tacStart: int, cursor: int, compileDone: bool}

val gotoDefinition = ref (fn _ => [])
val hover = ref (fn _ => [])
val hoverQuotation = ref (fn _ => [])
val goalStateAtPos :
    (hover_context * theorem_context -> goal_state_response option) ref =
  ref (fn _ => NONE)
val fixupTheoremLink = ref (fn _ => NONE)
val helpLookup = ref (fn _ => [])
val thmLookup : (string -> PrettyImpl.pretty option) ref =
  ref (fn _ => NONE)
type ide_symbol = {
  name: string, theory: string, class: string,
  file: string option, line: int, visible: bool }
val ideSymbols :
    ({query: string, prefixOnly: bool, limit: int} -> ide_symbol list) ref =
  ref (fn _ => [])
type search_result = {
  name: string,
  theory: string,
  class: string,
  statement: PrettyImpl.pretty,
  file: string option,
  line: int }
val dbSearch :
    ({selectors: string list, limit: int} -> search_result list) ref =
  ref (fn _ => [])

val resetForCompile : (unit -> unit) ref = ref (fn () => ())
val notifyCompileStart : (int option -> unit) ref = ref (fn _ => ())

type compileSnap = unit -> unit
val captureCompileSnap : (unit -> compileSnap) ref = ref (fn () => (fn () => ()))
val restoreCompileSnap : (compileSnap -> unit) ref = ref (fn f => f ())

datatype proof_status =
         Unseen | Cheated | Checking | Proved
       | Failed of string | Suspended of string | Diverged of string
type proof_state = {site: string, offset: int, status: proof_status}

type deferred = {site: string, offset: int, run: unit -> proof_status}
val deferProofs = ref false
val cheatSubstituted = ref false

local
  (* An `Sref`, because the answer `addNoCheatSite` gives is what stops
     the retract-and-re-elaborate cycle: a worker is told whether it is
     the first to report this site, and acts only if it is.  Two workers
     each told "yes" for one site is a duplicated recompile, and in the
     bad case a loop -- so the test and the add have to be one step,
     which a plain `ref` cannot give.  See the termination argument at
     `retract` in lsp/server.ML. *)
  val sites : string list Sref.t = Sref.new []
  fun member s ss = List.exists (fn s' => s' = s) ss
in
  fun isNoCheatSite s = member s (Sref.value sites)
  fun addNoCheatSite s =
      Sref.gen_update sites
        (fn ss => if member s ss then (ss, false) else (s :: ss, true))
  fun dropNoCheatSite s =
      Sref.update sites (List.filter (fn s' => s' <> s))
end
val currentProofOffset = ref 0
val currentProofOrd = ref 1
local
  (* Enqueued in reverse; the drain takes the whole queue in one step.

     An `Sref` rather than a plain ref: the deferring branch of the
     prover hook is reached from elaboration, and while that is one
     thread at a time, a superseded pass can still be draining this
     queue as its replacement fills it -- and any thread that runs a
     tactic reaches the hook, including the ones the server forks per
     goal-state request.  A dropped enqueue is a proof that is never
     checked and never reported, which is indistinguishable from one
     that passed. *)
  val q : deferred list Sref.t = Sref.new []
in
  fun enqueueDeferred d = Sref.update q (fn ds => d :: ds)
  fun takeDeferred () = List.rev (Sref.gen_update q (fn ds => ([], ds)))
end

type check_scope = {resumeFrom: int, keptFrom: int option, bytes: int}
val checkDeferred : (check_scope -> unit) ref = ref (fn _ => ())
val poolBusy : (unit -> bool) ref = ref (fn () => false)
val cancelProofsAtOrAfter : (int -> unit) ref = ref (fn _ => ())
val cancelProofAt : (int -> unit) ref = ref (fn _ => ())
val cancelAllProofs : (unit -> unit) ref = ref (fn () => ())
val proofStateChanged : (proof_state list -> unit) ref = ref (fn _ => ())

end
