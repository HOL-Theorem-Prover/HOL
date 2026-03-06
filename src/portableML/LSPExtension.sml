structure LSPExtension :> LSPExtension =
struct

val running = ref false
fun serverRunning () = !running

type posLC = int * int
type rangeLC = posLC * posLC
type range = int * int

type lines = int vector
fun mkLineCounter str = let
  fun loop i ls =
    if i >= String.size str then Vector.fromList (List.rev ls)
    else
      let val c = String.sub (str, i)
      in loop (i+1) (if c = #"\n" then i+1::ls else ls) end
  in loop 0 [] end

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

fun getLineCol lines index = let
  val line = partitionPoint (Vector.length lines) (fn i => Vector.sub (lines, i) <= index)
  in (line, index - (if line = 0 then 0 else Vector.sub (lines, line - 1))) end

fun fromLineCol lines (line, col) =
  if line = 0 then col else Vector.sub (lines, line - 1) + col

type plugin_data = (string, UniversalType.t) Binarymap.dict
val emptyPluginData = Binarymap.mkDict String.compare

type 'a tag = string * ('a -> UniversalType.t) * (UniversalType.t -> 'a)

fun getPluginData (map, (name, _, proj)) = Option.map proj (Binarymap.peek (map, name))
fun setPluginData (map, (name, inj, _), SOME v) = Binarymap.insert (map, name, inj v)
  | setPluginData (map, (name, _, _), NONE) = #1 (Binarymap.remove (map, name))

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

val plugins = ref []

fun inject (proj, inj) {name, init, beforeCompile, afterCompile} = {
  name = name, init = fn () => init (name, proj, inj),
  beforeCompile = beforeCompile,
  afterCompile = fn (r, map) =>
    setPluginData (map, (name, proj, inj),
      afterCompile (r, getPluginData (map, (name, proj, inj)))) }

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
  val p = {name = name, init = init, beforeCompile = fn () => (), afterCompile = #2}
  val _ = plugins := p :: ps
  in if serverRunning () then init () else () end

fun markServerStarted () = (running := true; app (fn {init, ...} => init ()) (!plugins))

fun getPlugins () = !plugins

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
  ppToString: PrettyImpl.pretty -> string }

val gotoDefinition = ref (fn _ => [])
val hover = ref (fn _ => [])
val fixupTheoremLink = ref (fn _ => NONE)
val helpLookup = ref (fn _ => [])

end
