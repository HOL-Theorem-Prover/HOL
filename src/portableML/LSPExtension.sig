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

type location_link = {
  origin: rangeLC option,
  range: rangeLC,
  selRange: rangeLC,
  uri: string option}

type server_context = {
  uri: string,
  lines: lines,
  plugins: plugin_data,
  fromFileLine: {file: string, line: int, origin: rangeLC option} -> location_link }

val gotoDefinition: (server_context * int -> location_link list) ref

val fixupTheoremLink:
  ({start: int, stop: int, text: string, uri: string} ->
   {file: string, line: int} option) ref

end;
