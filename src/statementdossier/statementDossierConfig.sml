structure statementDossierConfig :> statementDossierConfig =
struct

open statementDossierLib

fun bad field message = raise Fail (field ^ ": " ^ message)

fun table _ (TOML.TABLE fields) = fields
  | table field _ = bad field "expected a table"

fun fields field allowed value =
  let
    val fs = table field value
    val _ = List.app
      (fn (k, _) => if List.exists (fn a => k = a) allowed then ()
                    else bad field ("unknown field " ^ k)) fs
  in fs end

fun string _ (TOML.STRING s) = s
  | string field _ = bad field "expected a string"

fun array decode field (TOML.ARRAY xs) = map (decode field) xs
  | array _ field _ = bad field "expected an array"

fun required fs decode k =
  case List.find (fn (k', _) => k = k') fs of
    SOME (_, v) => decode k v
  | NONE => bad k "required field is missing"

fun default fs decode k initial =
  case List.find (fn (k', _) => k = k') fs of
    SOME (_, v) => decode k v
  | NONE => initial

fun optional fs decode k =
  case List.find (fn (k', _) => k = k') fs of
    SOME (_, v) => SOME (decode k v)
  | NONE => NONE

fun name field value =
  let val s = string field value in
    case String.fields (fn c => c = #"$") s of
      [thy, n] =>
        if thy <> "" andalso n <> "" then {Thy = thy, Name = n}
        else bad field ("expected Theory$Name, got " ^ s)
    | _ => bad field ("expected Theory$Name, got " ^ s)
  end

fun configuration path value =
  let
    val fs = fields "configuration"
      ["title", "preamble", "theorems", "expand_theories", "expand_consts",
       "stop_theories", "stop_consts", "equation_lemmas", "source_dirs",
       "outputs", "snippets", "assumptions", "supporting", "load_path",
       "theories"] value
    fun file field value =
      let val s = string field value in
        if s = "" then bad field "expected a nonempty path"
        else OS.Path.mkAbsolute {path = s, relativeTo = OS.Path.dir path}
      end
    fun source_dirs field v =
      map (fn (label, dir) => (label, file field dir)) (table field v)
    fun outputs field v =
      let
        fun output ("markdown", p) = (Markdown, file field p)
          | output ("html", p) = (Html, file field p)
          | output (k, _) = bad field ("unknown format " ^ k)
        val result = map output (table field v)
      in
        if null result then bad field "expected at least one output"
        else result
      end
    fun equations field v =
      map (fn (k, vs) => (name field (TOML.STRING k), array name field vs))
          (table field v)
    fun snippets field v =
      let val fs = fields field ["input", "output"] v
      in (required fs file "input", required fs file "output") end
    fun assumptions field v =
      let val fs = fields field ["theorem", "prose"] v
      in {theorem = required fs name "theorem",
          prose = required fs file "prose"} end
    val selected = required fs (array name) "theorems"
    val _ = if null selected then bad "theorems" "expected a nonempty array"
            else ()
    val cfg : config = {
      title = default fs string "title" "Stored theorem dossier",
      preamble = default fs string "preamble" "",
      theorems = selected,
      expand_theories = default fs (array string) "expand_theories" [],
      expand_consts = default fs (array name) "expand_consts" [],
      stop_theories = default fs (array string) "stop_theories" [],
      stop_consts = default fs (array name) "stop_consts" [],
      equation_lemmas = default fs equations "equation_lemmas" [],
      source_dirs = default fs source_dirs "source_dirs" [],
      outputs = required fs outputs "outputs",
      snippets = optional fs snippets "snippets",
      assumptions = optional fs assumptions "assumptions",
      supporting = default fs (array name) "supporting" []
    }
    val names = #theorems cfg @ #supporting cfg @ #expand_consts cfg @
      #stop_consts cfg @
      List.concat (map (fn (n, ns) => n :: ns) (#equation_lemmas cfg)) @
      (case #assumptions cfg of NONE => [] | SOME {theorem, ...} => [theorem])
    val theories = Lib.mk_set
      (default fs (array string) "theories" [] @
       map (fn {Thy, ...} => Thy) names @
       #expand_theories cfg @ #stop_theories cfg)
  in
    {config = cfg, load_path = default fs (array file) "load_path" [],
     theories = theories}
  end

fun read path =
  let
    val path = OS.FileSys.fullPath path
  in
    configuration path
      (TOML.TABLE (TOML.fromFile path)
       handle TOMLerror.ParseError e =>
         bad "configuration" (TOMLerror.toString e))
  end

end
