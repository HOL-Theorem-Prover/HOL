(* Compiled theory factories contain code, not initialized theorem values.
   Their applications still perform the ordinary kernel and theory setup. *)
structure TheoryModules =
struct

structure Save = PolyML.SaveState
structure Tags = Save.Tags
val namespace = PolyML.globalNameSpace

val hits = ref 0
val misses = ref 0
val writes = ref 0
fun statistics () = {hits = !hits, misses = !misses, writes = !writes}

fun read_text path =
  let val input = HOLFileSys.openIn path
  in HOLFileSys.inputAll input before HOLFileSys.closeIn input end

fun write_text path text =
  let val output = TextIO.openOut path
  in TextIO.output (output, text) before TextIO.closeOut output end

fun digest text =
  let
    fun read (offset, count) =
      let val n = Int.min (count, String.size text - offset)
      in (Byte.stringToBytes (String.substring (text, offset, n)), offset+n)
      end
  in
    SHA1.sha1String read 0
  end

fun mkdir path =
  (if OS.FileSys.isDir path then ()
   else raise Fail ("not a directory: " ^ path))
  handle OS.SysErr _ =>
    (if OS.Path.dir path = path then () else mkdir (OS.Path.dir path);
     OS.FileSys.mkDir path
       handle e as OS.SysErr _ =>
         if OS.FileSys.isDir path then () else raise e)

val serial = ref 0
fun temporary directory =
  let
    val n = !serial before serial := !serial + 1
    val pid = SysWord.toString
                (Posix.Process.pidToWord (Posix.ProcEnv.getpid ()))
  in
    OS.Path.concat (directory, "tmp-" ^ pid ^ "-" ^ Int.toString n)
  end

fun remove path = OS.FileSys.remove path handle OS.SysErr _ => ()
fun touch path = OS.FileSys.setTime (path, NONE) handle OS.SysErr _ => ()

(* The generated factory uses only these qualified structures, including
   primitive operations and its manifest argument/result types. *)
val required_structures =
  ["General", "Globals", "TextIO", "Thm", "String", "HOLFileSys",
   "TheoryReader", "Symtab", "Option", "Theory"]

fun core_bindings () =
  map (fn name =>
         case #lookupStruct namespace name of
             SOME value => (name, value)
           | NONE => raise Fail ("missing structure " ^ name))
      required_structures

fun same_bindings bindings =
  List.all
    (fn (name, value) =>
       case #lookupStruct namespace name of
           SOME current => PolyML.pointerEq (current, value)
         | NONE => false)
    bindings

fun factory_source text =
  let
    val start = "(* HOL theory initializer v1 *)"
    val stop = "(* HOL theory initializer end *)"
    val (prefix, rest) = Substring.position start (Substring.full text)
    val body = Substring.triml (String.size start) rest
    val (factory, tail) = Substring.position stop body
    fun newlines s = String.translate
      (fn #"\n" => "\n" | _ => "") s
  in
    if Substring.isEmpty rest orelse Substring.isEmpty tail then NONE
    else SOME {factory = newlines (Substring.string prefix ^ start) ^
                         Substring.string factory,
               application = Substring.string prefix ^
                 newlines (start ^ Substring.string factory ^ stop) ^
                 Substring.string (Substring.triml (String.size stop) tail)}
  end

fun read_factory directory key =
  let
    val hash = read_text (OS.Path.concat (directory, key ^ ".ref"))
    val _ = String.size hash = 40 andalso
            CharVector.all Char.isHexDigit hash orelse
            raise Fail "invalid module digest"
    val path = OS.Path.concat (directory, hash ^ ".pmo")
    (* Poly's native loader checks headers, not payload integrity. *)
    val _ = SHA1.sha1_file {filename = path} = hash orelse
            raise Fail "module digest mismatch"
    val (roots, id) = Save.loadModuleBasic path
    fun discard () = (Save.releaseModule id; NONE)
  in
    case roots of
        factory :: guards =>
          if Universal.tagIs Tags.functorTag factory andalso
             List.all (Universal.tagIs Tags.structureTag) guards andalso
             same_bindings
               (map (Universal.tagProject Tags.structureTag) guards)
          then (touch (OS.Path.concat (directory, key ^ ".ref"));
                touch path;
                SOME (Universal.tagProject Tags.functorTag factory))
          else discard ()
      | [] => discard ()
  end
  handle IO.Io _ => NONE
       | OS.SysErr _ => NONE
       | Fail _ => NONE

fun save_factory directory key base_id factory bindings =
  let
    val tmp = temporary directory
    val reference = temporary directory
    fun cleanup () = (remove tmp; remove reference)
  in
    (ignore (Save.saveDependentModuleBasic
       (tmp, Universal.tagInject Tags.functorTag factory ::
             map (Universal.tagInject Tags.structureTag) bindings,
        [(base_id, "")]));
     let
       val hash = SHA1.sha1_file {filename = tmp}
       val path = OS.Path.concat (directory, hash ^ ".pmo")
     in
       OS.FileSys.rename {old = tmp, new = path};
       write_text reference hash;
       OS.FileSys.rename
         {old = reference, new = OS.Path.concat (directory, key ^ ".ref")};
       writes := !writes + 1
     end)
    handle e => (cleanup (); PolyML.Exception.reraise e)
  end

fun load_source directory base_id use file =
  if not (String.isSuffix "Theory.sml" file) then use file
  else
    let
      val text = read_text file
    in
      case factory_source text of
          NONE => use file
        | SOME {application, ...} =>
          let
            val name = OS.Path.base (OS.Path.file file)
            val key = digest ("hol-theory-initializer-v1\000" ^
                              Byte.bytesToString base_id ^ text)
            fun cold () =
              let
                val bindings = core_bindings ()
                val _ = misses := !misses + 1
                val _ = use file
              in
                case #lookupFunct namespace name of
                    NONE => ()
                  | SOME factory =>
                    (save_factory directory key base_id (name, factory) bindings
                       handle IO.Io _ => ()
                            | OS.SysErr _ => ()
                            | Fail _ => ())
              end
          in
            case read_factory directory key of
                SOME (factory as (stored_name, _)) =>
                  if stored_name <> name then cold ()
                  else
                    (#enterFunct namespace factory;
                     hits := !hits + 1;
                     (* Do not retry after setup has started: load hooks can
                        have effects outside the kernel's Context. *)
                     QUse.useText {file = file, text = application})
              | NONE => cold ()
          end
    end

fun compile_factory file text =
  let
    val offset = ref 0
    val result = ref NONE
    fun read () =
      if !offset = String.size text then NONE
      else SOME (String.sub (text, !offset)) before offset := !offset + 1
    val _ = PolyML.compiler
      (read, [PolyML.Compiler.CPFileName file,
              PolyML.Compiler.CPResultFun
                (fn {functors = [factory], ...} => result := SOME factory
                  | _ => raise Fail "expected one theory factory")]) ()
  in
    Option.valOf (!result)
  end

fun produce directory base_id file =
  let
    val text = read_text file
  in
    case factory_source text of
        NONE => ()
      | SOME {factory, ...} =>
        let
          val key = digest ("hol-theory-initializer-v1\000" ^
                            Byte.bytesToString base_id ^ text)
        in
          case read_factory directory key of
              SOME _ => ()
            | NONE =>
              let
                val bindings = core_bindings ()
                val compiled = compile_factory file factory
              in
                save_factory directory key base_id compiled bindings
              end
        end
  end
  handle IO.Io _ => ()
       | OS.SysErr _ => ()
       | Fail _ => ()

fun configure {directory, base_state} =
  let
    val _ = Meta.moduleSourceLoader := (fn use => use)
    val _ = Meta.moduleProducer := (fn _ => ())
    val directory = OS.Path.mkAbsolute
                      {path = directory, relativeTo = OS.FileSys.getDir ()}
    fun same_state (_, path) =
      OS.FileSys.fullPath path = OS.FileSys.fullPath base_state
  in
    case List.find same_state (Save.showHierarchyWithIds ()) of
        NONE => false
      | SOME (base_id, _) =>
        (mkdir directory;
         Meta.moduleSourceLoader := load_source directory base_id;
         Meta.moduleProducer := produce directory base_id;
         true)
  end
  handle IO.Io _ => false
       | OS.SysErr _ => false
       | Fail _ => false

val _ = Meta.moduleCacheConfigure := SOME configure

end
