(* Theory value modules.  A theory's module holds its signature, its
   theorem values and the decoded .dat data (TheoryReader.decoded),
   saved against the HOL saved state only.  Modules live in one
   directory, named by the saved state's id, the theory and the SHA-1 of
   the .dat file they were decoded from.  A process that loads a theory
   from its .dat file writes the theory's module, up to
   Meta.theoryModuleWriteLimit modules per process, since each save
   scans everything the process has loaded; a later load in any process
   started from the same saved state installs the module and repeats
   only the registration, without compiling the generated ML or reading
   the .dat.  Meta.writeTheoryModules writes modules from .dat files
   alone, running none of a project's code, for module stores that
   project code must not write.  This relies on loaded theories' kernel
   ids being canonical (KernelSig.insert_sealed_type/_const): saved terms and
   theorems then mean the same thing in every such process, whatever
   was loaded before. *)
structure TheoryModules =
struct

structure Save = PolyML.SaveState
structure Tags = Save.Tags
val namespace = PolyML.globalNameSpace

(* A structure is a signature plus its record of values.  Modules save
   only the record's theorems, not the compiled structure (whose code,
   closures and mutable cells would make every module mutable and
   several times larger), and rebuild the structure on a warm load.
   Poly/ML builds structures from a signature and a record only in its
   debugger's name spaces; this mirrors the debugger's entry type to
   reach that.  The mirror must have the same constructors, in the same
   order and with the same arities, as Poly/ML's environEntry. *)
local
  type w = PolyML.CodeTree.machineWord
  datatype entry =
      EnvEndFunction of string * PolyML.location * w
    | EnvException of string * w * bool * unit list
    | EnvStartFunction of string * PolyML.location * w
    | EnvStructure of string * w * unit list
    | EnvTConstr of string * w
    | EnvTypeid of w * w
    | EnvVConstr of string * w * bool * int * unit list
    | EnvValue of string * w * unit list
  val nowhere = {file = "", startLine = 0, startPosition = 0,
                 endLine = 0, endPosition = 0}
in
fun make_structure (name, signature_value, record : w) =
  let
    val state : entry list * w list * PolyML.location =
        ([EnvStructure (name, RunCall.unsafeCast signature_value, [])],
         [record], nowhere)
    val space = PolyML.DebuggerInterface.debugNameSpace
                  (RunCall.unsafeCast state)
  in
    #lookupStruct space name
  end
end

(* The values a signature declares, in the order of the record it
   describes, taken by name from [entries]; NONE if one is missing.  A
   value's place is found by building the structure over a record of
   field numbers, which must cover every field: [entries] holds at least
   as many values as the signature declares. *)
fun signature_values (name, signature_value, entries) =
  let
    fun value_of v =
      PolyML.CodeTree.evalue (PolyML.NameSpace.Values.code v)
    fun values_of s = #allVal (PolyML.NameSpace.Structures.contents s) ()
    val table = List.foldl (fn (e, t) => Symtab.update e t) Symtab.empty
                            entries
    val numbers : int vector = Vector.tabulate (length entries, fn i => i)
  in
    case make_structure (name, signature_value, RunCall.unsafeCast numbers) of
        NONE => NONE
      | SOME numbered =>
        let
          val fields = values_of numbered
          val n = length fields
          val record = Array.array (n, NONE)
          fun place (value_name, v) =
            case (value_of v, Symtab.lookup table value_name) of
                (SOME w, SOME value) =>
                let val i : int = RunCall.unsafeCast w
                in
                  if 0 <= i andalso i < n andalso
                     not (Option.isSome (Array.sub (record, i)))
                  then Array.update (record, i, SOME value)
                  else raise Fail "field"
                end
              | _ => raise Fail "field"
        in
          List.app place fields;
          SOME (Vector.tabulate (n, fn i => valOf (Array.sub (record, i))))
        end
  end
  handle Fail _ => NONE | Option => NONE

val hits = ref 0
val misses = ref 0
val writes = ref 0
fun statistics () = {hits = !hits, misses = !misses, writes = !writes}

fun digest_reader text (offset, count) =
  let val n = Int.min (count, String.size text - offset)
  in (Byte.stringToBytes (String.substring (text, offset, n)), offset + n)
  end

fun file_digest path =
  let
    val input = HOLFileSys.openIn path
    val text = HOLFileSys.inputAll input before HOLFileSys.closeIn input
  in
    SHA1.sha1String (digest_reader text) 0
  end

fun hex bytes =
  String.concat
    (Word8Vector.foldr
       (fn (b, l) => StringCvt.padLeft #"0" 2 (Word8.toString b) :: l)
       [] bytes)

fun module_file base_id (thy, dat_digest) =
  hex base_id ^ "-" ^ thy ^ "-" ^ dat_digest ^ ".pmo"

fun mkdir path =
  (if OS.FileSys.isDir path then ()
   else raise Fail ("not a directory: " ^ path))
  handle OS.SysErr _ =>
    (if OS.Path.dir path = path then () else mkdir (OS.Path.dir path);
     OS.FileSys.mkDir path
       handle e as OS.SysErr _ =>
         if OS.FileSys.isDir path then () else raise e)

fun exists path = OS.FileSys.access (path, []) handle OS.SysErr _ => false

fun remove path = OS.FileSys.remove path handle OS.SysErr _ => ()

val serial = ref 0
fun temporary directory =
  let
    val n = !serial before serial := !serial + 1
    val pid = SysWord.toString
                (Posix.Process.pidToWord (Posix.ProcEnv.getpid ()))
  in
    OS.Path.concat (directory, "tmp-" ^ pid ^ "-" ^ Int.toString n)
  end

(* Runs [f] holding a write lock on the file [path], removed afterwards;
   does nothing if another process holds it. *)
fun with_lock path f =
  let
    open Posix.FileSys
    val fd = createf (path, O_WRONLY, O.flags [], S.flags [S.irusr, S.iwusr])
    val lock = Posix.IO.FLock.flock
                 {ltype = Posix.IO.F_WRLCK, whence = Posix.IO.SEEK_SET,
                  start = Position.fromInt 0, len = Position.fromInt 0,
                  pid = NONE}
    val locked = (ignore (Posix.IO.setlk (fd, lock)); true)
                 handle OS.SysErr _ => false
  in
    (if locked then (f () before remove path) else ())
    handle e => (Posix.IO.close fd; PolyML.Exception.reraise e);
    Posix.IO.close fd
  end
  handle OS.SysErr _ => ()

(* The generated theory source refers to these structures; a source load
   uses whatever they are bound to now.  A warm load uses the ones bound
   when this file was compiled, so modules are used and saved only while
   the current bindings are those, and a module is used only with the
   bindings it was saved under. *)
val required_structures =
  ["General", "Globals", "TextIO", "OS", "Option", "Type", "Term", "Thm",
   "HOLFileSys", "TheoryReader", "Symtab", "Theory"]

fun core_bindings () =
  map (fn name =>
         case #lookupStruct namespace name of
             SOME value => value
           | NONE => raise Fail ("missing structure " ^ name))
      required_structures

fun same_bindings bindings =
  ListPair.allEq
    (fn (name, value) =>
       case #lookupStruct namespace name of
           SOME current => PolyML.pointerEq (current, value)
         | NONE => false)
    (required_structures, bindings)

val compiled_bindings = core_bindings ()
fun unchanged_bindings () = same_bindings compiled_bindings

(* The theory name and hash a generated FooTheory.sml loads; the source
   loader identifies the theory by the same literals.  The file is read
   as text, never compiled. *)
fun sml_header file =
  let
    val input = HOLFileSys.openIn file
    val text = TextIO.inputN (input, 4096) before HOLFileSys.closeIn input
    fun literal key =
      let
        val (_, rest) = Substring.position key (Substring.full text)
        val rest = Substring.triml (String.size key) rest
        val (value, close) = Substring.splitl (fn c => c <> #"\"") rest
      in
        if Substring.isEmpty close then NONE
        else SOME (Substring.string value)
      end
  in
    case (literal "thyname = \"", literal "hash = \"") of
        (SOME thy, SOME hash) => SOME (thy, hash)
      | _ => NONE
  end
  handle IO.Io _ => NONE
       | OS.SysErr _ => NONE

type module =
     {signature_value : string * PolyML.NameSpace.Signatures.signatureVal,
      values : string * Thm.thm vector,
      data : TheoryReader.decoded,
      bindings : PolyML.NameSpace.Structures.structureVal list,
      id : Save.moduleId}

(* The module at [path], if it holds theory [thy]'s values decoded from a
   .dat file with digest [dat_digest], for structure [name]. *)
fun read_module path name (thy, dat_digest) : module option =
  if not (exists path) then NONE
  else
    let
      val (roots, id) = Save.loadModuleBasic path
      fun discard () = (Save.releaseModule id; NONE)
    in
      case roots of
          signature_root :: structure_root :: data_root :: digest_root ::
          guards =>
          if Universal.tagIs Tags.signatureTag signature_root andalso
             Universal.tagIs TheoryReader.values_tag structure_root andalso
             Universal.tagIs TheoryReader.decoded_tag data_root andalso
             Universal.tagIs TheoryReader.digest_tag digest_root andalso
             List.all (Universal.tagIs Tags.structureTag) guards
          then
            let
              val signature_value as (signature_name, _) =
                  Universal.tagProject Tags.signatureTag signature_root
              val values as (structure_name, _) =
                  Universal.tagProject TheoryReader.values_tag structure_root
              val data =
                  Universal.tagProject TheoryReader.decoded_tag data_root
            in
              if signature_name = name andalso structure_name = name andalso
                 TheoryReader.decoded_name data = thy andalso
                 Universal.tagProject TheoryReader.digest_tag digest_root =
                 dat_digest
              then
                SOME {signature_value = signature_value, values = values,
                      data = data,
                      bindings = map (#2 o Universal.tagProject
                                             Tags.structureTag) guards,
                      id = id}
              else discard ()
            end
          else discard ()
        | _ => discard ()
    end
    handle Fail _ => NONE
         | OS.SysErr _ => NONE
         | IO.Io _ => NONE

(* Whether a module's values mean the same here as where they were
   decoded: its parents' ids are canonical and the other theories'
   kernel entries it refers to are unchanged. *)
fun usable ({data, bindings, ...} : module) =
  unchanged_bindings () andalso same_bindings bindings andalso
  List.all TheoryReader.is_canonical (TheoryReader.decoded_parents data) andalso
  TheoryReader.refs_current data

(* The signature [text] declares, compiled without entering it in the
   global name space. *)
fun compile_signature name text =
  let
    val position = ref 0
    fun next () =
      if !position < String.size text then
        SOME (String.sub (text, !position)) before position := !position + 1
      else NONE
    val found = ref NONE
    fun result {signatures, ...} =
      case List.find (fn (n, _) => n = name) signatures of
          SOME (_, s) => found := SOME s
        | NONE => ()
    val parameters =
        [PolyML.Compiler.CPNameSpace namespace,
         PolyML.Compiler.CPOutStream (fn _ => ()),
         PolyML.Compiler.CPResultFun result]
  in
    PolyML.compiler (next, parameters) (); !found
  end

(* A module's roots, in the order read_module expects, built from a
   theory's decoded data.  The signature is the one export_theory
   prints for the theorems, so every value it declares is a theorem. *)
fun module_roots name dat_digest data bindings =
  let
    val thy = TheoryReader.decoded_name data
    val theorems = TheoryReader.decoded_theorems data
    fun visible (s, _, {private, ...} : DB_dtype.thminfo) =
      not private andalso not (TheoryPP.is_temp_binding s)
    val names_ok =
        Lexis.ok_identifier thy andalso name = thy ^ "Theory" andalso
        List.all (fn t as (s, _, _) => not (visible t) orelse
                                       Lexis.ok_sml_identifier s)
                 theorems
    val text = HOLPP.pp_to_string 75 TheoryPP.pp_sig
                 {name = thy, parents = [], all_thms = theorems}
  in
    if not names_ok then NONE
    else
      case compile_signature name text of
          NONE => NONE
        | SOME signature_value =>
          case signature_values
                 (name, signature_value,
                  map (fn (s, th, _) => (s, RunCall.unsafeCast th)) theorems)
           of
              NONE => NONE
            | SOME words =>
              SOME (Universal.tagInject Tags.signatureTag
                                        (name, signature_value) ::
                    Universal.tagInject TheoryReader.values_tag
                                        (name, RunCall.unsafeCast words) ::
                    Universal.tagInject TheoryReader.decoded_tag data ::
                    Universal.tagInject TheoryReader.digest_tag dat_digest ::
                    map (fn b => Universal.tagInject Tags.structureTag ("", b))
                        bindings)
  end

fun save_module path base_id roots =
  let
    val tmp = temporary (OS.Path.dir path)
  in
    (ignore (Save.saveDependentModuleBasic (tmp, roots, [(base_id, "")]));
     OS.FileSys.rename {old = tmp, new = path};
     writes := !writes + 1)
    handle e => (remove tmp; PolyML.Exception.reraise e)
  end

fun theory_file file =
  case OS.Path.ext file of
      SOME "sml" => String.isSuffix "Theory.sml" file
    | SOME "sig" => String.isSuffix "Theory.sig" file
    | _ => false

fun eligible () =
  (Thm.kernelid = "stdknl" orelse Thm.kernelid = "expknl") andalso
  TheoryReader.default_loader ()

(* What load_signature found for a theory, for its structure's load:
   the module whose signature it installed, if any; whether a module
   was there but refused; and the .sml header and .dat digest. *)
type found = {module : module option, refused : bool,
              header : string * string, dat_digest : string}
val found : (string * found) list ref = ref []

(* A module that is there but can't be used means the theory loads from
   its .dat; say so on stderr, so that a persistent fallback shows in the
   build log. *)
fun report_refused thy =
  TextIO.output (TextIO.stdErr, "theory modules: " ^ thy ^
                                ": module refused, loading from .dat\n")

fun take_found base =
  case List.partition (fn (b, _) => b = base) (!found) of
      ([], _) => NONE
    | ((_, f) :: _, rest) => (found := rest; SOME f)

fun load_signature directory base_id use file =
  let
    val base = OS.Path.base file
    val name = OS.Path.file base
  in
    case sml_header (base ^ ".sml") of
        NONE => use file
      | SOME (header as (thy, _)) =>
        case SOME (file_digest (base ^ ".dat"))
               handle IO.Io _ => NONE | OS.SysErr _ => NONE of
            NONE => use file
          | SOME dat_digest =>
            let
              val path = OS.Path.concat
                           (directory, module_file base_id (thy, dat_digest))
              val m = read_module path name (thy, dat_digest)
              val refused = exists path andalso not (Option.isSome m)
            in
              if refused then report_refused thy else ();
              case m of
                  NONE => use file
                | SOME m => #enterSig namespace (#signature_value m);
              found := (base, {module = m, refused = refused,
                               header = header, dat_digest = dat_digest})
                       :: !found
            end
  end

fun warm_load file hash ({signature_value, values, data, ...} : module) =
  let
    val name = #1 values
    val thy = TheoryReader.decoded_name data
    val structure_value =
        case make_structure (name, #2 signature_value,
                             RunCall.unsafeCast (#2 values)) of
            SOME s => s
          | NONE => raise Fail ("cannot rebuild structure " ^ name)
    val path = OS.Path.base file ^ ".dat"
    val _ = if !Globals.print_thy_loads
            then TextIO.print ("Loading " ^ name ^ " ... ") else ()
    val _ = TheoryReader.register_decoded hash data
    val _ = Theory.record_metadata thy
              {timestamp = HOLFileSys.modTime path, path = path}
    val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
    val _ = Theory.load_complete thy
  in
    #enterStruct namespace (name, structure_value);
    hits := !hits + 1
  end

(* Writes the module of a theory this process has just loaded from its
   .dat file, unless another process is writing it or wrote it since
   this one looked.  A failed write leaves the load as it was. *)
fun write_module directory base_id name (f : found) data =
  let
    val path = OS.Path.concat
                 (directory, module_file base_id (#1 (#header f),
                                                  #dat_digest f))
  in
    with_lock (OS.Path.base path ^ ".lock")
      (fn () =>
          if exists path andalso not (#refused f) then ()
          else
            case module_roots name (#dat_digest f) data (core_bindings ()) of
                NONE => ()
              | SOME roots => save_module path base_id roots)
  end
  handle e as Interrupt => PolyML.Exception.reraise e
       | _ => ()

fun cold_load directory base_id use file (f : found option) =
  let
    val name = OS.Path.file (OS.Path.base file)
    val _ = misses := !misses + 1
    val (_, data) = TheoryReader.capture_decoded use file
  in
    case (f, data) of
        (SOME f, SOME data) =>
        if !writes < !Meta.theoryModuleWriteLimit andalso
           TheoryReader.decoded_name data = #1 (#header f) andalso
           TheoryReader.is_canonical (TheoryReader.decoded_name data) andalso
           unchanged_bindings ()
        then write_module directory base_id name f data
        else ()
      | _ => ()
  end

fun load_structure directory base_id use file =
  case take_found (OS.Path.base file) of
      SOME (f as {module = SOME m, header = (_, hash), ...}) =>
      (* Checks before any registration; past them nothing is retried
         from source, since load hooks may already have run.  A module
         whose signature is installed stays loaded either way. *)
      if usable m then warm_load file hash m
      else (report_refused (#1 (#header f));
            cold_load directory base_id use file
                     (SOME {module = NONE, refused = true,
                            header = #header f, dat_digest = #dat_digest f}))
    | f => cold_load directory base_id use file f

fun load_source directory base_id use file =
  if not (theory_file file) orelse not (eligible ()) then use file
  else if OS.Path.ext file = SOME "sig" then
    load_signature directory base_id use file
  else load_structure directory base_id use file

fun base_id_of base_state =
  let
    fun same_state (_, path) =
      OS.FileSys.fullPath path = OS.FileSys.fullPath base_state
  in
    Option.map #1 (List.find same_state (Save.showHierarchyWithIds ()))
  end
  handle OS.SysErr _ => NONE

fun absolute directory =
  OS.Path.mkAbsolute {path = directory, relativeTo = OS.FileSys.getDir ()}

fun configure {directory, base_state} =
  let
    val _ = Meta.moduleSourceLoader := (fn use => use)
    val directory = absolute directory
  in
    case base_id_of base_state of
        NONE => false
      | SOME base_id =>
        (mkdir directory;
         Meta.moduleSourceLoader := load_source directory base_id;
         true)
  end
  handle IO.Io _ => false
       | OS.SysErr _ => false
       | Fail _ => false

type entry = {base : string, thy : string, hash : string,
              dat_digest : string, file : string}

(* Meta.writeTheoryModules.  Each theory up to the last one without a
   module in [directory] is registered in the kernel from its module or
   decoded from its .dat file, with no theorem bindings, theory data,
   hooks or project code; up to [limit] modules of decoded theories are
   saved to [output].  When every theory has a module, nothing is loaded. *)
fun write_modules {theories, directory, base_state, output, limit} =
  case (eligible () andalso unchanged_bindings (), base_id_of base_state) of
      (true, SOME base_id) =>
      (let
        val directory = absolute directory
        val output = absolute output
        val bindings = core_bindings ()
        fun entry sml =
          let
            val base = OS.Path.base sml
            val (thy, hash) =
                case sml_header (base ^ ".sml") of
                    SOME h => h
                  | NONE => raise Fail ("no theory header in " ^ sml)
          in
            if TheoryReader.is_canonical thy then NONE
            else
              let val dat_digest = file_digest (base ^ ".dat")
              in
                SOME {base = base, thy = thy, hash = hash,
                      dat_digest = dat_digest,
                      file = module_file base_id (thy, dat_digest)}
              end
          end
        fun missing (e : entry) =
          not (exists (OS.Path.concat (directory, #file e)))
        fun through_last_missing entries =
          #2 (List.foldr (fn (e, (seen, acc)) =>
                             let val seen = seen orelse missing e
                             in (seen, if seen then e :: acc else acc) end)
                         (false, []) entries)
        fun decode (e : entry, name, written) =
          let
            val (data, canonical) =
                TheoryReader.decode_thydata
                  {thyname = #thy e, path = #base e ^ ".dat", hash = #hash e}
          in
            case (canonical, module_roots name (#dat_digest e) data bindings) of
                (true, SOME roots) =>
                (save_module (OS.Path.concat (output, #file e)) base_id roots;
                 written + 1)
              | _ => written
          end
        fun theory (e : entry, written) =
          let
            val name = OS.Path.file (#base e)
          in
            case read_module (OS.Path.concat (directory, #file e)) name
                             (#thy e, #dat_digest e) of
                SOME m =>
                if usable m then
                  (TheoryReader.register_kernel (#hash e) (#data m);
                   written)
                else (Save.releaseModule (#id m); decode (e, name, written))
              | NONE => decode (e, name, written)
          end
          handle e as Interrupt => PolyML.Exception.reraise e
               | exn => (TextIO.output (TextIO.stdErr,
                                        "theory modules: " ^ #thy e ^ ": " ^
                                        General.exnMessage exn ^ "\n");
                         written)
        fun loop ([], written) = written
          | loop (e :: rest, written) =
            if written >= limit then written
            else loop (rest, theory (e, written))
      in
        case through_last_missing (List.mapPartial entry theories) of
            [] => 0
          | needed => (mkdir output; loop (needed, 0))
      end
      handle e as Interrupt => PolyML.Exception.reraise e
           | e => (TextIO.output (TextIO.stdErr,
                                  "theory modules: " ^
                                  General.exnMessage e ^ "\n");
                   !writes))
    | _ => 0

val _ = Meta.moduleCacheConfigure := SOME configure
val _ = Meta.moduleWriter := SOME write_modules

end
