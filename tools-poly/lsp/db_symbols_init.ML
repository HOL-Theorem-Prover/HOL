(* Installs `LSPExtension.ideSymbols', the one source of stored-theorem
   names for `workspace/symbol' and for completion.

   Two sources, and the difference between them is the `visible' field
   rather than two hooks:

   - HOL's `DB', which holds exactly the theories this process loaded --
     the bound script's ancestry.  A hit here is usable right now:
     `fooTheory.NAME' resolves as an SML value.  `visible = true'.

   - The `Theory.dat' files Holmake left in the project's object
     directories, read with `RawTheoryReader' without loading anything.
     A hit here is real and locatable but not in scope: using it means
     adding the theory to `Ancestors' first.  `visible = false'.

   Reading a theory rather than loading it is the point: loading seals
   it (`Theory.load_complete'), and a server that sealed every theory in
   the project to answer a symbol query would break the file it is
   actually serving. *)

val _ = Meta.load "RawTheoryReader"
val _ = Meta.load "theorystats"

local
  fun lower s = CharVector.map Char.toLower s

  (* `thy$name' addresses one theory, the way DB's own selectors do. *)
  fun splitThy q =
    case CharVector.findi (fn (_, c) => c = #"$") q of
      NONE => NONE
    | SOME (i, _) =>
        SOME (String.substring (q, 0, i),
              String.extract (q, i + 1, NONE))

  fun locFile loc =
    case loc of
      DB.Located {scriptpath, ...} =>
        (SOME (holpathdb.subst_pathvars scriptpath) handle _ => NONE)
    | DB.Unknown => NONE
  fun locLine loc =
    case loc of DB.Located {linenum, ...} => linenum | DB.Unknown => 0

  fun dbSym ((thy, nm), (_, cls, loc)) : LSPExtension.ide_symbol = {
    name = nm, theory = thy, class = DB_dtype.class_toString cls,
    file = locFile loc, line = locLine loc, visible = true}

  (* DB's name search is case-insensitive and understands its own small
     regexp language (`~ | ? * .'), so a query carrying one of those is
     a search, not an error -- but one it rejects raises, hence the
     handler at the call site. *)
  fun dbHits query =
    case splitThy query of
      SOME (thy, nm) => DB.selectDB [DB.SelTHY thy, DB.SelNM nm]
    | NONE => DB.find query

  (* ---------------- built, unloaded theories ---------------- *)

  (* Cache of one .dat's symbols, keyed by path, invalidated on mtime:
     a query per keystroke must not re-read every theory in the tree. *)
  val datCache :
      (string, Time.time * LSPExtension.ide_symbol list) Binarymap.dict ref =
    ref (Binarymap.mkDict String.compare)

  fun datSymbols path = let
    val stamp = HOLFileSys.modTime path
    fun fresh () = let
      val {name = thyname, tables, exports, ...} =
          RawTheoryReader.load_raw_thydata {path = path}
      val strv = #stringt tables
      fun str i = Vector.sub (strv, i)
      fun conv ({name, class, private, loc, ...}
                  : string RawTheory_dtype.raw_thm) =
        if private then NONE
        else let
          val loc' = SharingTables.translate_loc str loc
        in
          SOME {name = name, theory = thyname,
                class = RawTheory_dtype.class_toString class,
                file = locFile loc', line = locLine loc',
                visible = false} : LSPExtension.ide_symbol option
        end
      val syms = List.mapPartial conv (#thms exports)
      in syms before
         datCache := Binarymap.insert (!datCache, path, (stamp, syms))
      end
    in
      case Binarymap.peek (!datCache, path) of
        SOME (t, syms) => if t = stamp then syms else fresh ()
      | NONE => fresh ()
    end handle _ => []

  (* The directories this server already knows about: `Meta.loadPath' is
     built from the opened file's Holmakefile INCLUDES chain, so it is
     the project as this file sees it, without a tree walk of our own.
     `find_theory_files_action' reads a directory's object dir and picks
     out the *Theory.dat -- the same scan `theorystats' does. *)
  (* The scan itself is cached, not just the parsing of what it finds:
     a query runs per keystroke, and reading every load-path directory
     each time is dozens of `readdir's for a listing that changes only
     when someone builds a theory.  Keyed on the load path, which grows
     as files are opened, and re-done if the cached answer is more than
     a few seconds old so a freshly built theory does show up. *)
  type dat_scan = string list * Time.time * (string * string list) list
  val datScan : dat_scan option ref = ref NONE
  val scanMaxAge = Time.fromSeconds 10

  fun projectDats () = let
    val dirs = "." :: !Meta.loadPath
    val now = Time.now ()
    fun scan () = let
      val m = List.foldl (fn (d, m) => theorystats.find_theory_files_action d m
                                       handle _ => m)
                         Symtab.empty dirs
      val found = Symtab.dest m
      in datScan := SOME (dirs, now, found); found end
    in
      case !datScan of
        SOME (ds, t, found) =>
          if ds = dirs andalso Time.< (now - t, scanMaxAge) then found
          else scan ()
      | NONE => scan ()
    end

  (* A theory the process already loaded is answered from DB, with a
     statement and `visible = true'; reading its .dat as well would
     duplicate it as invisible. *)
  fun loadedThy thy =
    (thy = Theory.current_theory () orelse
     List.exists (fn t => t = thy) (Theory.ancestry "-"))
    handle _ => false

  fun unloadedSymbols () =
    List.concat
      (List.map (fn (thy, paths) =>
                    if loadedThy thy then []
                    else case paths of
                           p :: _ => datSymbols p
                         | [] => [])
                (projectDats ()))
    handle _ => []

  fun matches prefixOnly q sym = let
    val n = lower (#name (sym : LSPExtension.ide_symbol))
  in
    if prefixOnly then String.isPrefix q n
    else String.isSubstring q n
  end

  fun take n l = List.take (l, n) handle Subscript => l
in

val () = LSPExtension.ideSymbols := (fn {query, prefixOnly, limit} =>
  if query = "" then []
  else let
    val q = lower query
    val loaded = List.map dbSym (dbHits query) handle _ => []
    val loaded = List.filter (matches prefixOnly q) loaded
    (* Only pay for the on-disk scan when the ancestry did not already
       answer: it is the rarer question and the dearer one. *)
    val rest =
      if length loaded >= limit then []
      else List.filter (matches prefixOnly q) (unloadedSymbols ())
    in take limit (loaded @ rest) end
  handle _ => [])

end;
