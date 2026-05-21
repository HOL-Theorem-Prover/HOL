(* gen_reference_summary DOCFILES_DIR

   Walk DOCFILES_DIR for `*.smd` entries; group by the first
   dot-separated component of each filename; emit a SUMMARY.md
   on stdout suitable for mdbook.

   Each group becomes a mdbook "part title" (`# Header` line)
   followed by a flat list of its entries.  Entries whose name
   has no dot at all go into a synthetic "Miscellaneous" group
   at the end.

   Filenames that follow `<Struct>.<Function>.smd` are sorted
   case-insensitively by their second component (the function
   name) — this matches the reference-PDF concatenation order
   produced by `Md2TeX.sml`, which sorts alphabetically by
   entry-point rather than structure.  Within a group of
   same-function-name entries, ties are broken by structure name.

   Single-component entries (e.g. `Feedback.smd`, `Lib.smd` —
   docs for top-level structures themselves) sort first within
   their structure's group: clicking the group name in the
   sidebar reaches the structure-as-a-whole entry. *)

fun warn s =
    ( TextIO.output (TextIO.stdErr, s ^ "\n")
    ; TextIO.flushOut TextIO.stdErr )

fun die s = ( warn s ; OS.Process.exit OS.Process.failure )

fun emit s = TextIO.output (TextIO.stdOut, s)

(* List `*.smd` filenames (basenames only) in `dir`. *)
fun listSmd dir =
    let val strm = OS.FileSys.openDir dir
        fun loop acc =
            case OS.FileSys.readDir strm of
                NONE => (OS.FileSys.closeDir strm; acc)
              | SOME f =>
                  if String.isSuffix ".smd" f
                  then loop (f :: acc)
                  else loop acc
    in
      loop []
      handle e =>
        ( OS.FileSys.closeDir strm handle _ => ()
        ; die ("listSmd " ^ dir ^ ": " ^ General.exnMessage e) )
    end

fun dropExt name =
    if String.isSuffix ".smd" name
    then String.substring (name, 0, String.size name - 4)
    else name

(* For an entry filename, return:
   - the HOL structure name (used for sidebar grouping);
   - the displayable function name, with the structure prefix dropped.

   Filename conventions (mirroring Md2TeX.sml's `decode_stem`):
     - `Foo.smd`        -> (struct = "Foo", display = NONE)
                            single-component entry, e.g. docs for the
                            structure as a whole.
     - `Foo.bar.smd`    -> (struct = "Foo", display = "bar")
                            plain function-in-structure entry.
     - `Foo..xyz.smd`   -> (struct = "Foo", display = ".xyz")
                            UC_ASCII_Encode'd function name (HOL ident
                            containing chars like :, ?, *, ...).  We
                            don't decode here -- linking the decoder
                            into this build adds plumbing.  The
                            leading `.` preserved in the display label
                            hints that this entry is encoded. *)
fun splitName name =
    let val stem = dropExt name
    in
      case String.fields (fn c => c = #".") stem of
          [s]             => (s, NONE)
        | [s, f]          => (s, SOME f)
        | [s, "", encoded] =>
            (s, SOME ("." ^ encoded))
        | s :: rest =>
            (* No known producer of this shape; preserve the joined
               remainder unaltered rather than die. *)
            (s, SOME (String.concatWith "." rest))
        | [] => (stem, NONE)
    end

(* Group `[(struct, funcOpt, filename), …]` into
   `[(struct, [(funcOpt, filename), …]), …]`.  Preserves group
   discovery order. *)
fun groupByStruct entries =
    let
      fun upsert k v [] = [(k, [v])]
        | upsert k v ((k', vs) :: rest) =
            if k = k' then (k', v :: vs) :: rest
            else (k', vs) :: upsert k v rest
      fun loop [] acc = acc
        | loop ((s, f, n) :: rest) acc = loop rest (upsert s (f, n) acc)
    in
      loop entries []
    end

(* Sort entries within a structure: NONE (single-component, the
   structure-itself page) sorts first; otherwise case-insensitive
   by function name. *)
fun entryCmp ((NONE, _), (NONE, _)) = EQUAL
  | entryCmp ((NONE, _), _) = LESS
  | entryCmp (_, (NONE, _)) = GREATER
  | entryCmp ((SOME a, _), (SOME b, _)) =
      String.compare (CharVector.map Char.toLower a,
                      CharVector.map Char.toLower b)

(* Sort structures case-insensitively by name. *)
fun structCmp (s1, s2) =
    String.compare (CharVector.map Char.toLower s1,
                    CharVector.map Char.toLower s2)

(* Hand-rolled merge sort: this code links against bare HOL
   without Listsort or the SML/NJ ListMergeSort module. *)
fun takedrop n l =
    if n <= 0 then ([], l)
    else case l of
             [] => ([], [])
           | h :: t =>
               let val (p, d) = takedrop (n - 1) t
               in (h :: p, d) end

fun merge _ [] l2 = l2
  | merge _ l1 [] = l1
  | merge cmp (l1 as h1 :: t1) (l2 as h2 :: t2) =
      case cmp (h1, h2) of
          GREATER => h2 :: merge cmp l1 t2
        | _       => h1 :: merge cmp t1 l2

fun sortBy cmp xs =
    case xs of
        []  => []
      | [x] => [x]
      | _   => let val (p, s) = takedrop (List.length xs div 2) xs
               in merge cmp (sortBy cmp p) (sortBy cmp s) end

(* The display label for an entry in the per-structure sub-list:
   for `Foo.smd` (single-component, the structure-itself entry) the
   label is the structure name; for `Foo.bar.smd` and
   `Foo..xyz.smd` (with `xyz` UC_ASCII_Encode'd) just the function
   name -- the structure prefix is already visible in the parent
   sidebar group heading.  splitName already decoded the encoded
   form before we get here. *)
fun entryLabel struct_ NONE = struct_
  | entryLabel _ (SOME f) = f

(* The href for an entry: the filename (relative to src dir). *)
fun entryHref filename = filename

(* Backtick-wrap labels so the sidebar renders them in monospace
   (entries are HOL identifiers). *)
fun renderEntry struct_ (func, filename) =
    "- [`" ^ entryLabel struct_ func ^ "`](" ^ entryHref filename ^ ")\n"

(* mdbook part-title: `# Struct` as the section heading.  Renders
   in the sidebar as a non-clickable group label. *)
fun renderGroup (struct_, entries) =
    "\n# " ^ struct_ ^ "\n\n" ^
    String.concat (List.map (renderEntry struct_) entries)

fun renderSummary groups =
    "# Summary\n" ^
    String.concat (List.map renderGroup groups)

fun main () =
    let
      val dir = case CommandLine.arguments () of
                    [d] => d
                  | _ => die "usage: gen_reference_summary DOCFILES_DIR"
      val files = listSmd dir
      val () =
        if List.null files
        then die ("gen_reference_summary: no .smd files in " ^ dir)
        else ()
      val triples = List.map (fn f =>
                                 let val (s, fn_) = splitName f
                                 in (s, fn_, f) end)
                             files
      val grouped = groupByStruct triples
      (* sort entries within each group, then sort groups *)
      val groupsSorted =
          sortBy (fn ((s1, _), (s2, _)) => structCmp (s1, s2))
            (List.map (fn (s, es) =>
                          (s, sortBy entryCmp es)) grouped)
    in
      emit (renderSummary groupsSorted)
    end
