(* gen_reference_summary [--identifiers] DOCFILES_DIR

   Walk DOCFILES_DIR for `*.smd` entries; group by the first
   dot-separated component of each filename; emit a SUMMARY.md
   on stdout suitable for mdbook.

   With `--identifiers`, emit instead the entry-name table
   `identifiers.js` consumed by Manual/theme/hol-searcher.js --
   the same scan, in the same order, rendered as JS data rather
   than as a sidebar.  See Manual/Developers/manual-authoring.md
   for the format and for why the site needs a name lookup that
   bypasses the search index altogether.

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
     - `Foo..xyz.smd`   -> (struct = "Foo",
                            display = UC_ASCII_Encode.decode "xyz")
                            HOL identifier containing characters that
                            aren't filesystem-safe (e.g. `:`, `?`,
                            `*`) get their function name encoded; we
                            decode here so the sidebar shows the real
                            HOL name. *)
fun splitName name =
    let val stem = dropExt name
    in
      case String.fields (fn c => c = #".") stem of
          [s]             => (s, NONE)
        | [s, f]          => (s, SOME f)
        | [s, "", encoded] =>
            (s, SOME (UC_ASCII_Encode.decode encoded))
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

(* Backtick-wrap labels so the sidebar renders them in monospace
   (entries are HOL identifiers). *)
fun renderEntry struct_ (func, filename) =
    "  - [`" ^ entryLabel struct_ func ^ "`](" ^ filename ^ ")\n"

(* Emit one structure group.  If the group has a single-component
   entry (`<Struct>.smd`, the docs for the structure as a whole),
   use it as the parent's link target; otherwise emit a draft
   chapter `[Struct]()` -- mdbook renders it as a non-clickable
   parent under which the function entries are indented in the
   sidebar.  Either way the per-function entries are indented two
   spaces, which mdbook reads as a sub-chapter list. *)
fun renderGroup (struct_, entries) =
    let
      (* If a single-component entry (display = NONE) exists, it's
         the docs for the structure itself; use as parent link.  The
         rest are emitted as sub-entries. *)
      val (parent, children) =
          case List.partition (fn (f, _) => not (Option.isSome f)) entries of
              ([(_, filename)], rest) =>
                ("- [" ^ struct_ ^ "](" ^ filename ^ ")\n", rest)
            | _ => ("- [" ^ struct_ ^ "]()\n", entries)
    in
      parent ^ String.concat (List.map (renderEntry struct_) children)
    end

fun renderSummary groups =
    "# Summary\n\n" ^
    String.concat (List.map renderGroup groups)

(* ===== --identifiers mode ===== *)

(* Escape for a JS double-quoted string literal.  Only `\`, `"`
   and the C0 controls need it: UTF-8 bytes pass through
   untouched, as they do in mdbook's own searchindex.js, because
   every page loading this file declares <meta charset="UTF-8">.
   Defensive -- no entry name in help/Docfiles currently needs
   escaping -- but a new one must not be able to break the file. *)
fun jsEscape s =
    let
      val digits = "0123456789abcdef"
      fun hex n =
          String.implode [String.sub (digits, (n div 16) mod 16),
                          String.sub (digits, n mod 16)]
      fun esc c =
          if c = #"\\" then "\\\\"
          else if c = #"\"" then "\\\""
          else if Char.ord c < 32 then "\\u00" ^ hex (Char.ord c)
          else String.str c
    in
      String.translate esc s
    end

(* One `[qualified, short, page]` record.  `qualified` and `short`
   are the *decoded* names a reader would type (splitName has
   already undone any UC_ASCII_Encode'ing); `page` is the encoded
   stem plus `.html`, i.e. the filename mdbook actually renders.
   `short` is carried explicitly rather than recovered by splitting
   `qualified` at its last dot, because a decoded HOL identifier
   may itself contain a dot. *)
fun renderIdentifier struct_ (func, filename) =
    let
      val short = entryLabel struct_ func
      val qualified =
          case func of
              NONE => struct_
            | SOME _ => struct_ ^ "." ^ short
    in
      "[\"" ^ jsEscape qualified ^ "\",\"" ^ jsEscape short ^
      "\",\"" ^ jsEscape (dropExt filename) ^ ".html\"],\n"
    end

(* The whole scan as a JS data file.  One record per line, however
   long the line comes out: this is generated data, like the
   searchindex.js that sits beside it, not source to be read at 80
   columns. *)
fun renderIdentifiers groups =
    "/* Generated -- do not edit.  Loaded by Manual/theme/\n\
    \   hol-searcher.js; see Manual/Developers/manual-authoring.md.\n\
    \   Long data lines are intentional. */\n\
    \window.hol_identifiers = {entries: [\n" ^
    String.concat
      (List.map (fn (s, es) =>
                    String.concat (List.map (renderIdentifier s) es))
                groups) ^
    "]};\n"

fun main () =
    let
      val (identifiers, dir) =
          case CommandLine.arguments () of
              [d] => (false, d)
            | ["--identifiers", d] => (true, d)
            | _ => die "usage: gen_reference_summary [--identifiers] \
                       \DOCFILES_DIR"
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
      (* Both modes render `groupsSorted`, so the sidebar and the
         identifier table cannot disagree about which entries
         exist or in what order. *)
      emit (if identifiers then renderIdentifiers groupsSorted
            else renderSummary groupsSorted)
    end
