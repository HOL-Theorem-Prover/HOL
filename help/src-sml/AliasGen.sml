structure AliasGen = struct

(* ----------------------------------------------------------------------
   AliasGen — generate the alias entries in help/generated-alias-docs/
   from the canonical entries in help/Docfiles/.

   A canonical entry's YAML frontmatter declares its aliases:

       >>__ Parse.temp_set_grammars $ valOf $ grammarDB {thyname="hol"};
       ---
       aliases:
         - BasicProvers.Cases_on
       ---
       ## `Cases_on`
       ...

   The frontmatter may be preceded by polyscripter directive lines
   (`>>`, `>>__`, ...); those are preserved verbatim.

   For every alias listed, a stub entry is written to the output
   directory.  Stubs are build products: they are not in the repository
   and must not be edited.

       ---
       canonical: bossLib.Cases_on
       generated: true
       ---
       ## `Cases_on`
       ...

   The canonical also gets an "Also exported as ..." banner spliced
   into its body between the aliases-block markers; that is the only
   thing AliasGen writes back into help/Docfiles/.

   Modes:
     --check  : verify the canonicals' banners and the output directory
                are exactly what --regen would produce.  Exits 1 on any
                discrepancy.  Shares `plan` with --regen, so the two
                cannot drift apart.
     --regen  : write the stubs, delete stale ones, and refresh the
                canonicals' banners.
   ---------------------------------------------------------------------- *)

fun warn s = (TextIO.output(TextIO.stdErr, s ^ "\n");
              TextIO.flushOut TextIO.stdErr)
fun die s = (warn s; OS.Process.exit OS.Process.failure)

infix ++
val op++ = OS.Path.concat

(* ---- string helpers -------------------------------------------------- *)

fun trimNL s =
    let val n = size s
    in if n > 0 andalso String.sub(s, n - 1) = #"\n" then
         String.substring(s, 0, n - 1)
       else s
    end

val trimL = Substring.dropl Char.isSpace
val trimR = Substring.dropr Char.isSpace
fun trim s = Substring.string (trimR (trimL (Substring.full s)))

fun isBlank s = CharVector.all Char.isSpace s

(* Replace every occurrence of pat in s by rep. *)
fun replace_all (pat, rep) s =
    let
      val plen = size pat
      fun loop i acc =
          if plen = 0 orelse i + plen > size s then
            String.concat (List.rev (String.extract(s, i, NONE) :: acc))
          else if String.substring(s, i, plen) = pat then
            loop (i + plen) (rep :: acc)
          else
            loop (i + 1) (str (String.sub(s, i)) :: acc)
    in loop 0 [] end

(* ---- file I/O helpers ------------------------------------------------ *)

fun read_lines fname =
    let val istrm = TextIO.openIn fname
        fun loop acc =
            case TextIO.inputLine istrm of
                NONE => (TextIO.closeIn istrm; List.rev acc)
              | SOME s => loop (s::acc)
    in loop [] end

fun write_lines fname lines =
    let val ostrm = TextIO.openOut fname
    in List.app (fn s => TextIO.output(ostrm, s)) lines;
       TextIO.closeOut ostrm
    end

fun is_dir d = (OS.FileSys.isDir d) handle OS.SysErr _ => false

fun mkdir_p d =
    if d = "" orelse d = OS.Path.parentArc orelse d = OS.Path.currentArc
       orelse is_dir d
    then ()
    else (mkdir_p (OS.Path.dir d);
          OS.FileSys.mkDir d
          handle OS.SysErr _ =>
            if is_dir d then ()
            else die ("Couldn't create directory " ^ d))

fun file_exists f = OS.FileSys.access(f, [])

fun remove f = OS.FileSys.remove f
               handle OS.SysErr _ => warn ("Couldn't remove " ^ f)

(* ---- stem encoding (mirrors ParseDoc.encode_stem) -------------------- *)

fun safechar c = Char.isAlphaNum c orelse c = #"_"
val dotfields = String.fields (fn c => c = #".")

fun encode_stem s =
    case dotfields s of
        [x] => if CharVector.all safechar x then x
               else "." ^ UC_ASCII_Encode.encode x
      | [str,id] => if CharVector.all safechar id then s
                    else str ^ ".." ^ UC_ASCII_Encode.encode id
      | _ => raise Fail ("Badly formed stem: " ^ s)

fun decode_stem s =
    case dotfields s of
        [x] => s
      | ["", x] => UC_ASCII_Encode.decode x
      | [_, _] => s
      | [str, "", x] => str ^ "." ^ UC_ASCII_Encode.decode x
      | _ => raise Fail ("Badly encoded stem: " ^ s)

(* ---- preamble / frontmatter / body splitting ------------------------- *)

(* A .smd entry may open with polyscripter directive lines (typically
   the `>>__ Parse.temp_set_grammars ...` grammar pin) before its YAML
   frontmatter; see Manual/Tools/polyscripter.sml.  Split a file into
   (preamble, frontmatter-content, body), stripping the `---`
   delimiters.  A file with no frontmatter yields ([], [], all lines). *)
fun split_frontmatter (lines : string list) =
    let
      fun grab acc [] = NONE
        | grab acc ("---\n" :: ls) = SOME (List.rev acc, ls)
        | grab acc (l :: ls) = grab (l :: acc) ls
      fun scan pre [] = ([], [], lines)
        | scan pre ("---\n" :: rest) =
            (case grab [] rest of
                 SOME (fm, body) => (List.rev pre, fm, body)
               | NONE => ([], [], lines)) (* malformed: no closing --- *)
        | scan pre (l :: rest) =
            if String.isPrefix ">>" l orelse isBlank l then
              scan (l :: pre) rest
            else ([], [], lines)
    in
      scan [] lines
    end

(* ---- YAML mini-parser -----------------------------------------------

   Supports just the subset we need:
     key: value          (string)
     key:                (list)
       - item1
       - item2

   No nested mappings, no quoting, no escapes.
 ---------------------------------------------------------------------- *)

datatype yval = YStr of string | YList of string list

fun parse_yaml (lines : string list) : (string * yval) list =
    let
      fun keyVal raw =
          let val s = trimNL raw
              val (k, rest) = Substring.splitl (fn c => c <> #":")
                                               (Substring.full s)
          in
            if Substring.isEmpty rest then
              die ("Frontmatter line is missing its ':': " ^ s)
            else (trim (Substring.string k),
                  trim (Substring.string (Substring.triml 1 rest)))
          end
      fun isListItem s =
          let val ss = trimL (Substring.full (trimNL s))
          in not (Substring.isEmpty ss) andalso
             Substring.sub(ss, 0) = #"-"
          end
      fun listVal s =
          let val ss = trimL (Substring.full (trimNL s))
          in trim (Substring.string (Substring.triml 1 ss))
          end
      fun loop acc [] = List.rev acc
        | loop acc (l :: rest) =
          if isBlank l then loop acc rest
          else if isListItem l then
            die ("Unexpected list item with no preceding key: " ^ trimNL l)
          else
            let val (k, v) = keyVal l
            in if v = "" then
                 (* gather list items *)
                 let
                   fun lloop items rest =
                       case rest of
                           [] => (List.rev items, [])
                         | l :: rest' =>
                           if isBlank l then lloop items rest'
                           else if isListItem l then
                             lloop (listVal l :: items) rest'
                           else (List.rev items, l :: rest')
                   val (items, rest') = lloop [] rest
                 in loop ((k, YList items) :: acc) rest'
                 end
               else loop ((k, YStr v) :: acc) rest
            end
    in loop [] lines end

fun lookup_str fm k =
    case List.find (fn (k',_) => k' = k) fm of
        SOME (_, YStr s) => SOME s
      | SOME (_, YList _) =>
          die ("Frontmatter key '" ^ k ^ "' should be a string, got list")
      | NONE => NONE

fun lookup_list fm k =
    case List.find (fn (k',_) => k' = k) fm of
        SOME (_, YList xs) => SOME xs
      | SOME (_, YStr s) =>
          die ("Frontmatter key '" ^ k ^ "' should be a list, got string '" ^
               s ^ "'")
      | NONE => NONE

(* ---- per-file analysis ---------------------------------------------- *)

(* `aliases` is empty for the overwhelming majority of entries; a
   non-empty list makes the entry a canonical.  There is no third case:
   stubs live in the output directory, and a committed file carrying
   `canonical:` is an error reported by cross_check. *)
type entry = {
  stem : string,           (* decoded, e.g. "bossLib.Cases_on" or "Lib.++" *)
  encoded : string,        (* filename basename without .smd *)
  raw : string list,       (* the file exactly as read *)
  preamble : string list,  (* polyscripter lines ahead of the frontmatter *)
  fm : (string * yval) list,
  body : string list,
  aliases : string list    (* decoded stems *)
}

fun read_entry docdir fname : entry =
    let val raw = read_lines (docdir ++ fname)
        val (preamble, fm_lines, body) = split_frontmatter raw
        val fm = parse_yaml fm_lines
        val encoded = OS.Path.base fname
    in
      { stem = decode_stem encoded, encoded = encoded, raw = raw,
        preamble = preamble, fm = fm, body = body,
        aliases = case lookup_list fm "aliases" of
                      SOME xs => xs
                    | NONE => [] }
    end
    handle Fail msg => die (fname ^ ": " ^ msg)

(* Sorted, so that --regen's log and the order files are written in are
   reproducible rather than readdir-dependent. *)
fun list_smd_files docdir =
    let val dstrm = OS.FileSys.openDir docdir
        fun loop acc =
            case OS.FileSys.readDir dstrm of
                NONE => (OS.FileSys.closeDir dstrm;
                         Listsort.sort String.compare acc)
              | SOME s =>
                if OS.Path.ext s = SOME "smd" then loop (s :: acc)
                else loop acc
    in loop [] end

(* ---- stub generation ------------------------------------------------- *)

(* Pull the first ``` hol4 ... ``` block out of a body so we can carry
   the type signature over to the stub.  Returns the raw lines of the
   block (including fences), or [] for a prose-only entry -- an alias
   page with no signature beats one with a fabricated signature. *)
fun preserve_signature body =
    let
      fun isFence s = String.isPrefix "```" (trim s)
      fun grab acc [] = List.rev acc
        | grab acc (l::ls) =
            if isFence l then List.rev (l :: acc) else grab (l::acc) ls
      fun findStart [] = NONE
        | findStart (l::ls) =
            if isFence l then SOME (l, ls) else findStart ls
    in
      case findStart body of
          NONE => []
        | SOME (open_fence, rest) => grab [open_fence] rest
    end

(* Render a frontmatter block (without the ---/--- delimiters). *)
fun format_yaml fm =
    let
      fun lines (k, YStr s) = [k ^ ": " ^ s ^ "\n"]
        | lines (k, YList xs) =
            (k ^ ":\n") :: map (fn x => "  - " ^ x ^ "\n") xs
    in
      List.concat (map lines fm)
    end

(* Strip out the alias-related keys we manage; preserve everything else
   (e.g. title:) verbatim and in original order. *)
fun other_keys fm =
    List.filter
      (fn (k, _) => k <> "aliases" andalso
                    k <> "canonical" andalso
                    k <> "generated")
      fm

val HR = "------------------------------------------------------------\
         \------------\n"

fun stub_lines {alias, canonical, sig_block} =
    let val canon_enc = encode_stem canonical
        val alias_enc = encode_stem alias
        val display_id =
            case dotfields alias of
                [_, id] => id
              | _ => alias
        (* Entries whose filename had to be encoded carry an explicit
           title so pandoc doesn't name the page after the mangling. *)
        val title_fm = if alias_enc = alias then []
                       else [("title", YStr alias)]
        val fm = ("canonical", YStr canonical) ::
                 ("generated", YStr "true") ::
                 title_fm
    in
      ("---\n" :: format_yaml fm @ ["---\n"]) @
      [ "## `" ^ display_id ^ "`\n",
        "\n" ] @
      sig_block @
      [ "\n",
        HR,
        "\n",
        "Re-exported from [`" ^ canonical ^ "`](#" ^ canon_enc ^
          "). See that\n",
        "entry for full documentation.\n" ]
    end

(* ---- canonical aliases-block (in-body) ------------------------------- *)

val ALIAS_BEGIN = "<!-- BEGIN aliases-block -->\n"
val ALIAS_END = "<!-- END aliases-block -->\n"

fun aliases_block aliases =
    let val items =
            String.concatWith ", "
              (map (fn a => "[`" ^ a ^ "`](#" ^ encode_stem a ^ ")")
                   aliases)
    in [ ALIAS_BEGIN,
         "\n",
         "*Also exported as " ^ items ^ ".*\n",
         "\n",
         ALIAS_END ]
    end

(* Splice or replace an aliases-block in the body.  We place it
   immediately after the first horizontal-rule line (a row of dashes)
   following the type signature; if no HR is found, we place it after
   the type-signature fence.  An existing block (between ALIAS_BEGIN and
   ALIAS_END markers) is replaced verbatim. *)

fun is_hr s =
    let val t = trim s
    in size t >= 3 andalso CharVector.all (fn c => c = #"-") t end

fun is_open_fence s = String.isPrefix "```" (trim s)

(* Remove an existing aliases-block (between ALIAS_BEGIN and ALIAS_END)
   from body, including the surrounding blank lines that fence it. *)
fun strip_existing body =
    let fun before_begin acc [] = List.rev acc
          | before_begin acc (l :: ls) =
            if l = ALIAS_BEGIN then
              (* Drop one trailing blank in acc, if present. *)
              let val acc' = case acc of "\n" :: t => t | _ => acc
              in skip_to_end acc' ls end
            else before_begin (l :: acc) ls
        and skip_to_end acc [] = List.rev acc
          | skip_to_end acc (l :: ls) =
            if l = ALIAS_END then
              (* Drop one leading blank in ls, if present. *)
              let val ls' = case ls of "\n" :: t => t | _ => ls
              in before_begin acc ls' end
            else skip_to_end acc ls
    in before_begin [] body end

(* Emit [HR, blank, BEGIN, blank, text, blank, END, blank] then the rest
   of the body (with one leading blank dropped to avoid doubling). *)
fun splice_aliases body aliases =
    let val body = strip_existing body
        val block = aliases_block aliases
        fun emit_after_hr (hrl : string, ls : string list) =
            let val ls' = case ls of "\n" :: t => t | _ => ls
            in hrl :: "\n" :: block @ ("\n" :: ls')
            end
        fun afterHR acc [] = List.rev acc
          | afterHR acc (l :: ls) =
            if is_hr l then List.revAppend(acc, emit_after_hr (l, ls))
            else afterHR (l :: acc) ls
        fun afterFence acc [] = List.rev acc
          | afterFence acc (l :: ls) =
            if is_open_fence l then
              let
                fun closeFence acc' [] = List.rev acc'
                  | closeFence acc' (l' :: ls') =
                    if is_open_fence l' then
                      List.revAppend(acc', l' :: afterHR [] ls')
                    else closeFence (l' :: acc') ls'
              in closeFence (l :: acc) ls end
            else afterFence (l :: acc) ls
    in afterFence [] body end

(* ---- top-level operations ------------------------------------------- *)

(* Build the file the canonical *should* look like. *)
fun rebuild_canonical (e : entry) =
    let val aliases = #aliases e
        val body' = splice_aliases (#body e) aliases
        val fm = ("aliases", YList aliases) :: other_keys (#fm e)
        val fm_lines = "---\n" :: format_yaml fm @ ["---\n"]
    in #preamble e @ fm_lines @ body' end

(* The stubs the canonicals call for: (filename, contents) pairs. *)
fun expected_stubs entries =
    List.concat
      (map (fn e =>
               if null (#aliases e) then []
               else
                 let
                   val canonical = #stem e
                   val sigb = preserve_signature (#body e)
                   fun stub a =
                       (encode_stem a ^ ".smd",
                        stub_lines {
                          alias = a, canonical = canonical,
                          sig_block =
                            map (replace_all (canonical, a)) sigb })
                 in map stub (#aliases e) end)
           entries)

(* Consistency checks that don't depend on file contents. *)
fun cross_check outdir entries =
    let
      val errs = ref ([] : string list)
      fun err s = errs := s :: !errs

      val stems = List.foldl (fn (e, s) => Binaryset.add(s, #stem e))
                             (Binaryset.empty String.compare) entries

      fun check_not_stub (e : entry) =
          case lookup_str (#fm e) "canonical" of
              SOME c =>
                err (#stem e ^ ": carries 'canonical: " ^ c ^
                     "' but stub entries are generated into " ^ outdir ^
                     " and must not be committed")
            | NONE => ()

      (* Every (canonical, alias) pair, flattened, so the per-alias
         checks are a plain fold rather than a nest of List.apps. *)
      val pairs =
          List.concat (map (fn e => map (fn a => (#stem e, a)) (#aliases e))
                           entries)

      fun check1 ((canonical, a), claimed) =
          (if a = canonical then
             err (canonical ^ ": lists itself as an alias")
           else if Binaryset.member(stems, a) then
             err (canonical ^ ": alias '" ^ a ^
                  "' collides with a hand-written entry")
           else ();
           (ignore (encode_stem a)
            handle Fail msg =>
              err (canonical ^ ": alias '" ^ a ^ "': " ^ msg));
           case Binarymap.peek (claimed, a) of
               SOME other =>
                 (err ("alias '" ^ a ^ "' is claimed by both " ^ other ^
                       " and " ^ canonical);
                  claimed)
             | NONE => Binarymap.insert(claimed, a, canonical))
    in
      List.app check_not_stub entries;
      ignore (List.foldl check1 (Binarymap.mkDict String.compare) pairs);
      List.rev (!errs)
    end

(* Canonicals whose on-disk form differs from the regenerated one.
   Compares against the lines read_entry already held, so this needs no
   second pass over the filesystem. *)
fun canonical_updates entries =
    List.mapPartial
      (fn e =>
          if null (#aliases e) then NONE
          else
            let val rebuilt = rebuild_canonical e
            in if #raw e = rebuilt then NONE
               else SOME (#encoded e ^ ".smd", rebuilt)
            end)
      entries

(* Stubs whose on-disk form differs (or which are missing). *)
fun stub_updates outdir stubs =
    List.filter
      (fn (fname, contents) =>
          let val path = outdir ++ fname
          in not (file_exists path) orelse read_lines path <> contents end)
      stubs

(* Files in outdir that no canonical calls for.  Refuse to touch
   anything that isn't marked as ours. *)
fun stale_stubs outdir stubs =
    let
      val wanted = List.foldl (fn ((f, _), s) => Binaryset.add(s, f))
                              (Binaryset.empty String.compare) stubs
      (* A marker test, deliberately not a YAML parse: this runs on
         files we are about to delete, and a malformed one must reach
         the diagnostic below rather than die inside the parser. *)
      fun is_generated f =
          let val (_, fm_lines, _) = split_frontmatter (read_lines f)
          in List.exists (fn l => trim l = "generated: true") fm_lines end
          handle IO.Io _ => false
    in
      if not (file_exists outdir) then []
      else
        List.mapPartial
          (fn f =>
              if Binaryset.member(wanted, f) then NONE
              else if is_generated (outdir ++ f) then SOME f
              else die ((outdir ++ f) ^
                        " is not marked 'generated: true'; refusing to \
                        \delete it.  The alias output directory is \
                        \AliasGen's alone."))
          (list_smd_files outdir)
    end

(* Everything --check and --regen both need.  They share it so that
   --check reports exactly what --regen would write, by construction
   rather than by two implementations agreeing. *)
fun plan outdir entries =
    let
      (* Structural errors first and alone: expected_stubs below would
         raise on a malformed stem that cross_check has just reported. *)
      val errs = cross_check outdir entries
      val () = if null errs then ()
               else (List.app (fn e => warn ("ERROR: " ^ e)) errs;
                     warn (Int.toString (length errs) ^
                           " consistency error(s)");
                     OS.Process.exit OS.Process.failure)
      val stubs = expected_stubs entries
    in
      { stubs = stubs,
        cupd = canonical_updates entries,
        supd = stub_updates outdir stubs,
        stale = stale_stubs outdir stubs }
    end

fun do_check docdir outdir entries =
    let
      val {stubs, cupd, supd, stale} = plan outdir entries
    in
      List.app (fn (f, _) =>
                   warn ("Out of sync: " ^ (docdir ++ f) ^
                         " differs from its regenerated form")) cupd;
      List.app (fn (f, _) =>
                   warn ("Out of sync: " ^ (outdir ++ f) ^
                         " missing or stale")) supd;
      List.app (fn f => warn ("Stale: " ^ (outdir ++ f) ^
                              " no longer corresponds to any alias")) stale;
      if null cupd andalso null supd andalso null stale then
        (print ("AliasGen: " ^ Int.toString (length stubs) ^
                " alias entries consistent.\n");
         OS.Process.exit OS.Process.success)
      else (warn (Int.toString (length cupd + length supd + length stale) ^
                  " out-of-sync file(s)");
            OS.Process.exit OS.Process.failure)
    end

fun do_regen docdir outdir entries =
    let
      val {stubs, cupd, supd, stale} = plan outdir entries
      val () = mkdir_p outdir
    in
      List.app
        (fn f => (print ("Removing " ^ (outdir ++ f) ^ "\n");
                  remove (outdir ++ f);
                  let val txt = outdir ++ (OS.Path.base f ^ ".txt")
                  in if file_exists txt then remove txt else ()
                  end))
        stale;
      List.app
        (fn (f, contents) => (print ("Writing " ^ (outdir ++ f) ^ "\n");
                              write_lines (outdir ++ f) contents))
        supd;
      List.app
        (fn (f, contents) => (print ("Rewriting " ^ (docdir ++ f) ^ "\n");
                              write_lines (docdir ++ f) contents))
        cupd;
      print ("AliasGen: " ^ Int.toString (length stubs) ^
             " alias entries in " ^ outdir ^ "; " ^
             Int.toString (length supd) ^ " written, " ^
             Int.toString (length stale) ^ " removed, " ^
             Int.toString (length cupd) ^ " canonical(s) updated.\n");
      OS.Process.exit OS.Process.success
    end

(* ---- main ------------------------------------------------------------ *)

fun usage () =
    (warn ("Usage: " ^ CommandLine.name() ^
           " [--check | --regen] <docdir> <outdir>");
     OS.Process.exit OS.Process.failure)

fun main () =
    let
      val (mode, docdir, outdir) =
          case CommandLine.arguments() of
              ["--check", d, od] => (do_check, d, od)
            | ["--regen", d, od] => (do_regen, d, od)
            | [d, od] => (do_check, d, od)  (* default *)
            | _ => usage ()
      val files = list_smd_files docdir
      (* An empty scan is a configuration error, not consistency: it is
         how this tool silently did nothing for months after the
         Docfiles were renamed from .md to .smd underneath it. *)
      val () = if null files then
                 die ("No .smd files in " ^ docdir ^
                      "; that is not a documentation directory.")
               else ()
      val entries = map (read_entry docdir) files
    in
      mode docdir outdir entries
    end

end (* struct *)
