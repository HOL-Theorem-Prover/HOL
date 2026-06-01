structure AliasGen = struct

(* ----------------------------------------------------------------------
   AliasGen — keep alias entries in help/Docfiles/ in sync with their
   canonical sources.

   A canonical entry's YAML frontmatter declares its aliases:

       ---
       aliases:
         - bossLib.Cases_on
       ---
       ## `Cases_on`
       ...

   A stub entry's frontmatter points back at the canonical and is
   marked auto-generated:

       ---
       canonical: BasicProvers.Cases_on
       generated: true
       ---
       ## `Cases_on`
       ...

   Modes:
     --check  : verify all stubs match what would be generated, and
                that the canonical/alias relation is consistent.
                Exits 1 on any discrepancy.
     --regen  : rewrite stubs (and the alias-block in canonicals)
                from the canonical's frontmatter.
   ---------------------------------------------------------------------- *)

fun warn s = (TextIO.output(TextIO.stdErr, s ^ "\n");
              TextIO.flushOut TextIO.stdErr)
fun die s = (warn s; OS.Process.exit OS.Process.failure)

infix ++
val op++ = OS.Path.concat

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

(* ---- frontmatter / body splitting ------------------------------------ *)

(* A "frontmatter" is a leading "---\n" ... "---\n" block.  Strip the
   delimiters; return (frontmatter-content, body).  If the file has no
   frontmatter, return ([], all lines). *)
fun split_frontmatter (lines : string list) : string list * string list =
    case lines of
        "---\n" :: rest =>
          let
            fun grab acc [] = NONE
              | grab acc ("---\n" :: ls) = SOME (List.rev acc, ls)
              | grab acc (l :: ls) = grab (l :: acc) ls
          in
            case grab [] rest of
                SOME (fm, body) => (fm, body)
              | NONE => ([], lines) (* malformed: no closing --- *)
          end
      | _ => ([], lines)

(* ---- YAML mini-parser -----------------------------------------------

   Supports just the subset we need:
     key: value          (string)
     key:                (list)
       - item1
       - item2

   No nested mappings, no quoting, no escapes.
 ---------------------------------------------------------------------- *)

datatype yval = YStr of string | YList of string list

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

fun parse_yaml (lines : string list) : (string * yval) list =
    let
      fun keyVal raw =
          let val s = trimNL raw
              val (k, rest) = Substring.splitl (fn c => c <> #":")
                                               (Substring.full s)
              val key = trim (Substring.string k)
              val v = if Substring.isEmpty rest then ""
                      else trim (Substring.string (Substring.triml 1 rest))
          in (key, v) end
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

datatype kind = Canonical of string list  (* aliases (decoded stems) *)
              | Stub of string             (* canonical (decoded stem) *)
              | Plain                      (* no alias relationship *)

type entry = {
  stem : string,           (* decoded, e.g. "bossLib.Cases_on" or "Lib.++" *)
  encoded : string,        (* filename basename without .md *)
  fm : (string * yval) list,
  body : string list,
  kind : kind
}

fun classify fm =
    let val ali = lookup_list fm "aliases"
        val can = lookup_str fm "canonical"
    in case (ali, can) of
           (NONE, NONE) => Plain
         | (SOME [], NONE) => Plain
         | (SOME xs, NONE) => Canonical xs
         | (NONE, SOME c) => Stub c
         | (SOME _, SOME _) =>
             die "Frontmatter has both 'aliases' and 'canonical'"
    end

fun read_entry docdir fname : entry =
    let val path = docdir ++ fname
        val lines = read_lines path
        val (fm_lines, body) = split_frontmatter lines
        val fm = parse_yaml fm_lines
        val encoded = OS.Path.base fname
        val stem = decode_stem encoded
        val kind = classify fm
    in
      { stem = stem, encoded = encoded, fm = fm, body = body, kind = kind }
    end
    handle Fail msg => die (fname ^ ": " ^ msg)

fun list_md_files docdir =
    let val dstrm = OS.FileSys.openDir docdir
        fun loop acc =
            case OS.FileSys.readDir dstrm of
                NONE => (OS.FileSys.closeDir dstrm; List.rev acc)
              | SOME s =>
                if OS.Path.ext s = SOME "md" then loop (s :: acc)
                else loop acc
    in loop [] end

(* ---- stub body generation ------------------------------------------- *)

(* Pull the first ``` hol4 ... ``` block out of an existing body so we can
   preserve the type signature for the stub.  Returns the raw lines of the
   block (including fences) plus the literal "------" hr that sometimes
   follows.  If there is no such block, returns a placeholder. *)
fun preserve_signature body =
    let
      fun isFence s = String.isPrefix "```" (trim s)
      fun grab acc [] = (List.rev acc, [])
        | grab acc (l::ls) =
            if isFence l then (List.rev (l :: acc), ls)
            else grab (l::acc) ls
      fun findStart [] = NONE
        | findStart (l::ls) =
            if isFence l then SOME (l, ls) else findStart ls
    in
      case findStart body of
          NONE => ["``` hol4\n", "(* signature unknown *)\n", "```\n"]
        | SOME (open_fence, rest) =>
          let val (block, _) = grab [open_fence] rest
          in block end
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

fun stub_lines {stem, sig_block, canonical, extra_fm} =
    let val canon_enc = encode_stem canonical
        val display_id =
            case dotfields stem of
                [_, id] => id
              | [_] => stem
              | _ => stem
        val fm = ("canonical", YStr canonical) ::
                 ("generated", YStr "true") ::
                 extra_fm
    in
      ("---\n" :: format_yaml fm @ ["---\n"]) @
      [ "## `" ^ display_id ^ "`\n",
        "\n" ] @
      sig_block @
      [ "\n",
        "------------------------------------------------------------------------\n",
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
fun rebuild_canonical (e : entry) aliases =
    let val body' = splice_aliases (#body e) aliases
        val fm = ("aliases", YList aliases) :: other_keys (#fm e)
        val fm_lines = "---\n" :: format_yaml fm @ ["---\n"]
    in fm_lines @ body' end

(* Build the file an alias stub *should* look like. *)
fun rebuild_stub (e : entry) canonical =
    let val sig_block = preserve_signature (#body e)
    in
      stub_lines { stem = #stem e,
                   sig_block = sig_block,
                   canonical = canonical,
                   extra_fm = other_keys (#fm e) }
    end

fun original_lines docdir fname = read_lines (docdir ++ fname)

fun cross_check entries =
    let
      val by_stem =
          List.foldl
            (fn (e, m) => Binarymap.insert(m, #stem e, e))
            (Binarymap.mkDict String.compare)
            entries

      fun find s = Binarymap.peek (by_stem, s)
      val errs = ref ([] : string list)
      fun err s = errs := s :: !errs

      fun check_canonical (e as { stem, kind, ... } : entry) =
          case kind of
              Canonical aliases =>
              List.app (fn a =>
                           case find a of
                               NONE =>
                               err (stem ^ ": alias '" ^ a ^
                                    "' has no .md file")
                             | SOME ae =>
                               (case #kind ae of
                                    Stub c =>
                                    if c = stem then ()
                                    else err (stem ^ " <-> " ^ a ^
                                              ": stub points at '" ^ c ^ "'")
                                  | _ =>
                                    err (a ^
                                         " is listed as alias of " ^ stem ^
                                         " but its frontmatter is not a stub")))
                       aliases
            | _ => ()

      fun check_stub (e as { stem, kind, ... } : entry) =
          case kind of
              Stub c =>
              (case find c of
                   NONE => err (stem ^ ": canonical '" ^ c ^
                                "' has no .md file")
                 | SOME ce =>
                   (case #kind ce of
                        Canonical aliases =>
                        if List.exists (fn a => a = stem) aliases then ()
                        else err (stem ^ ": canonical " ^ c ^
                                  " does not list this stub as alias")
                      | _ => err (stem ^ ": canonical " ^ c ^
                                  " is not marked as canonical")))
            | _ => ()
    in
      List.app check_canonical entries;
      List.app check_stub entries;
      List.rev (!errs)
    end

(* Compute (path, expected-content) pairs for every file the regen would
   touch.  The same routine is used by --check (compare) and --regen
   (write). *)
fun expected_outputs docdir entries =
    List.mapPartial
      (fn e =>
          case #kind e of
              Canonical aliases =>
              let
                val original = original_lines docdir
                                  (#encoded e ^ ".md")
                val rebuilt = rebuild_canonical e aliases
              in
                if original = rebuilt then NONE
                else SOME (#encoded e ^ ".md", original, rebuilt)
              end
            | Stub c =>
              let
                val original = original_lines docdir
                                  (#encoded e ^ ".md")
                val rebuilt = rebuild_stub e c
              in
                if original = rebuilt then NONE
                else SOME (#encoded e ^ ".md", original, rebuilt)
              end
            | Plain => NONE)
      entries

fun do_check docdir entries =
    let val errs = cross_check entries
        val diffs = expected_outputs docdir entries
    in
      List.app (fn e => warn ("ERROR: " ^ e)) errs;
      List.app (fn (f, _, _) =>
                   warn ("Out of sync: " ^ f ^
                         " differs from regenerated form"))
               diffs;
      if null errs andalso null diffs then
        (print "AliasGen: all alias entries consistent.\n";
         OS.Process.exit OS.Process.success)
      else (warn (Int.toString (length errs) ^ " consistency error(s); " ^
                  Int.toString (length diffs) ^ " out-of-sync file(s)");
            OS.Process.exit OS.Process.failure)
    end

fun do_regen docdir entries =
    let val errs = cross_check entries
        val () = if null errs then ()
                 else (List.app (fn e => warn ("ERROR: " ^ e)) errs;
                       die "Refusing to regenerate while consistency errors present")
        val diffs = expected_outputs docdir entries
    in
      List.app
        (fn (f, _, rebuilt) =>
            (print ("Rewriting " ^ f ^ "\n");
             write_lines (docdir ++ f) rebuilt))
        diffs;
      print ("AliasGen: " ^ Int.toString (length diffs) ^
             " file(s) updated.\n");
      OS.Process.exit OS.Process.success
    end

(* ---- main ------------------------------------------------------------ *)

fun usage () =
    (warn ("Usage: " ^ CommandLine.name() ^
           " [--check | --regen] <docdir>");
     OS.Process.exit OS.Process.failure)

fun main () =
    let
      val (mode, docdir) =
          case CommandLine.arguments() of
              ["--check", d] => (do_check, d)
            | ["--regen", d] => (do_regen, d)
            | [d] => (do_check, d)  (* default *)
            | _ => usage ()
      val files = list_md_files docdir
      val entries = map (read_entry docdir) files
    in
      mode docdir entries
    end

end (* struct *)
