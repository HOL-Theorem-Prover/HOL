(*---------------------------------------------------------------------------*
 *                                                                           *
 *            HOL theories interpreted by SML structures.                    *
 *                                                                           *
 *---------------------------------------------------------------------------*)

structure TheoryPP :> TheoryPP =
struct

type thm      = Thm.thm;
type term     = Term.term
type hol_type = Type.hol_type
type shared_writemaps = {strings : string -> int, terms : Term.term -> string}
type shared_readmaps = {strings : int -> string, terms : string -> Term.term}
type thminfo = DB_dtype.thminfo
type sig_info_record = {
  name        : string,
  parents     : {name : string, url : string} list,
  all_thms    : (string * thm * thminfo) list
}
type struct_info_record = {
   theory      : string,
   parents     : (string*string) list,
   types       : (string*int) list,
   constants   : (string*hol_type) list,
   all_thms    : (string * thm * thminfo) list,
   mldeps      : string list,
   thydata     : string list * Term.term list *
                 (shared_writemaps -> HOLsexp.t) Symtab.table
 }

open Feedback Lib Portable Dep;

val ERR = mk_HOL_ERR "TheoryPP";

val temp_binding_pfx = "@temp"
val is_temp_binding = String.isPrefix temp_binding_pfx
fun temp_binding s = temp_binding_pfx ^ s
fun dest_temp_binding s =
  if is_temp_binding s then
    String.extract(s, size temp_binding_pfx, NONE)
  else raise ERR "dest_temp_binding" "String not a temp-binding"


val concat = String.concat;
val sort = Lib.sort (fn s1:string => fn s2 => s1<=s2);
val psort =
    Lib.sort (fn (s1:string,_:Thm.thm,_) => fn (s2,_:Thm.thm,_) => s1<=s2);
fun Thry s = s^"Theory";
fun ThrySig s = Thry s

fun with_parens pfn x =
  let open Portable PP
  in [add_string "(", pfn x, add_string ")"]
  end

fun pp_type mvartype mtype ty =
 let open Portable Type PP
     val pp_type = pp_type mvartype mtype
 in
  if is_vartype ty
  then case dest_vartype ty
        of "'a" => add_string "alpha"
         | "'b" => add_string "beta"
         | "'c" => add_string "gamma"
         | "'d" => add_string "delta"
         |  s   => add_string (mvartype^quote s)
  else
  case dest_thy_type ty
   of {Tyop="bool",Thy="min", Args=[]} => add_string "bool"
    | {Tyop="ind", Thy="min", Args=[]} => add_string "ind"
    | {Tyop="fun", Thy="min", Args=[d,r]} =>
          block INCONSISTENT 1 [
            add_string "(",
            pp_type d,
            add_string " -->",
            add_break (1,0),
            pp_type r,
            add_string ")"
          ]
   | {Tyop,Thy,Args} =>
          block INCONSISTENT (size mtype) [
            add_string mtype,
            add_string (quote Tyop),
            add_break (1,0),
            add_string (quote Thy),
            add_break (1,0),
            add_string "[",
            block INCONSISTENT 1 (
              pr_list pp_type [add_string ",", add_break (1,0)] Args
            ),
            add_string "]"
          ]
 end

val include_html_docs = ref true
val _ = Feedback.register_btrace
          ("TheoryPP.include_html_docs", include_html_docs)

fun classify As Ds Ts [] = (As,Ds,Ts)
  | classify As Ds Ts ((r as (s,th,i:thminfo))::rest) =
    let open DB_dtype
    in
      case #class i of
          Axm => classify (r::As) Ds Ts rest
        | Def => classify As (r::Ds) Ts rest
        | Thm => classify As Ds (r::Ts) rest
    end

fun html_escape s =
    let
      fun esc #"<" = "&lt;"
        | esc #">" = "&gt;"
        | esc #"&" = "&amp;"
        | esc #"\"" = "&quot;"
        | esc c = String.str c
    in
      String.translate esc s
    end

fun print_doc_html pp_thm info_record ostrm = let
  val {name,parents,all_thms} = info_record
  val parents' =
      Lib.sort (fn p1 : {name:string,url:string} => fn p2 => #name p1 <= #name p2)
               parents
  val rm_temp      = List.filter (fn (s, _, _) => not (is_temp_binding s))
  val all_thms'    = rm_temp all_thms
  val (axioms,definitions,theorems) = classify [] [] [] all_thms'
  val axioms'      = psort axioms
  val definitions' = psort definitions
  val theorems'    = psort theorems
  val filter_visible =
      List.mapPartial
        (fn (s, th, {private=false, loc, ...}:thminfo) => SOME (s, th, loc)
          | _ => NONE)
  val axioms''      = filter_visible axioms'
  val definitions'' = filter_visible definitions'
  val theorems''    = filter_visible theorems'
  val curr_docs_dir = OS.Path.concat (OS.FileSys.getDir(), ".hol/docs")
  fun src_url loc =
      case loc of
          DB_dtype.Unknown => NONE
        | DB_dtype.Located {scriptpath, linenum, ...} =>
          let
            val abs_sml = holpathdb.subst_pathvars scriptpath
            val {dir, file} = OS.Path.splitDirFile abs_sml
            val {base, ...} = OS.Path.splitBaseExt file
            val abs_html =
                OS.Path.concat (dir,
                  OS.Path.concat (".hol/docs", base ^ ".html"))
            val rel =
                OS.Path.mkRelative {path = abs_html, relativeTo = curr_docs_dir}
                handle OS.Path.Path => base ^ ".html"
          in
            SOME (rel ^ "#L" ^ Int.toString linenum)
          end
  fun out s = TextIO.output (ostrm, s)
  fun pp_to_stream th =
      let
        val pretty =
            if null (Thm.hyp th) andalso
               (Tag.isEmpty (Thm.tag th) orelse Tag.isDisk (Thm.tag th))
            then pp_thm th
            else
              with_flag (Globals.show_tags, true)
                        (with_flag (Globals.show_assums, true) pp_thm) th
      in
        PP.prettyPrint (out o html_escape, 75) pretty
      end
  fun pr_thm (s, th, loc) =
      let val esc = html_escape s in
        out "<div class=\"thm\" id=\""; out esc; out "\">\n";
        out "<div class=\"thm-name\"><a class=\"anchor\" href=\"#";
        out esc; out "\" aria-hidden=\"true\">#</a>";
        (case src_url loc of
             NONE => (out "<code>"; out esc; out "</code>")
           | SOME url =>
             (out "<a class=\"src-link\" href=\""; out (html_escape url);
              out "\"><code>"; out esc; out "</code></a>"));
        out "</div>\n<pre>";
        pp_to_stream th
          handle e =>
            (TextIO.print
               ("Failed to print theorem in theory export: " ^ s ^ "\n");
             TextIO.print (General.exnMessage e ^ "\n");
             raise e);
        out "</pre>\n</div>\n"
      end
  fun pr_thm_section _ [] = ()
    | pr_thm_section heading plist =
        (out "<section>\n<h2>"; out heading; out "</h2>\n";
         List.app pr_thm plist;
         out "</section>\n")
  fun pr_parent ({name=pname, url} : {name:string,url:string}) =
      (out "<li><a href=\""; out (html_escape url); out "\">";
       out (html_escape pname); out "</a></li>\n")
in
  out "<!DOCTYPE html>\n\
      \<html lang=\"en\">\n\
      \<head>\n\
      \<meta charset=\"UTF-8\">\n\
      \<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
      \<title>Theory: ";
  out (html_escape name);
  out "</title>\n\
      \<style>\n\
      \  :root {\n\
      \    --bg: #ffffff;\n\
      \    --fg: #1f2328;\n\
      \    --muted: #57606a;\n\
      \    --accent: #0969da;\n\
      \    --pre-bg: #f6f8fa;\n\
      \    --pre-border: #d0d7de;\n\
      \    --rule: #d8dee4;\n\
      \  }\n\
      \  html { background: var(--bg); }\n\
      \  body {\n\
      \    font-family: system-ui, -apple-system, \"Segoe UI\", Roboto,\n\
      \                 \"Helvetica Neue\", Arial, sans-serif;\n\
      \    color: var(--fg);\n\
      \    line-height: 1.55;\n\
      \    max-width: 60rem;\n\
      \    margin: 2rem auto;\n\
      \    padding: 0 1.25rem 3rem;\n\
      \  }\n\
      \  h1 { font-size: 1.9rem; margin: 0 0 1.25rem; }\n\
      \  h1 .thy-prefix { color: var(--muted); font-weight: 400; }\n\
      \  h2 {\n\
      \    font-size: 1.25rem;\n\
      \    margin: 2rem 0 0.75rem;\n\
      \    padding-bottom: 0.3rem;\n\
      \    border-bottom: 1px solid var(--rule);\n\
      \  }\n\
      \  ul.parents { list-style: none; padding: 0; margin: 0 0 1rem; }\n\
      \  ul.parents li { display: inline-block; margin: 0 0.5rem 0.4rem 0; }\n\
      \  ul.parents a {\n\
      \    background: var(--pre-bg);\n\
      \    border: 1px solid var(--pre-border);\n\
      \    border-radius: 999px;\n\
      \    padding: 0.15rem 0.7rem;\n\
      \    text-decoration: none;\n\
      \    color: var(--accent);\n\
      \    font-size: 0.92rem;\n\
      \  }\n\
      \  ul.parents a:hover { background: #eaeef2; }\n\
      \  .thm { margin: 1.1rem 0; }\n\
      \  .thm-name {\n\
      \    font-size: 1rem;\n\
      \    font-weight: 600;\n\
      \    margin-bottom: 0.25rem;\n\
      \  }\n\
      \  .thm-name code {\n\
      \    font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;\n\
      \    font-size: 0.95rem;\n\
      \  }\n\
      \  .src-link { color: inherit; text-decoration: none; }\n\
      \  .src-link:hover code {\n\
      \    text-decoration: underline; color: var(--accent);\n\
      \  }\n\
      \  .anchor {\n\
      \    color: var(--muted);\n\
      \    text-decoration: none;\n\
      \    margin-right: 0.4rem;\n\
      \    opacity: 0;\n\
      \    transition: opacity 0.1s;\n\
      \  }\n\
      \  .thm:hover .anchor, .thm:focus-within .anchor { opacity: 1; }\n\
      \  .thm:target { background: #fff8c5; border-radius: 6px; }\n\
      \  pre {\n\
      \    background: var(--pre-bg);\n\
      \    border: 1px solid var(--pre-border);\n\
      \    border-left: 3px solid var(--accent);\n\
      \    border-radius: 6px;\n\
      \    padding: 0.65rem 0.9rem;\n\
      \    margin: 0;\n\
      \    overflow-x: auto;\n\
      \    font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;\n\
      \    font-size: 0.92rem;\n\
      \    line-height: 1.5;\n\
      \  }\n\
      \</style>\n\
      \</head>\n\
      \<body>\n\
      \<h1><span class=\"thy-prefix\">Theory</span> ";
  out (html_escape name);
  out "</h1>\n";
  (case parents' of
       [] => ()
     | _ => (out "<h2>Parents</h2>\n<ul class=\"parents\">\n";
             List.app pr_parent parents';
             out "</ul>\n"));
  pr_thm_section "Axioms" axioms'';
  pr_thm_section "Definitions" definitions'';
  pr_thm_section "Theorems" theorems'';
  out "</body>\n</html>\n"
end

(* Write an HTML mirror of a Script.sml file with anchored line numbers,
   so that source-link URLs of the form "<thy>Script.html#Lnnn" land on
   the right line in any browser. *)
fun write_script_html {script_path, out_path} =
    let
      val instream = TextIO.openIn script_path
      val ostream = TextIO.openOut out_path
      fun out s = TextIO.output (ostream, s)
      val {file, ...} = OS.Path.splitDirFile script_path
      fun loop n =
          case TextIO.inputLine instream of
              NONE => ()
            | SOME line =>
              let
                val len = size line
                val (body, nl) =
                    if len > 0 andalso String.sub(line, len - 1) = #"\n" then
                      (String.substring(line, 0, len - 1), true)
                    else (line, false)
                val ns = Int.toString n
              in
                out "<span class=\"line\" id=\"L"; out ns; out "\">";
                out "<span class=\"line-num\">"; out ns; out "</span>";
                out (html_escape body);
                out "</span>";
                if nl then out "\n" else ();
                loop (n + 1)
              end
    in
      out "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n\
          \<meta charset=\"UTF-8\">\n\
          \<meta name=\"viewport\" \
                \content=\"width=device-width, initial-scale=1\">\n\
          \<title>Source: ";
      out (html_escape file);
      out "</title>\n\
          \<style>\n\
          \  :root { --bg:#ffffff; --fg:#1f2328; --muted:#6e7781;\n\
          \          --pre-bg:#f6f8fa; --pre-border:#d0d7de; --hl:#fff8c5; }\n\
          \  html { background: var(--bg); }\n\
          \  body { font-family: system-ui, -apple-system, sans-serif;\n\
          \         color: var(--fg); margin: 1.5rem auto; max-width: 80rem;\n\
          \         padding: 0 1rem 3rem; line-height: 1.4; }\n\
          \  h1 { font-size: 1.2rem; font-weight: 600; margin: 0 0 0.8rem; }\n\
          \  pre {\n\
          \    background: var(--pre-bg); border: 1px solid var(--pre-border);\n\
          \    border-radius: 6px; padding: 0.6rem 0.9rem; margin: 0;\n\
          \    overflow-x: auto;\n\
          \    font-family: ui-monospace, SFMono-Regular, Menlo, Consolas,\n\
          \                 monospace;\n\
          \    font-size: 0.9rem; line-height: 1.5;\n\
          \  }\n\
          \  .line-num { display: inline-block; width: 4em;\n\
          \              padding-right: 1em; text-align: right;\n\
          \              color: var(--muted); user-select: none; }\n\
          \  .line:target { background: var(--hl); }\n\
          \</style>\n\
          \</head>\n\
          \<body>\n\
          \<h1>";
      out (html_escape file);
      out "</h1>\n<pre>";
      loop 1
        handle e => (TextIO.closeIn instream;
                     TextIO.closeOut ostream;
                     raise e);
      out "</pre>\n</body>\n</html>\n";
      TextIO.closeIn instream;
      TextIO.closeOut ostream
    end

fun pp_sig info_record = let
  open PP
  val {name,parents,all_thms} = info_record
  val parents'     = sort parents
  val rm_temp      = List.filter (fn (s, _, _) => not (is_temp_binding s))
  val all_thms'    = rm_temp all_thms
  val (axioms,definitions,theorems) = classify [] [] [] all_thms'
  val axioms'      = psort axioms
  val definitions' = psort definitions
  val theorems'    = psort theorems
  fun vblock(header, ob_pr, obs) =
    block CONSISTENT 2 [
      add_string ("(*  "^header^ "  *)"), NL,
      block CONSISTENT 0 (pr_list ob_pr [NL] obs)
    ]

  val filter_visible =
      List.mapPartial (fn (s, th, {private=false,...}:thminfo) => SOME (s,th)
                      |            _                 => NONE)
  fun pthms (heading, ths) =
    vblock(heading,
           (fn (s,th,{private,...}:thminfo) =>
               block CONSISTENT 0
                     (if is_temp_binding s orelse private then []
                      else
                        [add_string("val "^ s ^ " : thm")])),
           ths)
in
  block CONSISTENT 0 [
    add_string ("signature "^ThrySig name^" ="), NL,
    block CONSISTENT 2 [
       add_string "sig", NL,
       block CONSISTENT 0 (
         [add_string"type thm = Thm.thm"] @
         (if null axioms' then []
          else [NL, NL, pthms ("Axioms",axioms')]) @
         (if null definitions' then []
          else [NL, NL, pthms("Definitions", definitions')]) @
         (if null theorems' then []
          else [NL, NL, pthms ("Theorems", theorems')])
       )
    ], NL,
    add_string"end", NL
  ]
end;

(*---------------------------------------------------------------------------
 *  Print a theory as a module.
 *---------------------------------------------------------------------------*)

val stringify = Lib.mlquote

fun is_atom t = Term.is_var t orelse Term.is_const t
fun strip_comb t = let
  fun recurse acc t = let
    val (f, x) = Term.dest_comb t
  in
    recurse (x::acc) f
  end handle HOL_ERR _ => (t, List.rev acc)
in
  recurse [] t
end

infix >>
open smpp

fun mlower s m =
  case m ((), []) of
      NONE => raise Fail ("Couldn't print Theory" ^ s)
    | SOME(_, (_, ps)) => PP.block PP.CONSISTENT 0 ps


fun pp_struct hash (info_record : struct_info_record) = let
  open Term Thm
  val {theory=name, parents=parents0, thydata, mldeps, all_thms,
       types,constants} = info_record
  val parents1 =
    List.mapPartial (fn (s,_) => if "min"=s then NONE else SOME (Thry s))
                    parents0
  val jump = add_newline >> add_newline
  fun pblock(ob_pr, obs) =
      case obs of
        [] => nothing
      |  _ =>
         block CONSISTENT 0
           (
           add_string "local open " >>
           block INCONSISTENT 0 (pr_list ob_pr (add_break (1,0)) obs) >>
           add_break(1,0) >>
           add_string "in end;"
           )

  fun pparent (s,_) = Thry s

  fun pr_bind(s, th, {private,...}:thminfo) = let
    val addsbl = pr_list add_string (add_break(1,2))
  in
    if is_temp_binding s orelse private then nothing
    else
      (* this rigmarole is necessary to allow ML bindings where the name is
         a datatype constructor or an infix, or both *)
      block CONSISTENT 0
        (block INCONSISTENT 0 (addsbl ["fun","op",s,"_","=","()"]) >>
         add_break(1,0) >>
         block INCONSISTENT 0 (addsbl ["val","op",s,"=","TDB.find",mlquote s]))
  end

  val bind_theorems =
     block CONSISTENT 0 (
       if null all_thms then nothing
       else
         block CONSISTENT 0 (pr_list pr_bind add_newline all_thms) >>
         add_newline
     )

  fun pr_ps NONE = nothing
    | pr_ps (SOME pp) = block CONSISTENT 0 (lift pp ())

  fun pr_psl l =
       block CONSISTENT 0
         (pr_list pr_ps (add_newline >> add_newline) l)
  fun pr_pcl l =
      block CONSISTENT 0 (
        pr_list (fn pf => block CONSISTENT 0 (lift pf ()))
                (add_newline >> add_newline)
                l
      )
  val datfile =
      mlquote (
        holpathdb.reverse_lookup {
          path = OS.Path.concat(OS.FileSys.getDir(), name ^ "Theory.dat")
        }
      )
  val m =
      block CONSISTENT 0 (
       add_string (String.concatWith " "
                       ["structure",Thry name,":>", ThrySig name,"="]) >>
       add_newline >>
       block CONSISTENT 2 (
          add_string "struct" >> jump >>
          block CONSISTENT 0 (
            block CONSISTENT 0 (
             add_string ("val _ = if !Globals.print_thy_loads") >>
             add_break (1,2) >>
             add_string
               ("then TextIO.print \"Loading "^ Thry name ^ " ... \"") >>
             add_break (1,2) >>
             add_string "else ()") >> jump >>
             add_string "open Type Term Thm"  >> add_newline >>
             pblock (add_string,
               Listsort.sort String.compare parents1 @ mldeps) >>
             add_newline >> add_newline >>
             block CONSISTENT 0 (
              add_string "structure TDB = struct" >> add_break(1,2) >>
              add_string "val path =" >> add_break(1,4) >>
                add_string ("holpathdb.subst_pathvars "^datfile) >>
                add_break(1,2) >>
              add_string "val timestamp = HOLFileSys.modTime path" >> add_break(1,2) >>
              add_string "val thydata = " >> add_break(1,4) >>
              block INCONSISTENT 0 (
                add_string "TheoryReader.load_thydata {" >> add_break (1,2) >>
                block CONSISTENT 0 (
                  block INCONSISTENT 2 (
                    add_string "thyname =" >> add_break(1,2) >>
                    add_string (mlquote name ^ ",")
                  ) >> add_break (1,0) >>
                  block INCONSISTENT 2 (
                    add_string "hash =" >> add_break(1,2) >>
                    add_string (mlquote hash ^ ",")
                  ) >> add_break (1,0) >>
                  block INCONSISTENT 2 (
                    add_string "path = path"
                  ) >>
                  add_break(1,~2) >> add_string "}"
                )
              ) >> add_break(1,2) >>
              add_string ("fun find s = #1 (valOf (Symtab.lookup thydata s))") >>
              add_break(1,0) >> add_string "end"
            ) >> add_break(1,0) >>
            add_string "val () = Theory.record_metadata" >> add_break(1,2) >>
            block INCONSISTENT 2 (
              add_string (mlquote name) >> add_break (1,0) >>
              add_string "{timestamp=TDB.timestamp, path=TDB.path}"
            ) >> jump >>
            bind_theorems
          )
        ) >> add_break(0,0) >>
        add_string "val _ = if !Globals.print_thy_loads then TextIO.print \
                   \\"done\\n\" else ()" >> add_newline >>
        add_string ("val _ = Theory.load_complete "^ stringify name) >>
        jump >>
        add_string "end" >> add_newline)
in
  mlower ": struct" m
end

(*---------------------------------------------------------------------------
 *  Print theory data separately.
 *---------------------------------------------------------------------------*)

fun pp_thydata (info_record : struct_info_record) = let
  open Term Thm
  val {theory = name, parents=parents0,
       thydata = (thydata_strings,thydata_tms, thydata), mldeps,
       all_thms,types,constants,...} = info_record
  val parents1 =
      List.mapPartial (fn (s,_) => if "min"=s then NONE else SOME (Thry s))
                      parents0
  open SharingTables

  val share_data = build_sharing_data {
        named_terms = [], named_types = [], unnamed_terms = [],
        unnamed_types = [],
        theorems = all_thms
      }
  val share_data = add_strings thydata_strings share_data
  val share_data = add_terms thydata_tms share_data

  local open HOLsexp in
  val enc_thid = pair_encode (String, String)
  val enc_thid_and_parents =
      curry (pair_encode(String, list_encode enc_thid))
  end (* local *)

  fun enc_incorporate_types types =
      let open HOLsexp
      in
        tagged_encode "incorporate-types"
                      (list_encode (pair_encode(String,Integer))) types
      end

  fun enc_incorporate_constants constants =
      let open HOLsexp
      in
        tagged_encode "incorporate-consts"
                      (list_encode
                         (pair_encode(String, Integer o write_type share_data)))
                      constants
      end

  fun chunks w s =
    if String.size s <= w then [s]
    else String.substring(s, 0, w) :: chunks w (String.extract(s, w, NONE))

  val enc_cpl = HOLsexp.pair_encode(HOLsexp.String, fn x => x)

  fun list_loadable shared_writers thydata_map =
    Symtab.fold
      (fn (k, data) => fn rest => (k, data shared_writers) :: rest)
      thydata_map
      []
  fun enc_loadable shared_writers thydata_map =
      let open HOLsexp in
        tagged_encode "loadable-thydata" (list_encode enc_cpl)
                      (list_loadable shared_writers thydata_map)
      end
  val thysexp =
      let open HOLsexp
      in
        List [
          Symbol "theory",
          enc_thid_and_parents name parents0,
          enc_sdata share_data,
          tagged_encode "incorporate" (
            pair_encode(enc_incorporate_types, enc_incorporate_constants)
          ) (types, constants),
          enc_loadable {terms = write_term share_data,
                        strings = write_string share_data}
                       thydata
        ]
      end
in
  mlower ": dat" (lift HOLsexp.printer thysexp)
end handle e as Interrupt => raise e
         | e => raise ERR "pp_thydata"
                      ("Caught exception: " ^ General.exnMessage e)



end;  (* TheoryPP *)
