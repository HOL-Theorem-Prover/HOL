(* Stored theorem statements and their definition closure, as Markdown
   or annotated HTML. See README.md for configuration and limitations. *)
structure statementDossierLib :> statementDossierLib =
struct

open HolKernel Parse boolSyntax

type name = {Thy : string, Name : string}

datatype output_format = Markdown | Html

type config = {
  title : string,
  preamble : string,
  theorems : name list,
  expand_theories : string list,
  expand_consts : name list,
  stop_theories : string list,
  stop_consts : name list,
  equation_lemmas : (name * name list) list,
  source_dirs : (string * string) list,
  outputs : (output_format * string) list,
  snippets : (string * string) option,
  assumptions : {theorem : name, prose : string} option,
  supporting : name list
}

fun key ({Thy, Name} : name) = Thy ^ "$" ^ Name

fun name_of_const c =
  let val {Thy, Name, ...} = dest_thy_const c
  in {Thy = Thy, Name = Name} end

(* The constants of HOL's logic itself, left out of the per-definition
   lists of unexpanded constants. *)
fun is_logical c =
  List.exists (fn t => t = #Thy (name_of_const c)) ["min", "bool"]

fun mem_name n ns = List.exists (fn m => key m = key n) ns

fun dedup key_of xs =
  let
    fun go _ [] acc = List.rev acc
      | go seen (x :: rest) acc =
          let val k = key_of x in
            if HOLset.member (seen, k) then go seen rest acc
            else go (HOLset.add (seen, k)) rest (x :: acc)
          end
  in
    go (HOLset.empty String.compare) xs []
  end

fun repeated keys =
  dedup (fn s => s)
    (List.filter (fn k =>
       length (List.filter (fn k' => k' = k) keys) > 1) keys)

fun loaded_theories () =
  dedup (fn s => s)
    (List.filter (fn s => s <> "-")
      ((current_theory () handle HOL_ERR _ => "-") :: ancestry "-"))

(* The files under a directory whose names end with suffix, as paths.
   Directories whose names start with a dot (build outputs, VCS metadata,
   worktrees) and symbolic links to directories are skipped. *)
fun files_under suffix dir =
  let
    fun walk dir acc =
      let
        val stream = OS.FileSys.openDir dir
        fun loop acc =
          case OS.FileSys.readDir stream of
            NONE => acc
          | SOME f =>
              let val path = OS.Path.concat (dir, f) in
                if String.isPrefix "." f then loop acc
                else
                  case SOME (OS.FileSys.isDir path)
                         handle OS.SysErr _ => NONE (* dangling link *) of
                    NONE => loop acc
                  | SOME true =>
                      if OS.FileSys.isLink path then loop acc
                      else loop (walk path acc)
                  | SOME false =>
                      if String.isSuffix suffix f then loop (path :: acc)
                      else loop acc
              end
        val result = loop acc
      in
        OS.FileSys.closeDir stream; result
      end
  in
    List.rev (walk dir [])
  end

(* The theories whose scripts (<thy>Script.sml) lie under the given
   directories. *)
fun script_theories dirs =
  let
    val suffix = "Script.sml"
    fun theory path =
      let val f = OS.Path.file path
      in String.substring (f, 0, size f - size suffix) end
  in
    List.concat (map (map theory o files_under suffix) dirs)
  end

(* ---------------------------------------------------------------------
   Collecting constants and types
   --------------------------------------------------------------------- *)

(* The constants of a term in order of first appearance, reading the
   term left to right (operator before operands).  Numerals count as
   atoms, so their encoding (NUMERAL, BIT1, ...) is left out. *)
fun theorem_terms th = hyp th @ [concl th]

fun consts_lr tm =
  let
    fun go t acc =
      if numSyntax.is_numeral t then acc else
      case dest_term t of
        CONST _ => t :: acc
      | VAR _ => acc
      | COMB (f, x) => go x (go f acc)
      | LAMB (_, b) => go b acc
  in
    dedup (key o name_of_const) (List.rev (go tm []))
  end

fun theorem_consts th =
  dedup (key o name_of_const)
    (List.concat (map consts_lr (theorem_terms th)))

fun theorem_vars th =
  op_mk_set aconv (List.concat (map free_vars_lr (theorem_terms th)))

fun statement_vars th =
  op_mk_set aconv (theorem_vars th @ fst (strip_forall (concl th)))

fun atoms tm =
  let
    fun go t acc =
      case dest_term t of
        COMB (f, x) => go x (go f acc)
      | LAMB (v, b) => go b (v :: acc)
      | _ => t :: acc
  in
    go tm []
  end

fun tyops_of_type ty acc =
  if is_vartype ty then acc
  else
    let val {Thy, Tyop, Args} = dest_thy_type ty in
      List.foldl (fn (a, acc) => tyops_of_type a acc)
        ({Thy = Thy, Name = Tyop} :: acc) Args
    end

(* The type operators in the types of the atoms of a term. *)
fun tyops_of tm =
  List.foldl (fn (a, acc) => tyops_of_type (type_of a) acc) [] (atoms tm)

(* Each constant that TypeBase attributes to a datatype or record type
   (constructors, case constant, field selectors and updates, size
   function), keyed by the constant, with its type and a label: the
   field name for selectors and updates, the constant's name otherwise. *)
fun type_index () =
  let
    fun add_info (info, m) =
      let
        val (thy, tyop) = TypeBasePure.ty_name_of info
        val ty = {Thy = thy, Name = tyop}
        fun own c = (c, if is_const c then #Name (name_of_const c) else "")
        val consts =
          map own (TypeBasePure.constructors_of info) @
          ([own (TypeBasePure.case_const_of info)]
           handle HOL_ERR _ => [] (* not a datatype, e.g. int *)) @
          List.concat
            (map (fn (f, {accessor, fupd, ...}) =>
                     [(accessor, "." ^ f), (fupd, "with " ^ f ^ " updated")])
                 (TypeBasePure.fields_of info)) @
          (case TypeBasePure.size_of info of
             SOME (t, _) => [own t]
           | NONE => [])
        fun add ((c, label), m) =
          if is_const c then
            Redblackmap.insert (m, key (name_of_const c), (ty, label))
          else m
      in
        List.foldl add m consts
      end
  in
    List.foldl add_info (Redblackmap.mkDict String.compare) (TypeBase.elts ())
  end

(* ---------------------------------------------------------------------
   Looking things up in the theorem database
   --------------------------------------------------------------------- *)

(* The script file and line HOL records for a stored theorem. *)
fun location_of ({Thy, Name} : name) =
  case DB.lookup {Thy = Thy, Name = Name} of
    SOME (_, {loc = DB.Located {scriptpath, linenum, ...}, ...}) =>
      SOME (scriptpath, linenum)
  | _ => NONE

(* Source generators can change line numbers. When sources are supplied,
   find the declaration in the original script instead. *)

(* The scripts under the source directories, by file name: the path to
   read, and the path to show. *)
fun script_index (source_dirs : (string * string) list) =
  let
    fun entries (label, dir) =
      let
        val skip = size (OS.Path.concat (dir, "x")) - 1
        fun shown path =
          (if label = "" then "" else label ^ "/") ^
          String.extract (path, skip, NONE)
      in
        map (fn path => (OS.Path.file path, (path, shown path)))
          (files_under "Script.sml" dir)
      end
  in
    List.concat (map entries source_dirs)
  end

val source_lines = ref (Redblackmap.mkDict String.compare)

fun lines_of path =
  case Redblackmap.peek (!source_lines, path) of
    SOME ls => ls
  | NONE =>
      let
        val stream = TextIO.openIn path
        val ls = String.fields (fn c => c = #"\n")
                   (TextIO.inputAll stream)
      in
        TextIO.closeIn stream;
        source_lines := Redblackmap.insert (!source_lines, path, ls);
        ls
      end

fun first_line pred lines =
  let
    fun go _ [] = NONE
      | go i (l :: rest) = if pred l then SOME i else go (i + 1) rest
  in
    go 1 lines
  end

(* Whether a line declares name with one of the keywords, as in
   "Theorem name:" or "Definition name[simp]:". *)
fun declares keywords name line =
  let
    val l = Substring.dropl Char.isSpace (Substring.full line)
    fun name_ends rest =
      case Substring.first rest of
        NONE => true
      | SOME c => not (Char.isAlphaNum c orelse c = #"_" orelse c = #"'")
    fun with_keyword kw =
      let val prefix = kw ^ " " ^ name in
        Substring.isPrefix prefix l andalso
        name_ends (Substring.triml (size prefix) l)
      end
  in
    List.exists with_keyword keywords
  end

(* The line declaring a stored theorem: its Theorem/Definition/... header;
   for the theorems an Inductive or Definition derives (name_def,
   name_rules, ...), the header declaring name; failing these, an ML
   binding or a quoted name. *)
fun declaration_line lines name =
  let
    val derived = ["_def", "_rules", "_ind", "_cases", "_strongind"]
    val stems =
      List.mapPartial
        (fn sfx => if String.isSuffix sfx name
                   then SOME (String.substring (name, 0, size name - size sfx))
                   else NONE)
        derived
    fun try [] = NONE
      | try (pred :: rest) =
          case first_line pred lines of
            SOME l => SOME l
          | NONE => try rest
  in
    try ([declares ["Theorem", "Triviality", "Definition", "Inductive",
                    "CoInductive"] name] @
         map (declares ["Inductive", "CoInductive", "Definition"]) stems @
         [declares ["val"] name,
          fn l => String.isSubstring ("\"" ^ name ^ "\"") l])
  end

(* Where a stored theorem is declared, as a path to show and a line, if
   its script is under the source directories.  A theorem without a
   recorded location (e.g. the rules of an inductive relation) is looked
   up in its theory's script. *)
fun source_location index (n as {Thy, Name}) =
  let
    val file =
      case location_of n of
        SOME (scriptpath, _) => OS.Path.file scriptpath
      | NONE => Thy ^ "Script.sml"
  in
    case List.find (fn (f, _) => f = file) index of
      NONE => if isSome (location_of n) then SOME (file, NONE) else NONE
    | SOME (_, (path, shown)) =>
        SOME (shown, declaration_line (lines_of path) Name)
  end

fun line_of n = case location_of n of SOME (_, l) => l | NONE => 0

(* The stored theorems of a theory, private ones included, in source
   order. *)
val theory_cache = ref (Redblackmap.mkDict String.compare)

fun theory_data thy =
  case Redblackmap.peek (!theory_cache, thy) of
    SOME d => d
  | NONE =>
      let
        fun entry ((thy, n), (th, {class, ...} : DB.thminfo)) =
          ({Thy = thy, Name = n}, th, class)
        fun cmp ((n1, _, _), (n2, _, _)) =
          case Int.compare (line_of n1, line_of n2) of
            EQUAL => String.compare (key n1, key n2)
          | order => order
        val d = Listsort.sort cmp (map entry (DB.thy thy))
      in
        theory_cache := Redblackmap.insert (!theory_cache, thy, d); d
      end

(* The heads of the left-hand sides of the clauses of a definition. *)
fun defined_heads th =
  let
    fun head clause =
      let
        val body = snd (strip_forall clause)
        val (f, _) = strip_comb (if is_eq body then lhs body else body)
      in
        if is_const f then [f] else []
      end
  in
    List.concat (map head (strip_conj (snd (strip_forall (concl th)))))
  end

(* The stored definitions of a constant, and whether they define it: the
   theorem <name>_def if its left-hand sides are headed by the constant,
   then the other definitions of its theory with such a clause, then the
   rules theorem <name>_rules of an inductive relation; failing all these
   (e.g. for new_specification), the definitions that mention it, which
   need not define it.  A recursive
   definition's <name>_def holds its equations, which may be a theorem
   derived from a definition stored as <name>_def_primitive (over WFREC)
   or not stored at all; the primitive is shown only without them. *)
fun definitions_of c =
  let
    val {Thy, Name} = name_of_const c
    val data = theory_data Thy
    fun named n = List.filter (fn (m, _, _) => #Name m = n) data
    fun headed (_, th, _) = List.exists (same_const c) (defined_heads th)
    val defs = List.filter (fn (_, _, class) => class = DB.Def) data
    val equations = List.filter headed (named (Name ^ "_def"))
    fun is_primitive (m, _, _) = #Name m = Name ^ "_def_primitive"
    val others =
      List.filter
        (fn d as (m, _, _) =>
            headed d andalso #Name m <> Name ^ "_def" andalso
            not (is_primitive d andalso not (null equations)))
        defs
    val chosen = equations @ others @ named (Name ^ "_rules")
    val mentioning =
      List.filter (fn (_, th, _) => can (find_term (same_const c)) (concl th))
        defs
    fun strip ds = map (fn (m, th, _) => (m, th)) ds
  in
    if null chosen then (strip mentioning, false) else (strip chosen, true)
  end

(* The equation lemmas of a constant c: theorems of its theory, named
   <c>_<something>, without assumptions, that are conjunctions of
   equations !xs. f x1 ... xn = rhs with distinct variables xi and f a
   constant not in rhs, one of them for c. *)
fun find_equation_lemmas c =
  let
    val {Thy, Name} = name_of_const c
    (* the constant an equation is for *)
    fun equation_for conj =
      let val body = snd (strip_forall conj) in
        if not (is_eq body) then NONE
        else
          let val (f, args) = strip_comb (lhs body) in
            if is_const f andalso List.all is_var args andalso
               length (op_mk_set aconv args) = length args andalso
               not (can (find_term (same_const f)) (rhs body))
            then SOME f
            else NONE
          end
      end
    fun is_lemma (n, th, class) =
      class = DB.Thm andalso null (hyp th) andalso
      String.isPrefix (Name ^ "_") (#Name n) andalso
      let val heads =
        map equation_for (strip_conj (snd (strip_forall (concl th))))
      in
        List.all isSome heads andalso
        List.exists (same_const c) (map valOf heads)
      end
  in
    map (fn (n, th, _) => (n, th)) (List.filter is_lemma (theory_data Thy))
  end

(* ---------------------------------------------------------------------
   The closure
   --------------------------------------------------------------------- *)

datatype role = Expanded | TypeConst of name | Boundary

type entry = {const : term, reached_from : name, defs : (name * thm) list,
              defines : bool, lemmas : (name * thm) list, uses : term list}

fun role_of (cfg : config) tyidx c =
  let val n = name_of_const c in
    if mem_name n (#stop_consts cfg) orelse
       List.exists (fn t => t = #Thy n) (#stop_theories cfg) then Boundary
    else
      case Redblackmap.peek (tyidx, key n) of
        SOME (ty, _) => TypeConst ty
      | NONE =>
          if List.exists (fn t => t = #Thy n) (#expand_theories cfg) orelse
             mem_name n (#expand_consts cfg)
          then Expanded
          else Boundary
  end

fun lemmas_for (cfg : config) c =
  let
    val n = name_of_const c
    val listed =
      List.concat (map (fn (m, ls) => if key m = key n then ls else [])
                       (#equation_lemmas cfg))
    val found = find_equation_lemmas c
  in
    dedup (key o fst)
      (found @ map (fn l => (l, DB.fetch (#Thy l) (#Name l))) listed)
  end

(* Breadth-first closure from the constants of the theorems: the expanded
   constants with their definitions, in order of first appearance, and all
   constants met, in the same order.  The constants of equation lemmas are
   followed like those of definitions, since a reader may read the lemma
   instead. *)
fun closure (cfg : config) tyidx theorems =
  let
    fun visit [] _ entries met = (List.rev entries, List.rev met)
      | visit ((c, from) :: queue) seen entries met =
          let val k = key (name_of_const c) in
            if HOLset.member (seen, k) then visit queue seen entries met
            else
              let val seen = HOLset.add (seen, k) in
                case role_of cfg tyidx c of
                  Expanded =>
                    let
                      val n = name_of_const c
                      val (defs, defines) = definitions_of c
                      val lemmas = lemmas_for cfg c
                      val uses =
                        List.filter (not o same_const c)
                          (dedup (key o name_of_const)
                             (List.concat
                                (map (theorem_consts o snd)
                                     (defs @ lemmas))))
                      val e = {const = c, reached_from = from, defs = defs,
                               defines = defines, lemmas = lemmas,
                               uses = uses}
                    in
                      visit (queue @ map (fn u => (u, n)) uses) seen
                        (e :: entries) (c :: met)
                    end
                | _ => visit queue seen entries (c :: met)
              end
          end
    val start =
      List.concat
        (map (fn (n, th) => map (fn c => (c, n)) (theorem_consts th))
             theorems)
  in
    visit start (HOLset.empty String.compare) [] []
  end

(* ---------------------------------------------------------------------
   Buckets

   What a reader must audit to know what a theorem hyps ==> concl says.
   The conclusion bucket holds the definitions that the conclusion
   reaches, and that the hypotheses fixing the variables it reads reach:
   what the claim means.  The hypothesis bucket holds the definitions the
   other hypotheses name directly: what is assumed, one level deep.  The
   rest is plumbing: definitions that the hypotheses' definitions rest on,
   or that only the equation lemmas use.
   --------------------------------------------------------------------- *)

datatype bucket = Conclusion | Hypothesis | Plumbing

(* The hypotheses and the conclusion of a theorem !xs. h1 /\ ... ==> c *)
fun hyps_and_goal th =
  let
    fun split body =
      if is_imp_only body then
        let
          val (ant, consequent) = dest_imp body
          val (hyps, goal) = split consequent
        in
          (strip_conj ant @ hyps, goal)
        end
      else ([], body)
    val (hyps, goal) = split (snd (strip_forall (concl th)))
  in
    (hyp th @ hyps, goal)
  end

(* The hypotheses that fix variables the conclusion reads, and the others.
   A hypothesis fixes variable v if it is an equation between v and a term
   without v; the variables of a fixing hypothesis are read in turn.  So
   x = f y counts with the conclusion when the conclusion reads x. *)
fun fixing_hypotheses hyps goal =
  let
    fun fixes read h =
      let
        fun eq_fixes v t =
          is_var v andalso tmem v read andalso not (free_in v t)
      in
        is_eq h andalso (eq_fixes (lhs h) (rhs h) orelse
                         eq_fixes (rhs h) (lhs h))
      end
    fun go read fixing rest =
      case List.partition (fixes read) rest of
        ([], _) => fixing
      | (new, rest) => go (free_varsl new @ read) (new @ fixing) rest
    val fixing = go (free_vars goal) [] hyps
  in
    List.partition (fn h => tmem h fixing) hyps
  end

(* The bucket of each expanded constant, keyed by constant, for theorem
   th; constants not in the map are plumbing.  The closure behind the
   conclusion follows the definitions only, not the equation lemmas,
   since the lemmas are proved. *)
fun buckets (cfg : config) (entries : entry list) th =
  let
    val by_key =
      List.foldl (fn (e, m) =>
        Redblackmap.insert (m, key (name_of_const (#const e)), e))
        (Redblackmap.mkDict String.compare) entries
    fun entry_of c = Redblackmap.peek (by_key, key (name_of_const c))
    fun def_uses (e : entry) =
      List.filter (not o same_const (#const e))
        (List.concat (map (theorem_consts o snd) (#defs e)))
    fun reach [] m = m
      | reach (c :: queue) m =
          let val k = key (name_of_const c) in
            case (Redblackmap.peek (m, k), entry_of c) of
              (NONE, SOME e) =>
                reach (queue @ def_uses e)
                  (Redblackmap.insert (m, k, Conclusion))
            | _ => reach queue m
          end
    val (hyps, goal) = hyps_and_goal th
    val (fixing, others) = fixing_hypotheses hyps goal
    val concl_map =
      reach (List.concat (map consts_lr (goal :: fixing)))
        (Redblackmap.mkDict String.compare)
    fun add_hyp (c, m) =
      let val k = key (name_of_const c) in
        if isSome (Redblackmap.peek (m, k)) orelse
           not (isSome (entry_of c)) then m
        else Redblackmap.insert (m, k, Hypothesis)
      end
  in
    List.foldl add_hyp concl_map (List.concat (map consts_lr others))
  end

(* ---------------------------------------------------------------------
   Documents

   The dossier is built as a small document, which is then written as
   markdown or as HTML.  Text printed by HOL is kept as a function of the
   target, so that HTML gets it from the printer with its annotations:
   the kind of each variable and constant, its type, and the constant
   behind an overloaded name.
   --------------------------------------------------------------------- *)

(* Plain text, or HTML in which a constant, given by its
   theory-qualified name, links to the anchor that href gives, if any. *)
datatype target = PlainText | Linked of string -> string option

type printed = target -> string

datatype inline =
    Text of string                    (* `...` in it is inline code *)
  | Code of string
  | Hol of printed                    (* inline code printed by HOL *)
  | Link of string * inline list      (* to an anchor of the document *)
  | HtmlLink of string * inline list  (* a link in HTML only *)
  | Target of string * inline list    (* an anchor in HTML only *)

datatype block =
    Heading of int * string option * inline list
  | Para of inline list
  | Pre of printed
  | Items of inline list list
  | Fold of string * block list
  | HtmlFold of string * block list   (* folded in HTML only *)
  | Raw of printed                    (* markdown, or HTML, as given *)

fun escape s =
  String.translate
    (fn #"<" => "&lt;" | #">" => "&gt;" | #"&" => "&amp;" | #"\"" => "&quot;"
      | c => String.str c)
    s

fun print_with backend pp x =
  Lib.with_flag (Globals.max_print_depth, ~1)
    (Lib.with_flag (Parse.current_backend, backend) (Lib.ppstring pp)) x

(* The HTML of a piece of printed text, from what lsp_terminal recorded
   about it. *)
fun segment_html href ({text, kind, name, ty} : PPBackEnd.pp_segment) =
  let
    val ty = if String.isPrefix ":" ty then String.extract (ty, 1, NONE)
             else ty
    fun span class title =
      "<span class=\"" ^ class ^ "\"" ^
      (if title = "" then "" else " title=\"" ^ escape title ^ "\"") ^ ">" ^
      escape text ^ "</span>"
  in
    case kind of
      "const" =>
        let val title = escape (name ^ " : " ^ ty) in
          case href name of
            SOME h => "<a class=\"const\" href=\"#" ^ h ^ "\" title=\"" ^
                      title ^ "\">" ^ escape text ^ "</a>"
          | NONE => span "const" (name ^ " : " ^ ty)
        end
    | "fv" => span "fv" ty
    | "bv" => span "bv" ty
    | "tyvar" => span "tyvar" ""
    | "tyop" => span "type" name
    | "tysyn" => span "type" name
    | _ => escape text
  end

(* Printed by pp, under the current grammar *)
fun hol pp x PlainText = print_with PPBackEnd.raw_terminal pp x
  | hol pp x (Linked href) =
      String.concat
        (map (segment_html href)
           (PPBackEnd.lsp_segments (print_with PPBackEnd.lsp_terminal pp x)))

fun hol_term tm = hol pp_term tm
fun hol_thm th target =
  Lib.with_flag (Globals.show_assums, true) (hol pp_thm th) target

(* A type, without the colon the printer puts before it *)
fun hol_type ty target =
  let val s = hol pp_type ty target in
    case target of
      PlainText => String.extract (s, 1, NONE)
    | Linked _ =>
        (* the colon is the first character outside any markup *)
        let
          val n = size s
          fun go i inside =
            if i >= n then s
            else
              case String.sub (s, i) of
                #"<" => go (i + 1) true
              | #">" => go (i + 1) false
              | #":" => if inside then go (i + 1) inside
                        else String.substring (s, 0, i) ^
                             String.extract (s, i + 1, NONE)
              | _ => go (i + 1) inside
        in
          go 0 false
        end
  end

fun literal s PlainText = s
  | literal s (Linked _) = escape s

fun numbered terms target =
  let
    fun indent s =
      String.concatWith "\n   " (String.fields (fn c => c = #"\n") s)
    fun item (i, t) =
      StringCvt.padLeft #" " 2 (Int.toString i) ^ ". " ^
      indent (hol_term t target)
  in
    String.concatWith "\n"
      (ListPair.map item (List.tabulate (length terms, fn i => i + 1), terms))
  end

fun collapse s = String.concatWith " " (String.tokens Char.isSpace s)

fun md_inline xs =
  let
    fun one (Text s) = s
      | one (Code s) = "`" ^ collapse s ^ "`"
      | one (Hol p) = "`" ^ collapse (p PlainText) ^ "`"
      | one (Link (h, xs)) = "[" ^ md_inline xs ^ "](#" ^ h ^ ")"
      | one (HtmlLink (h, xs)) = one (Link (h, xs))
      | one (Target (i, xs)) =
          "<a id=\"" ^ i ^ "\"></a>" ^ md_inline xs
  in
    String.concat (map one xs)
  end

fun markdown blocks =
  let
    fun one (Heading (level, id, xs)) =
          (case id of
             SOME i => ["<a id=\"" ^ i ^ "\"></a>", ""]
           | NONE => []) @
          [CharVector.tabulate (level, fn _ => #"#") ^ " " ^ md_inline xs, ""]
      | one (Para xs) = [md_inline xs, ""]
      | one (Pre p) = ["```", p PlainText, "```", ""]
      | one (Items xss) = map (fn xs => "- " ^ md_inline xs) xss @ [""]
      | one (Fold (summary, bs)) =
          ["<details><summary>" ^ summary ^ "</summary>", ""] @
          List.concat (map one bs) @ ["</details>", ""]
      | one (HtmlFold (_, bs)) = List.concat (map one bs)
      | one (Raw p) = [p PlainText, ""]
  in
    String.concat (map (fn l => l ^ "\n") (List.concat (map one blocks)))
  end

(* Text with `...` spans as inline code *)
fun html_text s =
  let
    fun go [] _ = []
      | go (p :: ps) in_code =
          (if in_code then "<code>" ^ escape p ^ "</code>" else escape p) ::
          go ps (not in_code)
  in
    String.concat (go (String.fields (fn c => c = #"`") s) false)
  end

fun html_inline href xs =
  let
    fun one (Text s) = html_text s
      | one (Code s) = "<code>" ^ escape s ^ "</code>"
      | one (Hol p) = "<code>" ^ p (Linked href) ^ "</code>"
      | one (Link (h, xs)) =
          "<a href=\"#" ^ h ^ "\">" ^ html_inline href xs ^ "</a>"
      | one (HtmlLink (h, xs)) = one (Link (h, xs))
      | one (Target (i, xs)) =
          "<span id=\"" ^ i ^ "\">" ^ html_inline href xs ^ "</span>"
  in
    String.concat (map one xs)
  end

val html_style = "\
  \body { font-family: system-ui, sans-serif; line-height: 1.45;\n\
  \       max-width: 62rem; margin: 2rem auto; padding: 0 1rem;\n\
  \       color: #1f2328 }\n\
  \code, pre { font-family: 'DejaVu Sans Mono', Menlo, Consolas, monospace;\n\
  \            font-size: 0.88em }\n\
  \pre { background: #f6f8fa; padding: 0.75rem; overflow-x: auto }\n\
  \h2, h3 { scroll-margin-top: 1rem }\n\
  \:target { background: #fff8c5 }\n\
  \.fv { color: #0550ae }\n\
  \.bv { color: #116329 }\n\
  \.tyvar { color: #8250df; font-style: italic }\n\
  \.type { color: #0a7480 }\n\
  \.const { color: #9a1b1b }\n\
  \a.const { text-decoration: none }\n\
  \a.const:hover { text-decoration: underline }\n\
  \[title] { cursor: help }\n\
  \a[title] { cursor: pointer }\n"

(* Opens the folded sections around the target of a link, so that a link
   into one shows its target. *)
val html_script = "\
  \function showTarget() {\n\
  \  var id = decodeURIComponent(location.hash.slice(1));\n\
  \  var t = document.getElementById(id);\n\
  \  if (!t) return;\n\
  \  for (var e = t; e; e = e.parentElement)\n\
  \    if (e.tagName === 'DETAILS') e.open = true;\n\
  \  t.scrollIntoView();\n\
  \}\n\
  \window.addEventListener('hashchange', showTarget);\n\
  \showTarget();\n"

fun html title href blocks =
  let
    fun one (Heading (level, id, xs)) =
          let val h = "h" ^ Int.toString level in
            "<" ^ h ^
            (case id of SOME i => " id=\"" ^ i ^ "\"" | NONE => "") ^ ">" ^
            html_inline href xs ^ "</" ^ h ^ ">\n"
          end
      | one (Para xs) = "<p>" ^ html_inline href xs ^ "</p>\n"
      | one (Pre p) = "<pre>" ^ p (Linked href) ^ "</pre>\n"
      | one (Items xss) =
          "<ul>\n" ^
          String.concat (map (fn xs => "<li>" ^ html_inline href xs ^ "</li>\n")
                           xss) ^
          "</ul>\n"
      | one (Fold (summary, bs)) =
          "<details><summary>" ^ escape summary ^ "</summary>\n" ^
          String.concat (map one bs) ^ "</details>\n"
      | one (HtmlFold (summary, bs)) = one (Fold (summary, bs))
      | one (Raw p) = p (Linked href) ^ "\n"
  in
    "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n\
    \<title>" ^ escape title ^ "</title>\n<style>\n" ^ html_style ^
    "</style>\n</head>\n<body>\n" ^
    String.concat (map one blocks) ^
    "<script>\n" ^ html_script ^ "</script>\n</body>\n</html>\n"
  end

(* ---------------------------------------------------------------------
   Rendering
   --------------------------------------------------------------------- *)

fun anchor prefix ({Thy, Name} : name) =
  let
    fun safe ch =
      if Char.isAlphaNum ch orelse ch = #"_" then String.str ch
      else "-" ^ StringCvt.padLeft #"0" 2 (Int.fmt StringCvt.HEX (ord ch))
  in
    prefix ^ "-" ^ String.translate safe Thy ^ "-" ^ String.translate safe Name
  end

(* inline lists joined by sep *)
fun commas _ [] = []
  | commas _ [xs] = xs
  | commas sep (xs :: rest) = xs @ (Text sep :: commas sep rest)

fun tag_text th =
  let
    val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    val foreign = List.filter (fn s => s <> "DISK_THM") oracles
    val problems =
      (if null (hyp th) then []
       else [[Text (Int.toString (length (hyp th)) ^ " assumption(s)")]]) @
      (if null foreign then []
       else [Text "oracle(s) " ::
             commas ", " (map (fn s => [Code s]) foreign)]) @
      (if null axioms then []
       else [Text "axiom(s) " :: commas ", " (map (fn s => [Code s]) axioms)])
  in
    if null problems then
      [Text "clean: no oracle tag besides `DISK_THM` (loaded from disk), \
            \no axiom, no assumption"]
    else Text "NOT CLEAN: " :: commas "; " problems
  end

(* The overloads under which the constants met print: the constants that
   print under another name, and the patterns over them that print
   differently, each as HOL prints it beside what it stands for.  A
   constant is shown applied to variables unless it prints as a prefix
   name, since its printed name may differ from its overload name (the
   overload <= of int_le prints as an infix token).  Datatype constants
   (field selectors, case constants, ...) are left out: they print by
   their own syntax, which the types section covers.  So are the
   internal names that start with a control character or a space
   (record update syntax and the like).  Each pattern item is an HTML
   target; the result pairs the items with the anchor of each pattern
   overload name, several names (<> and its Unicode form) sharing an item. *)
fun overload_anchor s = anchor "overload" {Thy = "", Name = s}

fun overload_items is_type_const href met shown_terms =
  let
    val oinfo = term_grammar.overload_info (term_grammar ())
    val met_keys =
      HOLset.addList (HOLset.empty String.compare,
                      map (key o name_of_const) met)
    fun visible s =
      s <> "" andalso
      (Char.isGraph (String.sub (s, 0)) orelse ord (String.sub (s, 0)) >= 128)
    val maps_to = Text " \226\134\166 "
    fun const_item c =
      let
        val n = name_of_const c
        val vs = Lib.mapi
                   (fn i => fn ty => mk_var ("x" ^ Int.toString (i + 1), ty))
                   (fst (strip_fun (type_of c)))
        val args = String.concat (map (fn v => " " ^ fst (dest_var v)) vs)
      in
        case Overload.overloading_of_term oinfo c of
          SOME s =>
            if s = #Name n orelse not (visible s) then NONE
            else
              let
                val app = list_mk_comb (c, vs)
                fun meaning text =
                  case href (key n) of
                    SOME h => HtmlLink (h, [Code text])
                  | NONE => Code text
              in
                if collapse (hol_term app PlainText) = s ^ args
                then SOME (NONE, [Hol (literal s), maps_to, meaning (key n)])
                else
                  SOME (NONE,
                        [Hol (hol_term app), maps_to, meaning (key n ^ args)])
              end
        | NONE => NONE
      end
    (* the names that stand for pattern t, so that it prints expanded *)
    fun aliases t =
      List.mapPartial
        (fn (s, {actual_ops, ...} : Overload.overloaded_op_info) =>
            if List.exists (aconv t) actual_ops then SOME s else NONE)
        (Overload.oinfo_ops oinfo)
    fun occurs body =
      List.exists (can (find_term (can (match_term body)))) shown_terms
    fun pattern_item s t =
      let
        val cs = consts_lr t
        val body = snd (strip_abs t)
      in
        if is_const t orelse not (visible s) orelse
           List.all is_type_const cs orelse
           not (List.all
                  (fn c => HOLset.member (met_keys, key (name_of_const c)))
                         cs) orelse
           not (occurs body)
        then NONE
        else
          let
            val expanded = hol (pp_term_without_overloads_on (aliases t)) body
          in
            if hol_term body PlainText = expanded PlainText then NONE
            else SOME (SOME s, [Hol (hol_term body), maps_to, Hol expanded])
          end
      end
    fun pattern_items (s, {actual_ops, ...} : Overload.overloaded_op_info) =
      List.mapPartial (pattern_item s) actual_ops
    val all =
      List.mapPartial const_item
        (List.filter (fn c => not (is_type_const c orelse is_logical c)) met) @
      List.concat (map pattern_items (Overload.oinfo_ops oinfo))
    val items = dedup (md_inline o #2) all
    fun target (NONE, item) = item
      | target (SOME s, item) =
          Target (overload_anchor s, [hd item]) :: tl item
    (* the anchor of the item that each name's item was merged into *)
    fun name_anchor (SOME s, item) =
          let val text = md_inline item in
            case List.find (fn (_, i) => md_inline i = text) items of
              SOME (SOME s', _) => SOME (s, overload_anchor s')
            | _ => NONE
          end
      | name_anchor (NONE, _) = NONE
  in
    (map target items, List.mapPartial name_anchor all)
  end

(* Snippets: pieces of code from documents that link into the HTML dossier,
   printed by HOL like the dossier's own text. The input holds records
   separated by NUL characters; a record is "i" (inline code) or "b" (a
   code block) followed by the text. A text of the form "Theorem name:
   ..." that names exactly one stored theorem is printed as that theorem;
   any other text that parses as a term, with the free and outer
   quantified variables of the dossier's theorems as context (a name
   bound with two types is left out), is printed as that term, provided
   it has no type variables and uses a constant whose definition or type
   the dossier describes. The output is a JSON object from each printed
   record to its HTML, whose links are fragments of the dossier. Records
   that are a single name, or that are not printed, are left out. *)
fun json_string s =
  let
    fun esc #"\"" = "\\\""
      | esc #"\\" = "\\\\"
      | esc #"\n" = "\\n"
      | esc c = if Char.ord c < 32
                then "\\u" ^ StringCvt.padLeft #"0" 4
                  (Int.fmt StringCvt.HEX (Char.ord c))
                else String.str c
  in
    "\"" ^ String.translate esc s ^ "\""
  end

fun snippet_context (cfg : config) =
  let
    val vars = List.concat
      (map (fn {Thy, Name} => statement_vars (DB.fetch Thy Name))
           (#theorems cfg))
    fun clashes v =
      List.exists (fn w => fst (dest_var w) = fst (dest_var v) andalso
                           type_of w <> type_of v) vars
  in
    op_mk_set aconv (List.filter (not o clashes) vars)
  end

fun is_name s =
  s <> "" andalso Char.isAlpha (String.sub (s, 0)) andalso
  CharVector.all (fn c => Char.isAlphaNum c orelse c = #"_" orelse c = #"'") s

fun theorem_of_snippet text =
  let
    val ss = Substring.dropl Char.isSpace (Substring.full text)
  in
    if not (Substring.isPrefix "Theorem " ss) then NONE
    else
      let
        val rest = Substring.dropl Char.isSpace (Substring.triml 8 ss)
        val (n, after) = Substring.splitl (fn c => c <> #":") rest
        val n = Substring.string (Substring.dropr Char.isSpace n)
        val found = List.mapPartial
          (fn thy => SOME ({Thy = thy, Name = n}, DB.fetch thy n)
                     handle HOL_ERR _ => NONE)
          (loaded_theories ())
      in
        case found of
          [f] => if Substring.isPrefix ":" after then SOME f else NONE
                    | _ => NONE
      end
  end

fun snippet_html (cfg : config) href context record =
  let
    val text = String.extract (record, 1, NONE)
    fun described c =
      case href (key (name_of_const c)) of
        SOME a => String.isPrefix "def-" a orelse String.isPrefix "type-" a
      | NONE => false
    val inline = String.isPrefix "i" record
  in
    if is_name text then NONE
    else
      case theorem_of_snippet text of
        SOME (n, th) =>
          let val link =
                if mem_name n (#theorems cfg)
                then "<a class=\"const\" href=\"#" ^ anchor "thm" n ^ "\">" ^
                     escape (#Name n) ^ "</a>"
                else escape (#Name n)
          in SOME ("Theorem " ^ link ^ ":\n" ^ hol_thm th (Linked href)) end
      | NONE =>
          let
            val tm = Feedback.trace ("show_typecheck_errors", 0)
                       (parse_in_context context) [QUOTE text]
          in
            if null (type_vars_in_term tm) andalso
               List.exists described (consts_lr tm)
            then SOME (if inline
                       then Lib.with_flag (Globals.linewidth, 100000)
                              (hol_term tm) (Linked href)
                       else hol_term tm (Linked href))
            else NONE
          end
          (* text that is not a term, or not one in this context *)
          handle HOL_ERR _ => NONE
  end

(* ---------------------------------------------------------------------
   Assumptions

   The prose that explains the hypotheses of one theorem, read from a
   markdown file: a "# " title line, an introduction, then one section per
   hypothesis, opened by "## key", where key is the hypothesis's head: the
   name of the constant it applies, or of the variable an equation
   names.  A section's last paragraph, if it starts with "Pinned by:",
   names in code spans the stored theorems shown after the prose.
   --------------------------------------------------------------------- *)

fun read_file path =
  let val i = TextIO.openIn path
      val s = TextIO.inputAll i
  in TextIO.closeIn i; s end

fun write_file path s =
  let val out = TextIO.openOut path in
    TextIO.output (out, s); TextIO.closeOut out
  end

(* (introduction, [(key, text)]) *)
fun parse_prose text =
  let
    val lines = String.fields (fn c => c = #"\n") text
    val lines = case lines of l :: ls => if String.isPrefix "# " l then ls
                                         else lines
                            | [] => []
    fun join ls = String.concatWith "\n" (rev ls)
    fun go [] key cur (intro, secs) =
          (case key of
             NONE => (join cur, rev secs)
           | SOME k => (intro, rev ((k, join cur) :: secs)))
      | go (l :: ls) key cur (intro, secs) =
          if String.isPrefix "## " l then
            let
              val k = collapse (String.extract (l, 3, NONE))
              val acc = case key of
                          NONE => (join cur, secs)
                        | SOME k' => (intro, (k', join cur) :: secs)
            in go ls (SOME k) [] acc end
          else go ls key (l :: cur) (intro, secs)
  in
    go lines NONE [] ("", [])
  end

(* The text of the code spans of markdown text, and the text with each
   span replaced by f of its text. *)
fun map_code_spans f text =
  let
    val n = size text
    fun close j = if j >= n then NONE
                  else if String.sub (text, j) = #"`" then SOME j
                  else close (j + 1)
    fun go i acc =
      if i >= n then String.concat (rev acc)
      else if String.sub (text, i) = #"`" then
        case close (i + 1) of
          SOME j =>
            go (j + 1) (f (String.substring (text, i + 1, j - i - 1)) :: acc)
        | NONE => String.concat (rev (String.extract (text, i, NONE) :: acc))
      else go (i + 1) (String.str (String.sub (text, i)) :: acc)
  in
    go 0 []
  end

fun code_spans text =
  let val found = ref [] in
    ignore (map_code_spans (fn s => (found := collapse s :: !found; "")) text);
    rev (!found)
  end

(* The prose without its "Pinned by:" paragraph, and the names that
   paragraph lists. *)
fun split_pinned text =
  let
    val trimmed = Substring.string
      (Substring.dropr Char.isSpace (Substring.full text))
    fun last_break i =
      if i < 0 then NONE
      else if String.substring (trimmed, i, 2) = "\n\n" then SOME i
      else last_break (i - 1)
    val (body, last) =
      case last_break (size trimmed - 2) of
        SOME i => (String.substring (trimmed, 0, i),
                   String.extract (trimmed, i + 2, NONE))
      | NONE => ("", trimmed)
  in
    if String.isPrefix "Pinned by:" last then (body, code_spans last)
    else (trimmed, [])
  end

fun stored_theorem s =
  let
    fun fetch thy n =
      SOME ({Thy = thy, Name = n}, DB.fetch thy n)
      handle HOL_ERR _ => NONE
  in
    case String.fields (fn c => c = #"$") s of
      [thy, n] => fetch thy n
    | [n] =>
        (case List.mapPartial (fn thy => fetch thy n)
                (loaded_theories ()) of
           [] => NONE
         | [f] => SOME f
         | _ => raise Fail ("statementDossierLib: ambiguous theorem " ^ s ^
                            "; use Thy$Name"))
    | _ => NONE
  end

(* The constants a name is printed for, by an overload *)
fun overloaded_consts s =
  case Overload.info_for_name
         (term_grammar.overload_info (term_grammar ())) s of
    SOME {actual_ops, ...} => List.filter is_const actual_ops
  | NONE => []

(* Whether a single name in the prose names something HOL knows: a
   constant, a stored theorem, a type, a theory, or a variable of vars. *)
fun known_name vars s =
  List.exists (fn v => fst (dest_var v) = s) vars orelse
  not (null (Term.decls s)) orelse not (null (overloaded_consts s)) orelse
  isSome (stored_theorem s) orelse
  not (null (Type.decls s)) orelse mem s (loaded_theories ())

(* Markdown to HTML, by pandoc *)
fun pandoc_html md =
  let
    val inp = OS.FileSys.tmpName ()
    val out = OS.FileSys.tmpName ()
    fun cleanup () = List.app
      (fn p => OS.FileSys.remove p handle OS.SysErr _ => ()) [inp, out]
    fun convert () =
      let
        val () = write_file inp md
        val ok = OS.Process.isSuccess
          (Systeml.systeml ["pandoc", "-f", "gfm", "-t", "html5",
                            "--wrap=none", inp, "-o", out])
      in
        if ok then read_file out
        else raise Fail "statementDossierLib: pandoc failed rendering prose"
      end
    val result = convert () handle e => (cleanup (); raise e)
  in
    cleanup (); result
  end

(* s with every occurrence of a replaced by b *)
fun replace_all a b s =
  let
    val n = size a
    fun go i acc start =
      if i + n > size s then
        String.concat (rev (String.extract (s, start, NONE) :: acc))
      else if String.substring (s, i, n) = a then
        go (i + n) (b :: String.substring (s, start, i - start) :: acc) (i + n)
      else go (i + 1) acc start
  in
    if n = 0 then s else go 0 [] 0
  end

(* The HTML of prose, its code spans printed by code_html *)
fun prose_html code_html text =
  let
    val spans = ref []
    fun hold s =
      let val i = length (!spans) in
        spans := code_html (collapse s) :: !spans;
        "HOLSPAN" ^ Int.toString i ^ "Z"
      end
    val md = map_code_spans hold text
    val held = rev (!spans)
    val body = pandoc_html md
  in
    #2 (List.foldl (fn (h, (i, b)) =>
                     (i + 1, replace_all
                       ("HOLSPAN" ^ Int.toString i ^ "Z") h b))
                  (0, body) held)
  end

(* The dossier described by cfg: its title, its blocks, and the anchor
   of each constant that has one, for links from printed text. *)
fun render (cfg : config) =
  let
    val theorems =
      map (fn n => (n, DB.fetch (#Thy n) (#Name n))) (#theorems cfg)
    val supporting =
      map (fn n => (n, DB.fetch (#Thy n) (#Name n))) (#supporting cfg)
    val tyidx = type_index ()
    val index = script_index (#source_dirs cfg)
    fun location n =
      case source_location index n of
        SOME (shown, SOME line) => [Code (shown ^ ":" ^ Int.toString line)]
      | SOME (shown, NONE) => [Code shown]
      | NONE => [Text "no source location recorded"]
    val (entries, met) = closure cfg tyidx theorems
    val bucket_maps = map (fn (n, th) => (n, buckets cfg entries th)) theorems
    fun bucket_in m c =
      getOpt (Redblackmap.peek (m, key (name_of_const c)), Plumbing)
    fun is_plumbing (e : entry) =
      List.all (fn (_, m) => bucket_in m (#const e) = Plumbing) bucket_maps
    val (audited, plumbing) = List.partition (not o is_plumbing) entries
    fun in_some b (e : entry) =
      List.exists (fn (_, m) => bucket_in m (#const e) = b) bucket_maps
    val in_conclusion = List.filter (in_some Conclusion) audited
    val oinfo = term_grammar.overload_info (term_grammar ())
    val shown_names = map (fn (n, _) => key n) theorems
    (* constant names shared by two theories are qualified *)
    val name_counts =
      List.foldl (fn (c, m) =>
                     let val s = #Name (name_of_const c) in
                       Redblackmap.insert
                         (m, s, 1 + getOpt (Redblackmap.peek (m, s), 0))
                     end)
        (Redblackmap.mkDict String.compare) met
    fun const_label c =
      let val n = name_of_const c in
        if getOpt (Redblackmap.peek (name_counts, #Name n), 0) > 1 then key n
        else #Name n
      end
    fun printed_as c =
      case Overload.overloading_of_term oinfo c of
        SOME s => if s = #Name (name_of_const c) then []
                  else [Text ", printed as ", Code s]
      | NONE => []
    val theorem_keys =
      HOLset.addList (HOLset.empty String.compare,
                      shown_names @ map (key o #1) supporting)
    fun ref_link n =
      if HOLset.member (theorem_keys, key n) then
        Link (anchor "thm" n, [Code (#Name n)])
      else Link (anchor "def" n, [Code (#Name n)])
    fun const_anchor c =
      let val n = name_of_const c in
        case role_of cfg tyidx c of
          Expanded => anchor "def" n
        | TypeConst ty => anchor "type" ty
        | Boundary => anchor "nx" n
      end
    val met_anchors =
      List.foldl (fn (c, m) => Redblackmap.insert (m, key (name_of_const c),
                                                   const_anchor c))
        (Redblackmap.mkDict String.compare) met
    fun href s = Redblackmap.peek (met_anchors, s)
    fun use_links cs =
      let
        val (expanded, others) =
          List.partition (fn c => role_of cfg tyidx c = Expanded) cs
        val (typed, boundary) =
          List.partition (fn c => case role_of cfg tyidx c of
                                    TypeConst _ => true | _ => false) others
        fun type_label c = Redblackmap.find (tyidx, key (name_of_const c))
        (* a label shared by constants of two types in this list, such as
           two fields of the same name, is qualified with the type *)
        fun shown_label c =
          let val (ty, label) = type_label c in
            if List.exists (fn d => let val (ty', label') = type_label d in
                                      label' = label andalso key ty' <> key ty
                                    end) typed
            then
              if String.isPrefix "." label then #Name ty ^ label
              else label ^ " of " ^ #Name ty
            else label
          end
        fun link c =
          case role_of cfg tyidx c of
            Expanded => [Link (const_anchor c, [Code (const_label c)])]
          | TypeConst _ => [Link (const_anchor c, [Code (shown_label c)])]
          | Boundary => [HtmlLink (const_anchor c, [Code (const_label c)])]
        fun line label [] = []
          | line label xs = [Para (Text label :: commas ", " (map link xs) @
                                   [Text "."])]
      in
        line "Expanded: " expanded @
        line "Datatype constants: " typed @
        line "Not expanded: " (List.filter (not o is_logical) boundary)
      end
    fun thm_block (n, th) =
      [Para ([Code (#Name n), Text " ("] @ location n @ [Text ")"]),
       Para (Text "Tag status: " :: tag_text th @ [Text "."]),
       Pre (hol_thm th)]

    fun theorem_section (n, th) =
      let
        val (hyps, goal) = hyps_and_goal th
        val vars = theorem_vars th
        fun var_line v target =
          let val (s, ty) = dest_var v in
            (case target of
               PlainText => s
             | Linked _ => "<span class=\"fv\">" ^ escape s ^ "</span>") ^
            " : " ^ hol_type ty target
          end
      in
        [Heading (2, SOME (anchor "thm" n), [Text "Theorem ", Code (#Name n)]),
         Para ([Text "Theory ", Code (#Thy n), Text ", "] @ location n @
               [Text "."]),
         Para (Text "Tag status: " :: tag_text th @ [Text "."]),
         Para [Text "As stored:"],
         Pre (hol_thm th)] @
        (if null vars then []
         else [Para [Text "Free variables:"],
               Pre (fn t => String.concatWith "\n"
                              (map (fn v => var_line v t) vars))]) @
        (if null hyps then
           [Para [Text "No assumptions or implication antecedents."]]
         else [Para [Text ("Assumptions and implication antecedents (" ^
                           Int.toString (length hyps) ^ "):")],
               Pre (numbered hyps),
               Para [Text "Conclusion:"],
               Pre (hol_term goal)]) @
        use_links (theorem_consts th)
      end


    (* Code spans of the prose: a variable of the theorems as written; a
       constant or a theorem with an entry linked to it; other code printed
       by HOL where snippet_html prints it. *)
    val snippet_ctx = snippet_context cfg
    fun plain_code s = "<code>" ^ escape s ^ "</code>"
    fun code_html s =
      if is_name s then
        if List.exists (fn v => fst (dest_var v) = s) snippet_ctx then
          plain_code s
        else
          case List.find (fn c => isSome (href (key (name_of_const c))))
                 (Term.decls s @ overloaded_consts s) of
            SOME c => "<a class=\"const\" href=\"#" ^
                      valOf (href (key (name_of_const c))) ^ "\">" ^
                      plain_code s ^ "</a>"
          | NONE =>
              (case stored_theorem s of
                 SOME (n, _) =>
                   if HOLset.member (theorem_keys, key n)
                   then "<a href=\"#" ^ anchor "thm" n ^ "\">" ^
                        plain_code s ^ "</a>"
                   else plain_code s
               | NONE => plain_code s)
      else
        case snippet_html cfg href snippet_ctx ("i" ^ s) of
          SOME h => "<code>" ^ h ^ "</code>"
        | NONE => plain_code s
    fun prose_block text =
      Raw (fn PlainText => text | Linked _ => prose_html code_html text)

    (* The assumptions: for each hypothesis of the theorem, in order, the
       hypothesis, the definition of its head, its prose and the theorems
       that pin it. *)
    val assumption_blocks =
      case #assumptions cfg of
        NONE => []
      | SOME {theorem = tn, prose} =>
        let
          val th = DB.fetch (#Thy tn) (#Name tn)
          val (hyps, _) = hyps_and_goal th
          val vars = statement_vars th
          fun head h =
            if is_eq h andalso is_var (lhs h) then fst (dest_var (lhs h))
            else
              let val (f, _) = strip_comb h in
                if is_const f then #Name (name_of_const f)
                else raise Fail ("statementDossierLib: " ^
                                 "no head for the hypothesis " ^
                                 term_to_string h)
              end
          val keyed = map (fn h => (head h, h)) hyps
          val (intro, sections) = parse_prose (read_file prose)
          fun has k = List.exists (fn (k', _) => k' = k)
          val pinned = map (fn (k, t) => (k, split_pinned t)) sections
          val unknown =
            dedup (fn s => s)
              (List.filter (fn s => is_name s andalso not (known_name vars s))
                 (List.concat (map code_spans (intro :: map #2 sections))))
          val unstored =
            List.concat (map (fn (_, (_, ns)) =>
                                List.filter (not o isSome o stored_theorem) ns)
                           pinned)
          fun fenced t =
            List.exists (fn l => String.isPrefix "```" (collapse l) orelse
                                 String.isPrefix "~~~" (collapse l))
              (String.fields (fn c => c = #"\n") t)
          (* a Pinned by paragraph that split_pinned did not take: not the
             last paragraph of its section, or written differently *)
          fun stray_pinned (_, (text, _)) =
            String.isSubstring "Pinned by" text
          val problems =
            List.concat (map (fn (k, (_, ns)) =>
              map (fn n => "duplicate pinning theorem " ^ n ^ " in " ^ k)
                  (repeated (map (fn n =>
                    case stored_theorem n of
                      SOME (name, _) => key name | NONE => n) ns))) pinned) @
            map (fn k => "two hypotheses with the head " ^ k)
              (repeated (map #1 keyed)) @
            map (fn k => "two sections for " ^ k) (repeated (map #1 sections)) @
            map (fn (k, _) => "a fenced code block in the prose for " ^ k)
              (List.filter (fenced o #2)
                 (("introduction", intro) :: sections)) @
            map (fn (k, _) => "the prose for " ^ k ^ " mentions Pinned by \
                              \other than in a last paragraph that starts \
                              \with \"Pinned by:\"")
              (List.filter stray_pinned
                 (("introduction", (intro, [])) :: pinned)) @
            map (fn (k, _) => "no prose for the hypothesis " ^ k)
              (List.filter (fn (k, _) => not (has k sections)) keyed) @
            map (fn (k, _) => "prose for " ^ k ^ ", the head of no hypothesis")
              (List.filter (fn (k, _) => not (has k keyed)) sections) @
            map (fn s => "the prose names " ^ s ^ ", which HOL does not know")
              unknown @
            map (fn s => "Pinned by names " ^ s ^
                         ", which is no stored theorem")
              unstored
          val () =
            if null problems then ()
            else raise Fail ("statementDossierLib: " ^ prose ^ ": " ^
                             String.concatWith "; " problems)
          fun definition h =
            let val (f, _) = strip_comb h in
              if is_eq h orelse not (is_const f) then []
              else
                case List.find
                       (fn (e : entry) => same_const (#const e) f) entries of
                  SOME e => Para [Text "Definition:"] ::
                            List.concat (map thm_block (#defs e))
                | NONE => []
            end
          fun section (k, h) =
            let
              val (text, names) =
                #2 (valOf (List.find (fn (k', _) => k' = k) pinned))
            in
              [Heading (3, SOME (anchor "hyp" {Thy = "", Name = k}),
                        [Hol (hol_term h)])] @
              definition h @ [prose_block text] @
              (if null names then []
               else Para [Text "Pinned by:"] ::
                    List.concat
                      (map (thm_block o valOf o stored_theorem) names))
            end
        in
          [Heading (2, SOME "assumptions",
                    [Text "Assumptions of ", Code (#Name tn)]),
           prose_block intro] @
          List.concat (map section keyed)
        end
    fun is_assumptions_theorem n =
      case #assumptions cfg of
        SOME {theorem, ...} => key theorem = key n
      | NONE => false

    (* Supporting theorems: stated, not expanded; only the constants with an
       entry are listed. *)
    fun supporting_section (n, th) =
      [Heading (3, SOME (anchor "thm" n), [Code (#Name n)]),
       Para ([Text "Theory ", Code (#Thy n), Text ", "] @ location n @
             [Text "."]),
       Para (Text "Tag status: " :: tag_text th @ [Text "."]),
       Pre (hol_thm th)] @
      use_links (List.filter (fn c => isSome (href (key (name_of_const c))))
                   (theorem_consts th))
    val supporting_blocks =
      if null supporting then []
      else
        [Heading (2, SOME "supporting", [Text "Supporting theorems"]),
         Para [Text "Additional stored statements selected by the caller. \
                    \Their constants are not expanded beyond the entries \
                    \above."]] @
        List.concat (map supporting_section supporting)

    (* The buckets an entry is in, by theorem *)
    fun bucket_tag const =
      let
        fun part label b =
          case List.filter (fn (_, m) => bucket_in m const = b) bucket_maps of
            [] => []
          | ts =>
              [Text label ::
               (if length ts = length theorems then [Text "every theorem"]
                else commas ", " (map (fn (n, _) => [ref_link n]) ts))]
        val parts = part "conclusion of " Conclusion @
                    part "hypotheses of " Hypothesis
      in
        Para (Text "Bucket: " ::
              (if null parts then [Text "plumbing"] else commas "; " parts) @
              [Text "."])
      end
    fun entry_section ({const, reached_from, defs, defines, lemmas, uses}
                       : entry) =
      let val n = name_of_const const in
        [Heading (3, SOME (anchor "def" n),
                  Code (const_label const) ::
                  (case Overload.overloading_of_term oinfo const of
                     SOME s => if s = #Name n then []
                               else [Text " (printed as ", Code s, Text ")"]
                   | NONE => [])),
         bucket_tag const,
         Para ([Text "Theory ", Code (#Thy n)] @ printed_as const @
               [Text "; type ", Hol (hol_type (type_of const)),
                Text "; first reached from ", ref_link reached_from,
                Text "."])] @
        (if null defs then
           [Para [Text "No definition found in the theorem database."]]
         else if defines then List.concat (map thm_block defs)
         else Para [Text ("No stored definition defines it; " ^
                          "these mention it:")] ::
              List.concat (map thm_block defs)) @
        (if null lemmas then []
         else Para [Text "Equation lemmas:"] ::
              List.concat (map thm_block lemmas)) @
        use_links uses
      end

    (* Types: those of datatype constants met, and those of the expanded
       theories that occur in the shown terms. *)
    val shown_terms =
      List.concat (map (theorem_terms o snd) theorems) @
      List.concat (map (fn e => List.concat
        (map (theorem_terms o snd) (#defs e @ #lemmas e))) entries)
    val type_consts =
      List.mapPartial (fn c => case role_of cfg tyidx c of
                                 TypeConst ty => SOME ty | _ => NONE) met
    val tyops = dedup key (List.concat (map (List.rev o tyops_of) shown_terms))
    fun expanded_theory thy =
      List.exists (fn t => t = thy) (#expand_theories cfg) andalso
      not (List.exists (fn t => t = thy) (#stop_theories cfg))
    val shown_types =
      dedup key (type_consts @ List.filter (expanded_theory o #Thy) tyops)
    fun info_of ({Thy, Name} : name) = TypeBase.read {Thy = Thy, Tyop = Name}
    val (described, plain) =
      List.partition (fn ty => isSome (info_of ty)) shown_types
    val unshown_types =
      List.filter (fn ty => not (mem_name ty shown_types)) tyops
    fun type_section ty =
      let
        val info = valOf (info_of ty)
        val fields = TypeBasePure.fields_of info
        fun body target =
          String.concatWith "\n"
            (if not (null fields) then
               "record" ::
               map (fn (f, {ty, ...}) =>
                       "  " ^ literal f target ^ " : " ^ hol_type ty target)
                 fields
             else
               "datatype" ::
               map (fn c => "  " ^ hol_term c target ^ " : " ^
                            hol_type (type_of c) target)
                 (TypeBasePure.constructors_of info))
      in
        [Heading (3, SOME (anchor "type" ty),
                  [Code (#Name ty), Text " (theory ",
                   Code (#Thy ty), Text ")"]),
         Pre body]
      end

    val boundary =
      List.filter (fn c => role_of cfg tyidx c = Boundary) met
    (* (theory, entry) pairs as one item per theory *)
    fun by_theory entries =
      let
        val thys =
          dedup (fn s => s) (Listsort.sort String.compare (map #1 entries))
      in
        map (fn thy =>
                [Code thy, Text ": "] @
                commas ", "
                  (map #2 (List.filter (fn (t, _) => t = thy) entries)))
          thys
      end
    fun is_type_const c =
      case role_of cfg tyidx c of TypeConst _ => true | _ => false
    val (overloads, overload_names) =
      overload_items is_type_const href met shown_terms
    val described_keys =
      HOLset.addList (HOLset.empty String.compare, map key described)
    (* Links from printed text: besides the constants met, the
       constructors printed in case expressions and type descriptions,
       and the names of pattern overloads.  The printer names a pattern
       overload with an empty theory. *)
    fun printed_href s =
      case href s of
        SOME h => SOME h
      | NONE =>
          if String.isPrefix "$" s then
            Option.map #2
              (List.find (fn (n, _) => n = String.extract (s, 1, NONE))
                 overload_names)
          else
            case Redblackmap.peek (tyidx, s) of
              SOME (ty, _) =>
                if HOLset.member (described_keys, key ty)
                then SOME (anchor "type" ty) else NONE
            | NONE => NONE
    (* The audit list.  Each bucket of a theorem is listed by theory, or
       as its difference from the same bucket of an earlier theorem when
       that difference is at most half as long. *)
    fun bucket_entries m b =
      List.filter (fn (e : entry) => bucket_in m (#const e) = b) audited
    fun entry_key (e : entry) = key (name_of_const (#const e))
    fun entry_thy (e : entry) = #Thy (name_of_const (#const e))
    fun entry_link (e : entry) =
      [Link (anchor "def" (name_of_const (#const e)),
             [Code (const_label (#const e))])]
    fun minus xs ys =
      List.filter (fn x =>
        not (List.exists (fn y => entry_key y = entry_key x) ys))
        xs
    (* theories in order of first appearance *)
    fun by_entry_theory es =
      map (fn thy => [Code thy, Text ": "] @
                     commas ", " (map entry_link
                            (List.filter (fn e => entry_thy e = thy) es)))
        (dedup (fn s => s) (map entry_thy es))
    fun bucket_list label b earlier es =
      let
        val head = Text (label ^ " (" ^ Int.toString (length es) ^ ")")
        fun delta (n, m) =
          let val es' = bucket_entries m b
          in (n, minus es es', minus es' es) end
        fun size (_, plus, less) = length plus + length less
        val full =
          if null es then [Para [head, Text ": none."]]
          else [Para [head, Text ":"], Items (by_entry_theory es)]
        val closest =
          List.foldl (fn (d, NONE) => SOME d
                       | (d, SOME d') =>
                           SOME (if size d < size d' then d else d'))
            NONE (map delta earlier)
      in
        case closest of
          SOME (d as (n, plus, less)) =>
            if 2 * size d <= length es then
              [Para ([head, Text ": as for ", ref_link n] @
                     (if null plus then []
                      else Text ", with " ::
                           commas ", " (map entry_link plus)) @
                     (if null less then []
                      else Text ", without " ::
                           commas ", " (map entry_link less)) @
                     [Text "."])]
            else full
        | NONE => full
      end
    fun theorem_audit i (n, m) =
      let val earlier = List.take (bucket_maps, i) in
        Heading (3, NONE, [ref_link n]) ::
        bucket_list "Conclusion" Conclusion earlier
          (bucket_entries m Conclusion) @
        bucket_list "Hypotheses" Hypothesis earlier
          (bucket_entries m Hypothesis)
      end
    val audit_list =
      [Heading (2, SOME "audit-list", [Text "Audit list"]),
       Para [Text "The definitions to read to know what each theorem \
                  \says.  Conclusion: the definitions that the conclusion \
                  \reaches, with the hypotheses that only fix variables it \
                  \reads (an equation `v = t`), followed through their \
                  \definitions: \
                  \what the claim means.  Hypotheses: the definitions the \
                  \other hypotheses name directly, one level deep: what is \
                  \assumed.  Every other definition is plumbing, which the \
                  \definitions above rest on; it is listed under ",
             Link ("plumbing", [Text "Plumbing"]),
             Text " near the end."],
       Para [Text ("Across the theorems: " ^
                   Int.toString (length audited) ^ " definitions to audit, " ^
                   Int.toString (length in_conclusion) ^
                   " of them in a conclusion bucket; " ^
                   Int.toString (length plumbing) ^ " plumbing.")]] @
      List.concat (Lib.mapi theorem_audit bucket_maps)
    val about =
      [Heading (2, SOME "about", [Text "About this dossier"]),
       Para [Text "Generated by `statementDossierLib` from the theorem \
                  \database: every statement, definition and type below is \
                  \printed by HOL.  Constants are expanded breadth-first, in \
                  \order of first appearance; each appears once, and later \
                  \mentions link back to it.  The lists of constants after \
                  \each item leave out the logical constants of theories \
                  \`min` and `bool`."],
       Para [Text ("Contents: " ^ Int.toString (length theorems) ^
                   " theorems, " ^ Int.toString (length entries) ^
                   " expanded constants (" ^ Int.toString (length audited) ^
                   " to audit, " ^ Int.toString (length plumbing) ^
                   " plumbing), " ^ Int.toString (length described) ^
                   " types, " ^ Int.toString (length boundary) ^
                   " constants not expanded.")],
       Para (Text "Theorems: " ::
             commas ", " (map (fn (n, _) => [ref_link n]) theorems) @
             [Text "."]),
       Fold ("Theories whose constants are expanded (" ^
             Int.toString (length (#expand_theories cfg)) ^ ")",
             [Para (commas ", "
                      (map (fn t => [Code t])
                         (Listsort.sort String.compare
                            (#expand_theories cfg))) @
                    [Text "."])]),
       Para (Text "Further expanded constants: " ::
             (if null (#expand_consts cfg) then [Text "none"]
              else commas ", " (map (fn n => [Code (key n)])
                                   (#expand_consts cfg))) @
             [Text "."]),
       Para (Text "Stopped at: " ::
             (if null (#stop_theories cfg) andalso null (#stop_consts cfg)
              then [Text "none"]
              else commas ", "
                     (map (fn t => [Code t]) (#stop_theories cfg) @
                      map (fn n => [Code (key n)]) (#stop_consts cfg))) @
             [Text "."])]
    val blocks =
      [Heading (1, NONE, [Text (#title cfg)]),
       Para [Text (#preamble cfg)]] @
      List.concat (map (fn (n, th) =>
                          theorem_section (n, th) @
                          (if is_assumptions_theorem n then assumption_blocks
                           else []))
                     theorems) @
      supporting_blocks @
      audit_list @
      [Heading (2, NONE, [Text "Definitions"]),
       Para [Text "The definitions to audit; the plumbing follows at the \
                  \end."]] @
      List.concat (map entry_section audited) @
      [Heading (2, NONE, [Text "Types"])] @
      List.concat (map type_section described) @
      (if null plain then []
       else [Para (Text "Types without TypeBase information: " ::
                   commas ", " (map (fn ty => [Code (key ty)]) plain) @
                   [Text "."])]) @
      [Heading (2, NONE, [Text "Overloads"]),
       Para [Text "Where the constants above print other than by their \
                  \names: on the left as HOL prints it, on the right what \
                  \that stands for."],
       if null overloads then Para [Text "None."] else Items overloads,
       Heading (2, SOME "not-expanded", [Text "Not expanded"]),
       Para [Text "Constants, by theory:"],
       Items (by_theory
                (map (fn c => let val n = name_of_const c in
                                (#Thy n, [Target (anchor "nx" n,
                                                  [Code (const_label c)])])
                              end)
                   boundary)),
       Para [Text "Types, by theory:"],
       Items (by_theory (map (fn ty => (#Thy ty, [Code (#Name ty)]))
                           unshown_types)),
       Heading (2, SOME "plumbing", [Text "Plumbing"]),
       Para [Text "The definitions in no theorem's conclusion or hypothesis \
                  \bucket, in the same order as above."],
       HtmlFold ("Plumbing definitions (" ^
                 Int.toString (length plumbing) ^ ")",
                 List.concat (map entry_section plumbing))] @
      about
  in
    (#title cfg, blocks, printed_href)
  end

(* Fails, naming them, if theorems, constants or stop theories named in
   cfg do not exist: a misspelt stop would silently expand everything
   behind it. *)
fun check_config (cfg : config) =
  let
    val loaded = loaded_theories ()
    fun missing what ok ns =
      map (fn n => what ^ " " ^ key n) (List.filter (not o ok) ns)
    val is_thm = can (fn {Thy, Name} => DB.fetch Thy Name)
    val is_constant = can prim_mk_const
    val problems =
      map (fn k => "duplicate theorem " ^ k)
        (repeated (map key (#theorems cfg @ #supporting cfg))) @
      (case #assumptions cfg of
         SOME {theorem, ...} =>
           if mem_name theorem (#theorems cfg) then []
           else ["assumptions theorem is not in theorems: " ^ key theorem]
       | NONE => []) @
      missing "theorem" is_thm
        (#theorems cfg @ #supporting cfg @
         List.concat (map #2 (#equation_lemmas cfg)) @
         (case #assumptions cfg of SOME {theorem, ...} => [theorem]
                                 | NONE => [])) @
      (case #assumptions cfg of
         SOME {prose, ...} =>
           if OS.FileSys.access (prose, [OS.FileSys.A_READ]) then []
           else ["prose file " ^ prose]
       | NONE => []) @
      missing "constant" is_constant
        (#expand_consts cfg @ #stop_consts cfg @
         map #1 (#equation_lemmas cfg)) @
      map (fn t => "theory " ^ t)
        (List.filter (fn t => not (mem t loaded))
           (#stop_theories cfg @ #expand_theories cfg))
  in
    if null problems then ()
    else raise Fail ("statementDossierLib: not found: " ^
                     String.concatWith ", " problems)
  end

(* Print the code of other pages as the dossier prints its terms. The input
   holds records separated by NUL characters: "i" and the text of an inline
   code span, or "b" and the text of a code block. A record is printed when
   its text is "Theorem name:" followed by anything, naming one stored
   theorem (the theorem is printed, not the text), or when it parses, in the
   context of the free and outer quantified variables, as a term without type
   variables using a constant the dossier defines. Single names are left to
   the page. The output is a JSON object from each printed record to its
   HTML, whose links are fragments of the HTML dossier. *)
fun write_snippets (cfg : config) href (input, output) =
  let
    val inp = TextIO.openIn input
    val records = List.filter (fn r => size r > 1)
                    (String.fields (fn c => c = #"\000") (TextIO.inputAll inp))
    val () = TextIO.closeIn inp
    val context = snippet_context cfg
    val printed = List.mapPartial
      (fn r => Option.map (fn h => (r, h)) (snippet_html cfg href context r))
      records
    val out = TextIO.openOut output
  in
    TextIO.output (out, "{\n" ^ String.concatWith ",\n"
      (map (fn (r, h) => json_string r ^ ": " ^ json_string h) printed) ^
      "\n}\n");
    TextIO.closeOut out
  end

(* Write the dossier described by cfg to each of #outputs cfg. *)
fun run (cfg : config) =
  let
    val () = check_config cfg
    val () = theory_cache := Redblackmap.mkDict String.compare
    val () = source_lines := Redblackmap.mkDict String.compare
    fun write (title, blocks, href) (format, path) =
      let
        val text =
          case format of
            Markdown => markdown blocks
          | Html => html title href blocks
        val out = TextIO.openOut path
      in
        TextIO.output (out, text);
        TextIO.closeOut out
      end
  in
    Feedback.trace ("Unicode", 1)
      (fn () => let val doc as (_, _, href) = render cfg in
                  List.app (write doc) (#outputs cfg);
                  Option.app (write_snippets cfg href) (#snippets cfg)
                end) ()
  end

end
