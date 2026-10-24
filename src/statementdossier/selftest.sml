open HolKernel Parse boolLib bossLib testutils
open arithmeticTheory listTheory
open statementDossierLib

fun check label b = (tprint label; if b then OK () else die "FAILED")
fun contains text part = String.isSubstring part text
fun read path =
  let val input = TextIO.openIn path
      val text = TextIO.inputAll input
  in TextIO.closeIn input; text end
fun write path text =
  let val output = TextIO.openOut path
  in TextIO.output (output, text); TextIO.closeOut output end

(* A report must also work in a session with no current theory. *)
val boot_output = OS.FileSys.tmpName ()
val _ = run {
  title = "Stored lists", preamble = "",
  theorems = [{Thy = "list", Name = "REVERSE_APPEND"}],
  expand_theories = [], expand_consts = [], stop_theories = [],
  stop_consts = [], equation_lemmas = [], source_dirs = [],
  outputs = [(Markdown, boot_output)], assumptions = NONE,
  supporting = [], snippets = NONE
}
val _ = check "Stored reports need no current theory"
  (contains (read boot_output) "REVERSE_APPEND")
val _ = check "Disk tags disclose missing axiom dependency metadata"
  (contains (read boot_output)
    "axiom dependencies are not retained in disk tags")
val _ = OS.FileSys.remove boot_output

val _ = new_theory "dossierTest"
val _ = Define `first (n:num) = n`
val _ = Define `second n = first n`
val _ = Define `admissible (n:num) = (0 < n)`
val _ = save_thm ("first_equation",
  prove (``first n = second n``, REWRITE_TAC [definition "second_def"]))
val root = save_thm ("root",
  prove (``admissible n ==> second n = n``,
         REWRITE_TAC [definition "second_def", definition "first_def"]))
val _ = save_thm ("quantified", GEN_ALL root)
val _ = save_thm ("repeated_head",
  prove (``admissible n /\ admissible m ==> second n = n``,
         REWRITE_TAC [definition "second_def", definition "first_def"]))
val _ = save_thm ("curried",
  prove (``admissible n ==> n = m ==> second n = m``,
         REWRITE_TAC [definition "second_def", definition "first_def"]
         THEN PROVE_TAC []))
val _ = save_thm ("kernel_hypothesis", ADD_ASSUM ``admissible hidden``
  (REFL ``second n``))
val _ = save_thm ("oracle_result", Thm.mk_oracle_thm "dossier-test"
  ([], ``second n = n``))
val _ = new_axiom ("axiom_result", ``second n = n``)
val _ = Datatype `sample = <| contents : num; label : bool |>`
val _ = save_thm ("record_result", REFL ``(r:sample).contents``)
val _ = save_thm ("recursive_result", REFL ``LENGTH (xs:num list)``)

val markdown_path = OS.FileSys.tmpName ()
val html_path = OS.FileSys.tmpName ()
val prose_path = OS.FileSys.tmpName ()
val snippets_in = OS.FileSys.tmpName ()
val snippets_out = OS.FileSys.tmpName ()
val _ = List.app (fn p => write p "")
  [markdown_path, html_path, prose_path, snippets_in, snippets_out]
fun named s = {Thy = "dossierTest", Name = s}

fun config {theorems, expand_theories, expand_consts, stop_theories,
            stop_consts, assumptions, supporting, snippets} : config = {
  title = "Statements <&\" >", preamble = "Public selftest",
  theorems = theorems, expand_theories = expand_theories,
  expand_consts = expand_consts, stop_theories = stop_theories,
  stop_consts = stop_consts, equation_lemmas = [], source_dirs = [],
  outputs = [(Markdown, markdown_path), (Html, html_path)],
  snippets = snippets, assumptions = assumptions, supporting = supporting
}
fun basic ns = config {
  theorems = map named ns, expand_theories = ["dossierTest"],
  expand_consts = [], stop_theories = [], stop_consts = [],
  assumptions = NONE, supporting = [], snippets = NONE
}
fun generate cfg = (run cfg; (read markdown_path, read html_path))
fun count text part =
  let
    val n = size part
    fun go i k =
      if i + n > size text then k
      else if String.substring (text, i, n) = part then go (i + n) (k + 1)
      else go (i + 1) k
  in go 0 0 end

val (md, html) = Lib.with_flag (Globals.max_print_depth, 0)
  generate (basic ["root"])
val stored = Feedback.trace ("Unicode", 1)
  (Lib.with_flag (current_backend, PPBackEnd.raw_terminal)
    (Lib.with_flag (Globals.show_assums, true) (Lib.ppstring pp_thm))) root
val _ = check "Stored statement printed verbatim" (contains md stored)
val _ = check "Cyclic equation-lemma closure visits each definition once"
  (count html "id=\"def-dossierTest-first\"" = 1 andalso
   count html "id=\"def-dossierTest-second\"" = 1)
val _ = check "Equation lemmas are discovered" (contains md "first_equation")
val _ = check "Free variable types are printed"
  (contains md "Free variables:" andalso contains md "n : num")
val _ = check "HTML title and text are escaped"
  (contains html "Statements &lt;&amp;&quot; &gt;" andalso
   not (contains html "Statements <&\" >"))
val _ = check "Printed constants have type tooltips and definition links"
  (contains html "href=\"#def-dossierTest-second\" title=\"" andalso
   contains html "dossierTest$second : num -&gt; num")

(* Check all generated fragment links, including anchors in folded content. *)
fun attributes marker text =
  let
    val n = size text
    val m = size marker
    fun ending i =
      if i >= n orelse String.sub (text, i) = #"\"" then i
      else ending (i + 1)
    fun go i acc =
      if i + m > n then rev acc
      else if String.substring (text, i, m) = marker then
        let val start = i + m
            val stop = ending start
        in go (stop + 1) (String.substring (text, start, stop-start) :: acc)
        end
      else go (i + 1) acc
  in go 0 [] end
val ids = attributes "id=\"" html
val refs = attributes "href=\"#" html
val _ = check "Every HTML fragment link has one target"
  (List.all (fn r => length (List.filter (fn i => i = r) ids) = 1) refs)
val _ = check "HTML anchor IDs are unique"
  (length ids = length (op_mk_set (fn x => fn y => x = y) ids))
val _ = check "Markdown fragment links retain boundary anchors"
  (List.all (fn r => contains md ("id=\"" ^ r ^ "\""))
     (List.filter (String.isPrefix "nx-") refs))

val stopped = config {
  theorems = [named "root"], expand_theories = ["dossierTest"],
  expand_consts = [named "first"], stop_theories = [],
  stop_consts = [named "first"], assumptions = NONE,
  supporting = [], snippets = NONE
}
val (_, boundary_html) = generate stopped
val _ = check "An explicit stop wins over expansion"
  (not (contains boundary_html "id=\"def-dossierTest-first\"") andalso
   contains boundary_html "id=\"nx-dossierTest-first\"")
val (_, theory_stop_html) = generate (config {
  theorems = [named "root"], expand_theories = ["dossierTest"],
  expand_consts = [named "second"], stop_theories = ["dossierTest"],
  stop_consts = [], assumptions = NONE, supporting = [], snippets = NONE
})
val _ = check "A theory stop wins over explicit constants"
  (not (contains theory_stop_html "id=\"def-dossierTest-second\""))
val (_, explicit_html) = generate (config {
  theorems = [named "root"], expand_theories = [],
  expand_consts = [named "second"], stop_theories = [], stop_consts = [],
  assumptions = NONE, supporting = [], snippets = NONE
})
val _ = check "Single-constant expansion stops at other definitions"
  (contains explicit_html "id=\"def-dossierTest-second\"" andalso
   contains explicit_html "id=\"nx-dossierTest-first\"")

val (curried_md, _) = generate (basic ["curried"])
val _ = check "Curried implication antecedents are listed separately"
  (contains curried_md "Assumptions and implication antecedents (2)")

val (hyp_md, hyp_html) = generate (basic ["kernel_hypothesis"])
val _ = check "Kernel assumptions are shown and traversed"
  (contains hyp_md "hidden" andalso contains hyp_md "1 assumption(s)" andalso
   contains hyp_html "id=\"def-dossierTest-admissible\"")
val _ = check "Variables only in kernel assumptions retain their types"
  (contains hyp_md "hidden : num")
val (trust_md, _) = generate (basic ["oracle_result", "axiom_result"])
val _ = check "Oracle and axiom tags remain visible"
  (contains trust_md "dossier-test" andalso contains trust_md "axiom(s)" andalso
   contains trust_md "axiom_result" andalso contains trust_md "NOT CLEAN")
val (_, record_html) = generate (basic ["record_result"])
val _ = check "Record selectors link to their field descriptions"
  (contains record_html "id=\"type-dossierTest-sample\"" andalso
   contains record_html "contents" andalso contains record_html "label")
val (recursive_md, _) = generate (config {
  theorems = [named "recursive_result"], expand_theories = ["list"],
  expand_consts = [], stop_theories = [], stop_consts = [],
  assumptions = NONE, supporting = [], snippets = NONE
})
val _ = check "Recursive equations are shown without primitive encoding"
  (contains recursive_md "LENGTH" andalso
   not (contains recursive_md "LENGTH_def_primitive"))

(* Markdown generation with prose never needs pandoc. *)
fun with_prose theorem : config = {
  title = "Assumptions", preamble = "", theorems = [named "root"],
  expand_theories = ["dossierTest"], expand_consts = [],
  stop_theories = [], stop_consts = [], equation_lemmas = [],
  source_dirs = [], outputs = [(Markdown, markdown_path)], snippets = NONE,
  assumptions = SOME {theorem = theorem, prose = prose_path}, supporting = []
}
val good_prose = "# Inputs\nA condition on `n`.\n\n## admissible\n\n\
  \The input `n` satisfies `admissible`.\n\nPinned by: `root`.\n"
val _ = write prose_path
  "## admissible\nInput.\n\nPinned by: `dossierTest$root`.\n"
val _ = run (with_prose (named "root"))
val _ = check "Qualified pinning names identify the stored theorem"
  (contains (read markdown_path) stored)
val _ = write prose_path good_prose
val _ = run (with_prose (named "root"))
val prose_md = read markdown_path
val _ = check "Checked assumption prose includes the stored pinning theorem"
  (contains prose_md "The input" andalso contains prose_md stored)
val _ = run {
  title = "Quantified inputs", preamble = "",
  theorems = [named "quantified"], expand_theories = ["dossierTest"],
  expand_consts = [], stop_theories = [], stop_consts = [],
  equation_lemmas = [], source_dirs = [],
  outputs = [(Markdown, markdown_path)], supporting = [], snippets = NONE,
  assumptions = SOME {theorem = named "quantified", prose = prose_path}
}
val _ = check "Prose can name outer quantified variables"
  (contains (read markdown_path) "The input")
fun rejects label expected cfg =
  (tprint label;
   ((run cfg; die "accepted invalid input")
    handle Fail msg => if contains msg expected then OK () else die msg))
fun bad_prose label expected text =
  (write prose_path text;
   rejects label expected (with_prose (named "root")))
val _ = bad_prose "Missing assumption prose is rejected" "no prose"
  "# Inputs\n"
val _ = bad_prose "Duplicate prose sections are rejected" "two sections"
  (good_prose ^ "\n## admissible\nDuplicate.\n")
val _ = bad_prose "Extra prose sections are rejected" "head of no hypothesis"
  (good_prose ^ "\n## absent\nExtra.\n")
val _ = bad_prose "Unknown formal names are rejected" "HOL does not know"
  "## admissible\n`not_a_HOL_name_28471`\n"
val _ = bad_prose "Unknown qualified prose names are rejected"
  "HOL does not know"
  "## admissible\n`noSuchTheory$noSuchConstant`\n"
val _ = bad_prose "Unknown qualified names in a loaded theory are rejected"
  "HOL does not know"
  "## admissible\n`dossierTest$not_a_HOL_name_28471`\n"
val _ = write prose_path
  "## admissible\n`dossierTest$first`, `list$list`, `arithmetic$<=`, \
  \and `dossierTest$root` are known.\n"
val _ = run (with_prose (named "root"))
val _ = check "Qualified constants, types and theorems are accepted"
  (contains (read markdown_path) "are known")
val _ = bad_prose "Unknown pinning theorems are rejected" "no stored theorem"
  "## admissible\nAn input.\n\nPinned by: `not_a_theorem_28471`.\n"
val _ = bad_prose "Duplicate pinning names are rejected" "duplicate pinning"
  "## admissible\nInput.\n\nPinned by: `root`, `root`.\n"
val _ = bad_prose "Aliased duplicate pinning names are rejected"
  "duplicate pinning"
  "## admissible\nInput.\n\nPinned by: `root`, `dossierTest$root`.\n"
val _ = bad_prose "Pinning references in the introduction are rejected"
  "last paragraph"
  "Pinned by: `root`.\n\n## admissible\nInput.\n"
val _ = bad_prose "Misplaced pinning paragraphs are rejected" "last paragraph"
  "## admissible\nPinned by: `root`.\n\nMore prose.\n"
val _ = bad_prose "Fenced code is rejected" "fenced code block"
  "## admissible\n```\nn\n```\n"
val _ = write prose_path good_prose
val _ = rejects "Assumptions must belong to a selected theorem"
  "not in theorems" (with_prose (named "kernel_hypothesis"))
val _ = rejects "Duplicate selected theorems are rejected" "duplicate theorem"
  (basic ["root", "root"])
val _ = rejects "Repeated hypothesis heads are rejected" "two hypotheses"
  {title = "Repeated heads", preamble = "",
   theorems = [named "repeated_head"], expand_theories = [],
   expand_consts = [], stop_theories = [], stop_consts = [],
   equation_lemmas = [], source_dirs = [],
   outputs = [(Markdown, markdown_path)], supporting = [], snippets = NONE,
   assumptions = SOME {theorem = named "repeated_head", prose = prose_path}}
val _ = save_thm ("TRUTH", boolTheory.TRUTH)
val _ = bad_prose "Ambiguous pinning names are rejected" "ambiguous theorem"
  "## admissible\nInput.\n\nPinned by: `TRUTH`.\n"
val _ = rejects "Unknown selected theorems are rejected" "not found"
  (basic ["does_not_exist"])
val _ = rejects "Misspelled expansion theories are rejected" "not found"
  (config {theorems = [named "root"], expand_theories = ["dossierTset"],
           expand_consts = [], stop_theories = [], stop_consts = [],
           assumptions = NONE, supporting = [], snippets = NONE})

(* A later database addition must be visible in the same HOL session. *)
val _ = save_thm ("first_new_equation",
  prove (``first n = n``, REWRITE_TAC [definition "first_def"]))
val (fresh_md, _) = generate (basic ["root"])
val _ = check "Repeated runs see new stored equation lemmas"
  (contains fresh_md "first_new_equation")

val _ = write snippets_in "i(second (3:num))\000bTheorem root: ignored text"
val (_, _) = generate (config {
  theorems = [named "root"], expand_theories = ["dossierTest"],
  expand_consts = [], stop_theories = [], stop_consts = [],
  assumptions = NONE, supporting = [],
  snippets = SOME (snippets_in, snippets_out)
})
val snippet_json = read snippets_out
val _ = check "Snippets use stored statements and definition links"
  (contains snippet_json "def-dossierTest-second" andalso
   contains snippet_json "thm-dossierTest-root" andalso
   contains snippet_json "admissible")

val source_dir = OS.FileSys.tmpName ()
(* tmpName creates a file in Poly/ML, but only returns a path in Moscow ML. *)
val _ = write source_dir ""
val _ = OS.FileSys.remove source_dir
val _ = OS.FileSys.mkDir source_dir
val source_script = OS.Path.concat (source_dir, "arithmeticScript.sml")
fun source_config () : config = {
  title = "Source locations", preamble = "",
  theorems = [{Thy = "arithmetic", Name = "LESS_EQ_IMP_LESS_SUC"}],
  expand_theories = [], expand_consts = [], stop_theories = [],
  stop_consts = [], equation_lemmas = [],
  source_dirs = [("sources", source_dir)],
  outputs = [(Markdown, markdown_path)], assumptions = NONE,
  supporting = [], snippets = NONE
}
val _ = write source_script "Theorem LESS_EQ_IMP_LESS_SUC:\n"
val _ = run (source_config ())
val _ = check "Source declarations override recorded line numbers"
  (contains (read markdown_path) "sources/arithmeticScript.sml:1")
val _ = write source_script "\n\nTheorem LESS_EQ_IMP_LESS_SUC:\n"
val _ = run (source_config ())
val _ = check "Repeated runs see source edits"
  (contains (read markdown_path) "sources/arithmeticScript.sml:3")
val _ = OS.FileSys.remove source_script
val _ = OS.FileSys.rmDir source_dir

val _ = List.app OS.FileSys.remove
  [markdown_path, html_path, prose_path, snippets_in, snippets_out]
val _ = print "statementDossierLib selftests passed\n"
