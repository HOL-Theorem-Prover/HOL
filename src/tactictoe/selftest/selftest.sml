open HolKernel boolLib tacticToe tttEval
open tttSetup tttUnfold tttSearch tttRecord
open testutils

val _ = print "\n"

fun check msg b =
  (tprint msg; if b then OK () else die "FAILED")

fun passok msg f =
  (tprint msg; f (); OK ())
  handle e => die ("FAILED: " ^ exnMessage e)

fun expect_holerr msg structname msgsub f =
  (tprint msg;
   (f (); die "FAILED: no exception")
   handle HOL_ERR herr =>
     if top_structure_of herr = structname andalso
        String.isSubstring msgsub (message_of herr)
     then OK ()
     else die ("FAILED: wrong HOL_ERR: " ^ top_structure_of herr ^
               "/" ^ message_of herr)
   | e => die ("FAILED: wrong exception: " ^ exnMessage e))

fun proves msg tm =
  (tprint msg;
   let val th = tactictoe tm in
     if aconv (concl th) tm then OK ()
     else die ("FAILED: conclusion mismatch: " ^
               term_to_string (concl th))
   end)
  handle e => die ("FAILED: " ^ exnMessage e)

fun ttt_closes msg tm =
  (tprint msg;
   let val (gl,_) = ttt ([],tm) in
     if null gl then OK ()
     else die ("FAILED: " ^ Int.toString (length gl) ^
               " subgoals remain")
   end)
  handle e => die ("FAILED: " ^ exnMessage e)

val cache_dir = HOLDIR ^ "/src/tactictoe/selftest/.hol/tactictoe-cache"
val _ = set_tactictoe_cache_dir cache_dir
fun tacdata_file thy = mlTacticData.current_tacdata_file thy
fun datafile () = tacdata_file "ConseqConv"

fun read_file file =
  let
    val ins = TextIO.openIn file
    fun loop acc =
      case TextIO.inputLine ins of
        NONE => (TextIO.closeIn ins; String.concat (rev acc))
      | SOME line => loop (line :: acc)
  in
    loop []
    handle e => (TextIO.closeIn ins; raise e)
  end

val _ = check "tacticToe public API type-checks"
  (let
     val _ : tactic = ttt
     val _ : term -> thm = tactictoe
     val _ : tnn -> tactic = ttt_tnn
     val _ : tnn -> term -> thm = tactictoe_tnn
     val _ : unit -> unit = clean_ttt_tacdata_cache
     val _ : real -> unit = set_timeout
     val _ : unit -> tactic = suggest
     val _ : tttSearch.searchtree option ref = searchtree_glob
     val _ : int option ref = suggest_depth
     val _ : string list ref = prioritize_stacl
   in true end)

val _ = check "TacticToe recording API type-checks"
  (let
     val _ : string -> unit = ttt_record_thy
     val _ : unit -> unit = ttt_record
     val _ : unit -> unit = ttt_clean_record
     val _ : unit -> unit = ttt_clean_savestate
     val _ : unit -> unit = ttt_record_savestate
     val _ : record_option list -> unit = ttt_record_opts
     val _ : record_config -> unit = ttt_record_cfg
     val _ : record_scope ->
       {stale : (string * reason) list, up_to_date : string list,
        out_of_scope_ancestors : string list} = ttt_record_plan
     val _ : unit -> manifest_entry list option = read_manifest
   in true end)

val saved_search_time = !ttt_search_time
val saved_metis_radius = !ttt_metis_radius
val saved_presel_radius = !ttt_presel_radius
val saved_prioritize = !prioritize_stacl
val saved_hh_use = !hh_use
val saved_suggest_depth = !suggest_depth

val _ = check "set_timeout writes ttt_search_time"
  (set_timeout 7.5; Real.== (!ttt_search_time, 7.5))

val _ = check "set_timeout accepts zero"
  (set_timeout 0.0; Real.== (!ttt_search_time, 0.0))

val _ = check "integer parameters are mutable"
  (let
     val m0 = !ttt_metis_radius
     val p0 = !ttt_presel_radius
   in
     ttt_metis_radius := m0 + 1;
     ttt_presel_radius := p0 * 2;
     !ttt_metis_radius = m0 + 1 andalso
     !ttt_presel_radius = p0 * 2
   end)

val _ = check "miscellaneous tacticToe refs are mutable"
  (prioritize_stacl := [];
   hh_use := true;
   suggest_depth := SOME 4;
   null (!prioritize_stacl) andalso !hh_use andalso
   !suggest_depth = SOME 4)

val _ =
  (ttt_search_time := saved_search_time;
   ttt_metis_radius := saved_metis_radius;
   ttt_presel_radius := saved_presel_radius;
   prioritize_stacl := saved_prioritize;
   hh_use := saved_hh_use;
   suggest_depth := saved_suggest_depth)

val plan0 = ttt_record_plan (Theories ["ConseqConv"])
val covered0 = map fst (#stale plan0) @ #up_to_date plan0

val _ = check "record plan covers ConseqConv"
  (List.exists (fn thy => thy = "ConseqConv") covered0)

val _ = check "record plan has non-empty scope"
  (not (null covered0))

val _ = check "manifest version is current"
  (manifest_format_version = 4)

val _ = check "read_manifest is callable before recording"
  (case read_manifest () of NONE => true | SOME _ => true)

val _ = check "sha256_string is deterministic"
  (let
     val h1 = aiLib.sha256_string "tactictoe\n"
     val h2 = aiLib.sha256_string "tactictoe\n"
     val h3 = aiLib.sha256_string "tactictoe changed\n"
   in
     h1 = h2 andalso h1 <> h3 andalso size h1 = 64
   end)

val _ = passok "record ConseqConv tactic data"
  (fn () => ttt_record_opts [Scope (Theories ["ConseqConv"])])

val _ = check "ConseqConv tactic data exists"
  (mlTacticData.exists_tacdata_thy "ConseqConv" andalso
   OS.FileSys.access (datafile (), []))

val _ = check "ConseqConv tactic data is non-empty"
  (Position.toInt (OS.FileSys.fileSize (datafile ())) > 0)

val _ = passok "record dry-run over ConseqConv"
  (fn () => ttt_record_opts
    [Scope (Theories ["ConseqConv"]), DryRun true])

val _ = passok "forced record dry-run over ConseqConv"
  (fn () => ttt_record_opts
    [Scope (Theories ["ConseqConv"]), Force true, DryRun true])

open metisTools ConseqConvTheory

val _ = set_timeout 10.0

val _ = proves "tactictoe proves T" T
val _ = proves "tactictoe proves not-F" ``~F``
val _ = proves "tactictoe proves T and T" ``T /\ T``
val _ = proves "tactictoe proves T or F" ``T \/ F``
val _ = proves "tactictoe proves all x. x = x" ``!x:bool. x = x``
val _ = proves "tactictoe proves all x. x implies x"
  ``!x:bool. x ==> x``

val _ = ttt_closes "ttt closes T" T
val _ = ttt_closes "ttt closes not-F" ``~F``
val _ = ttt_closes "ttt closes all x. x = x" ``!x:bool. x = x``

val _ = expect_holerr "tactictoe rejects non-bool terms"
  "tacticToe" "type bool expected"
  (fn () => ignore (tactictoe ``(1 + 1):num``))

val _ = expect_holerr "ttt rejects non-bool conclusions"
  "tacticToe" "type bool expected"
  (fn () => ignore (ttt ([], ``(1 + 1):num``)))

val _ = expect_holerr "ttt rejects non-bool assumptions"
  "tacticToe" "type bool expected"
  (fn () => ignore (ttt ([``(1 + 1):num``], T)))

val _ = set_timeout 2.0
val _ = searchtree_glob := NONE
val _ = (ttt ([],T); ()) handle _ => ()

val tree = !searchtree_glob
val _ = check "searchtree_glob is populated by ttt" (isSome tree)

val _ =
  case tree of
    NONE => die "FAILED: no search tree"
  | SOME stree =>
      let
        val visl = vistreel_of_searchtree stree
        fun count_ok (VisNode (_,n,_,_,_)) = n >= 0
        val total = List.foldl
          (fn (v,acc) => acc + length_vistree v) 0 visl
      in
        check "search-tree view has sane counts"
          (List.all count_ok visl andalso total >= 0);
        passok "print_vistree does not raise"
          (fn () => List.app print_vistree visl);
        check "suggest_proof returns a string"
          (size (suggest_proof stree) >= 0)
      end

val _ = passok "suggest with bounded depth does not raise"
  (fn () =>
    let val old = !suggest_depth in
      suggest_depth := SOME 3;
      ignore (suggest ());
      suggest_depth := old
    end)

val _ = passok "clean_ttt_tacdata_cache after search"
  (fn () => clean_ttt_tacdata_cache ())

val _ = passok "ttt works after cleaning in-memory tactic cache"
  (fn () => ignore (ttt ([],T)))

val _ = check "find_script locates ConseqConvScript.sml"
  (String.isSuffix "ConseqConvScript.sml" (find_script "ConseqConv"))

val _ = check "nonexistent tactic data is reported absent"
  (not (mlTacticData.exists_tacdata_thy "no_such_theory_for_ttt"))

open ttt_regressionTheory

fun rewrite_record_raw thy =
  let
    val _ = ttt_rewrite_thy thy
    val scriptorg = find_script thy
    val tttsml =
      tactictoe_scratch_dir_of () ^ "/scripts/" ^
      OS.Path.base scriptorg ^ "_ttt.sml"
  in
    smlExecScripts.exec_tttrecord_in_dir (OS.Path.dir scriptorg) tttsml
  end

val _ = passok "record rewriter regression tactic data"
  (fn () => rewrite_record_raw "ttt_regression")

val regression_data = read_file (tacdata_file "ttt_regression")

val _ = check "Q_TAC quotation step is recorded"
  (String.isSubstring "Q_TAC" regression_data andalso
   String.isSubstring "SUFF_TAC" regression_data andalso
   String.isSubstring "QUOTE" regression_data)

open arithmeticTheory dividesTheory gcdTheory

fun proves_by msg tm tac =
  (tprint msg;
   let val th = TAC_PROOF (([],tm), tac) in
     if aconv (concl th) tm then OK ()
     else die ("FAILED: conclusion mismatch: " ^
               term_to_string (concl th))
   end)
  handle e => die ("FAILED: " ^ exnMessage e)

val proof_theories = ["arithmetic", "divides", "gcd"]

val _ = passok "record proof.sml tactic data"
  (fn () => ttt_record_opts [Scope (Theories proof_theories)])

val _ = passok "proof.sml data is up-to-date after recording"
  (fn () => ttt_record_opts
    [Scope (Theories proof_theories), DryRun true])

val _ = clean_ttt_tacdata_cache ()
val _ = set_timeout 60.0

val _ = proves_by "sqrt2 example: even square implies even number"
  ``(divides 2 (a * a)) ==> divides 2 a``
  (REWRITE_TAC [divides_def] THEN ttt)

val _ = proves "sqrt2 example: equation gives even square"
  ``(a * a = 2 * (b * b)) ==> divides 2 (a * a)``

val _ = proves "sqrt2 example: equation gives even a"
  ``(a * a = 2 * (b * b)) ==> divides 2 a``

val _ = proves "sqrt2 example: even a gives four divides square"
  ``divides 2 a ==> divides (2 * 2) (a * a)``

val _ = proves "sqrt2 example: cancel common factor in divisibility"
  ``divides (2 * x) (2 * y) ==> divides x y``

val _ = proves "sqrt2 example: common divisibility reaches gcd"
  ``(divides 2 a /\ divides 2 b) ==> divides 2 (gcd a b)``

val _ = proves "sqrt2 example: one is not even"
  ``~((x = 1) /\ divides 2 x)``

val _ = proves "sqrt2 example: coprime gcd is not even"
  ``~(gcd a b = 1 /\ divides 2 (gcd a b))``

open listTheory rich_listTheory

val demo_theories = ["arithmetic", "list", "rich_list", "indexedLists"]

val _ = passok "record ttt_demo tactic data"
  (fn () => ttt_record_opts [Scope (Theories demo_theories)])

val _ = clean_ttt_tacdata_cache ()
val _ = set_timeout 30.0

val _ = proves "demo example: linear arithmetic"
  ``(2 * x + 1 = 3) ==> (x = 1)``

val _ = proves "demo example: constant map is replicate"
  ``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``
