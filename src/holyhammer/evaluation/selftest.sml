(* ========================================================================= *)
(* FILE          : selftest.sml                                              *)
(* DESCRIPTION   : Tests of the HolyHammer evaluation harness hhEval         *)
(* AUTHOR        : Lukasz Czajka                                             *)
(* ========================================================================= *)

open testutils hhTestLib

datatype prover = datatype hhProver.prover

fun same_real left right = Real.== (left, right)

fun same_real_option NONE NONE = true
  | same_real_option (SOME left) (SOME right) = same_real left right
  | same_real_option _ _ = false

val same_slice = hhProver.same_slice

fun same_journal_slice (expected : hhEval.journal_slice)
    (actual : hhEval.journal_slice) =
  same_slice (#slice expected) (#slice actual) andalso
  #szs expected = #szs actual andalso
  same_real (#time expected) (#time actual) andalso
  #cached expected = #cached actual

fun same_journal_entry (expected : hhEval.journal_entry)
    (actual : hhEval.journal_entry) =
  #run expected = #run actual andalso #thy expected = #thy actual andalso
  #thm expected = #thm actual andalso
  #goal_id expected = #goal_id actual andalso
  #cond expected = #cond actual andalso
  hhEval.string_of_regime (#regime expected) =
    hhEval.string_of_regime (#regime actual) andalso
  hhEval.string_of_selector (#selector expected) =
    hhEval.string_of_selector (#selector actual) andalso
  #engine expected = #engine actual andalso
  #ho expected = #ho actual andalso #fresh expected = #fresh actual andalso
  #prover expected = #prover actual andalso
  #prover_version expected = #prover_version actual andalso
  #nfacts expected = #nfacts actual andalso
  #timeout expected = #timeout actual andalso
  #szs expected = #szs actual andalso
  same_real (#t_prover expected) (#t_prover actual) andalso
  #axioms_used expected = #axioms_used actual andalso
  #recon_ok expected = #recon_ok actual andalso
  #recon_method expected = #recon_method actual andalso
  same_real_option (#t_recon expected) (#t_recon actual) andalso
  #stac expected = #stac actual andalso #error expected = #error actual andalso
  #stop expected = #stop actual andalso
  same_real_option (#t_total expected) (#t_total actual) andalso
  (case (#winner expected, #winner actual) of
       (NONE, NONE) => true
     | (SOME left, SOME right) => same_slice left right
     | _ => false) andalso
  ListPair.allEq (fn (left, right) => same_journal_slice left right)
    (#slices expected, #slices actual)

fun test_hhEval root =
  let
    val num_ty = Type.mk_type ("num", [])
    val num_fun_ty = Type.mk_type ("fun", [num_ty, num_ty])
    val bool_predicate_ty = Type.mk_type ("fun", [Type.bool, Type.bool])
    val x = Term.mk_var ("x", num_ty)
    val f = Term.mk_var ("f", num_fun_ty)
    val bool_predicate = Term.mk_var ("P", bool_predicate_ty)
    val residual_lambda : Term.term = ``(\x : num. x) = (\x. x)``
    val applied_bound_function : Term.term = ``!f : num -> num. f 0 = f 0``
    val connective_in_term = Term.mk_comb (bool_predicate, ``T /\ T``)
    val quantifier_in_term = Term.mk_comb (bool_predicate, ``!x : num. x = x``)
    val plain_first_order : Term.term = ``(1 : num) = 1``
    val binder_only : Term.term = ``!x : num. x = x``
    val beta_redex = Term.mk_comb (Term.mk_abs (x, x), ``0 : num``)
    val eta_redex = Term.mk_abs (x, Term.mk_comb (f, x))
    val _ = expect "HO classifier hand-labelled fixtures"
      (List.all (fn (tm, expected) =>
         hhEval.is_higher_order_goal tm = expected)
       [(residual_lambda, true), (applied_bound_function, true),
        (connective_in_term, true), (quantifier_in_term, true),
        (plain_first_order, false), (binder_only, false)])
    val _ = expect "HO classifier beta-eta invariant"
      (hhEval.is_higher_order_goal beta_redex =
         hhEval.is_higher_order_goal ``0 : num`` andalso
       hhEval.is_higher_order_goal eta_redex =
         hhEval.is_higher_order_goal f)
    val fresh_statement : Term.term = ``([] : num list) = []``
    val seen_statement : Term.term = ``(0 : num) = 0``
    val fresh_beta = Term.mk_comb
      (Term.mk_abs (x, fresh_statement), ``0 : num``)
    val _ = expect "fresh-symbol classifier fixtures"
      (hhEval.is_fresh_goal "list" fresh_statement andalso
       not (hhEval.is_fresh_goal "list" seen_statement) andalso
       not (hhEval.is_fresh_goal "fixture" fresh_statement))
    val _ = expect "fresh-symbol classifier beta invariant"
      (hhEval.is_fresh_goal "list" fresh_beta =
       hhEval.is_fresh_goal "list" fresh_statement)
    val holdir = join root "holdir"
    val sigobj = join holdir "sigobj"
    val src = join holdir "src"
    val _ = hhConfig.ensure_dir sigobj
    val _ = hhConfig.ensure_dir (join (join (join src "one") ".hol") "objs")
    val _ = hhConfig.ensure_dir (join (join (join src "two") ".hol") "objs")
    val _ = aiLib.write_file (join sigobj "SRCFILES")
      (join src "one/listTheory" ^ "\n" ^
       join src "two/arithmeticTheory" ^ "\n")
    (* Not aiLib.write_file: HOLFileSys would move a Theory.dat into a
       further .hol/objs. *)
    fun create_dat directory thy =
      TextIO.closeOut (TextIO.openOut (join (join (join directory ".hol")
        "objs") (thy ^ "Theory.dat")))
    val _ = create_dat (join src "one") "list"
    val _ = create_dat (join src "two") "arithmetic"
    val _ = create_dat (join src "two") "missing"
    val coverage = hhEval.stdlib_coverage ()
    val _ = expect_equal "SRCFILES corpus parser"
      ["arithmetic", "list"] (#srcfiles coverage)
    val _ = expect_equal "coverage check records discrepancy" ["missing"]
      (#added_from_dat coverage)
    val _ = expect_equal "stdlib corpus explicitly adds discrepancy"
      ["arithmetic", "list", "missing"] (hhEval.stdlib_theories ())
    val _ = expect "experiment directories default to src/holyhammer/eval"
      (hhEval.experiment_dir "fixture" =
         join (join (join src "holyhammer") "eval") "fixture")
    val expdir = join root "hheval"
    val _ = hhConfig.remove_tree expdir
    val journal = hhEval.journal_path expdir "list"
    val null_entry : hhEval.journal_entry =
      {run = "fixture", thy = "list", thm = "nil", goal_id = "list.nil",
       cond = "deps-e", regime = hhEval.Bushy, selector = hhEval.Deps,
       engine = SOME (hhEval.Prover Eprover), ho = false, fresh = false,
       prover = SOME Eprover,
       prover_version = NONE,
       nfacts = 0, timeout = 5,
       szs = hhEval.BrokenDeps, t_prover = 0.0, axioms_used = NONE,
       recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = NONE, stop = NONE, t_total = NONE, winner = NONE, slices = []}
    val full_entry : hhEval.journal_entry =
      {run = "fixture", thy = "list", thm = "cons", goal_id = "list.cons",
       cond = "knn-e", regime = hhEval.Chainy, selector = hhEval.Knn 128,
       engine = SOME (hhEval.Prover Eprover), ho = true, fresh = true,
       prover = SOME Eprover,
       prover_version = SOME "3.2.5", nfacts = 128,
       timeout = 10, szs = hhEval.Szs hhProver.SzsTheorem,
       t_prover = 1.25,
       axioms_used = SOME ["list.nil", "arithmetic.add"], recon_ok = SOME true,
       recon_method = SOME "metis", t_recon = SOME 0.5,
       stac = SOME "metis_tac [list_nil]", error = SOME "fixture",
       stop = NONE, t_total = NONE, winner = NONE, slices = []}
    val _ = expect "journal null-field round trip"
      (same_journal_entry null_entry
       (hhEval.parse_journal_line (hhEval.encode_journal_line null_entry)))
    val _ = expect "journal populated-field round trip"
      (same_journal_entry full_entry
       (hhEval.parse_journal_line (hhEval.encode_journal_line full_entry)))
    val load_entry : hhEval.journal_entry =
      {run = "fixture", thy = "list", thm = "__load__",
       goal_id = "list.__load__", cond = "__load__", regime = hhEval.Bushy,
       selector = hhEval.Deps, engine = NONE, ho = false, fresh = false,
       prover = NONE, prover_version = NONE, nfacts = 0, timeout = 0,
       szs = hhEval.LoadFailure, t_prover = 0.0, axioms_used = NONE,
       recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = SOME "fixture", stop = NONE, t_total = NONE, winner = NONE,
       slices = []}
    val load_line = hhEval.encode_journal_line load_entry
    val _ = expect "theory-load entries round-trip without an engine"
      (same_journal_entry load_entry (hhEval.parse_journal_line load_line)
       andalso String.isSubstring "\"engine\":\"prover\"" load_line
       andalso String.isSubstring "\"prover\":\"\"" load_line)
    val _ = hhEval.append_journal journal null_entry
    val _ = hhEval.append_journal journal full_entry
    val entries = hhEval.read_journal journal
    val _ = expect "journal append flushes both lines"
      (length entries = 2 andalso same_journal_entry null_entry (hd entries))
    val complete = [("list.nil", "deps-e"), ("list.cons", "knn-e")]
    val _ = expect "resume complete journal"
      (hhEval.journal_complete journal complete)
    val corrupt = TextIO.openAppend journal
    val _ = TextIO.output (corrupt, "{interrupted-write")
    val _ = TextIO.closeOut corrupt
    val _ = expect "resume ignores a truncated final journal record"
      (hhEval.journal_complete journal complete andalso
       length (hhEval.read_journal journal) = 2)
    val partial = hhEval.journal_path expdir "partial"
    val _ = hhEval.append_journal partial null_entry
    val _ = expect "resume partial journal"
      (not (hhEval.journal_complete partial complete))
    val empty = hhEval.journal_path expdir "empty"
    val _ = expect "resume empty journal"
      (not (hhEval.journal_complete empty complete))
    val retry = hhEval.journal_path expdir "retry"
    val retry_entry : hhEval.journal_entry =
      {run = "fixture", thy = "list", thm = "nil", goal_id = "list.nil",
       cond = "deps-e", regime = hhEval.Bushy, selector = hhEval.Deps,
       engine = SOME (hhEval.Prover Eprover), ho = false, fresh = false,
       prover = SOME Eprover,
       prover_version = NONE, nfacts = 0, timeout = 5,
       szs = hhEval.EvalError, t_prover = 0.0, axioms_used = NONE,
       recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = SOME "transient harness failure", stop = NONE,
       t_total = NONE, winner = NONE, slices = []}
    val _ = hhEval.append_journal retry retry_entry
    val _ = expect "resume retries harness errors"
      (not (hhEval.cell_completed (hhEval.read_completed retry)
        ("list.nil", "deps-e")))
    val run_failure = hhEval.journal_path expdir "runfailure"
    val _ = hhEval.append_journal run_failure
      {run = #run retry_entry, thy = #thy retry_entry,
       thm = #thm retry_entry, goal_id = #goal_id retry_entry,
       cond = #cond retry_entry, regime = #regime retry_entry,
       selector = #selector retry_entry, engine = #engine retry_entry,
       ho = #ho retry_entry, fresh = #fresh retry_entry,
       prover = #prover retry_entry,
       prover_version = NONE, nfacts = 0, timeout = 5,
       szs = hhEval.Szs (hhProver.RunFailure ""), t_prover = 0.0,
       axioms_used = NONE,
       recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = SOME "prover binary was missing", stop = NONE,
       t_total = NONE, winner = NONE, slices = []}
    val _ = expect "resume retries cells whose prover never ran"
      (not (hhEval.cell_completed (hhEval.read_completed run_failure)
        ("list.nil", "deps-e")))
    (* A resume appends past the torn record an interrupted worker left,
       so the malformed line ends up in the middle of the journal. *)
    val torn = hhEval.journal_path expdir "torn"
    val _ = hhEval.append_journal torn null_entry
    val torn_out = TextIO.openAppend torn
    val _ = TextIO.output (torn_out, "{interrupted-write\n")
    val _ = TextIO.closeOut torn_out
    val _ = hhEval.append_journal torn full_entry
    val _ = expect "resume ignores a truncated journal record mid-file"
      (hhEval.journal_complete torn complete andalso
       length (hhEval.read_journal torn) = 2)
    val condition : hhEval.condition =
      {cond_id = "knn-e", regime = hhEval.Chainy, selector = hhEval.Knn 128,
       engine = hhEval.Prover Eprover, timeout = 10, reconstruct = true}
    val parsed_condition =
      hhEval.parse_condition (hhEval.encode_condition condition)
    val _ = expect "condition serialization"
      (#cond_id parsed_condition = #cond_id condition andalso
       hhEval.string_of_regime (#regime parsed_condition) = "chainy" andalso
       hhEval.string_of_selector (#selector parsed_condition) = "knn128"
       andalso
       #engine parsed_condition = hhEval.Prover Eprover andalso
       #timeout parsed_condition = 10 andalso #reconstruct parsed_condition)
    val selectors =
      [(hhEval.Deps, "deps"), (hhEval.Knn 96, "knn96"),
       (hhEval.Mepo 96, "mepo96"), (hhEval.Mash 128, "mash128"),
       (hhEval.Mesh 256, "mesh256")]
    fun selector_round_trip (selector, spelling) =
      let
        val item : hhEval.condition =
          {cond_id = spelling, regime = hhEval.Chainy,
           selector = selector, engine = hhEval.Prover Eprover, timeout = 30,
           reconstruct = true}
        val parsed = hhEval.parse_condition (hhEval.encode_condition item)
      in
        hhEval.string_of_selector (#selector parsed) = spelling
      end
    val _ = expect "ensemble selector spelling round trips"
      (List.all selector_round_trip selectors)
    val malformed_selector =
      "{\"cond_id\":\"bad\",\"regime\":\"chainy\"," ^
      "\"selector\":\"mepo96x\",\"engine\":\"prover\"," ^
      "\"prover\":\"e\",\"timeout\":30,\"reconstruct\":true}"
    val _ = expect "selector grammar rejects suffixes and missing counts"
      ((ignore (hhEval.parse_condition malformed_selector);
        false) handle Fail _ => true)
    val sched_condition : hhEval.condition =
      {cond_id = "sched", regime = hhEval.Chainy,
       selector = hhEval.Knn 256,
       engine = hhEval.Sched
         {provers = [Eprover, Vampire], slices = 6, cores = 2,
          max_proofs = 3, export_workers = 2},
       timeout = 30, reconstruct = true}
    val parsed_sched_condition =
      hhEval.parse_condition (hhEval.encode_condition sched_condition)
    val _ = expect "Sched condition serialization"
      (#cond_id parsed_sched_condition = "sched" andalso
       #engine parsed_sched_condition = #engine sched_condition andalso
       #timeout parsed_sched_condition = 30 andalso
       #reconstruct parsed_sched_condition)
    val legacy_sched_condition =
      "{\"cond_id\":\"legacy\",\"regime\":\"chainy\"," ^
      "\"selector\":\"knn256\",\"engine\":\"sched\"," ^
      "\"provers\":[\"e\",\"vampire\"],\"slices\":6,\"cores\":2," ^
      "\"max_proofs\":3,\"timeout\":30,\"reconstruct\":true}"
    val _ = expect "Sched condition without export_workers gets the default"
      (#engine (hhEval.parse_condition legacy_sched_condition) =
         hhEval.Sched
           {provers = [Eprover, Vampire], slices = 6, cores = 2,
            max_proofs = 3,
            export_workers = hhConfig.default_export_workers})
    val perslice_condition : hhEval.condition =
      {cond_id = "perslice", regime = hhEval.Chainy,
       selector = hhEval.PerSlice, engine = #engine sched_condition,
       timeout = 30, reconstruct = true}
    val parsed_perslice =
      hhEval.parse_condition (hhEval.encode_condition perslice_condition)
    val _ = expect "PerSlice Sched condition serialization"
      (hhEval.string_of_selector (#selector parsed_perslice) =
         "perslice" andalso
       #engine parsed_perslice = #engine sched_condition)
    val invalid_perslice : hhEval.condition =
      {cond_id = "invalid-perslice", regime = hhEval.Chainy,
       selector = hhEval.PerSlice, engine = hhEval.Prover Eprover,
       timeout = 30, reconstruct = true}
    val _ = expect "PerSlice is rejected for non-Sched engines"
      ((hhEval.validate_condition invalid_perslice; false)
       handle Fail message => String.isSubstring "perslice" message)
    val invalid_sched : hhEval.condition =
      {cond_id = "invalid-sched", regime = hhEval.Bushy,
       selector = hhEval.Deps,
       engine = hhEval.Sched
         {provers = [Eprover], slices = 1, cores = 1, max_proofs = 1,
          export_workers = 1},
       timeout = 5, reconstruct = false}
    val _ = expect "Sched condition requires reconstruction"
      ((hhEval.validate_condition invalid_sched; false)
       handle Fail message =>
         String.isSubstring "Sched" message andalso
         String.isSubstring "reconstruct must be true" message)
    val schedule_slice : hhEval.journal_slice =
      {slice =
         {prover = Eprover, format = "fof", type_enc = "",
          lam_trans = "", nfacts = 256, filter = "mepo",
          extra_opts = ["--auto"], slice_size = 15},
       szs = hhProver.SzsTheorem, time = 1.75, cached = true}
    val competing_schedule_slice : hhEval.journal_slice =
      {slice =
         {prover = Eprover, format = "tx0-", type_enc = "mono_native_fool",
          lam_trans = "lifting", nfacts = 256, filter = "mepo",
          extra_opts = ["--auto"], slice_size = 15},
       szs = hhProver.SzsTheorem, time = 1.5, cached = false}
    val sched_entry : hhEval.journal_entry =
      {run = "fixture", thy = "list", thm = "scheduled",
       goal_id = "list.scheduled", cond = "sched",
       regime = hhEval.Chainy, selector = hhEval.Knn 256,
       engine = SOME (#engine sched_condition), ho = true, fresh = true,
       prover = SOME Eprover,
       prover_version = SOME "3.2.5", nfacts = 256, timeout = 30,
       szs = hhEval.Szs hhProver.SzsTheorem, t_prover = 1.75,
       axioms_used = SOME ["list.one"], recon_ok = SOME true,
       recon_method = SOME "metis", t_recon = SOME 0.25,
       stac = SOME "metis_tac [list_one]", error = NONE,
       stop = SOME "MaxProofs", t_total = SOME 2.0,
       winner = SOME (#slice schedule_slice),
       slices = [competing_schedule_slice, schedule_slice]}
    val sched_line = hhEval.encode_journal_line sched_entry
    val _ = expect "Sched journal round trip"
      (same_journal_entry sched_entry (hhEval.parse_journal_line sched_line))
    val sched_json = JSONParser.parseFile
      (let
         val path = join expdir "sched-line.json"
         val _ = aiLib.write_file path sched_line
       in
         path
       end)
    val _ = expect
      "Sched journal emits engine, HO, fresh, and exact winner fields"
      (JSONUtil.asString (JSONUtil.lookupField sched_json "engine") =
         "sched" andalso
       JSONUtil.asBool (JSONUtil.lookupField sched_json "ho") andalso
       JSONUtil.asBool (JSONUtil.lookupField sched_json "fresh") andalso
       JSONUtil.asString (JSONUtil.lookupField
         (JSONUtil.lookupField sched_json "winner") "format") = "fof" andalso
       JSONUtil.asString (JSONUtil.lookupField
         (hd (JSONUtil.arrayMap (fn item => item)
           (JSONUtil.lookupField sched_json "slices"))) "szs") = "Theorem")
    (* The pre-v4 prover-entry shape: no engine, ho or fresh fields. *)
    val old_format_line =
      "{\"run\":\"fixture\",\"thy\":\"list\",\"thm\":\"one\"," ^
      "\"goal_id\":\"list.one\",\"cond\":\"deps-e\"," ^
      "\"regime\":\"bushy\",\"selector\":\"deps\",\"prover\":\"e\"," ^
      "\"prover_version\":null,\"nfacts\":3,\"timeout\":5," ^
      "\"szs\":\"Theorem\",\"t_prover\":0.2,\"axioms_used\":null," ^
      "\"recon_ok\":null,\"recon_method\":null,\"t_recon\":null," ^
      "\"stac\":null,\"error\":null}"
    val torn = hhEval.journal_path expdir "torn"
    val _ = aiLib.write_file torn "{\"run\":\"fix\n"
    val _ = hhEval.append_journal torn sched_entry
    val _ = expect "resume skips torn journal lines"
      (hhEval.journal_complete torn [("list.scheduled", "sched")])
    val old_format = hhEval.journal_path expdir "old-format"
    val _ = aiLib.write_file old_format (old_format_line ^ "\n")
    val _ = hhEval.append_journal old_format sched_entry
    val _ = expect "old-format journal entries are rejected, not skipped"
      (((hhEval.read_journal old_format; false)
        handle Fail message =>
          String.isSubstring "unsupported hhEval journal entry" message))
    val header : hhEval.run_header =
      {expname = "fixture", date = "today", host = "host", hol_commit = "abc",
       provers = [{prover = Eprover, path = SOME "/e", version = SOME "3.2.5",
                   sha256 = SOME "123"}],
       corpus = [{thy = "list", theorem_count = 2, dep_stamp = "stamp"}],
       added_from_dat = ["missing"], conditions = [condition], sample = 1}
    val _ = hhEval.write_run_header expdir header
    val header_json = JSONParser.parseFile (join expdir "run.json")
    val _ = expect "run header writer"
      (JSONUtil.asString (JSONUtil.lookupField header_json "expname") =
       "fixture" andalso
       JSONUtil.asInt (JSONUtil.lookupField header_json "schema") = 4)
    fun resume_header conditions sample corpus : hhEval.run_header =
      {expname = #expname header, date = "later", host = #host header,
       hol_commit = #hol_commit header, provers = #provers header,
       corpus = corpus, added_from_dat = #added_from_dat header,
       conditions = conditions, sample = sample}
    fun resume_rejected field requested =
      ((hhEval.validate_run_header expdir requested; false)
       handle Fail message => String.isSubstring field message)
    val _ = hhEval.validate_run_header expdir
      (resume_header [condition] 1 (#corpus header))
    fun changed_condition selector engine timeout reconstruct =
      {cond_id = #cond_id condition, regime = #regime condition,
       selector = selector, engine = engine, timeout = timeout,
       reconstruct = reconstruct} : hhEval.condition
    val changed_conditions =
      [changed_condition (#selector condition) (#engine condition)
         (#timeout condition + 1) (#reconstruct condition),
       changed_condition hhEval.Deps (#engine condition)
         (#timeout condition) (#reconstruct condition),
       changed_condition (#selector condition) (hhEval.Prover Vampire)
         (#timeout condition) (#reconstruct condition),
       changed_condition (#selector condition) (#engine condition)
         (#timeout condition) (not (#reconstruct condition))]
    val _ = expect "resume rejects changed conditions with the same ID"
      (List.all (fn changed => resume_rejected "conditions"
        (resume_header [changed] 1 (#corpus header))) changed_conditions)
    val _ = expect "resume rejects changed sampling and corpus"
      (resume_rejected "sample"
         (resume_header [condition] 2 (#corpus header)) andalso
       resume_rejected "corpus" (resume_header [condition] 1 []))
    val _ = expect "resume rejects changed runtime hammer options"
      (with_hh_options [("filter", "mepo")] (fn () =>
        resume_rejected "hammer_options" header))
    val legacy_header =
      case header_json of
          JSON.OBJECT fields => JSON.OBJECT
            (List.filter (fn (key, _) => key <> "hammer_options") fields)
        | _ => raise Fail "expected a run header object"
    val _ = aiLib.write_file (join expdir "run.json")
      (JSONPrinter.valueToString legacy_header)
    val _ = expect "resume rejects headers without hammer settings"
      (resume_rejected "hammer_options" header)
    (* A run header reads the HOL commit with git, which must start
       through hhProver's spawn as the provers do. *)
    val _ = hhProver.reset_spawn_count ()
    val {hol_commit, ...} = hhEval.new_run_header
      {expname = "fixture", corpus = [], added_from_dat = [],
       conditions = [], sample = 1}
    val _ = expect "run header commands spawn through hhProver"
      (not (OS.FileSys.access ("/usr/bin/git", [OS.FileSys.A_EXEC])) orelse
       hhProver.spawn_count () = 1 andalso
       (hol_commit = "unknown" orelse
        (size hol_commit = 40 orelse size hol_commit = 64) andalso
        CharVector.all Char.isHexDigit hol_commit))
    val _ = hhEval.write_run_header expdir header
    val _ = expect "sample one selects every goal"
      (hhEval.sample_goal 1 "list.nil")
    val _ = expect "sample selection is deterministic"
      (hhEval.sample_goal 7 "list.nil" = hhEval.sample_goal 7 "list.nil")
    val _ = expect "invalid sample factor is rejected"
      ((hhEval.sample_goal 0 "list.nil"; false) handle Fail _ => true)
    val worker_options =
      [("filter", "mepo"), ("format", "tf0"),
       ("type_enc", "mono_native"), ("lam_trans", "lifting"),
       ("preplay_timeout", "1.75"), ("minimize_timeout", "3.5"),
       ("mono_instances", "17"), ("debug_dir", "quoted \"directory\"")]
    val script = with_hh_options worker_options (fn () =>
      hhEval.write_evalscript expdir "list" [condition] 7)
    val script_text = read_text script
    val _ = expect "worker script preserves runtime hammer options"
      (List.all (fn (key, value) => String.isSubstring
        ("hhConfig.hh_set (" ^ Portable.mlquote key ^ ", " ^
         Portable.mlquote value ^ ");") script_text) worker_options)
    val default_script = hhEval.write_evalscript expdir "list" [condition] 7
    val _ = expect "worker script preserves the default monomorph cap"
      (case #mono_instances (hhConfig.snapshot ()) of
           NONE => not (String.isSubstring
             "hhConfig.hh_set (\"mono_instances\""
             (read_text default_script))
         | SOME _ => true)
    val _ = expect "worker script is beside its theory"
      (OS.Path.dir script = join src "one" andalso
       script = hhEval.evalscript_path expdir "list")
    val _ = expect "worker script finds a theory absent from SRCFILES"
      (OS.Path.dir (hhEval.evalscript_path expdir "missing") = join src "two")
    val _ = expect "worker script loads hhEval from its directory"
      (String.isSubstring ("loadPath := " ^ Portable.mlquote
         (join (join (join Globals.HOLDIR "src") "holyhammer")
            "evaluation")) script_text andalso
       String.isSubstring "load \"hhEval\";" script_text)
    val _ = expect "worker script initializes the simp-data exporter"
      (String.isSubstring "load \"BasicProvers\";" script_text)
    val _ = expect "worker script can replay Metis proofs"
      (String.isSubstring "load \"metisTools\";" script_text)
    val _ = expect "worker script loads its theory"
      (String.isSubstring "load \"listTheory\";" script_text)
    val _ = expect "worker script establishes an isolated current theory"
      (String.isSubstring
        "Theory.new_theory \"hheval_worker_list\";" script_text)
    val _ = expect "worker script reflects condition settings"
      (String.isSubstring "hhEval.set_worker_settings" script_text andalso
       String.isSubstring "knn-e" script_text andalso
       String.isSubstring "sample = 7" script_text)
    val _ = expect "worker script calls eval_thy"
      (String.isSubstring "hhEval.eval_thy" script_text)
    val reportdir = join root "hheval-report"
    val report_journal = join reportdir "journal"
    val fixture_journal = join "test-data" "hheval-report/journal"
    fun copy_fixture name =
      aiLib.write_file (join report_journal name)
        (read_text (join fixture_journal name))
    val _ = hhConfig.remove_tree reportdir
    val _ = hhConfig.ensure_dir report_journal
    val _ = copy_fixture "list.jsonl"
    val _ = copy_fixture "arithmetic.jsonl"
    val _ = copy_fixture "sched.jsonl"
    fun subset_entry thm ho fresh recon : hhEval.journal_entry =
      {run = #run full_entry, thy = "subset", thm = thm,
       goal_id = "subset." ^ thm, cond = "subset-fixture",
       regime = hhEval.Bushy, selector = hhEval.Deps,
       engine = SOME (hhEval.Prover Eprover), ho = ho, fresh = fresh,
       prover = SOME Eprover,
       prover_version = #prover_version full_entry, nfacts = 3, timeout = 6,
       szs = hhEval.Szs hhProver.SzsTheorem, t_prover = 0.1,
       axioms_used = NONE,
       recon_ok = recon, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = NONE, stop = NONE, t_total = NONE, winner = NONE, slices = []}
    val subset_journal = join report_journal "subset.jsonl"
    val _ = hhEval.append_journal subset_journal
      (subset_entry "ho" true false (SOME true))
    val _ = hhEval.append_journal subset_journal
      (subset_entry "first_order" false true (SOME false))
    fun one_shot_entry cond thm selector : hhEval.journal_entry =
      {run = "fixture", thy = "ensemble", thm = thm,
       goal_id = "ensemble." ^ thm, cond = cond,
       regime = hhEval.Chainy, selector = selector,
       engine = SOME (hhEval.Prover Eprover), ho = false, fresh = false,
       prover = SOME Eprover, prover_version = SOME "3.2.5", nfacts = 96,
       timeout = 17, szs = hhEval.Szs hhProver.SzsTheorem,
       t_prover = 0.2,
       axioms_used = NONE, recon_ok = SOME true,
       recon_method = SOME "metis", t_recon = SOME 0.1,
       stac = SOME "metis_tac []", error = NONE, stop = NONE,
       t_total = NONE, winner = NONE, slices = []}
    val ensemble_journal = join report_journal "ensemble.jsonl"
    val _ = hhEval.append_journal ensemble_journal
      (one_shot_entry "report-mepo" "mepo" (hhEval.Mepo 96))
    val _ = hhEval.append_journal ensemble_journal
      (one_shot_entry "report-mash" "mash" (hhEval.Mash 96))
    val _ = hhEval.append_journal ensemble_journal
      (one_shot_entry "report-mesh" "mesh" (hhEval.Mesh 96))
    val collision_engine = hhEval.Sched
      {provers = [Z3], slices = 1, cores = 1, max_proofs = 1,
       export_workers = 1}
    fun collision_slice filter =
      hhProver.mk_slice Z3 ("fof", "", "") filter 77
    fun collision_entry thm filter recon : hhEval.journal_entry =
      let
        val slice = collision_slice filter
        val journal_slice : hhEval.journal_slice =
          {slice = slice, szs = hhProver.SzsTheorem, time = 0.3,
           cached = false}
      in
        {run = "fixture", thy = "collision", thm = thm,
         goal_id = "collision." ^ thm, cond = "filter-collision",
         regime = hhEval.Chainy, selector = hhEval.PerSlice,
         engine = SOME collision_engine, ho = false, fresh = false,
         prover = SOME Z3, prover_version = SOME "fixture",
         nfacts = 77, timeout = 19, szs = hhEval.Szs hhProver.SzsTheorem,
         t_prover = 0.3,
         axioms_used = NONE, recon_ok = SOME recon,
         recon_method = SOME "metis", t_recon = SOME 0.1,
         stac = SOME "metis_tac []", error = NONE, stop = SOME "MaxProofs",
         t_total = SOME 0.4, winner = SOME slice, slices = [journal_slice]}
      end
    val collision_journal = join report_journal "collision.jsonl"
    val _ = hhEval.append_journal collision_journal
      (collision_entry "mepo" "mepo" true)
    val _ = hhEval.append_journal collision_journal
      (collision_entry "mesh" "mesh" false)
    val report_corrupt = TextIO.openAppend (join report_journal "list.jsonl")
    val _ = TextIO.output (report_corrupt, "{in-progress")
    val _ = TextIO.closeOut report_corrupt
    val _ = hhEval.report reportdir
    val summary = JSONParser.parseFile (join reportdir "summary.json")
    fun array_field name value =
      JSONUtil.arrayMap (fn item => item) (JSONUtil.lookupField value name)
    fun named name wanted values =
      case List.find (fn value =>
        JSONUtil.asString (JSONUtil.lookupField value name) = wanted) values of
          SOME value => value
        | NONE => raise Fail ("missing report item: " ^ wanted)
    fun metric name value =
      JSONUtil.asInt (JSONUtil.lookupField
        (JSONUtil.lookupField value "metrics") name)
    val conditions = array_field "conditions" summary
    val e_condition = named "cond" "deps-e" conditions
    val vampire_condition = named "cond" "deps-vampire" conditions
    val sched_condition = named "cond" "sched-main" conditions
    val subset_condition = named "cond" "subset-fixture" conditions
    val mepo_condition = named "cond" "report-mepo" conditions
    val mash_condition = named "cond" "report-mash" conditions
    val mesh_condition = named "cond" "report-mesh" conditions
    val subset_rows = array_field "subsets" subset_condition
    val ho_subset = named "subset" "HO" subset_rows
    val non_ho_subset = named "subset" "non-HO" subset_rows
    val fresh_rows = array_field "fresh_subsets" subset_condition
    val seen_subset = named "subset" "seen" fresh_rows
    val fresh_subset = named "subset" "fresh" fresh_rows
    val portfolios = array_field "portfolios" summary
    val portfolio = named "key" "bushy/5s" portfolios
    val prover_rows = array_field "provers" portfolio
    val e_prover = named "prover" "e" prover_rows
    val vampire_prover = named "prover" "vampire" prover_rows
    val report_text =
      read_text (join reportdir "report.md")
    val _ = expect "report writes both output files"
      (OS.FileSys.access (join reportdir "summary.json", [OS.FileSys.A_READ])
       andalso
       OS.FileSys.access (join reportdir "report.md", [OS.FileSys.A_READ]))
    val _ = expect "report condition counts and quantiles"
      (metric "goals" e_condition = 5 andalso
       metric "attempted" e_condition = 4 andalso
       metric "proved" e_condition = 2 andalso
       metric "reconstructed" e_condition = 1 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField e_condition "metrics") "t_prover_p50"))
         0.2 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField e_condition "metrics") "t_prover_p90"))
         1.0 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField e_condition "metrics") "t_prover_max"))
         1.0 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField e_condition "metrics") "proved_pct"))
         50.0 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField e_condition "metrics") "reconstructed_pct"))
         25.0)
    val _ = expect "report second prover counts"
      (metric "goals" vampire_condition = 5 andalso
       metric "attempted" vampire_condition = 4 andalso
       metric "proved" vampire_condition = 3 andalso
       metric "reconstructed" vampire_condition = 2)
    val _ = expect "report schedule counts and total-time quantiles"
      (metric "goals" sched_condition = 4 andalso
       metric "attempted" sched_condition = 4 andalso
       metric "proved" sched_condition = 3 andalso
       metric "reconstructed" sched_condition = 2 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField sched_condition "metrics") "t_prover_p50"))
         0.8 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField sched_condition "metrics") "t_prover_p90"))
         1.2)
    val _ = expect "report portfolio union and unique solves"
      (metric "goals" portfolio = 6 andalso
       metric "attempted" portfolio = 5 andalso
       metric "proved" portfolio = 4 andalso
       metric "reconstructed" portfolio = 2 andalso
       JSONUtil.asInt (JSONUtil.lookupField e_prover "unique_proved") =
         1 andalso
       JSONUtil.asInt (JSONUtil.lookupField vampire_prover "unique_proved") =
         2 andalso
       JSONUtil.asInt (JSONUtil.lookupField e_prover
         "unique_reconstructed") = 0 andalso
       JSONUtil.asInt (JSONUtil.lookupField vampire_prover
         "unique_reconstructed") = 1)
    val _ = expect "report includes per-theory markdown table"
      (String.isSubstring "## Theories" report_text andalso
       String.isSubstring "| arithmetic | deps-e" report_text andalso
       String.isSubstring "| list | deps-vampire" report_text)
    val distributions = array_field "schedule_distributions" summary
    val sched_distribution = named "cond" "sched-main" distributions
    val stop_rows = array_field "stop_reasons" sched_distribution
    val max_proofs = named "value" "MaxProofs" stop_rows
    val comparisons = array_field "schedule_vs_union" summary
    val comparison = named "condition" "sched-main" comparisons
    val contributions = array_field "slice_contributions" summary
    fun collision_contribution filter =
      List.filter (fn row =>
        JSONUtil.asString (JSONUtil.lookupField row "format") = "fof" andalso
        JSONUtil.asString (JSONUtil.lookupField row "type_enc") = "" andalso
        JSONUtil.asString (JSONUtil.lookupField row "lam_trans") = "" andalso
        JSONUtil.asString (JSONUtil.lookupField row "prover") = "z3"
        andalso
        JSONUtil.asInt (JSONUtil.lookupField row "nfacts") = 77 andalso
        JSONUtil.asString (JSONUtil.lookupField row "filter") = filter)
        contributions
    val _ = expect "report HO subset arithmetic and slice contributions"
      (metric "goals" ho_subset = 1 andalso
       metric "proved" ho_subset = 1 andalso
       metric "reconstructed" ho_subset = 1 andalso
       metric "goals" non_ho_subset = 1 andalso
       metric "proved" non_ho_subset = 1 andalso
       metric "reconstructed" non_ho_subset = 0 andalso
       List.exists (fn row =>
         JSONUtil.asString (JSONUtil.lookupField row "format") = "fof" andalso
         JSONUtil.asInt (JSONUtil.lookupField row "wins") >= 1)
         contributions andalso
       String.isSubstring "## HO subsets" report_text andalso
       String.isSubstring "| deps-e | HO | 0 | 0 | 0 | - |" report_text andalso
       String.isSubstring "## Slice contributions" report_text)
    val _ = expect "report seen/fresh arithmetic and filter keys"
      (JSONUtil.asString (JSONUtil.lookupField subset_condition "filter") =
         "deps" andalso
       metric "goals" seen_subset = 1 andalso
       metric "proved" seen_subset = 1 andalso
       metric "reconstructed" seen_subset = 1 andalso
       metric "goals" fresh_subset = 1 andalso
       metric "proved" fresh_subset = 1 andalso
       metric "reconstructed" fresh_subset = 0 andalso
       List.exists (fn row =>
         JSONUtil.asString (JSONUtil.lookupField row "filter") = "mepo")
         contributions andalso
       String.isSubstring "## Seen/fresh subsets" report_text andalso
       String.isSubstring "| subset-fixture | deps | seen | 1 |" report_text)
    val _ = expect "report labels every one-shot ensemble filter"
      (JSONUtil.asString (JSONUtil.lookupField mepo_condition "filter") =
         "mepo" andalso
       JSONUtil.asString (JSONUtil.lookupField mash_condition "filter") =
         "mash" andalso
       JSONUtil.asString (JSONUtil.lookupField mesh_condition "filter") =
         "mesh" andalso
       String.isSubstring "| report-mepo | e | mepo |" report_text andalso
       String.isSubstring "| report-mash | e | mash |" report_text andalso
       String.isSubstring "| report-mesh | e | mesh |" report_text)
    val _ = expect "slice contributions distinguish filter-only collisions"
      (case (collision_contribution "mepo",
             collision_contribution "mesh") of
           ([mepo], [mesh]) =>
             JSONUtil.asInt (JSONUtil.lookupField mepo "wins") = 1 andalso
             JSONUtil.asInt
               (JSONUtil.lookupField mepo "reconstructed") = 1 andalso
             JSONUtil.asInt (JSONUtil.lookupField mesh "wins") = 1 andalso
             JSONUtil.asInt
               (JSONUtil.lookupField mesh "reconstructed") = 0
         | _ => false)
    val _ = expect "report schedule distributions"
      (JSONUtil.asInt (JSONUtil.lookupField max_proofs "count") = 2 andalso
       length (array_field "slices_run" sched_distribution) = 2 andalso
       String.isSubstring "2:1, 3:3" report_text andalso
       String.isSubstring "MaxProofs:2" report_text)
    val _ = expect "report schedule versus union comparison"
      (JSONUtil.asInt (JSONUtil.lookupField comparison "proved_delta") = ~1
       andalso JSONUtil.asInt
         (JSONUtil.lookupField comparison "reconstructed_delta") = 0 andalso
       String.isSubstring "## Schedule vs portfolio union" report_text andalso
       String.isSubstring "| sched-main | bushy/5s | 3 | 4 | -1 | 2 | 2 | 0 |"
         report_text)
  in
    ()
  end

fun test_actual_hhEval_corpus () =
  let
    val theories = hhEval.stdlib_theories ()
    val coverage = hhEval.stdlib_coverage ()
    val _ = expect "stdlib corpus contains list and arithmetic"
      (List.exists (fn theory => theory = "list") theories andalso
       List.exists (fn theory => theory = "arithmetic") theories)
    val _ = expect "stdlib coverage discrepancies are recorded"
      (List.all (fn theory => List.exists (fn item => item = theory) theories)
       (#added_from_dat coverage))
  in
    ()
  end

fun test_hhEval_integration () =
  case OS.Process.getEnv "HHEVAL_INTEGRATION_TEST" of
      SOME _ =>
        let
          val root =
            case OS.Process.getEnv "HOL4_HAMMER_EVAL_DIR" of
                SOME path => path
              | NONE => raise Fail "integration test has no evaluation dir"
          val condition : hhEval.condition =
            {cond_id = "bushy-deps-e", regime = hhEval.Bushy,
             selector = hhEval.Deps, engine = hhEval.Prover Eprover,
             timeout = 1,
             reconstruct = false}
          val scheduled : hhEval.condition =
            {cond_id = "runtime-options", regime = hhEval.Bushy,
             selector = hhEval.Deps,
             engine = hhEval.Sched {provers = [Eprover], slices = 1,
               cores = 1, max_proofs = 1, export_workers = 1},
             timeout = 1, reconstruct = true}
          fun run expname conditions = with_hh_options
            [("filter", "mepo"), ("format", "tf0"),
             ("type_enc", "mono_native"), ("lam_trans", "lifting")]
            (fn () => hhEval.run_eval
              {expname = expname, ncore = 1, thyl = ["pair", "option"],
               conditions = conditions})
          val _ = run "smoke" [condition]
          val expdir = join root "smoke"
          val pair_journal = hhEval.journal_path expdir "pair"
          val option_journal = hhEval.journal_path expdir "option"
          val journal_before = read_text pair_journal ^
            read_text option_journal
          val _ = expect "hhEval integration journals are valid"
            (not (null (hhEval.read_journal pair_journal)) andalso
             not (null (hhEval.read_journal option_journal)) andalso
             OS.FileSys.access (join expdir "run.json", [OS.FileSys.A_READ]))
          fun script_exists thy =
            OS.FileSys.access (hhEval.evalscript_path expdir thy, [])
          val _ = expect "hhEval removes worker scripts after the run"
            (not (script_exists "pair") andalso not (script_exists "option"))
          (* Simulates a driver killed before its cleanup handlers ran. *)
          val _ = aiLib.write_file (hhEval.evalscript_path expdir "pair") "\n"
          val _ = run "smoke" [condition]
          val _ = expect "hhEval resume sweeps stale worker scripts"
            (not (script_exists "pair"))
          val journal_after = read_text pair_journal ^
            read_text option_journal
          val _ = expect "hhEval integration resume is a no-op"
            (journal_before = journal_after)
          val changed : hhEval.condition =
            {cond_id = #cond_id condition, regime = #regime condition,
             selector = #selector condition, engine = #engine condition,
             timeout = 2, reconstruct = #reconstruct condition}
          val rejected =
            ((run "smoke" [changed]; false)
             handle Fail message =>
               String.isSubstring "conditions differs" message)
          val _ = expect "hhEval rejects incompatible completed runs"
            (rejected andalso journal_before =
              read_text pair_journal ^
              read_text option_journal)
          val _ = run "worker-options" [scheduled]
          val worker_dir = join root "worker-options"
          val worker_entries =
            hhEval.read_journal (hhEval.journal_path worker_dir "pair") @
            hhEval.read_journal (hhEval.journal_path worker_dir "option")
          val worker_slices = List.concat (map #slices worker_entries)
          val _ = expect "hhEval workers use runtime schedule settings"
            (not (null worker_slices) andalso
             List.all (fn {slice, ...} : hhEval.journal_slice =>
               #filter slice = "mepo" andalso #format slice = "tf0" andalso
               #type_enc slice = "mono_native" andalso
               #lam_trans slice = "lifting") worker_slices)
          (* pair and option are built before bossLib: their workers run
             on the hol.state0 heap. *)
          val _ = expect "hhEval workers reconstruct proofs"
            (List.exists (fn entry : hhEval.journal_entry =>
                 #recon_ok entry = SOME true)
               worker_entries)
        in
          ()
        end
    | NONE =>
        (case hhProver.probe (hhProver.config_of Eprover) of
             NONE => (tprint "hhEval integration (skipped: e absent)"; OK ())
           | SOME _ =>
               (tprint
                  "hhEval integration (skipped: set HHEVAL_INTEGRATION_TEST)";
                OK ()))

fun test_hhEval_pool_restriction () =
  let
    val pool = ["kept", "other", "kept"]
    val features =
      [("absent", [0]), ("kept", [1]), ("other", [2]), ("tail", [3])]
    fun old_restrict rows = List.filter (fn (name, _) =>
      List.exists (fn allowed => allowed = name) pool) rows
  in
    expect "hhEval set pool restriction preserves old rows and order"
      (hhEval.restrict_features_to_pool pool features = old_restrict features)
  end

fun test_hhEval_chainy_pools () =
  let
    (* Most ages are shared by three facts. The order by name differs from
       the order by age, and some age groups straddle a checkpoint. *)
    val local_facts = List.tabulate (769, fn n =>
      ("local." ^ Int.toString n, n * 257 mod 769 div 3))
    val ancestor_names = ["ancestor.first", "ancestor.last", "local.1"]
    val pool = hhEval.chainy_pool_by_age
      (Redblackmap.fromList String.compare
        (map (fn name => (name, ())) ancestor_names))
      (Redblackmap.fromList String.compare local_facts)
    fun compare age =
      let
        val expected = aiLib.mk_string_set (ancestor_names @
          List.mapPartial (fn (name, fact_age) =>
            if fact_age < age then SOME name else NONE) local_facts)
        val actual = Redblackmap.listKeys (pool age)
      in
        expect ("hhEval Chainy pool at age " ^ Int.toString age)
          (actual = expected)
      end
  in
    List.app compare [43, 171, 42, 0, 256, 128, 127, 85, 257, 43]
  end

(* test_hhEval runs in a child process whose HOLDIR is a fixture tree
   that it fills, with the hermetic home of HHCONFIG_TEST_ROOT, so that
   no user configuration applies. *)
fun run_hermetic_child () =
  let
    val status = with_fresh_dir (fn root => OS.Process.system
      ("/usr/bin/env -u HOL4_HAMMER_EVAL_DIR HHCONFIG_TEST_ROOT=" ^ root ^
       " HOLDIR=" ^ join root "holdir" ^ " ./selftest.exe"))
  in
    tprint "hhEval hermetic selftests";
    if OS.Process.isSuccess status then OK ()
    else die "FAILED: hhEval child selftest"
  end

val _ =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      SOME root => test_hhEval root
    | NONE =>
        (run_hermetic_child ();
         test_actual_hhEval_corpus ();
         test_hhEval_integration ();
         test_hhEval_pool_restriction ();
         test_hhEval_chainy_pools ())
