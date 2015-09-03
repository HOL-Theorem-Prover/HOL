structure func_decompileLib =
struct

open HolKernel boolLib bossLib Parse;
open listTheory wordsTheory pred_setTheory arithmeticTheory wordsLib pairTheory;
open set_sepTheory progTheory helperLib addressTheory combinTheory;

open GraphLangTheory graph_specsLib exportLib writerLib cond_cleanLib;


infix \\ val op \\ = op THEN;

val _ = max_print_depth := ~1;
val _ = set_trace "Unicode" 0;

local
  val export_fails = ref ([]:string list)
in
  fun add_export_fail sec_name = (export_fails := sec_name :: (!export_fails))
  fun get_export_fails () = rev (!export_fails)
  fun clear_export_fails () = (export_fails := [])
end;

fun func_export sec_name th funcs_def = let
  val f = th |> concl |> rand
  val name = sec_name
  val rhs = ``func_body_trans ^f``
  val lhs = mk_var(name,type_of rhs)
  val trans_def = new_definition(name,mk_eq(lhs,rhs))
  val _ = write_subsection "Evaluating graph"
  val c = REWRITE_CONV [func_body_trans_def,func_trans_def,funcs_def]
          THENC EVAL THENC PURE_REWRITE_CONV [GSYM word_sub_def]
          THENC prepare_for_export_conv
  val lemma = trans_def |> CONV_RULE (RAND_CONV c)
  val xs = lemma |> concl |> rand |> rator |> rand |> rand
                 |> listSyntax.dest_list |> fst
  val node_count = length xs |> int_to_string
  val msg = "The graph for `" ^ sec_name ^ "` has " ^ node_count ^ " nodes."
  val _ = write_line msg
  val _ = (writer_prints := false)
  val _ = map write_term xs
  val _ = (writer_prints := true)
  val ml_name = export_func lemma
  in (trans_def," o " ^ ml_name) end
  handle HOL_ERR _ => let
    val _ = print ("Export FAILED for " ^ sec_name ^ ".\n")
    val _ = add_export_fail sec_name
    in (TRUTH,"") end;

fun print_title (s:string) = ()

fun get_loction_as_word sec_name = let
  val tm = section_location sec_name
           |> Arbnumcore.fromHexString |> numSyntax.mk_numeral
  in ``n2w (^tm):word32`` end

fun func_decompile print_title sec_name = let
  val _ = (writer_prints := true)
  val _ = open_current sec_name
  val _ = print_title sec_name
  val thms = derive_insts_for sec_name
(*  val thms = clean_conds thms *)
  val code = thms |> hd |> concl |> rator |> rator |> rand
             handle Empty => (if !arch_name = ARM
                              then ``(ARM {}):code``
                              else ``(M0 {}):code``)
  val lemma = prove(``LIST_IMPL_INST ^code locs []``,
                    SIMP_TAC std_ss [LIST_IMPL_INST_def])
  fun combine [] = lemma
    | combine (th::thms) =
        MATCH_MP IMP_LIST_IMPL_INST (CONJ th (combine thms))
  val th = combine thms
  val entry = th |> concl |> rand |> rator |> rand
                 |> rator |> rator |> rand
              handle HOL_ERR _ => get_loction_as_word sec_name
  val th = MATCH_MP IMP_func_ok th |> Q.INST [`entry`|->`^entry`]
  val goal = th |> concl |> dest_imp |> fst
  val lemma = auto_prove "inst_locs_distinct"
    (goal,REWRITE_TAC [MAP,inst_loc_def] \\ EVAL_TAC)
  val th = MP th lemma
  val entry = th |> concl |> rand |> rand |> listSyntax.dest_cons |> fst
                 |> rator |> rator |> rand
              handle HOL_ERR _ => get_loction_as_word sec_name
  val name = stringSyntax.fromMLstring sec_name
  val th = th |> Q.INST [`name`|->`^name`,`entry`|->`^entry`]
  val funcs_def_rhs = th |> concl |> rand |> rand
  val funcs_name = sec_name ^ "_funcs"
  val funcs_def_lhs = mk_var(funcs_name,type_of funcs_def_rhs)
  val funcs_def = new_definition(funcs_name,``^funcs_def_lhs = ^funcs_def_rhs``)
  val th = CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM funcs_def)))) th
  in (th,func_export sec_name th funcs_def) end

fun list_mk_union [] = ``{}:'a set``
  | list_mk_union [x] = x
  | list_mk_union (x::xs) = pred_setSyntax.mk_union(list_mk_union xs,x)

(*
  val sec_name = "bi_finalise"
*)

fun prove_funcs_ok names = let
  val _ = clear_stack_intro_fails ()
  val _ = clear_graph_spec_fails ()
  val _ = clear_export_fails ()
  fun print_title sec_name = let
    fun find_index [] = ~2000
      | find_index (x::xs) = if x = sec_name then 1 else find_index xs + 1
    val i = find_index names
    val str = "Section " ^ sec_name ^ " (" ^
                int_to_string i ^ " of " ^ int_to_string (length names) ^ ")"
    in write_section str end
  (* decompile all sections *)
  val fs_and_trans_defs = map (func_decompile print_title) names
  val fs = map fst fs_and_trans_defs
  (* abbreviate all codes *)
  val all_code = fs |> map (rand o rator o rator o concl)
  val code_name = all_code |> hd |> rator
  val all_code = mk_comb(code_name, (all_code |> map rand |> list_mk_union))
  val all_code_def = new_definition("all_code",``all_code = ^all_code``);
  val code_case_of = TypeBase.case_def_of ``:code``;
  val pair_case_of = TypeBase.case_def_of ``:'a # 'b``;
  fun expend_code th = let
    val th = MATCH_MP func_ok_EXPEND_CODE th |> Q.SPEC `all_code`
    val goal = th |> concl |> dest_imp |> fst
    val lemma = auto_prove "expand_code" (goal,
      REWRITE_TAC [all_code_def,SUBSET_DEF,IN_UNION,code_case_of,pair_case_of]
      \\ CONV_TAC (DEPTH_CONV BETA_CONV)
      \\ REWRITE_TAC [all_code_def,SUBSET_DEF,IN_UNION,code_case_of,pair_case_of]
      \\ CONV_TAC (DEPTH_CONV BETA_CONV)
      \\ REWRITE_TAC [all_code_def,SUBSET_DEF,IN_UNION,code_case_of,pair_case_of]
      \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [])
    in MP th lemma end
  val fs = map expend_code fs
  (* package up into funcs_ok *)
  val code = fs |> hd |> concl |> rator |> rator |> rand
  val funcs = listSyntax.mk_list(fs |> map (rand o concl),``:func``)
  val lemma = prove(``EVERY (func_ok ^code locs) []``,
                    SIMP_TAC std_ss [EVERY_DEF])
  fun combine [] = lemma
    | combine (th::thms) =
        MATCH_MP IMP_EVERY_func_ok (CONJ th (combine thms))
  val th = combine fs
  val funcs = th |> concl |> rand
  val th = th |> Q.INST [`locs`|->`fs_locs ^funcs`]
              |> CONV_RULE (REWR_CONV (GSYM funcs_ok_def))
              |> DISCH_ALL |> DISCH T
              |> PURE_REWRITE_RULE [fs_locs_def,AND_IMP_INTRO]
  val goal = th |> concl |> dest_imp |> fst
  val _ = write_line ""
  val _ = write_section "Proving correctness of call offsets"
  fun prove_fs_locs goal =
    if goal = T then (TRUTH,true) else
    if is_conj goal then let
      val (x,y) = dest_conj goal
      val (th1,s1) = prove_fs_locs x
      val (th2,s2) = prove_fs_locs y
      in (CONJ th1 th2, s1 andalso s2) end
    else (MATCH_MP EQ_T (EVAL goal), true)
      handle HOL_ERR _ => let
        val (lhs,rhs) = dest_eq goal
        val name = lhs |> rand |> stringSyntax.fromHOLstring
        val v = optionSyntax.dest_some rhs |> rand
                   |> numSyntax.int_of_term |> int_to_hex
        val _ = write_line ("Failed to prove that " ^ name ^ " is at " ^ v ^ ".")
        in (mk_thm([],goal),false) end
      handle HOL_ERR _ => failwith "internal error"
  val (lemma,fs_locs_success) = prove_fs_locs goal
  val th = MP th lemma
  fun print_fs_locs_success () =
    write_line (if fs_locs_success
                then "No call offset failures."
                else "Failed to prove correctness of some call offsets.")
  val _ = if fs_locs_success then write_line "Offsets proved correct." else ()
  (* export top-level graph definition *)
  val funcs = th |> concl |> rand
  val trans_defs = map (fst o snd) fs_and_trans_defs
  val name = "complete_graph"
  val _ = open_current name
  val rhs = ``list_func_trans ^funcs``
  val lhs = mk_var(name,type_of rhs)
  val graph = new_definition(name,mk_eq(lhs,rhs))
  val c = REWRITE_CONV [list_func_trans_thm] THENC EVAL
          THENC REWRITE_CONV (map GSYM trans_defs)
          THENC prepare_for_export_conv
  val lemma = graph |> CONV_RULE (RAND_CONV c)
  val _ = write_section "Summary"
  val _ = print_stack_intro_report ()
  val _ = print_graph_spec_report ()
  val _ = print_export_report ()
  val _ = print_fs_locs_success ()
  val _ = close_current ()
  in th end

(*

  val base_name = "loop-m0/example"
  val base_name = "kernel-gcc-O1/kernel"
  val () = read_files base_name ["f"]
  val _ = (skip_proofs := true)
  val _ = (skip_proofs := false)
  val names = section_names()
  local val randgen = Random.newgen()
  in fun get_rand_name () =
       el (Random.range(1,length names) randgen) names end

  val _ = func_decompile print_title (get_rand_name ());
  val _ = func_decompile print_title sec_name;

  val _ = max_print_depth := 5;

  val th = prove_funcs_ok names

*)

end
