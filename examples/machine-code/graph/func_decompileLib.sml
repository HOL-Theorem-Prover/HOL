structure func_decompileLib :> func_decompileLib =
struct

open HolKernel boolLib bossLib Parse;
open listTheory wordsTheory pred_setTheory
open GraphLangTheory
open backgroundLib file_readerLib derive_specsLib graph_specsLib exportLib;
open writerLib cond_cleanLib;

val _ = max_print_depth := ~1;
val _ = set_trace "Unicode" 0;

local
  val export_fails = ref ([]:string list)
in
  fun add_export_fail sec_name = (export_fails := sec_name :: (!export_fails))
  fun get_export_fails () = rev (!export_fails)
  fun clear_export_fails () = (export_fails := [])
end;

local
  val th = bit_field_insert |> SPEC_ALL |> REWRITE_RULE [LET_THM]
  val pat = th |> UNDISCH |> concl |> dest_eq |> fst
in
  fun remove_bif_field_insert_conv tm = let
    val (i,t) = match_term pat tm
    val lemma = INST i (INST_TYPE t th)
                |> CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL)
    val lemma = MP lemma TRUTH
                |> CONV_RULE ((RAND_CONV o RAND_CONV) EVAL THENC
                              RAND_CONV BETA_CONV)
    in lemma end
    handle HOL_ERR _ => NO_CONV tm
end

(*
val funcs_def = TRUTH
*)

fun func_export sec_name th funcs_def = let
  val f = th |> concl |> rand
  val name = sec_name
  val rhs = ``func_body_trans ^f``
  val lhs = mk_var(name,type_of rhs)
  val name = tidy_up_name name
  val trans_def = new_definition(name,mk_eq(lhs,rhs))
  val _ = write_subsection "Evaluating graph"
  val c = REWRITE_CONV [func_body_trans_def,func_trans_def,funcs_def]
          THENC REWRITE_CONV [wordsTheory.word_extract_mask,export_init_rw,
                 GSYM SignedDiv_def, GSYM UnsignedDiv_def]
          THENC EVAL THENC PURE_REWRITE_CONV [GSYM word_sub_def,GSYM w2w_def]
          THENC (DEPTH_CONV remove_bif_field_insert_conv)
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
  val str = section_location sec_name
  val str = if size str <= 8 then str else String.substring(str,8,size str - 8)
  val tm = str |> Arbnumcore.fromHexString |> numSyntax.mk_numeral
  in wordsSyntax.mk_n2w(tm,tysize ()) end

val sec_name = "f"

fun func_decompile print_title sec_name = let
  val _ = (writer_prints := true)
  val _ = open_current sec_name
  val _ = print_title sec_name
  val thms = derive_insts_for sec_name
(*  val thms = clean_conds thms *)
  val code = thms |> hd |> concl |> rator |> rator |> rand
             handle Empty => (case !arch_name of
                                ARM   => ``ARM {}``
                              | ARM8  => ``ARM8 {}``
                              | M0    => ``M0 {}``
                              | RISCV => ``RISCV {}``)
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
  val funcs_name = tidy_up_name funcs_name
  val funcs_def_lhs = mk_var(funcs_name,type_of funcs_def_rhs)
  val funcs_def = new_definition(funcs_name,``^funcs_def_lhs = ^funcs_def_rhs``)
  val th = CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM funcs_def)))) th
  in (th,func_export sec_name th funcs_def) end

fun list_mk_union [] = ``{}:'a set``
  | list_mk_union [x] = x
  | list_mk_union (x::xs) = pred_setSyntax.mk_union(list_mk_union xs,x)

fun arch_to_string () =
  case !arch_name of
    RISCV => "riscv"
  | ARM   => "arm"
  | ARM8  => "arm8"
  | M0    => "m0";

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
(*
  val bad_fs = fs |> filter (can (find_term pred_setSyntax.is_empty) o
                             rand o rator o rator o concl)
  val fs = fs |> filter (not o can (find_term pred_setSyntax.is_empty) o
                         rand o rator o rator o concl)
*)
  val all_code = fs |> map (rand o rator o rator o concl)
  val code_name = all_code |> hd |> rator
  val all_code = mk_comb(code_name, (all_code |> map rand |> list_mk_union))
  val all_code_name = "all_" ^ arch_to_string () ^ "_code"
  val all_code_var = mk_var(all_code_name,type_of all_code)
  val all_code_def = new_definition(all_code_name,mk_eq(all_code_var,all_code))
  val all_code_const = all_code_def |> concl |> dest_eq |> fst
  val pair_case_of = TypeBase.case_def_of ``:'a # 'b``;
  fun expend_code th = let
    val th = MATCH_MP func_ok_EXPEND_CODE th |> SPEC all_code_const
    val goal = th |> concl |> dest_imp |> fst
    val lemma = auto_prove "expand_code" (goal,
      REWRITE_TAC [all_code_def,SUBSET_DEF,IN_UNION,pair_case_of,
                   ARM_def,ARM8_def,M0_def,RISCV_def]
      \\ CONV_TAC (DEPTH_CONV BETA_CONV)
      \\ REWRITE_TAC [all_code_def,SUBSET_DEF,IN_UNION,pair_case_of]
      \\ CONV_TAC (DEPTH_CONV BETA_CONV)
      \\ REWRITE_TAC [all_code_def,SUBSET_DEF,IN_UNION,pair_case_of]
      \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [])
    in MP th lemma end
  val fs = map expend_code fs
  (* complete fs *)
  val _ = write_subsection "\nCompleting graph"
  val fs = let
    val all = fs |> map (rand o concl)
    val w_var = mk_var("w",wsize ())
    val pat = ``locs (name:string) = SOME ^w_var``
    fun f tm = subst (fst (match_term pat tm)) ``Func name ^w_var []``
    val extra = graph_specsLib.try_map (fn x => x) f (flatten (map hyp fs))
    val all_rator = map rator all
    val extra = filter (fn ex => not (term_mem (rator ex) all_rator)) extra
    val r = fs |> hd |> concl |> rator
    val extra_fs = map (fn tm => prove(mk_comb(r,tm),
                     SIMP_TAC (srw_ss()) [func_ok_def])) extra
    (*
    val th = hd extra_fs
    val th = mk_thm([],``func_ok all_riscv_code locs (Func "__ctzdi2" 2147580890w [])``)
    *)
    fun export_empty th = let
      val sec_name = th |> concl |> rand |> rator |> rator |> rand
                        |> stringLib.fromHOLstring
      in func_export sec_name th TRUTH end
    val _ = map export_empty extra_fs
    in fs @ extra_fs end
  (* package up into funcs_ok *)
  val code = fs |> hd |> concl |> rator |> rator |> rand
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
    if aconv goal T then (TRUTH,true) else
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
                else (has_failures := true;
                      "Failed to prove correctness of some call offsets."))
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

  val base_name = "example-arm8/SysModel"
  val _ = read_files base_name []
  val _ = open_current "test"
  val sec_name = "after"
  val _ = func_decompile print_title sec_name

  val names = section_names()
  val res = prove_funcs_ok names

  val base_name = "kernel-riscv/kernel-riscv"
  val base_name = "loop-riscv/example"
  val base_name = "seL4-kernel/arm/kernel"
  val _ = read_files base_name []
  val _ = open_current "test"
  val sec_name = "lookupSlot"
  val sec_name = "memzero"
  val sec_name = "memcpy"
  val sec_name = "isIRQPending"
  val sec_name = "get_num_avail_p_regs"
  val sec_name = "ndks_boot"
  val sec_name = "num_avail_p_regs"
  val sec_name = "resolveAddressBits"

  val names = ["performInvocation_Reply","performInvocation_Endpoint"]
  val names = section_names()

  val base_name = "loop-riscv/example"
  val _ = read_files base_name []
  val _ = open_current "test"
  val sec_name = "memcpy"
  val sec_name = "memzero"
  val names = section_names()

  val base_name = "kernel-gcc-O1/kernel"
  val base_name = "loop/example"
  val base_name = "loop-m0/example"
  val () = read_files base_name []
  val _ = (skip_proofs := true)
  val _ = (skip_proofs := false)
  val names = section_names()

  val sec_name = "g"

  local val randgen = Random.newgen()
  in fun get_rand_name () =
       el (Random.range(1,length names) randgen) names end

  val _ = func_decompile print_title (get_rand_name ());
  val _ = func_decompile print_title sec_name;

  val _ = max_print_depth := 5;

  val th = prove_funcs_ok names

*)

end
