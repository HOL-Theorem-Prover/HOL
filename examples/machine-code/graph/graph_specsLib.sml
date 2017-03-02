structure graph_specsLib =
struct

open HolKernel boolLib bossLib Parse;
open listTheory wordsTheory pred_setTheory arithmeticTheory wordsLib pairTheory;
open set_sepTheory progTheory helperLib addressTheory combinTheory;

open backgroundLib file_readerLib derive_specsLib stack_introLib writerLib;

open GraphLangTheory

infix \\ val op \\ = op THEN;

val code_case_of = TypeBase.case_def_of ``:code``;

val emp_pat = ``emp:'a set set``
val s_var = mk_var("s",``:state``)

fun get_pc_pat () = let
  val (_,_,_,pc) = get_tools ()
  in ``^pc w`` end

local
  val var_bool_pat = ``var_bool n s``
  val var_nat_pat = ``var_nat n s``
  val var_word8_pat = ``var_word8 n s``
  val var_word32_pat = ``var_word32 n s``
  val var_mem_pat = ``var_mem n s``
in
  fun var_lookup tm =
    can (match_term var_bool_pat) tm orelse
    can (match_term var_nat_pat) tm orelse
    can (match_term var_word8_pat) tm orelse
    can (match_term var_word32_pat) tm orelse
    can (match_term var_mem_pat) tm
  fun mk_update (x,y) =
    if can (match_term var_bool_pat) x then
      pairSyntax.mk_pair(x |> rator |> rand,mk_abs(s_var,mk_comb(``VarBool``,y)))
    else if can (match_term var_nat_pat) x then
      pairSyntax.mk_pair(x |> rator |> rand,mk_abs(s_var,mk_comb(``VarNat``,y)))
    else if can (match_term var_word8_pat) x then
      pairSyntax.mk_pair(x |> rator |> rand,mk_abs(s_var,mk_comb(``VarWord8``,y)))
    else if can (match_term var_word32_pat) x then
      pairSyntax.mk_pair(x |> rator |> rand,mk_abs(s_var,mk_comb(``VarWord32``,y)))
    else if can (match_term var_mem_pat) x then
      pairSyntax.mk_pair(x |> rator |> rand,mk_abs(s_var,mk_comb(``VarMem``,y)))
    else failwith "should not happen (mk_update)"
end

local
  val arm_state_inst = arm_STATE_thm |> concl |> find_terms var_lookup
          |> map (fn tm =>
            let
              val str = tm |> rator |> rand |> stringSyntax.fromHOLstring
              val ty = type_of tm
            in mk_var(str,ty) |-> tm end)
          |> (fn x => (``dmem:word32 set`` |->
                       ``(var_dom "dom" s):word32 set``)::
                      (``dom_stack:word32 set`` |->
                       ``(var_dom "dom_stack" s):word32 set``)::
                      (``mode:word5`` |->
                       ``w2w (var_word8 "mode" s):word5``)::x) |> INST
  val arm_state = arm_STATE_thm |> concl |> rator |> rand
  val arm_state_parts = arm_STATE_thm |> concl |> rand |> list_dest dest_star
  val arm_state_type = arm_state_parts |> hd |> type_of
  val arm_state_combs = map (fn tm => (rator tm,rand tm)) arm_state_parts
  val arm_state_thm = arm_STATE_thm
  val m0_state_inst = m0_STATE_thm |> concl |> find_terms var_lookup
          |> map (fn tm =>
            let
              val str = tm |> rator |> rand |> stringSyntax.fromHOLstring
              val ty = type_of tm
            in mk_var(str,ty) |-> tm end)
          |> (fn x => (``dmem:word32 set`` |->
                       ``(var_dom "dom" s):word32 set``)::
                      (``dom_stack:word32 set`` |->
                       ``(var_dom "dom_stack" s):word32 set``)::
                      (mk_var("count",``:num``) |->
                       ``(var_nat "clock" s):num``)::
                      (``mode:Mode`` |->
                       ``Mode_Thread:Mode``)::x) |> INST
  val m0_state = m0_STATE_thm |> concl |> rator |> rand
  val m0_state_parts = m0_STATE_thm |> concl |> rand |> list_dest dest_star
  val m0_state_type = m0_state_parts |> hd |> type_of
  val m0_state_combs = map (fn tm => (rator tm,rand tm)) m0_state_parts
  val m0_state_thm = m0_STATE_thm
in
  fun state_tools () =
    case (!arch_name) of
      ARM => (arm_state_inst, arm_state, arm_state_parts,
              arm_state_type, arm_state_combs, arm_state_thm)
    | M0 => (m0_state_inst, m0_state, m0_state_parts, m0_state_type,
              m0_state_combs, m0_state_thm)
end

val STATE_INTRO_RULE_input = ref TRUTH
(*
  val th = !STATE_INTRO_RULE_input
*)
fun STATE_INTRO_RULE th = let
  val (state_inst, state, state_parts,
       state_type, state_combs, state_thm) = state_tools ()
  val pc_pat = get_pc_pat ()
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) []
              |> REWRITE_RULE [SPEC_MOVE_COND] |> UNDISCH_ALL
              |> Q.INST [`curr`|->`stack`]
  (* make pre into just ``STATE s`` *)
  val th = state_inst th
  val (_,pre,_,_) = dest_spec (concl th)
  val ps = list_dest dest_star pre
  val pc = first (can (match_term pc_pat)) ps
  val missing_parts = diff state_parts ps
  val frame = list_mk_star missing_parts state_type
  val th = SPEC_FRAME_RULE th frame
  val (_,pre,_,_) = dest_spec (concl th)
  val goal = mk_eq(pre,mk_star(state,pc))
  val conv = PURE_REWRITE_CONV [state_thm,emp_STAR] THENC
             BINOP_CONV STAR_AC_CONV THENC REWRITE_CONV []
  val lemma = auto_conv_prove "STATE_INTRO_RULE - 1" goal conv
  val th = th |> CONV_RULE (PRE_CONV (REWR_CONV lemma))
  (* make post into just state *)
  val th = PURE_REWRITE_RULE [STAR_IF] th
  val (_,_,_,post) = dest_spec (concl th)
  fun fix_post_conv post = let
    val ps = list_dest dest_star post
    val pc = first (can (match_term pc_pat)) ps
    val ps = filter (not o can (match_term pc_pat)) ps
    val ps = filter (not o can (match_term emp_pat)) ps
    fun find_match x [] = fail ()
      | find_match x ((n,y)::xs) =
          if x = n then y else find_match x xs
    fun find_all_matches tm =
      [(find_match (rator tm) state_combs,rand tm)]
      handle HOL_ERR _ => let
        val x = repeat rator tm
        val y = first (fn tm => x = repeat rator tm) state_parts
        fun dest_app tm = let
          val (x,y) = dest_comb tm
          val (f,xs) = dest_app x
          in (f,xs @ [y]) end handle HOL_ERR _ => (tm,[])
        val xs = zip (dest_app y |> snd) (dest_app tm |> snd)
        in xs end
    val qs = ps |> map find_all_matches |> flatten
                |> filter (fn (x,y) => x <> y) |> all_distinct
    val new_s = listSyntax.mk_list(
                  foldl (fn ((x,y),s) => mk_update(x,y)::s) [] qs,
                  ``:string # (state -> variable)``)
    val new_s = ``apply_update ^new_s ^s_var``
    val goal = mk_eq(post,mk_star(mk_comb(rator state,new_s),pc))
    val conv = (REWRITE_CONV [state_thm,var_update_thm,
                  apply_update_def,
                  CONS_11,NOT_CONS_NIL,GSYM NOT_CONS_NIL]
                THENC (DEPTH_CONV stringLib.string_EQ_CONV)
                THENC REWRITE_CONV [] THENC SIMP_CONV (srw_ss()) []
                THENC PURE_REWRITE_CONV [state_thm,emp_STAR]
                THENC BINOP_CONV STAR_AC_CONV THENC REWRITE_CONV [])
    val lemma = auto_conv_prove "STATE_INTRO_RULE - 2" goal conv
    in lemma end
  fun fix_if_post_conv post =
    if is_cond post then BINOP_CONV fix_if_post_conv post
    else fix_post_conv post
  val th = th |> CONV_RULE (POST_CONV fix_if_post_conv)
  in th end
  handle HOL_ERR e =>
    (STATE_INTRO_RULE_input := th;
     report_error "STATE_INTRO_RULE" (HOL_ERR e))

fun write_transform th1 th2_opt th_res = let
  val clean_th = REWRITE_RULE [] o DISCH_ALL
  val _ = write_line "Proved:"
  val _ = write_thm (clean_th th_res)
  val _ = write_line "Using:"
  val _ = write_thm (clean_th th1)
  val _ = (case th2_opt of NONE => () | SOME th => write_thm (clean_th th))
  in th_res end

fun mk_code_term c =
  case (!arch_name) of ARM => ``ARM ^c`` | M0 => ``M0 ^c``;

val make_ASM_input = ref TRUTH;
val make_CALL_input = ref TRUTH;
val make_SWITCH_input = ref TRUTH;

local
  fun read_pc_assum hs = let
    val h = first (can (match_term ``var_word32 "pc" s = w``)) hs
    in (h |> rand,filter (fn tm => tm <> h) hs) end
  fun read_pc_update th = let
    val tm = find_term (can (match_term ``("pc" =+ VarWord32 (n2w n))``))
               (concl th) |> rand |> rand
    in (mk_comb(``Jump``,tm),th) end
    handle HOL_ERR _ => let
    val tm = find_term (can (match_term ``("pc" =+ pat)``)) (concl th)
    val x = ``var_word32 "ret" s``
    val assum = mk_eq(tm |> rand,``^s_var "ret"``)
    val rw = RAND_CONV (fn tm => ASSUME assum) tm
    val th = RW1 [rw] th
    in (``Return``,th) end
  fun read_state_update th = let
    val (_,_,_,q) = dest_spec (concl th)
    in q |> rand end
  val simp = SIMP_CONV std_ss [IMPL_INST_def,exec_next_def,CONS_11,NOT_CONS_NIL,
        check_jump_def,get_assert_def,APPLY_UPDATE_THM,
        stringTheory.CHR_11,code_case_of]
  fun has_call_tag th =
    can (find_term (can dest_call_tag)) (concl (DISCH_ALL th))
  val ret_and_all_names =
    ret_and_all_names_def |> concl |> rand
                          |> REWRITE_CONV [all_names_def,APPEND] |> concl |> rand
                          |> listSyntax.dest_list |> fst
  fun dest_supdate tm =
    listSyntax.dest_list tm |> fst |> map pairSyntax.dest_pair
  fun prepare_supdate_for_call th = let
    val (_,pre,_,post) = dest_spec (concl th)
    val pc1 = pre |> rand |> rand
    val tm = post |> rator |> rand |> rand |> rator |> rand
    val supdate = dest_supdate tm
    val r0 = ``"r0"``
    val r14 = ``"r14"``
    val ret_str = ``"ret"``
    val r0_input_str = ``"r0_input"``
    val (is_tail_call,ret) = let
      val u = first (fn (t,x) => t = r14) supdate |> snd
      val res = EVAL ``(^u s = VarWord32 (^pc1+4w)) \/ (^u s = VarWord32 (^pc1+2w))``
        |> concl |> rand
      in if res = T then
           (false,mk_comb(``Jump``,u |> dest_abs |> snd |> rand))
         else (true,``Return``) end handle HOL_ERR _ => (true,``Return``)
    fun get_assign tm =
      if tm = r0_input_str then
        pairSyntax.mk_pair(r0_input_str,``var_acc ^r0``)
      else let
        val tm2 = if is_tail_call then tm else
                  if tm = ret_str then r14 else tm
        val rhs = first (fn (t,x) => (t = tm2)) supdate |> snd
                  handle HOL_ERR _ => ``var_acc ^tm``
        in pairSyntax.mk_pair(tm,rhs) end
    val new_supdate = map get_assign ret_and_all_names
    val new_supdate = listSyntax.mk_list(new_supdate,type_of (hd new_supdate))
    val x = post |> rator |> rand |> rator
    val goal = ``^x (apply_update ^tm s) = ^x (apply_update ^new_supdate s)``
    val lemma = auto_prove "prepare_supdate_for_call" (goal,
      TRY (MATCH_MP_TAC arm_STATE_all_names)
      \\ TRY (MATCH_MP_TAC m0_STATE_all_names)
      \\ REWRITE_TAC [all_names_def,EVERY_DEF,apply_update_def,
           combinTheory.APPLY_UPDATE_THM,var_acc_def]
      \\ CONV_TAC (DEPTH_CONV BETA_CONV)
      \\ CONV_TAC (DEPTH_CONV stringLib.string_EQ_CONV)
      \\ REWRITE_TAC [all_names_def,EVERY_DEF,apply_update_def,
           combinTheory.APPLY_UPDATE_THM,var_acc_def])
    val th = CONV_RULE ((RAND_CONV o RATOR_CONV o RAND_CONV)
               (REWR_CONV lemma)) th
    in (th,ret) end
(*
  val th = !make_CALL_input
*)
  fun make_CALL th = let
    val th = STATE_INTRO_RULE th
    val hs = filter (fn tm => tm <> T) (hyp th)
    val tag = first (can dest_call_tag) hs
    val fname = fst (dest_call_tag tag)
    val th = th |> DISCH_ALL |> PURE_REWRITE_RULE [CALL_TAG_def] |> UNDISCH_ALL
    val (_,pre,_,post) = dest_spec (concl th)
    val pc1 = pre |> rand |> rand
    val pc2 = post |> rand |> rand
    val supdate = post |> rator |> rand |> rand |> rator |> rand
    val hs = filter (fn tm => tm <> T) (hyp th)
    val side = if length hs = 0 then ``NONE:(state->bool) option``
               else ``SOME ^(mk_abs(s_var,list_mk_conj hs))``
    val (th,ret) = prepare_supdate_for_call th
    val (_,pre,_,post) = dest_spec (concl th)
    val supdate = post |> rator |> rand |> rand |> rator |> rand
    val name = stringSyntax.fromMLstring fname
    val i = ``Inst ^pc1 (K T) (CALL ^side ^supdate ^name ^ret)``
    val (m,_,c,_) = dest_spec (concl th)
    val goal = ``(locs ^name = SOME ^pc2) ==> IMPL_INST ^(mk_code_term c) locs ^i``
(*
  set_goal([],goal)
*)
    val lemma = auto_prove "make_CALL" (goal,
      CONV_TAC simp \\ REPEAT STRIP_TAC \\ IMP_RES_TAC ret_lemma
      \\ ASM_SIMP_TAC std_ss [code_case_of]
      \\ NTAC 20 (ONCE_REWRITE_TAC [var_word32_apply_update])
      \\ CONV_TAC (DEPTH_CONV stringLib.string_EQ_CONV)
      \\ ASM_REWRITE_TAC [apply_update_NIL]
      \\ SIMP_TAC std_ss [next_ok_def,check_ret_def]
      \\ TRY (REWRITE_TAC [ret_and_all_names_def,all_names_def,MAP,APPEND]
        \\ REWRITE_TAC [all_names_def,EVERY_DEF,apply_update_def,
             combinTheory.APPLY_UPDATE_THM,var_acc_def,var_word32_def]
        \\ EVAL_TAC \\ NO_TAC)
      \\ (DISCH_ALL th |> DISCH T
            |> PURE_REWRITE_RULE [AND_IMP_INTRO] |> MATCH_MP_TAC)
      \\ ASM_REWRITE_TAC [] \\ FULL_SIMP_TAC (srw_ss()) [])
    val th = lemma |> UNDISCH_ALL |> SIMP_RULE std_ss [word_add_n2w]
    in th end
    handle HOL_ERR e =>
      (make_CALL_input := th;
       report_error "make_CALL" (HOL_ERR e))
(*
  val th = !make_ASM_input
*)
  fun make_ASM th =
    if has_call_tag th then make_CALL th else let
    val th = STATE_INTRO_RULE th
    val (_,pre,_,post) = dest_spec (concl th)
    val pc1 = pre |> rand |> rand
    val pc2 = post |> rand |> rand
    val supdate = post |> rator |> rand |> rand |> rator |> rand
    val (jmp,th) = if wordsSyntax.is_n2w pc2 then (``Jump ^pc2``,th) else
      (``Return``,let
         val lemma = ASSUME (mk_eq(pc2,``var_word32 "ret" s``))
         in CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV (fn tm => lemma)))) th end)
    val hs = filter (fn tm => tm <> T) (hyp th)
    val side = if length hs = 0 then ``NONE:(state->bool) option``
               else ``SOME ^(mk_abs(s_var,list_mk_conj hs))``
    val i = ``Inst ^pc1 (K T) (ASM ^side ^supdate ^jmp)``
    val th = RW [apply_update_NIL] th
    val (m,_,c,_) = dest_spec (concl th)
    val goal = ``IMPL_INST ^(mk_code_term c) locs ^i``
(*
  set_goal([],goal)
*)
    val lemma = auto_prove "make_ASM" (goal,
      CONV_TAC simp \\ REPEAT STRIP_TAC \\ IMP_RES_TAC ret_lemma
      \\ ASM_SIMP_TAC std_ss [code_case_of]
      \\ NTAC 20 (ONCE_REWRITE_TAC [var_word32_apply_update])
      \\ CONV_TAC (DEPTH_CONV stringLib.string_EQ_CONV)
      \\ ASM_REWRITE_TAC [apply_update_NIL] THEN1 EVAL_TAC THEN1 EVAL_TAC
      \\ (DISCH_ALL th |> DISCH T
            |> PURE_REWRITE_RULE [AND_IMP_INTRO] |> MATCH_MP_TAC)
      \\ ASM_REWRITE_TAC [] \\ FULL_SIMP_TAC (srw_ss()) [])
    in lemma end
    handle HOL_ERR e =>
      (make_ASM_input := th;
       report_error "make_ASM" (HOL_ERR e))
(*
  val th = !make_SWITCH_input
*)
  fun make_SWITCH th = let
    val th = STATE_INTRO_RULE th
    (* val th = SIMP_RULE std_ss [Once EQ_SYM_EQ] th *)
    val post = th |> concl |> rand
    val pre =
      th |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
         |> CONV_RULE ((RATOR_CONV o RAND_CONV) (REWRITE_CONV []))
         |> concl |> dest_imp |> fst
    val pre = mk_abs(s_var,pre)
    fun get_simp_asm x1 = let
      val upd = x1 |> rator |> rand |> rand |> rator |> rand
      val pc = x1 |> rand |> rand
      in ``ASM (SOME ^pre) ^upd (Jump ^pc)`` end
    fun dest_ifs post = let
      val (g,x1,x2) = dest_cond post
      val next1 = get_simp_asm x1
      val next2 = dest_ifs x2
      in ``IF (\s. ^g) ^next1 ^next2`` end
      handle HOL_ERR _ => get_simp_asm post
    val next = dest_ifs post
    val pc1 = th |> concl |> rator |> rator |> rand |> rand |> rand
    val i = ``Inst ^pc1 (K T) ^next``
    val (m,_,c,_) = dest_spec (concl th)
    val goal = ``IMPL_INST ^(mk_code_term c) locs ^i``
    val lemma = auto_prove "make_SWITCH" (goal,
      REWRITE_TAC [IMPL_INST_IF_SPLIT]
      \\ CONV_TAC (DEPTH_CONV BETA_CONV)
      \\ REPEAT STRIP_TAC
      \\ CONV_TAC simp \\ REPEAT STRIP_TAC
      \\ TRY (EVAL_TAC \\ NO_TAC)
      \\ MP_TAC (DISCH_ALL th)
      \\ ASM_REWRITE_TAC []
      \\ STRIP_TAC
      \\ TRY (POP_ASSUM MATCH_MP_TAC)
      \\ ASM_REWRITE_TAC [var_word32_def,var_acc_def]
      \\ EVAL_TAC)
    in lemma end
    handle HOL_ERR e =>
      (make_SWITCH_input := th;
       report_error "make_SWITCH" (HOL_ERR e))
in
  fun make_INST (i:int,(th,l:int,j:int option),NONE) =
       write_transform th NONE
        (if not (is_cond (rand (concl th)))
         then make_ASM th else make_SWITCH th)
    | make_INST (i,(th1',l',j'),SOME (th2',l:int,j:int option)) = let
        val th1 = make_INST (i,(th1',l',j'),NONE)
        val th2 = th2' |> make_ASM
        val not_guard = th2 |> concl |> find_term (can (match_term ``ASM (SOME k)``))
                            |> rand |> rand |> dest_abs |> snd
        val guard = dest_neg not_guard handle HOL_ERR _ => mk_neg not_guard
        val c = (RAND_CONV o RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss [])
        val th = MATCH_MP IMPL_INST_IF (CONJ th1 th2)
                 |> CONV_RULE (BINOP1_CONV (SIMP_CONV std_ss []))
                 |> MATCH_MP T_IMP |> SPEC (mk_abs(s_var,guard))
        val th = RW1 [IMPL_INST_SIMP_IF] th
                 |> SIMP_RULE std_ss [IMPL_INST_IF_RW]
        in write_transform th1' (SOME th2') th end
end

(*
val (i:int,(th,l:int,j:int option),NONE) =
  first (fn (i,(th,_,_),_) => i = 52) thms

val (i:int,(th,l:int,j:int option),NONE) = thms |> el 2

val (_,(th1,_,_),SOME (th2,l:int,j:int option)) = first (not o can make_INST) thms

*)

fun try_map g f [] = []
  | try_map g f (x::xs) = let
      val y = f x
      in y :: try_map g f xs end
      handle HOL_ERR _ =>
        (g x; try_map g f xs)

val graph_spec_fails = ref ([] : (int * string) list);

fun print_graph_spec_fail (pos,sec_name) = let
  val str = ("Graph spec failed in " ^ sec_name ^ " for pos " ^
              (int_to_hex pos) ^ ".")
  in (write_line str; print (str ^ "\n")) end

fun add_graph_spec_fail pos sec_name =
  (print_graph_spec_fail (pos,sec_name);
   graph_spec_fails := (pos, sec_name) :: (!graph_spec_fails));

fun clear_graph_spec_fails () = (graph_spec_fails := []);

fun print_graph_spec_report () =
  (if length (!graph_spec_fails) = 0 then
    (write_line "No graph spec failures."; [])
   else (map print_graph_spec_fail (!graph_spec_fails)))

fun get_pc_val th = let
  val pc_pat = get_pc_pat ()
  val (_,p,_,_) = dest_spec (concl th)
  in find_term (can (match_term pc_pat)) p
       |> rand |> rand |> numSyntax.int_of_term end

fun derive_insts_for sec_name = let
  val thms = dervie_specs_for sec_name
  val _ = write_subsection "Proving inst theorems"
  val _ = (writer_prints := false)
  val insts = try_map (fn (_,(th,_,_),_) =>
    add_graph_spec_fail (get_pc_val th) sec_name) make_INST thms
  val _ = (writer_prints := true)
  val inst_count = int_to_string (length insts)
  val _ = write_line (inst_count ^ " inst theorems describe instructions.")
  in insts end;

end
