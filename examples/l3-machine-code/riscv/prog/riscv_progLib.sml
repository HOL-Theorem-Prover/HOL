structure riscv_progLib :> riscv_progLib =
struct

open HolKernel boolLib bossLib
open stateLib riscv_progTheory

structure Parse =
struct
   open Parse
   val (Type, Term) =
       riscv_progTheory.riscv_prog_grammars
         |> apsnd ParseExtras.grammar_loose_equality
         |> parse_from_grammars
end

open Parse

val ERR = Feedback.mk_HOL_ERR "riscv_progLib"

(* ------------------------------------------------------------------------ *)

val riscv_proj_def = riscv_progTheory.riscv_proj_def
val riscv_comp_defs = riscv_progTheory.component_defs

fun syn n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "riscv_prog"
val riscv_1 = syn 2 HolKernel.dest_monop HolKernel.mk_monop
val riscv_2 = syn 3 HolKernel.dest_binop HolKernel.mk_binop
val riscv_3 = syn 4 HolKernel.dest_triop HolKernel.mk_triop
val byte = wordsSyntax.mk_int_word_type 8
val word5 = wordsSyntax.mk_int_word_type 5
val half = wordsSyntax.mk_int_word_type 16
val word = wordsSyntax.mk_int_word_type 32
val dword = wordsSyntax.mk_int_word_type 64
val (_, mk_riscv_procID, dest_riscv_procID, _) = riscv_1 "riscv_procID"
val (_, _, dest_riscv_ID, is_riscv_ID) = riscv_2 "riscv_ID"
val (_, mk_riscv_c_PC, dest_riscv_c_PC, _) = riscv_2 "riscv_c_PC"
val (_, mk_riscv_MEM, dest_riscv_MEM, is_riscv_MEM) = riscv_2 "riscv_MEM8"
val (_, mk_riscv_gpr, dest_riscv_gpr, is_riscv_gpr) = riscv_3 "riscv_c_gpr"
val (_, _, dest_riscv_PC, _) = riscv_1 "riscv_PC"
val (_, _, dest_riscv_REG, _) = riscv_2 "riscv_REG"
val st = Term.mk_var ("s", ``:riscv_state``)
val id_tm = ``^st.procID``

(* -- *)

val riscv_select_state_thms =
   List.map (fn t => stateLib.star_select_state_thm riscv_proj_def [] ([], t))
            riscv_comp_defs

val riscv_select_state_pool_thm =
  CONJ
   (pool_select_state_thm riscv_proj_def []
      (utilsLib.SRW_CONV
         [pred_setTheory.INSERT_UNION_EQ, stateTheory.CODE_POOL, riscv_instr_def]
         ``CODE_POOL riscv_instr {(pc, [w1;w2])}``))
   (pool_select_state_thm riscv_proj_def []
      (utilsLib.SRW_CONV
         [pred_setTheory.INSERT_UNION_EQ, stateTheory.CODE_POOL, riscv_instr_def]
         ``CODE_POOL riscv_instr {(pc, [w1;w2;w3;w4])}``))

local
  val riscv_instr_tm =
     Term.prim_mk_const {Thy = "riscv_prog", Name = "riscv_instr"}
  val strip_concat =
    HolKernel.strip_binop wordsSyntax.dest_word_concat
  val pc_tm = ``^st.c_PC ^id_tm``
  val pc_var = stateLib.gvar "pc" dword
  fun is_mem_access tm =
     case Lib.total boolSyntax.dest_eq tm of
        SOME (l, r) =>
           (bitstringSyntax.is_v2w r orelse wordsSyntax.is_word_literal r)
           andalso can (match_term ``^st.MEM8 _``) l
      | NONE => false
  fun hide_with_genvar (x: term) = x |-> Term.genvar (Term.type_of x)
  fun to_hide tm =
    case boolSyntax.dest_strip_comb tm of
       ("riscv$riscv_state_c_update_fupd", [t, _]) => combinSyntax.dest_K_1 t
     | ("riscv$riscv_state_log_fupd", [t, _]) => combinSyntax.dest_K_1 t
     | _ => raise ERR "" ""
  fun hide_hidden tm =
    let
      val (l, r) = boolSyntax.dest_eq tm
      val s = optionSyntax.dest_some r
      val sbst = List.map (hide_with_genvar o to_hide)
                   (HolKernel.find_terms (Lib.can to_hide) s)
    in
      boolSyntax.mk_eq (l, optionSyntax.mk_some (Term.subst sbst s))
    end
  fun mem_to_int tm =
    tm |> lhs |> rand |> rand |> rand |> numSyntax.int_of_term
    handle HOL_ERR _ => 0
in
  val last_input = ref TRUTH;
(*
  val thm = !last_input
*)
  fun mk_riscv_code_pool thm =
    let
      val _ = (last_input := thm)
      val id = stateLib.gvar "id" byte
      val pc = stateLib.gvar "pc" dword
      val pc_subst = Term.subst [id_tm |-> id, pc_tm |-> pc]
      val thm = thm |> DISCH_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
      val (a, tm) = (List.map pc_subst ## pc_subst) (Thm.dest_thm thm)
      val (m, a) = List.partition is_mem_access a
      val _ = length m = 2 orelse length m = 4 orelse
              failwith "cannot find code assumptions"
      val m = sort (fn x => fn y => mem_to_int x <= mem_to_int y) m
      val opc = listSyntax.mk_list(map rand m,type_of (rand (hd m)))
    in
      (mk_riscv_c_PC (id, pc),
       boolSyntax.rand (stateLib.mk_code_pool (riscv_instr_tm, pc, opc)),
       boolSyntax.list_mk_imp (a, hide_hidden tm))
    end
end

(* -- *)

local
   val addr_eq_conv =
      SIMP_CONV (bool_ss++wordsLib.WORD_ARITH_ss++wordsLib.WORD_ARITH_EQ_ss) []
in
   val memory_introduction =
      stateLib.introduce_map_definition
         (riscv_progTheory.riscv_MEMORY_INSERT, addr_eq_conv)
end

(* -- *)

val state_id =
   utilsLib.mk_state_id_thm riscvTheory.riscv_state_component_equality
      [["c_PC", "c_gpr"],
       ["c_PC", "c_Skip", "c_gpr"],
       ["c_Skip", "c_gpr"],
       ["c_PC"],
       ["c_PC","c_Skip"],
       ["c_Skip"],
       ["c_gpr"],
       ["c_Skip","c_gpr"],
       ["c_NextFetch", "c_PC"],
       ["c_NextFetch", "c_PC", "c_gpr"],
       ["c_NextFetch", "c_PC", "c_Skip"],
       ["c_NextFetch", "c_PC", "c_Skip", "c_gpr"],
       ["MEM8", "c_PC"],
       ["MEM8", "c_PC", "c_Skip"]
      ]

val riscv_frame =
   Thm.CONJ riscv_progTheory.c_gpr_frame
     (stateLib.update_frame_state_thm riscv_proj_def
        (["c_NextFetch", "c_PC", "MEM8", "c_Skip"]))

val ricv_frame_hidden =
  stateLib.update_hidden_frame_state_thm riscv_proj_def
    [``^st with c_update := x``,
     ``^st with log := x``
    ]

(* -- *)

local
   fun other_index tm =
     (case fst (boolSyntax.dest_strip_comb tm) of
         "riscv_prog$riscv_exception" => 0
       | "riscv_prog$riscv_procID" => 1
       | "riscv_prog$riscv_c_NextFetch" => 16
       | "riscv_prog$riscv_c_MCSR" => 17
       | "riscv_prog$riscv_c_PC" => 18
       | _ => ~1)
      handle HOL_ERR r => (print_term tm; raise HOL_ERR r)
   val total_dest_lit = Lib.total wordsSyntax.dest_word_literal
   fun word_compare (w1, w2) =
      case (total_dest_lit w1, total_dest_lit w2) of
         (SOME x1, SOME x2) => Arbnum.compare (x1, x2)
       | (SOME _, NONE) => General.GREATER
       | (NONE, SOME _) => General.LESS
       | (NONE, NONE) => Term.compare (w1, w2)
   val register = #2 o dest_riscv_gpr
   val address = HolKernel.strip_binop wordsSyntax.dest_word_add o
                 fst o dest_riscv_MEM
in
   fun psort p =
      let
         val (m, rst) = List.partition is_riscv_MEM p
         val (r, rst) = List.partition is_riscv_gpr rst
      in
         mlibUseful.sort_map other_index Int.compare rst @
         mlibUseful.sort_map register Term.compare r @
         mlibUseful.sort_map address (mlibUseful.lex_list_order word_compare) m
      end
end

local
  fun fix_id (p, q) =
    let
      val id = case List.find (Lib.can dest_riscv_c_PC) p of
                  SOME tm => fst (dest_riscv_c_PC tm)
                | NONE => raise ERR "riscv_write_footprint" "no PC assertion"
      val procid = mk_riscv_procID id
    in
      (procid :: p, procid :: q)
    end
  fun c_gpr_write (p, q, v) =
    let
      val ((id, v1), tm) = combinSyntax.dest_update_comb v
      val (l, gpr) = combinSyntax.strip_update v1
      val _ = gpr ~~ Term.mk_comb (tm, id) orelse
                    raise ERR "c_gpr_write" (Hol_pp.term_to_string v)
      val nq = List.map (fn (n, x) => mk_riscv_gpr (id, n, x)) l
      val not_in_p =
        List.filter
          (fn (n, _) =>
             List.all (fn ptm => case Lib.total dest_riscv_gpr ptm of
                                    SOME (id2, n2, _) =>
                                      not (id ~~ id2 andalso n ~~ n2)
                                  | NONE => true) p) l
      val np = List.map (fn (n, _) => mk_riscv_gpr (id, n, stateLib.vvar dword))
                 not_in_p
    in
      (np @ p, nq @ q)
    end
in
  val riscv_write_footprint =
    fix_id o
    stateLib.write_footprint riscv_1 riscv_2
     [("riscv$riscv_state_MEM8_fupd", "riscv_MEM8", ``^st.MEM8``),
      ("riscv$riscv_state_c_PC_fupd", "riscv_c_PC", ``^st.c_PC``),
      ("riscv$riscv_state_c_NextFetch_fupd", "riscv_c_NextFetch",
       ``^st.c_NextFetch``),
      ("riscv$riscv_state_c_Skip_fupd", "riscv_c_Skip", ``^st.c_Skip``)
     ] [] []
     [("riscv$riscv_state_c_gpr_fupd", c_gpr_write)
     ]
     (K false)
end

val riscv_mk_pre_post =
   stateLib.mk_pre_post
     riscv_progTheory.RISCV_MODEL_def riscv_comp_defs mk_riscv_code_pool []
     riscv_write_footprint psort

(* ------------------------------------------------------------------------ *)

local
   val SK = Option.SOME o Lib.K
   fun reg_index tm =
     Lib.with_exn wordsSyntax.uint_of_word tm (ERR "reg_index" "")
   val rname_reg = (Lib.curry (op ^) "r" o Int.toString o reg_index o List.last)
   val riscv_rmap =
     fn "riscv_prog$riscv_MEM8" => SK "b"
      | "riscv_prog$riscv_c_MCSR" => SK "mcsr"
      | "riscv_prog$riscv_c_gpr" => SOME rname_reg
      | "riscv_prog$riscv_REG" => SOME rname_reg
      | _ => NONE
in
   val riscv_rename = stateLib.rename_vars (riscv_rmap, ["b"])
end

local
  val rwts =
    List.map bitstringLib.v2w_n2w_CONV
       (List.tabulate
          (32, fn i => bitstringSyntax.padded_fixedwidth_of_num
                         (Arbnum.fromInt i, 5)))
  fun dest_reg tm = let val (_, n, v) = dest_riscv_gpr tm in (n, v) end
  val reg_width = 5
  val proj_reg = NONE : (term -> int) option
  val reg_conv = Conv.QCONV (REWRITE_CONV rwts)
  val ok_conv = Conv.DEPTH_CONV wordsLib.word_EQ_CONV
                THENC Conv.QCONV (SIMP_CONV (bool_ss++boolSimps.CONJ_ss) [])
  fun asm (tm: term) = (raise ERR "" "") : thm
  val model_tm = ``RISCV_MODEL``
in
  val combinations =
    stateLib.register_combinations
       (dest_reg, reg_width, proj_reg, reg_conv, ok_conv, asm, model_tm)
end

local
  val id0 = wordsSyntax.mk_wordii (0, 8)
  val rv64 = wordsSyntax.mk_wordii (2, 2)
  val rv64_rule =
    PURE_REWRITE_RULE
      [GSYM riscv_progTheory.riscv_REG_def, GSYM riscv_progTheory.riscv_PC_def]
  val (_, mk_mcpuid, _, _) = HolKernel.syntax_fns1 "riscv" "MachineCSR_mcpuid"
  val (_, mk_ArchBase, _, _) = HolKernel.syntax_fns1 "riscv" "mcpuid_ArchBase"
  val pre = progSyntax.strip_star o temporal_stateSyntax.dest_pre' o Thm.concl


  fun specialize_to_rv64i th =
(*
val SOME tm = List.find is_riscv_ID (pre th)
*)
    case List.find is_riscv_ID (pre th) of
       SOME tm =>
         let
           val (id, mcsr) = dest_riscv_ID tm
           val archbase = boolSyntax.mk_eq (mk_ArchBase (mk_mcpuid mcsr), rv64)
         in
           th |> Thm.INST [id |-> id0]
              |> rv64_rule
              |> PURE_REWRITE_RULE [ASSUME archbase]
              |> Conv.CONV_RULE (Conv.DEPTH_CONV wordsLib.word_EQ_CONV)
              |> REWRITE_RULE []
              |> Thm.DISCH archbase
              |> Conv.CONV_RULE stateLib.MOVE_COND_CONV
              |> helperLib.MERGE_CONDS_RULE
              |> stateLib.introduce_triple_definition
                   (true, riscv_progTheory.riscv_RV64I_def)
         end
     | NONE => raise ERR "specialize_to_rv64i" "no ID assertion"
  val to_rv64 = ref true
in
  fun set_to_rv64 b = to_rv64 := b
  fun spec_to_rv64 thm = if !to_rv64 then specialize_to_rv64i thm else thm
  fun reg_idx tm =
    if !to_rv64 then fst (dest_riscv_REG tm) else #2 (dest_riscv_gpr tm)
end

local
  val SPEC_IMP_RULE =
    Conv.CONV_RULE
      (Conv.REWR_CONV (Thm.CONJUNCT1 (Drule.SPEC_ALL boolTheory.IMP_CLAUSES))
       ORELSEC stateLib.MOVE_COND_CONV)
  val rule =
    PURE_REWRITE_RULE [set_sepTheory.SEP_CLAUSES] o
    Q.INST [`p1`|->`emp`, `p2`|->`emp`]
  val RISCV_PC_INTRO0 = rule RISCV_PC_INTRO
  val RISCV_TEMPORAL_PC_INTRO0 = rule RISCV_TEMPORAL_PC_INTRO
  fun MP_RISCV_PC_INTRO th =
     Lib.tryfind (fn thm => MATCH_MP thm th)
        [RISCV_PC_INTRO, RISCV_PC_INTRO0,
         RISCV_TEMPORAL_PC_INTRO, RISCV_TEMPORAL_PC_INTRO0]
  val cnv = REWRITE_CONV [alignmentTheory.aligned_numeric,
                          cond_branch_aligned]
  fun RISCV_PC_bump_intro th =
    let
      val c = riscv_c_PC_def |> SPEC_ALL |> concl |> lhs |> repeat rator
    in
      if not (can (find_term (fn x => aconv x c)) (th |> concl |> rand)) then
        th
      else
        th |> helperLib.HIDE_POST_RULE ``riscv_c_Skip id``
           |> Conv.CONV_RULE
               (helperLib.POST_CONV (helperLib.MOVE_OUT_CONV ``riscv_c_PC id``))
           |> Conv.CONV_RULE
               (helperLib.POST_CONV (helperLib.MOVE_OUT_CONV ``riscv_c_Skip id``))
           |> MP_RISCV_PC_INTRO
           |> Conv.CONV_RULE (Conv.LAND_CONV cnv)
           |> SPEC_IMP_RULE
    end
in
  fun riscv_introduction th =
    th |> PURE_REWRITE_RULE [aligned_1_intro]
       |> riscv_rename
       |> stateLib.introduce_triple_definition (true, riscv_progTheory.riscv_ID_def)
       |> helperLib.HIDE_PRE_RULE ``riscv_c_Skip id``
       |> stateLib.introduce_triple_definition
             (false, riscv_progTheory.riscv_ID_PC_def)
       |> RISCV_PC_bump_intro
       |> helperLib.MERGE_CONDS_RULE
       |> PURE_REWRITE_RULE [jal_aligned, jalr_aligned,
                             DECIDE ``a /\ (b ==> a) = a``,
                             DECIDE ``a /\ c /\ (b ==> a) = c /\ a``]
       |> spec_to_rv64
       |> memory_introduction
       |> helperLib.HIDE_POST_RULE ``riscv_RV64I``
       |> helperLib.HIDE_PRE_RULE ``riscv_RV64I``
end

local
  val component_11 = Drule.CONJUNCTS riscv_progTheory.riscv_component_11
  val riscv_rwts = List.drop (utilsLib.datatype_rewrites true "riscv"
                                ["riscv_state"], 1)
  val STATE_TAC = ASM_REWRITE_TAC riscv_rwts
  val EXTRA_TAC =
    TRY (
    Q.PAT_ASSUM `xxx /\ yyy`
      (fn th => SIMP_TAC std_ss [SIMP_RULE (std_ss++boolSimps.CONJ_ss) [] th])
      )
  fun eval_Skip thm =
    let
      val pat = riscvTheory.Skip_def |> SPEC_ALL |> concl |> lhs
      val tms = find_terms (can (match_term pat)) (concl thm)
      val Skip_conv = SIMP_CONV (srw_ss())
                       [riscvTheory.Skip_def,combinTheory.APPLY_UPDATE_THM]
    in REWRITE_RULE (map Skip_conv tms) thm end
  val pc_assum = ``¬word_bit 0 (s.c_PC s.procID)``
in
  val spec =
    stateLib.spec
      riscv_progTheory.RISCV_IMP_SPEC
      riscv_progTheory.RISCV_IMP_TEMPORAL
      [riscv_opcode_bytes, boolTheory.DE_MORGAN_THM]
      []
      (riscv_select_state_pool_thm :: riscv_select_state_thms)
      [riscv_frame, ricv_frame_hidden, state_id]
      component_11
      [dword, word5]
      EXTRA_TAC STATE_TAC
  val intro_spec = riscv_introduction o spec
  fun riscv_spec tm =
    let
       val thm = riscv_stepLib.riscv_step tm
       val thm = DISCH pc_assum thm |> UNDISCH
       val thm = eval_Skip thm
       val t = riscv_mk_pre_post thm
       val thm_ts = combinations (thm, t)
(*
       val x = hd thm_ts
       val th = spec x
       val res = riscv_introduction th
*)
    in
       List.map (fn x => (print "."; intro_spec x)) thm_ts
    end
end

fun tdistinct tl = HOLset.numItems (listset tl) = length tl

local
  fun check_unique_reg_CONV tm =
    let
      val p = progSyntax.strip_star (temporal_stateSyntax.dest_pre' tm)
      val rp = List.mapPartial (Lib.total reg_idx) p
    in
      if tdistinct rp
         then Conv.ALL_CONV tm
      else raise ERR "check_unique_reg_CONV" "duplicate register"
    end
  val PRE_CONV = Conv.RATOR_CONV o Conv.RATOR_CONV o Conv.RAND_CONV
  fun DEPTH_COND_CONV cnv =
    Conv.ONCE_DEPTH_CONV
      (fn tm =>
         if progSyntax.is_cond tm
           then Conv.RAND_CONV cnv tm
         else raise ERR "COND_CONV" "")
  val POST_CONV = Conv.RAND_CONV
  val POOL_CONV = Conv.RATOR_CONV o Conv.RAND_CONV
  fun LIST_CONV c tm =
    if listSyntax.is_nil tm then ALL_CONV tm else
      (RAND_CONV (LIST_CONV c) THENC RATOR_CONV (RAND_CONV c)) tm
  val OPC_CONV =
    POOL_CONV o Conv.RATOR_CONV o Conv.RAND_CONV o Conv.RAND_CONV o LIST_CONV
  exception FalseTerm
  fun NOT_F_CONV tm =
    if Feq tm then raise FalseTerm else Conv.ALL_CONV tm
  val WGROUND_RW_CONV =
    Conv.DEPTH_CONV (utilsLib.cache 10 Term.compare bitstringLib.v2w_n2w_CONV)
    THENC utilsLib.WGROUND_CONV
  val PRE_COND_CONV =
    helperLib.PRE_CONV
       (DEPTH_COND_CONV
          (WGROUND_RW_CONV
           THENC REWRITE_CONV []
           THENC NOT_F_CONV)
        THENC PURE_ONCE_REWRITE_CONV [stateTheory.cond_true_elim])
  val cnv =
    check_unique_reg_CONV
    THENC PRE_COND_CONV
    THENC PRE_CONV WGROUND_RW_CONV
    THENC OPC_CONV bitstringLib.v2w_n2w_CONV
    THENC POST_CONV WGROUND_RW_CONV
    THENC helperLib.POST_CONV (stateLib.PC_CONV "riscv_prog$riscv_PC")
in
  fun simp_triple_rule thm =
    riscv_rename (Conv.CONV_RULE cnv thm)
    handle FalseTerm => raise ERR "simp_triple_rule" "condition false"
end

local
  fun dest_v2w_list tm =
    listSyntax.dest_list tm
    |> fst |> map (fst o listSyntax.dest_list o rand)
    |> rev |> flatten |> (fn xs => listSyntax.mk_list(xs,type_of T))
  val get_opcode =
    dest_v2w_list o
    snd o pairSyntax.dest_pair o
    hd o pred_setSyntax.strip_set o
    temporal_stateSyntax.dest_code' o
    Thm.concl
  val spec_label_set = ref (Redblackset.empty String.compare)
  val init_net = utilsLib.mk_rw_net (fn _ => raise ERR "" "") []
  val spec_rwts = ref init_net
  val add1 = utilsLib.add_to_rw_net get_opcode
  val add_specs = List.app (fn thm => spec_rwts := add1 (thm, !spec_rwts))
  fun find_spec opc = Lib.total (utilsLib.find_rw (!spec_rwts)) opc
  val spec_spec_last_fail = ref (T,TRUTH)
  (*
  val (opc, thm) = !spec_spec_last_fail
  *)
  fun spec_spec opc thm =
    let
       val thm_opc = get_opcode thm
       val a = fst (Term.match_term thm_opc opc)
       val thm = Thm.INST a thm
    in
       simp_triple_rule thm
    end handle HOL_ERR e => (spec_spec_last_fail := (opc,thm); raise HOL_ERR e)
  fun err e s = raise ERR "riscv_spec_hex" (e ^ ": " ^ s)
  fun find_opc opc =
    List.filter (fn (_, p) => Lib.can (Term.match_term p) opc)
      riscv_stepLib.riscv_dict
  val split_branches = stateLib.split_cond true dest_riscv_PC
in
  fun riscv_config rv64 =
    ( set_to_rv64 rv64
    ; spec_label_set := Redblackset.empty String.compare
    ; spec_rwts := init_net
    )
(*
val (s,tm) = hd (find_opc opc)
*)
  fun addInstruction (s, tm) =
    if Redblackset.member (!spec_label_set, s)
      then false
    else ( print s
         ; add_specs (riscv_spec tm)
         ; spec_label_set := Redblackset.add (!spec_label_set, s)
         ; true)
  fun riscv_spec_hex () =
    fn s =>
      let
        val opc = riscv_stepLib.hex_to_padded_opcode s
        fun loop e =
          if (print "\n"; List.exists addInstruction (find_opc opc))
            then riscv_spec_hex () s
          else err e s
      in
        case find_spec opc of
           SOME thms =>
             (case List.mapPartial (Lib.total (spec_spec opc)) thms of
                 [] => loop "failed to find suitable spec"
               | [th] => split_branches th
               | _ => err "more than one spec" s)
         | NONE => loop "failed to add suitable spec"
      end
   val riscv_spec_hex = riscv_spec_hex ()
end

(* ------------------------------------------------------------------------ *)

(* Testing...

   [(2147580452, "c591", "beqz\ta1,ffffffff80017a30 <memzero+0xc>\r"),
    (2147580454, "00053023", "sd\tzero,0(a0)\r"),
    (2147580458, "15e1", "addi\ta1,a1,-8\r"),
    (2147580460, "0521", "addi\ta0,a0,8\r"),
    (2147580462, "fde5", "bnez\ta1,ffffffff80017a26 <memzero+0x2>\r"),
    (2147580464, "8082", "ret\r")]: (int * string * string) list

   [(2147580516, "ca19", "beqz\ta2,ffffffff80017a7a <memcpy+0x16>\r"),
    (2147580518, "962a", "add\ta2,a2,a0\r"),
    (2147580520, "87aa", "mv\ta5,a0\r"),
    (2147580522, "0005c703", "lbu\ta4,0(a1)\r"),
    (2147580526, "0785", "addi\ta5,a5,1\r"),
    (2147580528, "0585", "addi\ta1,a1,1\r"),
    (2147580530, "fee78fa3", "sb\ta4,-1(a5)\r"),
    (2147580534, "fec79ae3", "bne\ta5,a2,ffffffff80017a6a <memcpy+0x6>\r"),
    (2147580538, "8082", "ret\r")]: (int * string * string) list

val riscv_tools = riscv_decompLib.riscv_tools
val (riscv_spec,_,_,_) = riscv_tools

riscv_progLib.riscv_spec_hex s

val s = "fee78fa3"; riscv_spec_hex s;
val s = "0005c703"; riscv_spec_hex s;

val th = hd (riscv_spec_hex s)
memory_introduction th

val s = "410093"; riscv_spec_hex s;
val s = "21180B3"; riscv_spec_hex s;
val s = "108133"; riscv_spec_hex s;
val s = "800000EF"; riscv_spec_hex s;
val s = "943a"; riscv_spec_hex s;
val s = "072a"; riscv_spec_hex s;
val s = "e436"; riscv_spec_hex s;

riscv_spec_hex "410093"
riscv_spec_hex "21180B3"
riscv_spec_hex "108133"
riscv_spec_hex "FFF08093"
riscv_spec_hex "FE008EE3"

val s = "00053023"

val tm = bitstringSyntax.bitstring_of_hexstring s
val th = riscv_spec tm
val thm = riscv_stepLib.riscv_step tm

val s = "800000EF"
val tm = bitstringSyntax.bitstring_of_hexstring s

fun riscv_spec_from_hex s = let
  val tm = bitstringSyntax.bitstring_of_hexstring s
  in riscv_spec tm end

filter (not o can riscv_spec_from_hex) vs

(* currently failing: *)
val xs = ["e436", "fc06", "f822", "e82a", "e032"]

riscv_spec_hex s

open riscv_progLib

val imp_spec = RISCV_IMP_SPEC
val imp_temp = riscv_progTheory.RISCV_IMP_TEMPORAL
val read_thms = [riscv_opcode_bytes, boolTheory.DE_MORGAN_THM]: thm list
val write_thms = []: thm list
val select_state_thms = (riscv_select_state_pool_thm :: riscv_select_state_thms)
val frame_thms = [riscv_frame, ricv_frame_hidden, state_id]
val map_tys = [dword, word5]
val mk_pre_post = riscv_mk_pre_post
val write = riscv_write_footprint
val EXTRA_TAC = ALL_TAC

val () = riscv_config true
val () = riscv_config false
val () = stateLib.set_temporal true

local
   val gen = Random.newgenseed 1.0
   fun random_bit () =
      if Random.range (0, 2) gen = 0 then boolSyntax.T else boolSyntax.F
in
   fun random_hex tm =
      let
         val l = Term.free_vars tm
         val s = List.map (fn v => v |-> random_bit ()) l
      in
         bitstringSyntax.hexstring_of_term (Term.subst s tm)
      end
   fun hex s =
      riscv_spec_hex s
      handle e as HOL_ERR _ => (print ("\n\n" ^ s ^ "\n\n"); raise e)
end

val tst = Count.apply hex o random_hex

val d = List.filter (fn (s, _) => String.size s < 3 orelse
                                  not (String.substring (s, 0, 3) = "JAL"))
          riscv_stepLib.riscv_dict

val l = List.map (I ## tst) d

val SOME (_, tm) = Lib.assoc1 "ADD" riscv_stepLib.riscv_dict
val s = random_hex tm
val thms = tst tm


val tm = bitstringSyntax.bitstring_of_hexstring "8082"

*)

(* ------------------------------------------------------------------------ *)

end
