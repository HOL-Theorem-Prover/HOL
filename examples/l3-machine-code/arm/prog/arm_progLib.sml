structure arm_progLib :> arm_progLib =
struct

open HolKernel boolLib bossLib
open stateLib spec_databaseLib arm_progTheory

structure Parse =
struct
   open Parse
   val (Type, Term) = parse_from_grammars arm_progTheory.arm_prog_grammars
end

open Parse

val ERR = Feedback.mk_HOL_ERR "arm_progLib"

(* ------------------------------------------------------------------------ *)

val arm_proj_def = arm_progTheory.arm_proj_def
val arm_comp_defs = arm_progTheory.component_defs

local
   val pc = Term.prim_mk_const {Thy = "arm", Name = "RName_PC"}
in
   val step_1 = HolKernel.syntax_fns1 "arm_step"
   val arm_1 =
      HolKernel.syntax_fns
         {n = 2, dest = HolKernel.dest_monop, make = HolKernel.mk_monop}
         "arm_prog"
   val arm_2 =
      HolKernel.syntax_fns
         {n = 3, dest = HolKernel.dest_binop, make = HolKernel.mk_binop}
         "arm_prog"
   val word5 = wordsSyntax.mk_int_word_type 5
   val word = wordsSyntax.mk_int_word_type 32
   val dword = wordsSyntax.mk_int_word_type 64
   val (_, _, dest_arm_instr, _) = arm_1 "arm_instr"
   val (_, _, dest_arm_CPSR_E, _) = arm_1 "arm_CPSR_E"
   val (_, _, dest_arm_CONFIG, _) = arm_1 "arm_CONFIG"
   val (_, _, dest_arm_MEM, is_arm_MEM) = arm_2 "arm_MEM"
   val (_, mk_arm_REG, dest_arm_REG, is_arm_REG) = arm_2 "arm_REG"
   val (_, _, dest_arm_FP_REG, is_arm_FP_REG) = arm_2 "arm_FP_REG"
   val (_, _, dest_arm_Extensions, is_arm_Extensions) = arm_2 "arm_Extensions"
   val (_, mk_rev_e, _, _) = step_1 "reverse_endian"
   fun mk_arm_PC v = mk_arm_REG (pc, v)
end

(* -- *)

val arm_select_state_thms =
   List.map (fn t => stateLib.star_select_state_thm arm_proj_def [] ([], t))
            arm_comp_defs

val arm_select_state_pool_thm =
   pool_select_state_thm arm_proj_def []
      (utilsLib.SRW_CONV
         [pred_setTheory.INSERT_UNION_EQ, stateTheory.CODE_POOL, arm_instr_def]
         ``CODE_POOL arm_instr {(pc, opc)}``)

(* -- *)

val state_id =
   utilsLib.mk_state_id_thm armTheory.arm_state_component_equality
      [["REG", "undefined"],
       ["FP", "REG", "undefined"],
       ["CPSR", "CurrentCondition", "Encoding", "REG", "undefined"],
       ["CPSR", "CurrentCondition", "Encoding", "undefined"],
       ["MEM", "REG", "undefined"]
      ]

val fp_id =
   utilsLib.mk_state_id_thm armTheory.FP_component_equality
      [["REG"], ["FPSCR"]]

val arm_frame =
   stateLib.update_frame_state_thm arm_proj_def
     (List.map (fn s => "CPSR." ^ s)
         ["N", "Z", "C", "V", "Q", "A", "I", "F", "J", "T", "E", "M", "GE",
          "IT", "psr'rst"] @
      List.map (fn s => "FP.FPSCR." ^ s) ["N", "Z", "C", "V"] @
      ["REG", "MEM", "FP.REG"])

val arm_frame_hidden =
   stateLib.update_hidden_frame_state_thm arm_proj_def
      [``s with Encoding := x``,
       ``s with CurrentCondition := x``,
       ``s with undefined := x``]

(* -- *)

local
   val arm_instr_tm = Term.prim_mk_const {Thy = "arm_prog", Name = "arm_instr"}
   fun is_mem_access v tm =
      case Lib.total boolSyntax.dest_eq tm of
         SOME (l, r) =>
            stateLib.is_code_access ("arm$arm_state_MEM", v) l andalso
            (wordsSyntax.is_word_literal r orelse bitstringSyntax.is_v2w r)
       | NONE => false
   val dest_opc = fst o listSyntax.dest_list o fst o bitstringSyntax.dest_v2w
   val ty32 = fcpSyntax.mk_int_numeric_type 32
   fun list_mk_concat l =
      bitstringSyntax.mk_v2w
         (listSyntax.mk_list
            (List.concat (List.map dest_opc l), Type.bool), ty32)
in
   fun mk_arm_code_pool thm =
      let
         val r15 = stateLib.gvar "pc" word
         val r15_a = mk_arm_PC r15
         val (a, tm) = Thm.dest_thm thm
         val r15_subst = Term.subst [``s.REG RName_PC`` |-> r15]
         val a = List.map r15_subst a
         val (m, a) = List.partition (is_mem_access r15) a
         val m = List.map dest_code_access m
         val m = mlibUseful.sort_map fst Int.compare m
         val opc = list_mk_concat (List.map snd (List.rev m))
      in
         (r15_a,
          boolSyntax.rand (stateLib.mk_code_pool (arm_instr_tm, r15, opc)),
          list_mk_imp (a, r15_subst tm))
      end
end

local
   val pc_tm = Term.mk_var ("pc", word)
   fun is_big_end tm =
      case Lib.total dest_arm_CPSR_E tm of
         SOME t => t = boolSyntax.T
       | NONE => false
   fun is_pc_relative tm =
      case Lib.total dest_arm_MEM tm of
         SOME (t, _) => fst (utilsLib.strip_add_or_sub t) = pc_tm
       | NONE => false
   fun rwt (w, a) =
      [Drule.SPECL [a, w] arm_progTheory.MOVE_TO_TEMPORAL_ARM_CODE_POOL,
       Drule.SPECL [a, w] arm_progTheory.MOVE_TO_ARM_CODE_POOL]
   fun move_to_code wa =
      REWRITE_RULE
       ([stateTheory.BIGUNION_IMAGE_1, stateTheory.BIGUNION_IMAGE_2,
         set_sepTheory.STAR_ASSOC, set_sepTheory.SEP_CLAUSES,
         arm_progTheory.disjoint_arm_instr_thms, arm_stepTheory.concat_bytes] @
        List.concat (List.map rwt wa))
   val err = ERR "DISJOINT_CONV" ""
   val cnv =
      LAND_CONV wordsLib.WORD_EVAL_CONV
      THENC REWRITE_CONV [arm_progTheory.sub_intro]
   fun split_arm_instr tm =
      Lib.with_exn (pairSyntax.dest_pair o dest_arm_instr) tm err
   val byte_chunks = stateLib.group_into_chunks (dest_arm_MEM, 4, false)
   val rev_end_rule =
      PURE_REWRITE_RULE
        [arm_stepTheory.concat_bytes, arm_stepTheory.reverse_endian_bytes]
   fun rev_intro x =
      rev_end_rule o Thm.INST (List.map (fn (w, _: term) => w |-> mk_rev_e w) x)
in
   fun DISJOINT_CONV tm =
      let
         val (l, r) = Lib.with_exn pred_setSyntax.dest_disjoint tm err
         val (a, x) = split_arm_instr l
         val y = snd (split_arm_instr r)
         val a = case utilsLib.strip_add_or_sub a of
                    (_, [(false, w)]) => wordsSyntax.mk_word_2comp w
                  | (_, [(false, w), (true, x)]) =>
                      wordsSyntax.mk_word_add (wordsSyntax.mk_word_2comp w, x)
                  | _ => raise err
         val thm =
            Conv.CONV_RULE cnv
               (Drule.SPECL [a, pc_tm, x, y] arm_progTheory.DISJOINT_arm_instr)
      in
         if Thm.concl thm = tm
            then Drule.EQT_INTRO thm
         else raise err
      end
   fun extend_arm_code_pool thm =
      let
         val (p, q) = temporal_stateSyntax.dest_pre_post' (Thm.concl thm)
         val lp = progSyntax.strip_star p
      in
         if Lib.exists is_pc_relative lp
            then let
                    val be = Lib.exists is_big_end lp
                    val (s, wa) = byte_chunks lp
                 in
                    if List.null s
                       then thm
                    else let
                            val thm' =
                               move_to_code wa (Thm.INST (List.concat s) thm)
                         in
                            if be then rev_intro wa thm' else thm'
                         end
                 end
         else thm
      end
end

(* -- *)

fun reg_index tm =
   case Lib.total Term.dest_thy_const tm of
      SOME {Thy = "arm", Name = "RName_PC", ...} => 15
    | _ => Lib.with_exn (wordsSyntax.uint_of_word o Term.rand) tm
                        (ERR "reg_index" "")

local
   fun other_index tm =
      case fst (Term.dest_const (boolSyntax.rator tm)) of
         "cond" => 0
       | "arm_exception" => 1
       | "arm_CPSR_A" => 2
       | "arm_CPSR_I" => 3
       | "arm_CPSR_F" => 4
       | "arm_CPSR_psr'rst" => 5
       | "arm_CPSR_IT" => 6
       | "arm_CPSR_J" => 10
       | "arm_CPSR_E" => 11
       | "arm_CPSR_T" => 12
       | "arm_CPSR_M" => 13
       | "arm_CPSR_N" => 14
       | "arm_CPSR_Z" => 15
       | "arm_CPSR_C" => 16
       | "arm_CPSR_V" => 17
       | "arm_CPSR_Q" => 18
       | "arm_CPSR_GE" => 19
       | "arm_FP_FPSCR_N" => 20
       | "arm_FP_FPSCR_Z" => 21
       | "arm_FP_FPSCR_C" => 22
       | "arm_FP_FPSCR_V" => 23
       | _ => ~1
   val int_of_v2w = bitstringSyntax.int_of_term o fst o bitstringSyntax.dest_v2w
   val total_dest_lit = Lib.total wordsSyntax.dest_word_literal
   fun word_compare (w1, w2) =
      case (total_dest_lit w1, total_dest_lit w2) of
         (SOME x1, SOME x2) => Arbnum.compare (x1, x2)
       | (SOME _, NONE) => General.GREATER
       | (NONE, SOME _) => General.LESS
       | (NONE, NONE) => Term.compare (w1, w2)
   fun reg_compare (r1, r2) =
      case (r1, r2) of
         (mlibUseful.INL i, mlibUseful.INL j) => Int.compare (i, j)
       | (mlibUseful.INL _, mlibUseful.INR _) => General.GREATER
       | (mlibUseful.INR _, mlibUseful.INL _) => General.LESS
       | (mlibUseful.INR i, mlibUseful.INR j) => Term.compare (i, j)
   fun reg tm =
      case Lib.total reg_index tm of
         SOME i => mlibUseful.INL i
       | NONE => mlibUseful.INR tm
   val register = reg o fst o dest_arm_REG
   fun fp_reg tm =
      case Lib.total int_of_v2w tm of
         SOME i => mlibUseful.INL i
       | NONE => mlibUseful.INR tm
   val fp_register = fp_reg o fst o dest_arm_FP_REG
   val address = HolKernel.strip_binop (Lib.total wordsSyntax.dest_word_add) o
                 fst o dest_arm_MEM
in
   fun psort p =
      let
         val (m, rst) = List.partition is_arm_MEM p
         val (r, rst) = List.partition is_arm_REG rst
         val (c, rst) = List.partition is_arm_FP_REG rst
         val (e, rst) = List.partition is_arm_Extensions rst
      in
         mlibUseful.sort_map other_index Int.compare rst @
         mlibUseful.sort_map (fst o dest_arm_Extensions) Term.compare e @
         mlibUseful.sort_map register reg_compare r @
         mlibUseful.sort_map fp_register reg_compare c @
         mlibUseful.sort_map address (mlibUseful.lex_list_order word_compare) m
      end
end

local
   val st = Term.mk_var ("s", ``:arm_state``)
   val cpsr_footprint =
      stateLib.write_footprint arm_1 arm_2 []
        [("arm$PSR_N_fupd", "arm_CPSR_N"),
         ("arm$PSR_Z_fupd", "arm_CPSR_Z"),
         ("arm$PSR_C_fupd", "arm_CPSR_C"),
         ("arm$PSR_V_fupd", "arm_CPSR_V"),
         ("arm$PSR_Q_fupd", "arm_CPSR_Q"),
         ("arm$PSR_J_fupd", "arm_CPSR_J"),
         ("arm$PSR_T_fupd", "arm_CPSR_T"),
         ("arm$PSR_E_fupd", "arm_CPSR_E"),
         ("arm$PSR_A_fupd", "arm_CPSR_A"),
         ("arm$PSR_I_fupd", "arm_CPSR_I"),
         ("arm$PSR_F_fupd", "arm_CPSR_F"),
         ("arm$PSR_M_fupd", "arm_CPSR_M"),
         ("arm$PSR_IT_fupd", "arm_CPSR_IT"),
         ("arm$PSR_GE_fupd", "arm_CPSR_GE"),
         ("arm$PSR_psr'rst_fupd", "arm_CPSR_psr'rst")
         ] [] []
        (fn (s, l) => s = "arm$arm_state_CPSR" andalso l = [st])
   val fpscr_footprint =
      stateLib.write_footprint arm_1 arm_2 []
        [("arm$FPSCR_N_fupd", "arm_FP_FPSCR_N"),
         ("arm$FPSCR_Z_fupd", "arm_FP_FPSCR_Z"),
         ("arm$FPSCR_C_fupd", "arm_FP_FPSCR_C"),
         ("arm$FPSCR_V_fupd", "arm_FP_FPSCR_V")] [] []
        (fn _ => true)
   val fp_footprint =
      stateLib.write_footprint arm_1 arm_2
        [("arm$FP_REG_fupd", "arm_FP_REG", ``^st.FP.REG``)] [] []
        [("arm$FP_FPSCR_fupd", fpscr_footprint)]
        (fn (s, l) => s = "arm$arm_state_FP" andalso l = [st])
in
   val arm_write_footprint =
      stateLib.write_footprint arm_1 arm_2
        [("arm$arm_state_MEM_fupd", "arm_MEM", ``^st.MEM``),
         ("arm$arm_state_REG_fupd", "arm_REG", ``^st.REG``)]
        [] []
        [("arm$arm_state_FP_fupd", fp_footprint),
         ("arm$arm_state_CPSR_fupd", cpsr_footprint),
         ("arm$arm_state_Encoding_fupd", fn (p, q, _) => (p, q)),
         ("arm$arm_state_undefined_fupd", fn (p, q, _) => (p, q)),
         ("arm$arm_state_CurrentCondition_fupd", fn (p, q, _) => (p, q))]
        (K false)
end

val arm_mk_pre_post =
   stateLib.mk_pre_post
      arm_progTheory.ARM_MODEL_def arm_comp_defs mk_arm_code_pool []
      arm_write_footprint psort

(* ------------------------------------------------------------------------ *)

val REG_CONV =
   Conv.QCONV
     (REWRITE_CONV
        [EVAL ``R_mode mode 15w``,
         arm_stepTheory.v2w_ground4, arm_stepTheory.v2w_ground5])

val REG_RULE = Conv.CONV_RULE REG_CONV o utilsLib.ALL_HYP_CONV_RULE REG_CONV

local
   val dest_reg = dest_arm_REG
   val reg_width = 4
   val proj_reg = SOME reg_index
   val reg_conv = REG_CONV
   val ok_conv = ALL_CONV
   val r15 = wordsSyntax.mk_wordii (15, 4)
   fun asm tm = Thm.ASSUME (boolSyntax.mk_neg (boolSyntax.mk_eq (tm, r15)))
   val model_tm = ``ARM_MODEL``
in
   val reg_combinations =
      stateLib.register_combinations
         (dest_reg, reg_width, proj_reg, reg_conv, ok_conv, asm, model_tm)
end

local
   val dest_reg = dest_arm_FP_REG
   val reg_width = 5
   val proj_reg = NONE
   val reg_conv = REG_CONV
   val ok_conv = ALL_CONV
   fun asm (tm: term) = (raise ERR "" ""): thm
   val model_tm = ``ARM_MODEL``
in
   val fp_combinations =
      stateLib.register_combinations
         (dest_reg, reg_width, proj_reg, reg_conv, ok_conv, asm, model_tm)
end

fun combinations thm_t =
   case fp_combinations thm_t of
      [_] => reg_combinations thm_t
    | l => l

(* ------------------------------------------------------------------------ *)

local
   val arm_rename1 =
      Lib.total
        (fn "arm_prog$arm_CPSR_N" => "n"
          | "arm_prog$arm_CPSR_Z" => "z"
          | "arm_prog$arm_CPSR_C" => "c"
          | "arm_prog$arm_CPSR_V" => "v"
          | "arm_prog$arm_CPSR_Q" => "q"
          | "arm_prog$arm_CPSR_A" => "a"
          | "arm_prog$arm_CPSR_F" => "f"
          | "arm_prog$arm_CPSR_I" => "i"
          | "arm_prog$arm_CPSR_GE" => "ge"
          | "arm_prog$arm_CPSR_IT" => "it"
          | "arm_prog$arm_CPSR_M" => "mode"
          | "arm_prog$arm_CPSR_psr'rst" => "psr_other"
          | "arm_prog$arm_FP_FPSCR_N" => "fp_n"
          | "arm_prog$arm_FP_FPSCR_Z" => "fp_z"
          | "arm_prog$arm_FP_FPSCR_C" => "fp_c"
          | "arm_prog$arm_FP_FPSCR_V" => "fp_v"
          | "arm_prog$arm_FP_FPSCR_RMode" => "rmode"
          | "arm_prog$arm_CP15" => "cp15"
          | _ => fail())
   val arm_rename2 =
      Lib.total
        (fn "arm_prog$arm_FP_REG" =>
              Lib.curry (op ^) "d" o Int.toString o wordsSyntax.uint_of_word
          | "arm_prog$arm_REG" =>
              Lib.curry (op ^) "r" o Int.toString o reg_index
          | "arm_prog$arm_MEM" => K "b"
          | _ => fail())
in
   val arm_rename = stateLib.rename_vars (arm_rename1, arm_rename2, ["b"])
end

local
   val arm_CPSR_T_F = List.map UNDISCH (CONJUNCTS arm_progTheory.arm_CPSR_T_F)
   val MOVE_COND_RULE = Conv.CONV_RULE stateLib.MOVE_COND_CONV
   val SPEC_IMP_RULE =
      Conv.CONV_RULE
        (Conv.REWR_CONV (Thm.CONJUNCT1 (Drule.SPEC_ALL boolTheory.IMP_CLAUSES))
         ORELSEC MOVE_COND_CONV)
   fun TRY_DISCH_RULE thm =
      case List.length (Thm.hyp thm) of
         0 => thm
       | 1 => MOVE_COND_RULE (Drule.DISCH_ALL thm)
       | _ => thm |> Drule.DISCH_ALL
                  |> PURE_REWRITE_RULE [boolTheory.AND_IMP_INTRO]
                  |> MOVE_COND_RULE
   val flag_introduction =
      helperLib.MERGE_CONDS_RULE o TRY_DISCH_RULE o
      PURE_REWRITE_RULE arm_CPSR_T_F
   val addr_eq_conv =
      SIMP_CONV (bool_ss++wordsLib.WORD_ARITH_ss++wordsLib.WORD_ARITH_EQ_ss) []
   val reg_eq_conv = PURE_REWRITE_CONV [arm_stepTheory.R_mode_11]
                     THENC Conv.DEPTH_CONV wordsLib.word_EQ_CONV
                     THENC REWRITE_CONV []
   val arm_PC_INTRO0 =
      arm_PC_INTRO |> Q.INST [`p1`|->`emp`, `p2`|->`emp`]
                   |> PURE_REWRITE_RULE [set_sepTheory.SEP_CLAUSES]
   val arm_TEMPORAL_PC_INTRO0 =
      arm_TEMPORAL_PC_INTRO |> Q.INST [`p1`|->`emp`, `p2`|->`emp`]
                            |> PURE_REWRITE_RULE [set_sepTheory.SEP_CLAUSES]
   fun MP_arm_PC_INTRO th =
      Lib.tryfind (fn thm => MATCH_MP thm th)
         [arm_PC_INTRO, arm_TEMPORAL_PC_INTRO,
          arm_PC_INTRO0, arm_TEMPORAL_PC_INTRO0]
   val cnv = REWRITE_CONV [alignmentTheory.aligned_numeric,
                           arm_progTheory.Aligned_Branch]
   val arm_PC_bump_intro =
      SPEC_IMP_RULE o
      Conv.CONV_RULE (Conv.LAND_CONV cnv) o
      MP_arm_PC_INTRO o
      Conv.CONV_RULE
         (helperLib.POST_CONV (helperLib.MOVE_OUT_CONV ``arm_REG RName_PC``))
   fun is_big_end tm =
      case Lib.total (pairSyntax.strip_pair o dest_arm_CONFIG) tm of
         SOME [_, _, t, _, _] => t = boolSyntax.T
       | _ => false
   val le_word_memory_introduction =
      stateLib.introduce_map_definition
         (arm_progTheory.arm_WORD_MEMORY_INSERT, addr_eq_conv) o
      stateLib.chunks_intro false arm_progTheory.arm_WORD_def
   val be_word_memory_introduction =
      stateLib.introduce_map_definition
         (arm_progTheory.arm_BE_WORD_MEMORY_INSERT, addr_eq_conv) o
      stateLib.chunks_intro true arm_progTheory.arm_BE_WORD_def
   val le_sep_array_introduction =
      stateLib.sep_array_intro
         false arm_progTheory.arm_WORD_def [arm_stepTheory.concat_bytes]
   val be_sep_array_introduction =
      stateLib.sep_array_intro
         true arm_progTheory.arm_BE_WORD_def [arm_stepTheory.concat_bytes]
   val concat_bytes_rule =
      Conv.CONV_RULE
         (helperLib.POST_CONV (PURE_REWRITE_CONV [arm_stepTheory.concat_bytes]))
in
   val memory_introduction =
      stateLib.introduce_map_definition
         (arm_progTheory.arm_MEMORY_INSERT, addr_eq_conv)
   val fp_introduction =
      concat_bytes_rule o
      stateLib.introduce_map_definition
         (arm_progTheory.arm_FP_REGISTERS_INSERT, Conv.ALL_CONV)
   val gp_introduction =
      concat_bytes_rule o
      stateLib.introduce_map_definition
         (arm_progTheory.arm_REGISTERS_INSERT, reg_eq_conv)
   val sep_array_introduction =
      stateLib.pick_endian_rule
        (is_big_end, be_sep_array_introduction, le_sep_array_introduction)
   val word_memory_introduction =
      Conv.CONV_RULE
         (stateLib.PRE_COND_CONV
            (SIMP_CONV (bool_ss++boolSimps.CONJ_ss)
                [alignmentTheory.aligned_numeric])) o
      concat_bytes_rule o
      stateLib.pick_endian_rule
        (is_big_end, be_word_memory_introduction, le_word_memory_introduction)
   val arm_intro =
      flag_introduction o
      arm_PC_bump_intro o
      stateLib.introduce_triple_definition (false, arm_PC_def) o
      stateLib.introduce_triple_definition (true, arm_CONFIG_def) o
      extend_arm_code_pool o
      arm_rename
end

local
   fun is_mode tm =
      case Lib.total wordsSyntax.dest_word_extract tm of
         SOME (_, _, _, ty) => ty = fcpSyntax.mk_int_numeric_type 5
       | NONE => false
   val config0 = GSYM (SPEC_ALL arm_CONFIG_def)
   val mode0 = ``mode: word5``
   val (_, mk_goodmode, _, _) = step_1 "GoodMode"
in
   fun change_config_rule thm =
      let
         val mode = HolKernel.find_term is_mode (Thm.concl thm)
         val config = Thm.INST [mode0 |-> mode] config0
      in
        thm
        |> stateLib.MOVE_COND_RULE (mk_goodmode mode)
        |> MATCH_MP progTheory.SPEC_DUPLICATE_COND
        |> CONV_RULE (RAND_CONV (helperLib.STAR_REWRITE_CONV config))
      end
end

local
   val RName_PC_tm = Term.prim_mk_const {Thy = "arm", Name = "RName_PC"}
   fun spec_rewrites thm tms = List.map (REWRITE_CONV [thm]) tms
   val spec_rwts =
      spec_rewrites armTheory.Extend_def
         [``Extend (T, w:'a word): 'b word``,
          ``Extend (F, w:'a word): 'b word``] @
      spec_rewrites arm_stepTheory.UpdateSingleOfDouble_def
         [``UpdateSingleOfDouble T v w``,
          ``UpdateSingleOfDouble F v w``] @
      spec_rewrites arm_stepTheory.SingleOfDouble_def
         [``SingleOfDouble T w``,
          ``SingleOfDouble F w``]
   fun check_unique_reg_CONV tm =
      let
         val p = progSyntax.strip_star (temporal_stateSyntax.dest_pre' tm)
         val rp = List.mapPartial (Lib.total (fst o dest_arm_REG)) p
         val dp = List.mapPartial (Lib.total (fst o dest_arm_FP_REG)) p
      in
         if not (Lib.mem RName_PC_tm rp) andalso
            Lib.mk_set rp = rp andalso Lib.mk_set dp = dp
            then Conv.ALL_CONV tm
         else raise ERR "check_unique_reg_CONV" "duplicate register"
      end
   exception FalseTerm
   fun NOT_F_CONV tm =
      if tm = boolSyntax.F then raise FalseTerm else Conv.ALL_CONV tm
   val WGROUND_RW_CONV =
      Conv.DEPTH_CONV (utilsLib.cache 10 Term.compare bitstringLib.v2w_n2w_CONV)
      THENC utilsLib.WALPHA_CONV
      THENC utilsLib.WGROUND_CONV
      THENC utilsLib.WALPHA_CONV
   val cnv =
      REG_CONV
      THENC check_unique_reg_CONV
      THENC WGROUND_RW_CONV
      THENC stateLib.PRE_COND_CONV
               (DEPTH_CONV DISJOINT_CONV
                THENC REWRITE_CONV [alignmentTheory.aligned_numeric]
                THENC numLib.REDUCE_CONV
                THENC NOT_F_CONV)
      THENC helperLib.POST_CONV
              (PURE_REWRITE_CONV spec_rwts
               THENC stateLib.PC_CONV "arm_prog$arm_PC")
in
   fun simp_triple_rule thm =
      arm_rename (Conv.CONV_RULE cnv thm)
      handle FalseTerm => raise ERR "simp_triple_rule" "condition false"
end

local
   val v3 = Term.mk_var ("x3", Type.bool)
   val v4 = Term.mk_var ("x4", Type.bool)
   val v5 = Term.mk_var ("x5", Type.bool)
   val v6 = Term.mk_var ("x6", Type.bool)
   val vn = listSyntax.mk_list ([v3, v4, v5, v6], Type.bool)
   val vn = bitstringSyntax.mk_v2w (vn, fcpSyntax.mk_int_numeric_type 4)
in
   val get_stm_base =
      Arbnum.toInt o fst o
      mlibUseful.min Arbnum.compare o
      List.map Arbnum.fromString o
      String.tokens (Lib.equal #",") o snd o
      utilsLib.splitAtChar (Char.isDigit)
   fun stm_wb_thms base thm =
      let
        val (x3, x4, x5, x6) =
           utilsLib.padLeft false 4 (bitstringSyntax.int_to_bitlist base)
           |> List.map bitstringSyntax.mk_b
           |> Lib.quadruple_of_list
      in
         [REG_RULE (Thm.INST [v3 |-> x3, v4 |-> x4, v5 |-> x5, v6 |-> x6] thm),
          Drule.ADD_ASSUM
            (boolSyntax.mk_neg
                (boolSyntax.mk_eq (vn, wordsSyntax.mk_wordii (base, 4)))) thm]
      end
end

datatype memory = Flat | Array | Map | Map32
type opt = {gpr_map: bool, fpr_map: bool, mem: memory, temporal: bool}

local
   val gpr_map_options =
      [["map-gpr", "gpr-map", "reg-map", "map-reg"],
       ["no-gpr-map", "no-map-gpr"]]
   val fpr_map_options =
      [["map-fpr", "fpr-map"],
       ["no-fpr-map", "no-map-fpr"]]
   val mem_options =
      [["map-mem", "mem-map", "mapped"],
       ["map-mem32", "mem-map32", "mapped32"],
       ["array-mem", "mem-array", "array"],
       ["flat-map", "mem-flat", "flat"]]
   val temporal_options =
      [["temporal"],
       ["not-temporal"]]
   fun isDelim c = Char.isPunct c andalso c <> #"-" orelse Char.isSpace c
   val memopt =
      fn 0 => Map
       | 1 => Map32
       | 2 => Array
       | 3 => Flat
       | _ => raise ERR "process_rule_options" ""
in
   fun basic_opt () =
      {gpr_map = false, fpr_map = false, mem = Flat,
       temporal = stateLib.generate_temporal()}: opt
   val default_opt =
      {gpr_map = false, fpr_map = false, mem = Map, temporal = false}: opt
   fun proj_opt ({gpr_map, fpr_map, mem, ...}: opt) = (gpr_map, fpr_map, mem)
   fun closeness (target: opt) (opt: opt)  =
      (case (#gpr_map opt, #gpr_map target) of
          (false, true) => 0
        | (true, false) => ~100
        | (_, _) => 1) +
      (case (#fpr_map opt, #fpr_map target) of
          (false, true) => 0
        | (true, false) => ~100
        | (_, _) => 1) +
      (case (#mem opt, #mem target) of
          (Flat, _) => 0
        | (_, Flat) => ~100
        | (m1, m2) => if m1 = m2 then 1 else ~10)
   fun convert_opt_rule (opt: opt) (target: opt) =
      (if #gpr_map target andalso not (#gpr_map opt)
          then gp_introduction
       else Lib.I) o
      (if #fpr_map target andalso not (#fpr_map opt)
          then fp_introduction
       else Lib.I) o
      (if #mem target = #mem opt
         then Lib.I
       else case #mem target of
               Flat => Lib.I
             | Array => sep_array_introduction
             | Map => memory_introduction
             | Map32 => word_memory_introduction
             )
   fun process_rule_options s =
      let
         val l = String.tokens isDelim s
         val l = List.map utilsLib.lowercase l
         val (fpr_map, l) =
            utilsLib.process_opt fpr_map_options "Introduce FPR map"
               (#fpr_map default_opt) l (Lib.equal 0)
         val (gpr_map, l) =
            utilsLib.process_opt gpr_map_options "Introduce GPR map"
               (#gpr_map default_opt) l (Lib.equal 0)
         val (mem, l) =
            utilsLib.process_opt mem_options "MEM type"
               (#mem default_opt) l memopt
         val (temporal, l) =
            utilsLib.process_opt temporal_options "Temoporal triple"
               (#temporal default_opt) l (Lib.equal 0)
      in
         if List.null l
            then {gpr_map = gpr_map,
                  fpr_map = fpr_map,
                  mem = mem,
                  temporal = temporal}: opt
         else raise ERR "process_options"
                    ("Unrecognized option" ^
                     (if List.length l > 1 then "s" else "") ^
                     ": " ^ String.concat (commafy l))
      end
end

local
   fun thm_eq thm1 thm2 = Term.aconv (Thm.concl thm1) (Thm.concl thm2)
   val mk_thm_set = Lib.op_mk_set thm_eq
   val component_11 =
      case Drule.CONJUNCTS arm_progTheory.arm_component_11 of
         [r, m, _, fp] => [r, m, fp]
       | _ => raise ERR "component_11" ""
   val sym_R_x_pc =
      REWRITE_RULE [utilsLib.qm [] ``(a = RName_PC) = (RName_PC = a)``]
         arm_stepTheory.R_x_pc
   val EXTRA_TAC =
      RULE_ASSUM_TAC (REWRITE_RULE [sym_R_x_pc, arm_stepTheory.R_x_pc])
      THEN ASM_REWRITE_TAC [boolTheory.DE_MORGAN_THM]
   val arm_rwts = tl (utilsLib.datatype_rewrites true "arm"
                        ["arm_state", "PSR", "FP", "FPSCR"])
   val STATE_TAC = ASM_REWRITE_TAC arm_rwts
   val basic_spec =
      stateLib.spec
           arm_progTheory.ARM_IMP_SPEC arm_progTheory.ARM_IMP_TEMPORAL
           [arm_stepTheory.get_bytes]
           []
           (arm_select_state_pool_thm :: arm_select_state_thms)
           [arm_frame, arm_frame_hidden, state_id, fp_id]
           component_11
           [word, word5, ``:RName``]
           EXTRA_TAC STATE_TAC
   fun is_stm_wb s =
      let
         val s' =
            utilsLib.lowercase (fst (utilsLib.splitAtChar (Lib.equal #";") s))
      in
         String.isPrefix "stm" s' andalso String.isSuffix "(wb)" s' andalso
         List.exists
            (fn p => String.isPrefix p (String.extract (s', 3, NONE)))
            ["ia", "ib", "da", "db"]
      end
   val get_opcode =
      fst o bitstringSyntax.dest_v2w o
      snd o pairSyntax.dest_pair o
      List.last o pred_setSyntax.strip_set o
      temporal_stateSyntax.dest_code' o
      Thm.concl
   val rev_endian = ref (Lib.I : term list -> term list)
   val is_be_tm = Term.aconv ``s.CPSR.E``
   fun set_endian opt =
      let
         val l = arm_configLib.mk_config_terms opt
      in
         if List.exists is_be_tm l
            then rev_endian := utilsLib.rev_endian
         else rev_endian := Lib.I
      end
   val (reset_db, set_current_opt, get_current_opt, add1_pending, find_spec,
        list_db) =
      spec_databaseLib.mk_spec_database basic_opt default_opt proj_opt
         closeness convert_opt_rule get_opcode (arm_intro o basic_spec)
   val current_config = ref "vfp"
   val newline = ref "\n"
   val the_step = ref (arm_stepLib.arm_step (!current_config))
   val spec_label_set = ref (Redblackset.empty String.compare)
   fun reset_specs () =
      (reset_db (); spec_label_set := Redblackset.empty String.compare)
   fun configure config options =
      let
         val opt = process_rule_options options
      in
         if arm_configLib.mk_config_terms (!current_config) =
            arm_configLib.mk_config_terms config andalso
            #temporal (get_current_opt ()) = #temporal opt
            then ()
         else ( reset_specs ()
              ; set_endian config
              ; the_step := arm_stepLib.arm_step config
              )
         ; stateLib.set_temporal (#temporal opt)
         ; current_config := config
         ; set_current_opt opt
      end
   fun arm_spec_opt config opt =
      let
         val () = configure config opt
         val step = !the_step
      in
         fn s =>
            if is_stm_wb s
               then let
                       val l = step s
                       val l = stm_wb_thms (get_stm_base s) (hd l) @ tl l
                       val thms_ts = List.map (fn t => (t, arm_mk_pre_post t)) l
                    in
                       List.app (fn x => (print "."; add1_pending x)) thms_ts
                       ; thms_ts
                    end
            else let
                    val thms = step s
                    val ts = List.map arm_mk_pre_post thms
                    val thms_ts = (thms, ts) |> ListPair.zip
                                             |> List.map combinations
                                             |> List.concat
                 in
                    List.app (fn x => (print "."; add1_pending x)) thms_ts
                    ; thms_ts
                 end
      end
   val the_spec = ref (arm_spec_opt (!current_config) "")
   fun spec_spec opc thm =
      let
         val thm_opc = get_opcode thm
         val a = fst (Term.match_term thm_opc opc)
      in
         simp_triple_rule (Thm.INST a thm)
      end
in
   val list_db = list_db
   fun set_newline s = newline := s
   fun arm_config config opt = the_spec := arm_spec_opt config opt
   fun arm_spec s =
      List.map (fn t => (print "+"; basic_spec t)) ((!the_spec) s) before
      print (!newline)
   fun addInstructionClass s =
      ( print (" " ^ s)
      ; if Redblackset.member (!spec_label_set, s)
           then ()
        else ( (!the_spec) s
             ; spec_label_set := Redblackset.add (!spec_label_set, s)
             )
      )
   fun arm_spec_hex looped s =
      let
         val i = arm_stepLib.hex_to_bits_32 s
         val opc = listSyntax.mk_list (!rev_endian i, Type.bool)
      in
         case find_spec opc of
            SOME (new, thms) =>
              let
                 val l = List.mapPartial (Lib.total (spec_spec opc)) thms
              in
                 if List.null l
                    then loop looped i "failed to find suitable spec" s
                 else (if new then print (!newline) else (); mk_thm_set l)
              end
          | NONE => loop looped i "failed to add suitable spec" s
      end
   and loop looped i e s =
      if looped
         then raise ERR "arm_spec_hex" (e ^ ": " ^ s)
      else ( List.app addInstructionClass (arm_stepLib.arm_instruction i)
           ; arm_spec_hex true s)
   val arm_spec_hex = arm_spec_hex false
   val arm_spec_code =
      List.map arm_spec_hex o
      (armAssemblerLib.arm_code: string quotation -> string list)
end

(* ------------------------------------------------------------------------ *)

(* Testing...

val () = arm_config "vfp" "flat"
val () = arm_config "vfp" "array"
val () = arm_config "vfp" "mapped"
val () = arm_config "vfp" "mapped32"

val () = arm_config "vfp" "map-fpr,flat"
val () = arm_config "vfp" "map-fpr,array"
val () = arm_config "vfp" "map-fpr,mapped"
val () = arm_config "vfp" "map-fpr,mapped32"

val () = arm_config "vfp" "map-reg,flat"
val () = arm_config "vfp" "map-reg,array"
val () = arm_config "vfp" "map-reg,mapped"
val () = arm_config "vfp" "map-reg,mapped32"

val () = arm_config "vfp,be" "flat"
val () = arm_config "vfp,be" "array"
val () = arm_config "vfp,be" "mapped"
val () = arm_config "vfp,be" "mapped32"

val () = arm_config "vfp,be" "map-reg,flat"
val () = arm_config "vfp,be" "map-reg,array"
val () = arm_config "vfp,be" "map-reg,mapped"
val () = arm_config "vfp,be" "map-reg,mapped32"

val () = arm_config "vfp" "flat,temporal"
val () = arm_config "vfp" "array,temporal"
val () = arm_config "vfp" "mapped,temporal"
val () = arm_config "vfp" "mapped32,temporal"

val () = arm_config "vfp" "map-reg,flat,temporal"
val () = arm_config "vfp" "map-reg,array,temporal"
val () = arm_config "vfp" "map-reg,mapped,temporal"
val () = arm_config "vfp" "map-reg,mapped32,temporal"

val () = arm_config "vfp,be" "flat,temporal"
val () = arm_config "vfp,be" "array,temporal"
val () = arm_config "vfp,be" "mapped,temporal"
val () = arm_config "vfp,be" "mapped32,temporal"

val () = arm_config "vfp,be" "map-reg,flat,temporal"
val () = arm_config "vfp,be" "map-reg,array,temporal"
val () = arm_config "vfp,be" "map-reg,mapped,temporal"
val () = arm_config "vfp,be" "map-reg,mapped32,temporal"

val thm = arm_intro (last (arm_spec "STMIA;3,2,1"))
  arm_spec_hex "E881000E"; (* STMIA;3,2,1 *)
  arm_spec_hex "E891000E"; (* LDMIA;3,2,1 *)

val arm_spec = Count.apply arm_spec
val arm_spec_hex = Count.apply arm_spec_hex
val arm_spec_code = Count.apply arm_spec_code

set_trace "stateLib.spec" 1

  arm_spec_code `mrs r1, cpsr`
  arm_spec_code `msr cpsr, r1` (* forces user mode *)
  arm_spec_code `msr cpsr_f, r1`
  arm_spec_code `msr cpsr_x, #0x0000ff00`
  arm_spec_code `msr cpsr_s, #0x00ff0000`
  arm_spec_code `msr cpsr_f, #0xf0000000`

  (* The following RFE instructions change the operating mode.
     As such, arm_CONFIG is not automatically introduced in the post-condition.
     This is achieved with some post-processing.
  *)

  val f = List.map (List.map change_config_rule)

  (f o arm_spec_code) `rfeia r1!`
  (f o arm_spec_code) `rfeia r1`

  (*

  val thm = arm_spec_code `rfeia r1` |> hd |> hd

  *)

  arm_spec_hex "E79F2003"  (* ldr r2, [pc, r3] *)
  arm_spec_hex "E18F20D4"  (* ldrd r2, r3, [pc, r4] *)
  arm_spec_hex "E51F2018"  (* ldr r2, [pc, #-24] *)
  arm_spec_hex "E14F21D8"  (* ldrd r2, r3, [pc, #-24] *)

  arm_spec_hex "E59F100C"
  Count.apply arm_spec_hex "E1CF00DC"

  arm_spec "VLDR (single,+imm,pc)"
  arm_spec "VLDR (double,+imm,pc)"
  arm_spec "VLDR (single,-imm,pc)"
  arm_spec "VLDR (double,-imm,pc)"
  arm_spec "LDR (+lit)"
  arm_spec "LDR (-lit)"
  arm_spec "LDR (+reg,pre,pc)"
  arm_spec "LDR (-reg,pre,pc)"
  arm_spec "LDRD (+lit)"
  arm_spec "LDRD (-lit)"
  arm_spec "LDRD (+reg,pre,pc)"
  arm_spec "LDRD (-reg,pre,pc)"

  arm_spec "VMOV (single,reg)";
  arm_spec "VMOV (double,reg)";
  arm_spec "VMOV (single,imm)";
  arm_spec "VMOV (double,imm)";
  arm_spec "VMRS (nzcv)";
  arm_spec "VMRS";
  arm_spec "VCMP (single,zero)";
  arm_spec "VCMP (double,zero)";
  arm_spec "VCMP (single)";
  arm_spec "VCMP (double)";

  arm_spec "VADD (single)";
  arm_spec "VSUB (single)";
  arm_spec "VMUL (single)";
  arm_spec "VMLA (single)";
  arm_spec "VMLS (single)";
  arm_spec "VNMUL (single)";
  arm_spec "VNMLA (single)";
  arm_spec "VNMLS (single)";
  arm_spec "VLDR (single,+imm)";
  arm_spec "VLDR (single,-imm)";
  arm_spec "VLDR (single,+imm,pc)";
  arm_spec "VLDR (single,-imm,pc)";
  arm_spec "VSTR (single,+imm)";
  arm_spec "VSTR (single,-imm)";
  arm_spec "VSTR (single,+imm,pc)";
  arm_spec "VSTR (single,-imm,pc)"

  arm_spec "VADD (double)";
  arm_spec "VSUB (double)";
  arm_spec "VMUL (double)";
  arm_spec "VMLA (double)";
  arm_spec "VMLS (double)";
  arm_spec "VNMUL (double)";
  arm_spec "VNMLA (double)";
  arm_spec "VNMLS (double)";
  arm_spec "VLDR (double,+imm)";
  arm_spec "VLDR (double,-imm)";
  arm_spec "VLDR (double,+imm,pc)";
  arm_spec "VLDR (double,-imm,pc)";
  arm_spec "VSTR (double,+imm)";
  arm_spec "VSTR (double,-imm)";
  arm_spec "VSTR (double,+imm,pc)";
  arm_spec "VSTR (double,-imm,pc)"

  arm_spec_hex "ed907a00"; (* vldr *)
  arm_spec_hex "edd16a00"; (* vldr *)
  arm_spec_hex "ee676a26"; (* vmul *)
  arm_spec_hex "edd15a00"; (* vldr *)
  arm_spec_hex "ed936a00"; (* vldr *)
  arm_spec_hex "ed925a00"; (* vldr *)
  arm_spec_hex "edd17a01"; (* vldr *)
  arm_spec_hex "ed817a00"; (* vstr *)
  arm_spec_hex "ee775a65"; (* vsub *)
  arm_spec_hex "ee477a05"; (* vmla *)
  arm_spec_hex "ee456a86"; (* vmla *)
  arm_spec_hex "edc17a01"; (* vstr *)
  arm_spec_hex "ee767aa7"; (* vadd *)
  arm_spec_hex "edc37a00"; (* vstr *)

  arm_spec_hex "F1010200"; (* SETEND *)
  arm_spec_hex "EA000001"; (* B + *)
  arm_spec_hex "EAFFFFFB"; (* B - *)
  arm_spec_hex "EB000001"; (* BL + *)
  arm_spec_hex "EBFFFFFB"; (* BL - *)
  arm_spec_hex "E12FFF11"; (* BX *)
  arm_spec_hex "E12FFF1F"; (* BX pc *)
  arm_spec_hex "FA000001"; (* BLX + *)
  arm_spec_hex "FAFFFFFB"; (* BLX - *)
  arm_spec_hex "E12FFF31"; (* BLX *)
  (* arm_spec_hex "E12FFF3F"; (* BLX pc - not supported *) *)
  arm_spec_hex "E1A01001"; (* MOV *)
  arm_spec_hex "E1B01001"; (* MOVS *)
  arm_spec_hex "E1A01002"; (* MOV *)
  arm_spec_hex "E1A0100F"; (* MOV *)
  (* arm_spec_hex "E1A0F001"; (* MOV pc, r1 - not supported *) *)
  (* arm_spec_hex "E3A0F00C"; (* MOV pc, #12 - not supported *) *)
  arm_spec_hex "E3A0100C"; (* MOV r1, #12 *)
  arm_spec_hex "E3E0100C"; (* MOV r1, #-12 - needs SUB CONV? *)
  arm_spec_hex "E1110001"; (* TST *)
  arm_spec_hex "E1110002"; (* TST *)
  arm_spec_hex "E11F0001"; (* TST *)
  arm_spec_hex "E111000F"; (* TST *)
  arm_spec_hex "E1110001"; (* TST *)
  arm_spec_hex "E31100FF"; (* TST *)
  arm_spec_hex "E3110000"; (* TST *)
  arm_spec_hex "E0421002"; (* SUB *)
  arm_spec_hex "E0521002"; (* SUBS *)
  arm_spec_hex "E052100F"; (* SUBS *)
  arm_spec_hex "E0922212"; (* ADDS *)
  arm_spec_hex "E0922102"; (* ADDS *)
  arm_spec_hex "E0921453"; (* ADDS *)
  (* arm_spec_hex "E09F1453"; (* ADDS -- fail unpredictable *) *)
  arm_spec_hex "E0A21453"; (* ADC *)
  arm_spec_hex "E0B21453"; (* ADCS *)
  arm_spec_hex "E1B011C2"; (* ASRS *)
  arm_spec_hex "E0214392"; (* MLA *)
  arm_spec_hex "E0314392"; (* MLAS *)

  arm_spec_hex "E5921003"; (* LDR pre *)
  arm_spec_hex "E5121003"; (* LDR pre *)
  arm_spec_hex "E5321080"; (* LDR pre wb *)
  arm_spec_hex "E5961080"; (* LDR pre *)
  arm_spec_hex "E7911001"; (* LDR pre *)
  arm_spec_hex "E59F1000"; (* LDR pc base *)
  arm_spec_hex "E79F1001"; (* LDR pre pc base *)
  arm_spec_hex "E7921063"; (* LDR pre reg rrx *)
  arm_spec_hex "E4921004"; (* LDR post imm *)
  arm_spec_hex "E4121004"; (* LDR post -imm *)
  arm_spec_hex "E6921002"; (* LDR post reg *)
  arm_spec_hex "E6121002"; (* LDR post -reg *)
  arm_spec_hex "E6121003"; (* LDR post -reg *)
  arm_spec_hex "E6921103"; (* LDR post reg *)

  arm_spec_hex "E59F1020"; (* LDR (+lit) *)
  arm_spec_hex "E51F1020"; (* LDR (-lit) *)
  arm_spec_hex "E1CF02D0"; (* LDRD (+lit) *)
  arm_spec_hex "E14F02D0"; (* LDRD (-lit) *)

  arm_spec_hex "E5D21004"; (* LDRB pre *)
  arm_spec_hex "E7D21102"; (* LDRB reg pre *)
  arm_spec_hex "E6D21102"; (* LDRB reg post *)
  arm_spec_hex "E19110D2"; (* LDRSB reg pre *)
  arm_spec_hex "E19110B2"; (* LDRH reg pre *)
  arm_spec_hex "E09210F3"; (* LDRSH reg post *)
  arm_spec_hex "E09210F2"; (* LDRSH reg post *)

  arm_spec_hex "E1C200D4"; (* LDRD pre *)
  arm_spec_hex "E14200D4"; (* LDRD pre *)
  arm_spec_hex "E1E200D4"; (* LDRD pre wb *)
  arm_spec_hex "E0C200D4"; (* LDRD post *)
  arm_spec_hex "E04200D4"; (* LDRD post *)
  arm_spec_hex "E08200D3"; (* LDRD post reg *)
  arm_spec_hex "E00200D3"; (* LDRD post reg *)

  arm_spec_hex "E5821003"; (* STR pre *)
  arm_spec_hex "E5021003"; (* STR pre *)
  arm_spec_hex "E5221080"; (* STR pre wb *)
  arm_spec_hex "E5861080"; (* STR pre *)
  arm_spec_hex "E7811001"; (* STR pre *)
  arm_spec_hex "E58F1000"; (* STR pc base  ** NOT WORKING *)
  arm_spec_hex "E78F1001"; (* STR pre pc base *)
  arm_spec_hex "E7821063"; (* STR pre reg rrx *)
  arm_spec_hex "E4821004"; (* STR post imm *)
  arm_spec_hex "E4021004"; (* STR post -imm *)
  arm_spec_hex "E6821002"; (* STR post reg *)
  arm_spec_hex "E6021002"; (* STR post -reg *)
  arm_spec_hex "E6021003"; (* STR post -reg *)
  arm_spec_hex "E6821103"; (* STR post reg *)

  arm_spec_hex "E5C21004"; (* STRB pre *)
  arm_spec_hex "E7C21102"; (* STRB reg pre *)
  arm_spec_hex "E6C21102"; (* STRB reg post *)
  arm_spec_hex "E18110B2"; (* STRH reg pre *)

  arm_spec_hex "E1C200F4"; (* STRD pre *)
  arm_spec_hex "E14200F4"; (* STRD pre *)
  arm_spec_hex "E1E200F4"; (* STRD pre wb *)
  arm_spec_hex "E0C200F4"; (* STRD post *)
  arm_spec_hex "E04200F4"; (* STRD post *)
  arm_spec_hex "E08200F3"; (* STRD post reg *)
  arm_spec_hex "E00200F3"; (* STRD post reg *)

  arm_spec_hex "E1031091"; (* SWP *)
  arm_spec_hex "E1031092"; (* SWP *)
  arm_spec_hex "E1431091"; (* SWPB *)
  arm_spec_hex "E1431092"; (* SWPB *)

  arm_spec_hex "E891000E"; (* LDMIA;3,2,1 *)
  arm_spec_hex "E991000E"; (* LDMIB;3,2,1 *)
  arm_spec_hex "E811000E"; (* LDMDA;3,2,1 *)
  arm_spec_hex "E911000E"; (* LDMDB;3,2,1 *)

  arm_spec_hex "E881000E"; (* STMIA;3,2,1 *)
  arm_spec_hex "E981000E"; (* STMIB;3,2,1 *)
  arm_spec_hex "E801000E"; (* STMDA;3,2,1 *)
  arm_spec_hex "E901000E"; (* STMDB;3,2,1 *)
  arm_spec_hex "e88c03ff"; (* STMIA;9,8,7,6,5,4,3,2,1,0 *)

  arm_spec_hex "E8B1001C"; (* LDMIA (wb);4,3,2 *)
  arm_spec_hex "E8A1001C"; (* STMIA (wb);4,3,2 *)
  arm_spec_hex "E8A10082"; (* STMIA (wb);7,1 *)

  arm_spec_hex "01A00000"; (* MOVEQ *)
  arm_spec_hex "11A00000"; (* MOVNE *)
  arm_spec_hex "21A00000"; (* MOVCS *)
  arm_spec_hex "31A00000"; (* MOVCC *)
  arm_spec_hex "41A00000"; (* MOVMI *)
  arm_spec_hex "51A00000"; (* MOVPL *)
  arm_spec_hex "61A00000"; (* MOVVS *)
  arm_spec_hex "71A00000"; (* MOVVC *)
  arm_spec_hex "81A00000"; (* MOVHI *)
  arm_spec_hex "91A00000"; (* MOVLS *)
  arm_spec_hex "A1A00000"; (* MOVGE *)
  arm_spec_hex "B1A00000"; (* MOVLT *)
  arm_spec_hex "C1A00000"; (* MOVGT *)
  arm_spec_hex "D1A00000"; (* MOVLE *)

List.length hex_list
val () = Count.apply (List.app (General.ignore o arm_spec_hex)) hex_list

val () =
   Count.apply (List.app
      (fn s =>
         let
            val thm = Count.apply arm_spec_hex s
            val () = print (s ^ ":\n")
         in
            print_thm thm; print "\n\n"
         end))
         hex_list

fun exclude s = List.exists (fn e => String.isPrefix e s) ["LDM", "STM"]

val l = List.filter (not o exclude) (arm_stepLib.list_instructions ())

val pos = ref 0;

val () = List.app (fn s => (addInstructionClass s; Portable.inc pos))
                  (List.drop (l, !pos))

use "arm_tests.sml";
val l = Lib.mk_set arm_tests
length arm_tests
length l

val fails = ref ([]:string list)
val pos = ref 0;

val () =
   (Count.apply
      (List.app (fn s => (arm_spec_hex s
                          handle HOL_ERR _ => (fails := s::(!fails); [TRUTH])
                          ; Portable.inc pos)))
      (List.drop (l, !pos))
    ; print "Done\n")

fails
pos
List.length (!fails)

val stp = arm_stepLib.arm_step_hex ""
val dec = arm_stepLib.arm_decode_hex ""
val fs = List.map (fn s => (s, Lib.total dec s)) (!fails)

val s = List.nth (l, !pos)
val thm = step (List.nth (l, !pos))
val thm = Count.apply arm_spec (List.nth (l, !pos))

(* --- *)

val imp_spec = ARM_IMP_SPEC
val read_thms = [arm_stepTheory.get_bytes]
val write_thms = []: thm list
val select_state_thms = (arm_select_state_pool_thm :: arm_select_state_thms)
val frame_thms = [arm_frame, arm_frame_hidden, state_id, fp_id]
val map_tys = [word, word5, ``:RName``]
val mk_pre_post = arm_mk_pre_post
val write = arm_write_footprint

val model_def = arm_progTheory.ARM_MODEL_def
val comp_defs = arm_comp_defs
val cpool = mk_arm_code_pool
val extras = []: footprint_extra list
val write_fn = arm_write_footprint

*)

(* ------------------------------------------------------------------------ *)

end
