structure m0_progLib :> m0_progLib =
struct

open HolKernel boolLib bossLib
open stateLib spec_databaseLib m0_progTheory

structure Parse =
struct
   open Parse
   val (Type, Term) = parse_from_grammars m0_progTheory.m0_prog_grammars
end

open Parse

val ERR = Feedback.mk_HOL_ERR "m0_progLib"

(* ------------------------------------------------------------------------ *)

val m0_proj_def = m0_progTheory.m0_proj_def
val m0_comp_defs = m0_progTheory.component_defs

local
   val pc = Term.prim_mk_const {Thy = "m0", Name = "RName_PC"}
   val step_1 = HolKernel.syntax_fns1 "m0_step"
   fun syn n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "m0_prog"
   val m0_0 = syn 1 HolKernel.dest_monop HolKernel.mk_monop
in
   val m0_1 = syn 2 HolKernel.dest_monop HolKernel.mk_monop
   val m0_2 = syn 3 HolKernel.dest_binop HolKernel.mk_binop
   val byte = wordsSyntax.mk_int_word_type 8
   val half = wordsSyntax.mk_int_word_type 16
   val word = wordsSyntax.mk_int_word_type 32
   val (_, _, dest_m0_AIRCR_ENDIANNESS, _) = m0_1 "m0_AIRCR_ENDIANNESS"
   val (_, _, dest_m0_CONFIG, _) = m0_1 "m0_CONFIG"
   val (_, mk_data_to_thumb2, _, _) = m0_0 "data_to_thumb2"
   val (_, mk_m0_MEM, dest_m0_MEM, is_m0_MEM) = m0_2 "m0_MEM"
   val (_, mk_m0_REG, dest_m0_REG, is_m0_REG) = m0_2 "m0_REG"
   val (_, mk_rev_e, _, _) = step_1 "reverse_endian"
   fun mk_m0_PC v = mk_m0_REG (pc, v)
end

(* -- *)

val m0_select_state_thms =
   List.map (fn t => stateLib.star_select_state_thm m0_proj_def [] ([], t))
            m0_comp_defs

val m0_select_state_pool_thm =
   utilsLib.map_conv
     (pool_select_state_thm m0_proj_def [] o
      utilsLib.SRW_CONV
         [pred_setTheory.INSERT_UNION_EQ, stateTheory.CODE_POOL, m0_instr_def])
     [``CODE_POOL m0_instr {(pc, INL opc)}``,
      ``CODE_POOL m0_instr {(pc, INR opc)}``]

(* -- *)

val state_id =
   utilsLib.mk_state_id_thm m0Theory.m0_state_component_equality
      [["PSR", "REG", "count", "pcinc"],
       ["MEM", "REG", "count", "pcinc"],
       ["REG", "count", "pcinc"]
      ]

val m0_frame =
   stateLib.update_frame_state_thm m0_proj_def
      ["PSR.N", "PSR.Z", "PSR.C", "PSR.V", "count", "REG", "MEM"]

val m0_frame_hidden =
   stateLib.update_hidden_frame_state_thm m0_proj_def
      [``s with pcinc := x``]

(* -- *)

local
   val m0_instr_tm = Term.prim_mk_const {Thy = "m0_prog", Name = "m0_instr"}
   fun is_mem_access v tm =
      case Lib.total boolSyntax.dest_eq tm of
         SOME (l, r) =>
            stateLib.is_code_access ("m0$m0_state_MEM", v) l andalso
            (wordsSyntax.is_word_literal r orelse bitstringSyntax.is_v2w r)
       | NONE => false
   val dest_opc = fst o listSyntax.dest_list o fst o bitstringSyntax.dest_v2w
   val ty16 = fcpSyntax.mk_int_numeric_type 16
   val ty32 = fcpSyntax.mk_int_numeric_type 32
   fun list_mk_concat ty l =
      bitstringSyntax.mk_v2w
         (listSyntax.mk_list
            (List.concat (List.map dest_opc l), Type.bool), ty)
   val rearrange = fn [a, b, c, d] => [c, d, a, b] | l => l
   fun mk_inl_or_inr l =
      if List.length l = 2
         then sumSyntax.mk_inl (list_mk_concat ty16 l, word)
      else sumSyntax.mk_inr (list_mk_concat ty32 (rearrange l), half)
in
   fun mk_m0_code_pool thm =
      let
         val r15 = stateLib.gvar "pc" word
         val r15_a = mk_m0_PC r15
         val (a, tm) = Thm.dest_thm thm
         val r15_subst = Term.subst [``s.REG RName_PC`` |-> r15]
         val a = List.map r15_subst a
         val (m, a) = List.partition (is_mem_access r15) a
         val m = List.map dest_code_access m
         val m = mlibUseful.sort_map fst Int.compare m
         val opc = mk_inl_or_inr (List.map snd (List.rev m))
      in
         (r15_a,
          boolSyntax.rand (stateLib.mk_code_pool (m0_instr_tm, r15, opc)),
          list_mk_imp (a, r15_subst tm))
      end
end

local
   val pc_tm = ``alignment$align 2 (pc + 4w: word32)``
   fun is_pc_relative tm =
      case Lib.total dest_m0_MEM tm of
         SOME (t, _) => fst (utilsLib.strip_add_or_sub t) = pc_tm
       | NONE => false
   fun is_big_end tm =
      case Lib.total dest_m0_AIRCR_ENDIANNESS tm of
         SOME t => t = boolSyntax.T
       | NONE => false
   val byte_chunks = stateLib.group_into_chunks (dest_m0_MEM, 4, false)
   fun rwt (w, a) =
      [Drule.SPECL [a, w] m0_progTheory.MOVE_TO_TEMPORAL_M0_CODE_POOL,
       Drule.SPECL [a, w] m0_progTheory.MOVE_TO_M0_CODE_POOL]
   fun move_to_code wa =
      REWRITE_RULE
       ([stateTheory.BIGUNION_IMAGE_1, stateTheory.BIGUNION_IMAGE_2,
         set_sepTheory.STAR_ASSOC, set_sepTheory.SEP_CLAUSES,
         m0_progTheory.disjoint_m0_instr_thms, m0_stepTheory.concat_bytes] @
        List.concat (List.map rwt wa))
   val rev_end_rule =
      PURE_REWRITE_RULE
        [m0_stepTheory.concat_bytes, m0_stepTheory.reverse_endian_bytes]
   fun rev_intro x =
      rev_end_rule o Thm.INST (List.map (fn (w, _: term) => w |-> mk_rev_e w) x)
in
   fun extend_m0_code_pool thm =
      let
         val (p, q) = temporal_stateSyntax.dest_pre_post' (Thm.concl thm)
         val lp = progSyntax.strip_star p
      in
         if Lib.exists is_pc_relative lp
            then let
                    val be = List.exists is_big_end lp
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
   case Term.dest_thy_const tm of
      {Thy = "m0", Name = "RName_0", ...} => 0
    | {Thy = "m0", Name = "RName_1", ...} => 1
    | {Thy = "m0", Name = "RName_2", ...} => 2
    | {Thy = "m0", Name = "RName_3", ...} => 3
    | {Thy = "m0", Name = "RName_4", ...} => 4
    | {Thy = "m0", Name = "RName_5", ...} => 5
    | {Thy = "m0", Name = "RName_6", ...} => 6
    | {Thy = "m0", Name = "RName_7", ...} => 7
    | {Thy = "m0", Name = "RName_8", ...} => 8
    | {Thy = "m0", Name = "RName_9", ...} => 9
    | {Thy = "m0", Name = "RName_10", ...} => 10
    | {Thy = "m0", Name = "RName_11", ...} => 11
    | {Thy = "m0", Name = "RName_12", ...} => 12
    | {Thy = "m0", Name = "RName_SP_main", ...} => 13
    | {Thy = "m0", Name = "RName_SP_process", ...} => 13
    | {Thy = "m0", Name = "RName_LR", ...} => 14
    | {Thy = "m0", Name = "RName_PC", ...} => 15
    | _ => raise ERR "reg_index" ""

local
   fun other_index tm =
      case fst (Term.dest_const (boolSyntax.rator tm)) of
         "m0_exception" => 0
       | "m0_CONTROL_SPSEL" => 1
       | "m0_AIRCR" => 2
       | "m0_count" => 3
       | "m0_PSR_N" => 9
       | "m0_PSR_Z" => 10
       | "m0_PSR_C" => 11
       | "m0_PSR_V" => 12
       | _ => ~1
   val int_of_v2w = bitstringSyntax.int_of_term o fst o bitstringSyntax.dest_v2w
   val total_dest_lit = Lib.total wordsSyntax.dest_word_literal
   val total_dest_reg = Lib.total (wordsSyntax.uint_of_word o Term.rand)
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
       | NONE => (case total_dest_reg tm of
                     SOME i => mlibUseful.INL i
                   | NONE => mlibUseful.INR tm)
   val register = reg o fst o dest_m0_REG
   val address = HolKernel.strip_binop (Lib.total wordsSyntax.dest_word_add) o
                 fst o dest_m0_MEM
in
   fun psort p =
      let
         val (m, rst) = List.partition is_m0_MEM p
         val (r, rst) = List.partition is_m0_REG rst
      in
         mlibUseful.sort_map other_index Int.compare rst @
         mlibUseful.sort_map register reg_compare r @
         mlibUseful.sort_map address (mlibUseful.lex_list_order word_compare) m
      end
end

local
   val st = Term.mk_var ("s", ``:m0_state``)
   val psr_footprint =
      stateLib.write_footprint m0_1 m0_2 []
        [("m0$PSR_N_fupd", "m0_PSR_N"),
         ("m0$PSR_Z_fupd", "m0_PSR_Z"),
         ("m0$PSR_C_fupd", "m0_PSR_C"),
         ("m0$PSR_V_fupd", "m0_PSR_V")] [] []
        (fn (s, l) => s = "m0$m0_state_PSR" andalso l = [st])
in
   val m0_write_footprint =
      stateLib.write_footprint m0_1 m0_2
        [("m0$m0_state_MEM_fupd", "m0_MEM", ``^st.MEM``),
         ("m0$m0_state_REG_fupd", "m0_REG", ``^st.REG``)]
        [("m0$m0_state_count_fupd", "m0_count")] []
        [("m0$m0_state_PSR_fupd", psr_footprint),
         ("m0$m0_state_pcinc_fupd", fn (p, q, _) => (p, q))]
        (K false)
end

val m0_mk_pre_post =
   stateLib.mk_pre_post
      m0_progTheory.M0_MODEL_def m0_comp_defs mk_m0_code_pool []
      m0_write_footprint psort

(* ------------------------------------------------------------------------ *)

local
   val sp = wordsSyntax.mk_wordii (13, 4)
   val registers = List.tabulate (16, fn i => wordsSyntax.mk_wordii (i, 4))
                   |> Lib.pluck (Lib.equal sp) |> snd
   val R_name_tm = Term.prim_mk_const {Thy = "m0_step", Name = "R_name"}
   val R_name_b_tm = Term.mk_comb (R_name_tm, Term.mk_var ("b", Type.bool))
   val mk_R_main = Lib.curry Term.mk_comb R_name_b_tm
   val R_main =
      utilsLib.map_conv
         (SIMP_CONV (srw_ss()) [m0_stepTheory.R_name_def])
         (List.map mk_R_main registers @
          [``^R_name_tm F ^sp``, ``^R_name_tm T ^sp``])
   val rwts = List.take (utilsLib.datatype_rewrites false "m0" ["RName"], 2)
in
   val REG_CONV =
      Conv.QCONV (REWRITE_CONV (rwts @ [R_main, m0_stepTheory.v2w_ground4]))
   val REG_RULE = Conv.CONV_RULE REG_CONV o utilsLib.ALL_HYP_CONV_RULE REG_CONV
end

local
   val dest_reg = dest_m0_REG
   val reg_width = 4
   val proj_reg = SOME reg_index
   val reg_conv = REG_CONV
   val ok_conv = ALL_CONV
   val r15 = wordsSyntax.mk_wordii (15, 4)
   fun asm tm = Thm.ASSUME (boolSyntax.mk_neg (boolSyntax.mk_eq (tm, r15)))
   val model_tm = ``M0_MODEL``
in
   val combinations =
      stateLib.register_combinations
         (dest_reg, reg_width, proj_reg, reg_conv, ok_conv, asm, model_tm)
end

(* ------------------------------------------------------------------------ *)

local
   val m0_rename1 =
      Lib.total
        (fn "m0_prog$m0_PSR_N" => "n"
          | "m0_prog$m0_PSR_Z" => "z"
          | "m0_prog$m0_PSR_C" => "c"
          | "m0_prog$m0_PSR_V" => "v"
          | "m0_prog$m0_AIRCR_ENDIANNESS" => "endianness"
          | "m0_prog$m0_CurrentMode" => "mode"
          | "m0_prog$m0_count" => "count"
          | _ => fail())
   val m0_rename2 =
      Lib.total
        (fn "m0_prog$m0_REG" => Lib.curry (op ^) "r" o Int.toString o reg_index
          | "m0_prog$m0_MEM" => K "b"
          | _ => fail())
in
   val m0_rename = stateLib.rename_vars (m0_rename1, m0_rename2, ["b"])
end

local
   val m0_PSR_T_F = List.map UNDISCH (CONJUNCTS m0_progTheory.m0_PSR_T_F)
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
      helperLib.MERGE_CONDS_RULE o TRY_DISCH_RULE o PURE_REWRITE_RULE m0_PSR_T_F
   val addr_eq_conv =
      SIMP_CONV (bool_ss++wordsLib.WORD_ARITH_ss++wordsLib.WORD_ARITH_EQ_ss) []
   val m0_PC_INTRO0 =
      m0_PC_INTRO |> Q.INST [`p1`|->`emp`, `p2`|->`emp`]
                  |> PURE_REWRITE_RULE [set_sepTheory.SEP_CLAUSES]
   val m0_TEMPORAL_PC_INTRO0 =
      m0_TEMPORAL_PC_INTRO |> Q.INST [`p1`|->`emp`, `p2`|->`emp`]
                           |> PURE_REWRITE_RULE [set_sepTheory.SEP_CLAUSES]
   fun MP_m0_PC_INTRO th =
      Lib.tryfind (fn thm => MATCH_MP thm th)
         [m0_PC_INTRO, m0_TEMPORAL_PC_INTRO,
          m0_PC_INTRO0, m0_TEMPORAL_PC_INTRO0]
   val cnv =
      REWRITE_CONV [alignmentTheory.aligned_numeric,
                    m0_stepTheory.Aligned_Branch,
                    m0_stepTheory.Aligned_LoadStore]
   val m0_PC_bump_intro =
      SPEC_IMP_RULE o
      Conv.CONV_RULE (Conv.LAND_CONV cnv) o
      MP_m0_PC_INTRO o
      Conv.CONV_RULE
         (helperLib.POST_CONV (helperLib.MOVE_OUT_CONV ``m0_REG RName_PC``))
   fun is_big_end tm =
      case Lib.total (pairSyntax.dest_pair o dest_m0_CONFIG) tm of
         SOME (t, _) => t = boolSyntax.T
       | _ => false
   val le_sep_array_introduction =
      stateLib.sep_array_intro
         false m0_progTheory.m0_WORD_def [m0_stepTheory.concat_bytes]
   val be_sep_array_introduction =
      stateLib.sep_array_intro
         true m0_progTheory.m0_BE_WORD_def [m0_stepTheory.concat_bytes]
   val concat_bytes_rule =
      Conv.CONV_RULE
         (helperLib.POST_CONV (PURE_REWRITE_CONV [m0_stepTheory.concat_bytes]))
in
   val memory_introduction =
      stateLib.introduce_map_definition
         (m0_progTheory.m0_MEMORY_INSERT, addr_eq_conv)
   val register_introduction =
      concat_bytes_rule o
      stateLib.introduce_map_definition
         (m0_progTheory.m0_REGISTERS_INSERT, REG_CONV)
   val sep_array_introduction =
      stateLib.pick_endian_rule
        (is_big_end, be_sep_array_introduction, le_sep_array_introduction)
   val m0_introduction =
      flag_introduction o
      m0_PC_bump_intro o
      stateLib.introduce_triple_definition (false, m0_PC_def) o
      stateLib.introduce_triple_definition (true, m0_CONFIG_def) o
      extend_m0_code_pool o
      m0_rename
end

local
   fun check_unique_reg_CONV tm =
      let
         val p = progSyntax.strip_star (temporal_stateSyntax.dest_pre' tm)
         val rp = List.mapPartial (Lib.total (fst o dest_m0_REG)) p
      in
         if Lib.mk_set rp = rp
            then Conv.ALL_CONV tm
         else raise ERR "check_unique_reg_CONV" "duplicate register"
      end
   fun DEPTH_COND_CONV cnv =
      Conv.ONCE_DEPTH_CONV
        (fn tm =>
            if progSyntax.is_cond tm
               then Conv.RAND_CONV cnv tm
            else raise ERR "COND_CONV" "")
   val POOL_CONV = Conv.RATOR_CONV o Conv.RAND_CONV
   val OPC_CONV = POOL_CONV o Conv.RATOR_CONV o Conv.RAND_CONV o Conv.RAND_CONV
   exception FalseTerm
   fun NOT_F_CONV tm =
      if tm = boolSyntax.F then raise FalseTerm else Conv.ALL_CONV tm
   val WGROUND_RW_CONV =
      Conv.DEPTH_CONV (utilsLib.cache 10 Term.compare bitstringLib.v2w_n2w_CONV)
      THENC utilsLib.WALPHA_CONV
      THENC utilsLib.WGROUND_CONV
      THENC utilsLib.WALPHA_CONV
   val PRE_COND_CONV =
      helperLib.PRE_CONV
         (DEPTH_COND_CONV
             (REWRITE_CONV [alignmentTheory.aligned_numeric]
              THENC NOT_F_CONV)
          THENC PURE_ONCE_REWRITE_CONV [stateTheory.cond_true_elim])
   val cnv =
      REG_CONV
      THENC check_unique_reg_CONV
      THENC WGROUND_RW_CONV
      THENC PRE_COND_CONV
      THENC helperLib.POST_CONV (stateLib.PC_CONV "m0_prog$m0_PC")
in
   fun simp_triple_rule thm =
      m0_rename (Conv.CONV_RULE cnv thm)
      handle FalseTerm => raise ERR "simp_triple_rule" "condition false"
end

local
   fun mk_bool_list l = listSyntax.mk_list (l, Type.bool)
   fun reverse_end b l =
      mk_bool_list (if b then List.drop (l, 8) @ List.take (l, 8) else l)
in
   fun mk_thumb2_pair bigend tm =
      let
         val t = fst (bitstringSyntax.dest_v2w tm)
         val l = fst (listSyntax.dest_list t)
         val r = reverse_end bigend
      in
         if 16 < List.length l
            then let
                    val l1 = List.take (l, 16)
                    val l2 = List.drop (l, 16)
                 in
                    pairSyntax.mk_pair (r l1, r l2)
                 end
         else if bigend
            then r l
         else t
      end
   val get_code = snd o pairSyntax.dest_pair o List.last o
                  pred_setSyntax.strip_set o
                  temporal_stateSyntax.dest_code' o Thm.concl
   fun get_opcode bigend = mk_thumb2_pair bigend o boolSyntax.rand o get_code
end

datatype memory = Flat | Array | Map
type opt = {gpr_map: bool, mem: memory, temporal: bool}

local
   val gpr_map_options =
      [["map-gpr", "gpr-map", "reg-map", "map-reg"],
       ["no-gpr-map", "no-map-gpr"]]
   val mem_options =
      [["map-mem", "mem-map", "mapped"],
       ["array-mem", "mem-array", "array"],
       ["flat-map", "mem-flat", "flat"]]
   val temporal_options =
      [["temporal"],
       ["not-temporal"]]
   fun isDelim c = Char.isPunct c andalso c <> #"-" orelse Char.isSpace c
   val memopt =
      fn 0 => Map
       | 1 => Array
       | 2 => Flat
       | _ => raise ERR "process_rule_options" ""
in
   fun basic_opt () =
      {gpr_map = false, mem = Flat,
       temporal = stateLib.generate_temporal()}: opt
   val default_opt = {gpr_map = false, mem = Map, temporal = false}: opt
   fun proj_opt ({gpr_map, mem, ...}: opt) = (gpr_map, mem)
   fun closeness (target: opt) (opt: opt)  =
      (case (#gpr_map opt, #gpr_map target) of
          (false, true) => 0
        | (true, false) => ~100
        | (_, _) => 1) +
      (case (#mem opt, #mem target) of
          (Flat, _) => 0
        | (_, Flat) => ~100
        | (m1, m2) => if m1 = m2 then 1 else ~10)
   fun convert_opt_rule (opt: opt) (target: opt) =
      (if #gpr_map target andalso not (#gpr_map opt)
          then register_introduction
       else Lib.I) o
      (if #mem target = #mem opt
         then Lib.I
       else case #mem target of
               Flat => Lib.I
             | Array => sep_array_introduction
             | Map => memory_introduction)
   fun process_rule_options s =
      let
         val l = String.tokens isDelim s
         val l = List.map utilsLib.lowercase l
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
            then {gpr_map = gpr_map, mem = mem, temporal = temporal}: opt
         else raise ERR "process_options"
                    ("Unrecognized option" ^
                     (if List.length l > 1 then "s" else "") ^
                     ": " ^ String.concat (commafy l))
      end
end

local
   val component_11 =
      (case Drule.CONJUNCTS m0_progTheory.m0_component_11 of
          [r, _, m, _] => [r, m]
        | _ => raise ERR "component_11" "")
   val sym_R_x_pc =
      REWRITE_RULE [utilsLib.qm [] ``(a = RName_PC) = (RName_PC = a)``]
         m0_stepTheory.R_x_pc
   val EXTRA_TAC =
      RULE_ASSUM_TAC (REWRITE_RULE [sym_R_x_pc, m0_stepTheory.R_x_pc])
      THEN ASM_REWRITE_TAC [boolTheory.DE_MORGAN_THM]
   val m0_rwts = tl (utilsLib.datatype_rewrites true "m0" ["m0_state", "PSR"])
   val STATE_TAC = ASM_REWRITE_TAC m0_rwts
   val spec =
      stateLib.spec
           m0_progTheory.M0_IMP_SPEC
           m0_progTheory.M0_IMP_TEMPORAL_NEXT
           [m0_stepTheory.get_bytes]
           []
           (m0_select_state_pool_thm :: m0_select_state_thms)
           [m0_frame, m0_frame_hidden, state_id]
           component_11
           [word, ``:RName``]
           EXTRA_TAC STATE_TAC
   val newline = ref "\n"
   fun x n = Term.mk_var ("x" ^ Int.toString n, Type.bool)
   fun stm_base s =
      if String.isPrefix "STM" s
         then let
                 val (x0,x1,x2) =
                    s |> utilsLib.splitAtChar (Char.isDigit)
                      |> snd
                      |> String.tokens (Lib.equal #",")
                      |> List.map Arbnum.fromString
                      |> mlibUseful.min Arbnum.compare
                      |> fst
                      |> Arbnum.toInt
                      |> bitstringSyntax.int_to_bitlist
                      |> utilsLib.padLeft false 3
                      |> List.map bitstringSyntax.mk_b
                      |> Lib.triple_of_list
              in
                 SOME [x 0 |-> x0, x 1 |-> x1, x 2 |-> x2]
              end
              handle General.Size => raise ERR "stm_base" "base too large"
      else NONE
   val bigend = ref false
   fun get_opc thm = get_opcode (!bigend) thm
   val (reset_db, set_current_opt, get_current_opt, add1_pending, find_spec,
        list_db) =
      spec_databaseLib.mk_spec_database basic_opt default_opt proj_opt
         closeness convert_opt_rule get_opc (m0_introduction o spec)
   val the_step = ref (m0_stepLib.thumb_step (!bigend, false))
   val spec_label_set = ref (Redblackset.empty String.compare)
   fun reset_specs () =
      (reset_db (); spec_label_set := Redblackset.empty String.compare)
   fun configure be options =
      let
         val opt = process_rule_options options
      in
         if !bigend = be andalso #temporal (get_current_opt ()) = #temporal opt
            then ()
         else ( reset_specs ()
              ; bigend := be
              ; the_step := m0_stepLib.thumb_step (be, false)
              )
         ; stateLib.set_temporal (#temporal opt)
         ; set_current_opt opt
      end
   fun m0_spec_opt be opt =
      let
         val () = configure be opt
         val step = !the_step
      in
         fn s =>
            let
               val thms = step s
               val thms = case (thms, stm_base s) of
                             ([thm], SOME m) =>
                               [REG_RULE (Thm.INST m thm), thm]
                           | _ => thms
               val ts = List.map m0_mk_pre_post thms
               val thms_ts =
                  List.concat
                     (List.map combinations (ListPair.zip (thms, ts)))
            in
               List.map (fn x => (print "."; add1_pending x)) thms_ts
               ; thms_ts
            end
      end
   val the_spec = ref (m0_spec_opt (!bigend) "")
   fun spec_spec opc thm =
      let
         val thm_opc = get_opc thm
         val a = fst (Term.match_term thm_opc opc)
      in
         simp_triple_rule (Thm.INST a thm)
      end
in
   val list_db = list_db
   fun set_newline s = newline := s
   fun m0_config be opt = the_spec := m0_spec_opt be opt
   fun m0_spec s = List.map spec ((!the_spec) s)
   fun addInstructionClass s =
      if Redblackset.member (!spec_label_set, s)
         then false
      else (print (" " ^ s)
            ; (!the_spec) s
            ; spec_label_set := Redblackset.add (!spec_label_set, s)
            ; true)
   fun m0_spec_hex looped s =
      let
         val opc = m0_stepLib.hex_to_bits s
      in
         case find_spec opc of
            SOME (new, thms) =>
              let
                 val l = List.mapPartial (Lib.total (spec_spec opc)) thms
              in
                 if List.null l
                    then loop looped opc "failed to find suitable spec" s
                 else (if new then print (!newline) else (); l)
              end
          | NONE => loop looped opc "failed to add suitable spec" s
      end
   and loop looped opc e s =
      if looped orelse
         not (addInstructionClass (m0_stepLib.thumb_instruction opc))
         then raise ERR "m0_spec_hex" (e ^ ": " ^ s)
      else m0_spec_hex true s
   val m0_spec_hex = m0_spec_hex false
   val m0_spec_code = List.map m0_spec_hex o
                      (m0AssemblerLib.m0_code: string quotation -> string list)
end

(* ------------------------------------------------------------------------ *)

(* Testing...

open m0_progLib

m0_config false "flat"
m0_config false "array"
m0_config false "mapped"
m0_config false "reg-map,flat"
m0_config false "reg-map,array"
m0_config false "reg-map,mapped"

m0_config true "flat"
m0_config true "array"
m0_config true "mapped"
m0_config true "reg-map,flat"
m0_config true "reg-map,array"
m0_config true "reg-map,mapped"

m0_config false "temporal,flat"
m0_config false "temporal,array"
m0_config false "temporal,mapped"
m0_config false "temporal,reg-map,flat"
m0_config false "temporal,reg-map,array"
m0_config false "temporal,reg-map,mapped"

m0_config true "temporal,flat"
m0_config true "temporal,array"
m0_config true "temporal,mapped"
m0_config true "temporal,reg-map,flat"
m0_config true "temporal,reg-map,array"
m0_config true "temporal,reg-map,mapped"

m0_spec_hex "4906" (* ldr r1, [pc, #24] *)
m0_spec_hex "B406" (* push {r1, r2} *)

list_db ()

local
   val gen = Random.newgenseed 1.0
   fun random_bit () =
      if Random.range (0, 2) gen = 0 then boolSyntax.T else boolSyntax.F
   val d_list = fst o listSyntax.dest_list
   fun mk_hextstring tm =
      case Lib.total pairSyntax.dest_pair tm of
         SOME (l, r) =>
            bitstringSyntax.hexstring_of_term
               (listSyntax.mk_list (d_list l @ d_list r, Type.bool))
       | NONE => bitstringSyntax.hexstring_of_term tm
in
   fun random_hex tm =
      let
         val l = Term.free_vars tm
         val s = List.map (fn v => v |-> random_bit ()) l
      in
         mk_hextstring (Term.subst s tm)
      end
end

val l = m0_stepLib.list_instructions()
        |> List.filter (fn (s, _) => s <> "ADD (pc)")
        |> List.map (random_hex o snd)

val tst = Count.apply (fn s => case Lib.total m0_spec_hex s of
                                  SOME l => mlibUseful.INL (s, l)
                                | NONE => mlibUseful.INR s)

val results = List.map tst l

val ok = List.mapPartial (fn mlibUseful.INL (s, _) => SOME s | _ => NONE) results
val failing = List.mapPartial (fn mlibUseful.INR s => SOME s | _ => NONE) results

val step = m0_stepLib.thumb_step (false, false)
val step_hex = m0_stepLib.thumb_step_hex (false, false)
val dec_hex = m0_stepLib.thumb_decode_hex false
step_hex "C205"
dec_hex "C205"
m0_spec_hex "C205"
val s = m0_stepLib.thumb_instruction (m0_stepLib.hex_to_bits ("C205"))
step s

m0_config (false, false)
m0_config (true, true)

m0_spec "B.W"

m0_spec "BL"
m0_spec "B.W"

m0_spec "ADCS"
m0_spec_hex "416B"

m0_spec_hex "F302B3DA"
val s = "PUSH;7,6,4,3,2,1,0"

val ev = m0_stepLib.thumb_step (false, false)
val ev = m0_stepLib.thumb_step_hex (false, false)
ev "451F" (* unredictable *)
ev "CF21" (* not supported?? ldmia r7!, {r0, r5} *)

ev "LDM (wb); 0, 5"

ok
failing
List.length ok
List.length failing

val imp_spec = M0_IMP_SPEC
val read_thms = [m0_stepTheory.get_bytes]
val write_thms = []: thm list
val select_state_thms = (m0_select_state_pool_thm :: m0_select_state_thms)
val frame_thms = [m0_frame, m0_frame_hidden, state_id]
val map_tys = [word, ``:RName``]
val mk_pre_post = m0_mk_pre_post
val write = m0_write_footprint

*)

(* ------------------------------------------------------------------------ *)

end
