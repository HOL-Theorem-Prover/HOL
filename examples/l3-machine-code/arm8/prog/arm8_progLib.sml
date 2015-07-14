structure arm8_progLib :> arm8_progLib =
struct

open HolKernel boolLib bossLib
open stateLib spec_databaseLib arm8_progTheory

structure Parse =
struct
   open Parse
   val (Type, Term) = parse_from_grammars arm8_progTheory.arm8_prog_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "arm8_progLib"

(* ------------------------------------------------------------------------ *)

val arm_proj_def = arm8_progTheory.arm8_proj_def
val arm_comp_defs = arm8_progTheory.component_defs

val step_1 = HolKernel.syntax_fns1 "arm8_step"
fun syn n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "arm8_prog"
val arm_1 = syn 2 HolKernel.dest_monop HolKernel.mk_monop
val arm_2 = syn 3 HolKernel.dest_binop HolKernel.mk_binop
val word5 = wordsSyntax.mk_int_word_type 5
val word = wordsSyntax.mk_int_word_type 32
val dword = wordsSyntax.mk_int_word_type 64
val pc_tm = Term.mk_var ("pc", dword)
val (_, _, dest_arm8_instr, _) = arm_1 "arm8_instr"
val (_, mk_arm8_PC, dest_arm8_PC, is_arm8_PC) = arm_1 "arm8_PC"
val (_, _, dest_arm8_MEM, is_arm8_MEM) = arm_2 "arm8_MEM"
val (_, mk_arm8_REG, dest_arm8_REG, is_arm8_REG) = arm_2 "arm8_REG"

(* -- *)

val arm_select_state_thms =
   List.map (fn t => stateLib.star_select_state_thm arm_proj_def [] ([], t))
            arm_comp_defs

val arm_select_state_pool_thm =
   pool_select_state_thm arm8_proj_def []
      (utilsLib.SRW_CONV
         [pred_setTheory.INSERT_UNION_EQ, stateTheory.CODE_POOL, arm8_instr_def]
         ``CODE_POOL arm8_instr {(pc, opc)}``)

(* -- *)

val state_id =
   utilsLib.mk_state_id_thm arm8Theory.arm8_state_component_equality
      [
       ["PSTATE", "REG", "branch_hint"],
       ["PSTATE", "branch_hint"],
       ["MEM", "PC", "SP_EL0", "branch_hint"],
       ["MEM", "PC", "REG", "branch_hint"],
       ["MEM", "PC", "branch_hint"],
       ["REG", "SP_EL0", "branch_hint"],
       ["REG", "branch_hint"]
      ]

val arm_frame =
   stateLib.update_frame_state_thm arm_proj_def
      ["PSTATE.N", "PSTATE.Z", "PSTATE.C", "PSTATE.V", "SP_EL0", "PC", "REG",
       "MEM"]

val arm_frame_hidden =
   stateLib.update_hidden_frame_state_thm arm_proj_def
      [``s with branch_hint := x``]

(* -- *)

local
   val arm_instr_tm =
      Term.prim_mk_const {Thy = "arm8_prog", Name = "arm8_instr"}
   fun is_mem_access v tm =
      case Lib.total boolSyntax.dest_eq tm of
         SOME (l, r) =>
            stateLib.is_code_access ("arm8$arm8_state_MEM", v) l andalso
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
         val r15 = stateLib.gvar "pc" dword
         val r15_a = mk_arm8_PC r15
         val (a, tm) = Thm.dest_thm thm
         val r15_subst = Term.subst [``s.PC`` |-> r15]
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
   val err = ERR "DISJOINT_CONV" ""
   val cnv =
      LAND_CONV wordsLib.WORD_EVAL_CONV
      THENC REWRITE_CONV [arm8_progTheory.sub_intro, wordsTheory.WORD_ADD_ASSOC]
   fun split_arm_instr tm =
      Lib.with_exn (pairSyntax.dest_pair o dest_arm8_instr) tm err
in
   fun DISJOINT_CONV tm =
      let
         val (l, r) = Lib.with_exn pred_setSyntax.dest_disjoint tm err
         val (a, x) = split_arm_instr l
         val y = snd (split_arm_instr r)
         val a = case utilsLib.strip_add_or_sub a of
                    (_, [(false, w)]) => wordsSyntax.mk_word_2comp w
                  | (_, [(true, w)]) => w
                  | (_, [(true, w), (true, x)]) =>
                      wordsSyntax.mk_word_add (w, x)
                  | (_, [(false, w), (true, x)]) =>
                      wordsSyntax.mk_word_add (wordsSyntax.mk_word_2comp w, x)
                  | _ => raise err
         val thm =
            Conv.CONV_RULE cnv
               (Drule.SPECL [a, pc_tm, x, y] arm8_progTheory.DISJOINT_arm_instr)
      in
         if Thm.concl thm = tm
            then Drule.EQT_INTRO thm
         else raise err
      end
end

local
   fun is_pc_relative tm =
      case Lib.total dest_arm8_MEM tm of
         SOME (t, _) => fst (utilsLib.strip_add_or_sub t) = pc_tm
       | NONE => false
   fun rwt (w, a) =
      [Drule.SPECL [a, w] arm8_progTheory.MOVE_TO_TEMPORAL_ARM_CODE_POOL,
       Drule.SPECL [a, w] arm8_progTheory.MOVE_TO_ARM_CODE_POOL]
   fun move_to_code wa =
      REWRITE_RULE
       ([stateTheory.BIGUNION_IMAGE_1, stateTheory.BIGUNION_IMAGE_2,
         set_sepTheory.STAR_ASSOC, set_sepTheory.SEP_CLAUSES,
         arm8_progTheory.disjoint_arm_instr_thms,
         arm8_stepTheory.concat_bytes] @
        List.concat (List.map rwt wa))
   val byte_chunks = stateLib.group_into_chunks (dest_arm8_MEM, 4, false)
   val strip_pre =
      progSyntax.strip_star o fst o temporal_stateSyntax.dest_pre_post' o
      Thm.concl
in
   val chunk32 = stateLib.chunks_intro_pre_process arm8_progTheory.arm8_WORD_def
   fun extend_arm_code_pool thm =
      if Lib.exists is_pc_relative (strip_pre thm)
         then let
                 val thm' = chunk32 thm
                 val (s, wa) = byte_chunks (strip_pre thm')
              in
                 if List.null s
                    then thm
                 else move_to_code wa (Thm.INST (List.concat s) thm')
              end
      else thm
end

(* -- *)

fun reg_index tm = Lib.with_exn wordsSyntax.uint_of_word tm (ERR "reg_index" "")

local
   fun other_index tm =
      case fst (Term.dest_const (boolSyntax.rator tm)) of
         "cond" => 0
       | "arm8_PC" => 1
       | "arm8_exception" => 2
       | "arm8_PSTATE_EL" => 3
       | "arm8_SCTLR_EL1_E0E" => 4
       | "arm8_PSTATE_N" => 5
       | "arm8_PSTATE_Z" => 6
       | "arm8_PSTATE_C" => 7
       | "arm8_PSTATE_V" => 8
       | "arm8_SP_EL0" => 9
       | "arm8_TCR_EL1_TBI0" => 10
       | "arm8_TCR_EL1_TBI1" => 11
       | _ => ~1
   val int_of_v2w = bitstringSyntax.int_of_term o fst o bitstringSyntax.dest_v2w
   val total_dest_lit = Lib.total wordsSyntax.dest_word_literal
   fun word_compare (w1, w2) =
      case (total_dest_lit w1, total_dest_lit w2) of
         (SOME x1, SOME x2) => Arbnum.compare (x1, x2)
       | (SOME _, NONE) => General.GREATER
       | (NONE, SOME _) => General.LESS
       | (NONE, NONE) => Term.compare (w1, w2)
   val register = fst o dest_arm8_REG
   val address = HolKernel.strip_binop (Lib.total wordsSyntax.dest_word_add) o
                 fst o dest_arm8_MEM
in
   fun psort p =
      let
         val (m, rst) = List.partition is_arm8_MEM p
         val (r, rst) = List.partition is_arm8_REG rst
      in
         mlibUseful.sort_map other_index Int.compare rst @
         mlibUseful.sort_map register Term.compare r @
         mlibUseful.sort_map address (mlibUseful.lex_list_order word_compare) m
      end
end

local
   val st = Term.mk_var ("s", ``:arm8_state``)
   val pstate_footprint =
      stateLib.write_footprint arm_1 arm_2 []
        [("arm8$ProcState_N_fupd", "arm8_PSTATE_N"),
         ("arm8$ProcState_Z_fupd", "arm8_PSTATE_Z"),
         ("arm8$ProcState_C_fupd", "arm8_PSTATE_C"),
         ("arm8$ProcState_V_fupd", "arm8_PSTATE_V")
         ] [] []
        (fn (s, l) => s = "arm8$arm8_state_PSTATE" andalso l = [st])
in
   val arm_write_footprint =
      stateLib.write_footprint arm_1 arm_2
        [("arm8$arm8_state_MEM_fupd", "arm8_MEM", ``^st.MEM``),
         ("arm8$arm8_state_REG_fupd", "arm8_REG", ``^st.REG``)]
        [("arm8$arm8_state_SP_EL0_fupd",  "arm8_SP_EL0")]
        [("arm8$arm8_state_PC_fupd",  "arm8_PC")]
        [
         ("arm8$arm8_state_PSTATE_fupd", pstate_footprint),
         ("arm8$arm8_state_branch_hint_fupd", fn (p, q, _) => (p, q))
        ]
        (K false)
end

local
   val model_def = arm8_progTheory.ARM8_MODEL_def
   val comp_defs = arm_comp_defs
   val cpool = mk_arm_code_pool
   val extras = [] : footprint_extra list
   val write_fn = arm_write_footprint
in
   val arm_mk_pre_post =
      stateLib.mk_pre_post model_def comp_defs cpool extras write_fn psort
end

(* ------------------------------------------------------------------------ *)

local
   val rwts =
      List.map bitstringLib.v2w_n2w_CONV
         (List.tabulate
            (32, fn i => bitstringSyntax.padded_fixedwidth_of_int (i, 5)))
in
   val REG_CONV = Conv.QCONV (REWRITE_CONV rwts)
end

local
   val dest_reg = dest_arm8_REG
   val width_reg = 5
   val proj_reg = NONE
   val reg_conv = REG_CONV
   val ok_conv = Conv.DEPTH_CONV wordsLib.word_EQ_CONV
                 THENC Conv.QCONV (SIMP_CONV (bool_ss++boolSimps.CONJ_ss) [])
   fun asm_rule (tm: term) = (raise ERR "" "") : thm
   val model_tm = ``ARM8_MODEL``
in
   val combinations =
      stateLib.register_combinations
         (dest_reg, width_reg, proj_reg, reg_conv, ok_conv, asm_rule, model_tm)
end

(* ------------------------------------------------------------------------ *)

local
   val arm_rename1 =
      Lib.total
        (fn "arm8_prog$arm8_PSTATE_N" => "n"
          | "arm8_prog$arm8_PSTATE_Z" => "z"
          | "arm8_prog$arm8_PSTATE_C" => "c"
          | "arm8_prog$arm8_PSTATE_V" => "v"
          | "arm8_prog$arm8_SP_EL0" => "sp"
          | _ => fail())
   val arm_rename2 =
      Lib.total
        (fn "arm8_prog$arm8_REG" =>
              Lib.curry (op ^) "r" o Int.toString o reg_index
          | "arm8_prog$arm8_MEM" => K "b"
          | _ => fail())
in
   val arm_rename = stateLib.rename_vars (arm_rename1, arm_rename2, ["b"])
end

local
   open stateLib
   val addr_eq_conv =
      SIMP_CONV (bool_ss++wordsLib.WORD_ARITH_ss++wordsLib.WORD_ARITH_EQ_ss) []
   val concat_bytes_rule =
      Conv.CONV_RULE
         (stateLib.PRE_COND_CONV
             (SIMP_CONV (bool_ss++boolSimps.CONJ_ss)
                 [alignmentTheory.aligned_numeric,
                  alignmentTheory.aligned_imp, DECIDE ``2 < 3n``])) o
      PURE_REWRITE_RULE [arm8_stepTheory.concat_bytes]
   val chunk64 = chunks_intro_pre_process arm8_progTheory.arm8_DWORD_def
in
   val byte_memory_introduction =
      introduce_map_definition
         (arm8_progTheory.arm8_MEMORY_INSERT, addr_eq_conv)
   val word_memory_introduction =
      concat_bytes_rule o
      introduce_map_definition
         (arm8_progTheory.arm8_WORD_MEMORY_INSERT, addr_eq_conv) o
      chunks_intro false arm8_progTheory.arm8_WORD_def o chunk32
   val dword_memory_introduction =
      concat_bytes_rule o
      introduce_map_definition
         (arm8_progTheory.arm8_DWORD_MEMORY_INSERT, addr_eq_conv) o
      chunks_intro false arm8_progTheory.arm8_DWORD_def o chunk64
   val sep_array32_introduction =
      sep_array_intro
         false arm8_progTheory.arm8_WORD_def [arm8_stepTheory.concat_bytes] o
      chunk32
   val sep_array64_introduction =
      sep_array_intro
         false arm8_progTheory.arm8_DWORD_def [arm8_stepTheory.concat_bytes] o
      chunk64
end

local
   val reg_eq_conv = Conv.DEPTH_CONV wordsLib.word_EQ_CONV
                     THENC REWRITE_CONV []
in
   val gp_introduction =
      stateLib.introduce_map_definition
         (arm8_progTheory.arm8_REGISTERS_INSERT, reg_eq_conv)
end

local
   val MOVE_COND_RULE = Conv.CONV_RULE stateLib.MOVE_COND_CONV
   val SPEC_IMP_RULE =
      Conv.CONV_RULE
        (Conv.REWR_CONV (Thm.CONJUNCT1 (Drule.SPEC_ALL boolTheory.IMP_CLAUSES))
         ORELSEC MOVE_COND_CONV)
   val arm8_PC_INTRO0 =
      arm8_PC_INTRO |> Q.INST [`p1`|->`emp`, `p2`|->`emp`]
                    |> PURE_REWRITE_RULE [set_sepTheory.SEP_CLAUSES]
   val arm8_TEMPORAL_PC_INTRO0 =
      arm8_TEMPORAL_PC_INTRO |> Q.INST [`p1`|->`emp`, `p2`|->`emp`]
                             |> PURE_REWRITE_RULE [set_sepTheory.SEP_CLAUSES]
   fun MP_arm_PC_INTRO th =
      Lib.tryfind (fn thm => MATCH_MP thm th)
         [arm8_PC_INTRO, arm8_TEMPORAL_PC_INTRO,
          arm8_PC_INTRO0, arm8_TEMPORAL_PC_INTRO0]
   val cnv = REWRITE_CONV [alignmentTheory.aligned_numeric]
   val arm_PC_bump_intro =
      SPEC_IMP_RULE o
      Conv.CONV_RULE (Conv.LAND_CONV cnv) o
      MP_arm_PC_INTRO o
      Conv.CONV_RULE
         (helperLib.POST_CONV
            (helperLib.LIST_MOVE_OUT_CONV false
               [``arm8_prog$arm8_PC``,
                ``arm8_prog$arm8_exception``,
                ``arm8_prog$arm8_PSTATE_EL``,
                ``arm8_prog$arm8_SCTLR_EL1_E0E``,
                ``arm8_prog$arm8_TCR_EL1_TBI0``,
                ``arm8_prog$arm8_TCR_EL1_TBI1``,
                ``arm8_prog$arm8_SCTLR_EL1_SA0``]))
in
   val arm_intro =
      arm_PC_bump_intro o
      stateLib.introduce_triple_definition (false, arm8_pc_def) o
      extend_arm_code_pool
end

local
   val dest_some_pair =
      Lib.total (pairSyntax.dest_pair o optionSyntax.dest_some)
   fun mask_subst tm =
      case Lib.total boolSyntax.dest_eq tm of
         SOME (l, r) =>
            (case (dest_some_pair l, dest_some_pair r) of
                (SOME (l1, l2), SOME (r1, r2)) => [r1 |-> l1, r2 |-> l2]
              | _ => [])
       | NONE => []
   val rule =
      REWRITE_RULE [stateTheory.cond_true_elim, boolTheory.DE_MORGAN_THM]
in
   fun DecodeBitMasks_RULE thm =
      let
         val p = temporal_stateSyntax.dest_pre' (Thm.concl thm)
         val p = progSyntax.strip_star p
      in
         case List.mapPartial (Lib.total progSyntax.dest_cond) p of
            [tm] => let
                       val s = mask_subst tm
                    in
                       rule (if List.null s then thm else Thm.INST s thm)
                    end
          | _ => thm
      end
end

local
   val rwt = utilsLib.map_conv (SIMP_CONV bool_ss [])
               [``if b then x else T``, ``if b then x else F``]
   fun check_unique_reg_CONV tm =
      let
         val p = progSyntax.strip_star (temporal_stateSyntax.dest_pre' tm)
         val rp = List.mapPartial (Lib.total (fst o dest_arm8_REG)) p
      in
         if Lib.mk_set rp = rp
            then Conv.ALL_CONV tm
         else raise ERR "check_unique_reg_CONV" "duplicate register"
      end
   exception FalseTerm
   fun NOT_F_CONV tm =
      if tm = boolSyntax.F then raise FalseTerm else Conv.ALL_CONV tm
   fun is_reducible tm =
      case Lib.total boolSyntax.dest_strip_comb tm of
         SOME ("arm8$LSL", [_]) => true
       | SOME ("arm8$ASR", [_]) => true
       | SOME ("arm8$LSR", [_]) => true
       | SOME ("arm8$ROR", [_]) => true
       | SOME ("arm8$ShiftValue", [_]) => true
       | SOME ("arm8$DecodeRegExtend", [_]) => true
       | SOME ("arm8$ExtendWord", [_]) => true
       | SOME ("arm8$ConditionTest", [_]) => true
       | SOME ("arm8$DecodeBitMasks", [_]) => true
       | SOME ("fcp$dimindex", [_]) => true
       | _ => false
   val cnv = Conv.CHANGED_CONV arm8_stepLib.ARM8_CONV
   val SELECTIVE_ARM8_CONV =
      Conv.DEPTH_CONV (fn tm => if is_reducible tm then cnv tm else NO_CONV tm)
   val WGROUND_RW_CONV =
      Conv.DEPTH_CONV (utilsLib.cache 10 Term.compare bitstringLib.v2w_n2w_CONV)
      THENC utilsLib.WALPHA_CONV
      THENC utilsLib.WGROUND_CONV
      THENC utilsLib.WALPHA_CONV
      THENC SELECTIVE_ARM8_CONV
      THENC REWRITE_CONV [rwt, arm8_stepTheory.ExtendValue_0]
   val cnv =
      REG_CONV
      THENC check_unique_reg_CONV
      THENC stateLib.PRE_COND_CONV (REWRITE_CONV [] THENC NOT_F_CONV)
      THENC arm8_stepLib.DATATYPE_CONV
      THENC WGROUND_RW_CONV
      THENC stateLib.PRE_COND_CONV
               (Conv.DEPTH_CONV DISJOINT_CONV
                THENC REWRITE_CONV
                        [alignmentTheory.aligned_numeric,
                         alignmentTheory.aligned_0,
                         optionTheory.NOT_NONE_SOME]
                THENC NOT_F_CONV)
      THENC helperLib.POST_CONV (stateLib.PC_CONV "arm8_prog$arm8_pc")
in
   fun simp_triple_rule thm =
      arm_rename (DecodeBitMasks_RULE (Conv.CONV_RULE cnv thm))
      handle FalseTerm => raise ERR "simp_triple_rule" "condition false"
end

datatype memory = Flat | Array32 | Array64 | Map8 | Map32 | Map64
type opt = {gpr_map: bool, mem: memory, temporal: bool}

local
   val gpr_map_options =
      [["map-gpr", "gpr-map", "reg-map", "map-reg"],
       ["no-gpr-map", "no-map-gpr"]]
   val mem_options =
      [["map-mem8", "mem-map8", "mapped8", "map8"],
       ["map-mem32", "mem-map32", "mapped32", "map32"],
       ["map-mem64", "mem-map64", "mapped64", "map64"],
       ["array-mem32", "mem-array32", "array32"],
       ["array-mem64", "mem-array64", "array64"],
       ["flat-map", "mem-flat", "flat"]]
   val temporal_options =
      [["temporal"],
       ["not-temporal"]]
   fun isDelim c = Char.isPunct c andalso c <> #"-" orelse Char.isSpace c
   val memopt =
      fn 0 => Map8
       | 1 => Map32
       | 2 => Map64
       | 3 => Array32
       | 4 => Array64
       | 5 => Flat
       | _ => raise ERR "process_rule_options" ""
in
   fun basic_opt () =
      {gpr_map = false, mem = Flat,
       temporal = stateLib.generate_temporal()}: opt
   val default_opt = {gpr_map = false, mem = Map8, temporal = false}: opt
   fun proj_opt ({gpr_map, mem, ...}: opt) = (gpr_map, mem)
   fun closeness (target: opt) (opt: opt) =
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
          then gp_introduction
       else Lib.I) o
      (if #mem target = #mem opt
         then Lib.I
       else case #mem target of
               Flat => Lib.I
             | Array32 => sep_array32_introduction
             | Array64 => sep_array64_introduction
             | Map8 => byte_memory_introduction
             | Map32 => word_memory_introduction
             | Map64 => dword_memory_introduction
             )
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
   val v31 = wordsSyntax.mk_wordii (31, 5)
   fun get_cond tm = let val (c, _, _) = boolSyntax.dest_cond tm in c end
   fun is_cond_31 tm =
      case Lib.total boolSyntax.dest_cond tm of
         SOME (c, v, _) =>
           (Lib.total wordsSyntax.uint_of_word v = SOME 0 andalso
            case Lib.total boolSyntax.dest_eq c of
               SOME (l, r) => r = v31 andalso bitstringSyntax.is_v2w l
             | NONE => false)
       | NONE => false
   fun all_assigns acc =
      fn [] => acc
       | (h: Term.term) :: t =>
          all_assigns
            (List.map (fn s => ASSUME h :: s) acc @
             List.map (fn s => ASSUME (boolSyntax.mk_neg h) :: s) acc) t
   val all_assigns = all_assigns [[]]
in
   fun split_on_31 th =
      let
         val tm = boolSyntax.list_mk_conj (Thm.concl th :: Thm.hyp th)
         val l = Lib.mk_set (HolKernel.find_terms is_cond_31 tm)
      in
         if List.null l
            then [th]
         else let
                 val assigns = all_assigns (List.map get_cond l)
                 fun rule rwts =
                    arm8_stepLib.REG_31_RULE
                       (utilsLib.FULL_CONV_RULE (REWRITE_CONV rwts) th)
              in
                 List.filter (not o utilsLib.vacuous) (List.map rule assigns)
              end
      end
end

local
   val arm_step =
      List.map
         (PURE_REWRITE_RULE
            [arm8_stepTheory.mem_half_def,
             arm8_stepTheory.mem_word_def,
             arm8_stepTheory.mem_dword_def]) o
      arm8_stepLib.arm8_step o Option.valOf o arm8_stepLib.arm8_pattern
   fun thm_eq thm1 thm2 = Term.aconv (Thm.concl thm1) (Thm.concl thm2)
   val mk_thm_set = Lib.op_mk_set thm_eq
   val component_11 = Drule.CONJUNCTS arm8_progTheory.arm8_component_11
   val arm_rwts = tl (utilsLib.datatype_rewrites true "arm8"
                        ["arm8_state", "ProcState"])
   val imp_spec = arm8_progTheory.ARM8_IMP_SPEC
   val imp_temp = arm8_progTheory.ARM8_IMP_TEMPORAL
   val read_thms = [arm8_stepTheory.get_bytes] : thm list
   val write_thms = [] : thm list
   val select_state_thms = arm_select_state_pool_thm :: arm_select_state_thms
   val frame_thms = [arm_frame, arm_frame_hidden, state_id]
   val map_tys = [word5, word, dword]
   val EXTRA_TAC = ASM_REWRITE_TAC [boolTheory.DE_MORGAN_THM]
   val STATE_TAC = ASM_REWRITE_TAC arm_rwts
   val basic_spec =
      stateLib.spec imp_spec imp_temp read_thms write_thms select_state_thms
         frame_thms component_11 map_tys EXTRA_TAC STATE_TAC
   val get_opcode =
      fst o bitstringSyntax.dest_v2w o
      snd o pairSyntax.dest_pair o
      List.last o pred_setSyntax.strip_set o
      temporal_stateSyntax.dest_code' o
      Thm.concl
   val (reset_db, set_current_opt, get_current_opt, add1_pending, find_spec,
        list_db) =
      spec_databaseLib.mk_spec_database basic_opt default_opt proj_opt
         closeness convert_opt_rule get_opcode (arm_intro o basic_spec)
   val spec_label_set = ref (Redblackset.empty String.compare)
   fun reset_specs () =
      (reset_db (); spec_label_set := Redblackset.empty String.compare)
   fun spec_spec opc thm =
      let
         val thm_opc = get_opcode thm
         val a = fst (Term.match_term thm_opc opc)
      in
         simp_triple_rule (Thm.INST a thm)
      end
   fun pend_spec s =
      let
         val thms = arm_step s
         val thms = List.concat (List.map split_on_31 thms)
         val ts = List.map arm_mk_pre_post thms
         val thms_ts = ListPair.zip (thms, ts)
         val thms_ts = List.concat (List.map combinations thms_ts)
      in
         List.map (fn x => (print "."; add1_pending x)) thms_ts
         ; thms_ts
      end
   val string_to_opcode =
      bitstringSyntax.bitstring_of_hexstring o StringCvt.padLeft #"0" 8
in
   val list_db = list_db
   fun arm8_config options =
      let
         val opt = process_rule_options options
      in
         if #temporal (get_current_opt ()) = #temporal opt
            then ()
         else (reset_specs (); stateLib.set_temporal (#temporal opt))
         ; set_current_opt opt
      end
   fun arm8_spec s =
      List.map (fn t => (print "+"; basic_spec t)) (pend_spec s) before
      print "\n"
   fun addInstructionClass s =
      ( print (" " ^ s)
      ; if Redblackset.member (!spec_label_set, s)
           then ()
        else ( pend_spec s
             ; spec_label_set := Redblackset.add (!spec_label_set, s)
             )
      )
   fun arm8_spec_hex looped s =
      let
         val opc = string_to_opcode s
      in
         case find_spec opc of
         (*
         val SOME (new, thms) = find_spec opc
         *)
            SOME (new, thms) =>
              let
                 val l = List.mapPartial (Lib.total (spec_spec opc)) thms
              in
                 if List.null l
                    then loop looped opc "failed to find suitable spec" s
                 else (if new then print "\n" else ();  mk_thm_set l)
              end
          | NONE => loop looped opc "failed to add suitable spec" s
      end
   and loop looped opc e s =
      if looped
         then raise ERR "arm8_spec_hex" (e ^ ": " ^ s)
      else ( case arm8_stepLib.arm8_instruction opc of
             (*
             val SOME s = arm8_stepLib.arm8_instruction opc
             val () = addInstructionClass s
             *)
                SOME s => addInstructionClass s
              | NONE => raise ERR "arm8_spec_hex" "not supported"
           ; arm8_spec_hex true s)
   val arm8_spec_hex = arm8_spec_hex false
   val arm8_spec_code = List.map arm8_spec_hex o arm8AssemblerLib.arm8_code
end

(* ------------------------------------------------------------------------ *)

(* Testing...

open arm8_progLib

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
end

val random = random_hex o Option.valOf o arm8_stepLib.arm8_pattern

val hex = List.map random arm8_stepLib.arm8_names

val failed = ref ([] : string list)

val l = Lib.mapfilter
           (fn s => (print (s ^ "\n"); arm8_spec_hex s)
                    handle e as HOL_ERR _ =>
                       (failed := s :: !failed; raise e)) (failed := []; hex)

List.map arm8_stepLib.arm8_decode_hex (!failed)

val () = arm8_config "map-reg"
val () = arm8_config "temporal"
val () = arm8_config "not-temporal"
val () = arm8_config "map8"
val () = arm8_config "map32"
val () = arm8_config "map64"
val () = arm8_config "array32"
val () = arm8_config "array64"
val () = arm8_config "flat"

arm8_spec_hex (random "AddSubShiftedRegister32-1")
arm8_spec_hex (random "BranchRegisterJMP")
arm8_spec_hex (random "LoadStoreImmediate-1-1")
arm8_spec_hex (random "LoadStoreImmediate-1-2")
arm8_spec_hex (random "LoadStoreImmediate-1-3")
arm8_spec_hex (random "LoadStoreImmediate-1-4")
arm8_spec_hex (random "LoadStoreImmediate-2-3")
arm8_spec_hex (random "LoadStoreImmediate-2-5")

val thm = hd (arm8_spec_hex (random "LoadLiteral-2"))
val thm = hd (arm8_spec_hex (random "LoadLiteral-3"))
val thm = hd (arm8_spec_hex (random "LoadLiteral-4"))

*)

(* ------------------------------------------------------------------------ *)

end
