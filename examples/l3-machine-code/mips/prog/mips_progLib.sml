structure mips_progLib :> mips_progLib =
struct

open HolKernel boolLib bossLib
open stateLib mips_progTheory

structure Parse =
struct
   open Parse
   val (Type, Term) = parse_from_grammars mips_progTheory.mips_prog_grammars
end

open Parse

val ERR = Feedback.mk_HOL_ERR "mips_progLib"

(* ------------------------------------------------------------------------ *)

val mips_proj_def = mips_progTheory.mips_proj_def
val mips_comp_defs = mips_progTheory.component_defs

fun syn n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "mips_prog"
val mips_1 = syn 2 HolKernel.dest_monop HolKernel.mk_monop
val mips_2 = syn 3 HolKernel.dest_binop HolKernel.mk_binop
val byte = wordsSyntax.mk_int_word_type 8
val word5 = wordsSyntax.mk_int_word_type 5
val word = wordsSyntax.mk_int_word_type 32
val dword = wordsSyntax.mk_int_word_type 64
val (_, _, dest_BranchTo, _) = mips_1 "mips_BranchTo"
val (_, _, dest_BranchDelay, _) = mips_1 "mips_BranchDelay"
val (_, mk_mips_PC, dest_mips_PC, _) = mips_1 "mips_PC"
val (_, mk_mips_MEM, dest_mips_MEM, is_mips_MEM) = mips_2 "mips_MEM"
val (_, mk_mips_gpr, dest_mips_gpr, is_mips_gpr) = mips_2 "mips_gpr"
val (_, mk_mips_FGR, dest_mips_FGR, is_mips_FGR) = mips_2 "mips_FGR"
val st = Term.mk_var ("s", ``:mips_state``)

(* -- *)

val mips_select_state_thms =
   List.map (fn t => star_select_state_thm mips_proj_def [] ([], t))
            mips_comp_defs

val mips_select_state_pool_thm =
   pool_select_state_thm mips_proj_def []
      (utilsLib.SRW_CONV
         [pred_setTheory.INSERT_UNION_EQ, stateTheory.CODE_POOL, mips_instr_def]
         ``CODE_POOL mips_instr {(pc, opc)}``)

local
   val mips_instr_tm =
      Term.prim_mk_const {Thy = "mips_prog", Name = "mips_instr"}
   fun is_mem_access v tm =
      case Lib.total boolSyntax.dest_eq tm of
         SOME (l, r) =>
            stateLib.is_code_access ("mips$mips_state_MEM", v) l andalso
            (wordsSyntax.is_word_literal r orelse bitstringSyntax.is_v2w r)
       | NONE => false
   val dest_opc = fst o listSyntax.dest_list o fst o bitstringSyntax.dest_v2w
   val ty32 = fcpSyntax.mk_int_numeric_type 32
   fun list_mk_concat l =
      bitstringSyntax.mk_v2w
         (listSyntax.mk_list
            (List.concat (List.map dest_opc l), Type.bool), ty32)
in
   fun mk_mips_code_pool thm =
      let
         val pc = stateLib.gvar "pc" dword
         val pc_a = mk_mips_PC pc
         val (a, tm) = Thm.dest_thm thm
         val pc_subst = Term.subst [``^st.PC`` |-> pc]
         val a = List.map pc_subst a
         val (m, a) = List.partition (is_mem_access pc) a
         val m = List.map dest_code_access m
         val m = mlibUseful.sort_map fst Int.compare m
         val opc = list_mk_concat (List.map snd (List.rev m))
      in
         (pc_a,
          boolSyntax.rand (stateLib.mk_code_pool (mips_instr_tm, pc, opc)),
          list_mk_imp (a, pc_subst tm))
      end
end

(* -- *)

val state_id =
   utilsLib.mk_state_id_thm mipsTheory.mips_state_component_equality
      [["CP0", "PC", "gpr"],
       ["CP0", "PC", "exceptionSignalled", "fcsr"],
       ["CP0", "PC", "exceptionSignalled", "gpr"],
       ["CP0", "PC", "exceptionSignalled"],
       ["CP0", "PC", "exceptionSignalled", "hi"],
       ["CP0", "PC", "exceptionSignalled", "lo"],
       ["CP0", "PC", "exceptionSignalled", "hi", "lo"],
       ["CP0", "PC", "exceptionSignalled", "gpr", "hi", "lo"],
       ["CP0", "LLbit", "PC"],
       ["CP0", "LLbit", "PC", "exceptionSignalled"],
       ["CP0", "LLbit", "PC", "exceptionSignalled", "gpr"],
       ["CP0", "LLbit", "PC", "gpr"],
       ["CP0", "PC"],
       ["CP0", "PC", "lo"],
       ["CP0", "PC", "hi"],
       ["CP0", "PC", "hi", "lo"],
       ["CP0", "PC", "gpr", "hi", "lo"],
       ["CP0", "LLbit", "MEM", "PC"],
       ["CP0", "LLbit", "MEM", "PC", "exceptionSignalled"],
       ["CP0", "MEM", "PC"],
       ["CP0", "MEM", "PC", "exceptionSignalled", "gpr"],
       ["MEM", "PC", "exceptionSignalled"],
       ["MEM", "PC", "exceptionSignalled", "gpr"],
       ["MEM", "PC"],
       ["CP0", "FGR", "PC", "exceptionSignalled"],
       ["FGR", "PC", "exceptionSignalled"],
       ["gpr", "hi", "lo"],
       ["gpr"],
       ["fcsr"]]

val CP0_id =
   utilsLib.mk_state_id_thm mipsTheory.CP0_component_equality [["Status"]]

val mips_frame =
   stateLib.update_frame_state_thm mips_proj_def
     (List.map (fn s => "CP0." ^ s)
         ["Count", "Cause", "EPC", "Debug", "ErrCtl", "LLAddr",
          "Status.ERL", "Status.EXL", "Status.CU1"] @
      ["PC", "BranchDelay", "BranchTo", "exceptionSignalled", "LLbit",
       "hi", "lo", "gpr", "fcsr.FCC", "MEM", "FGR"])

(* -- *)

local
   fun dest_const tm =
     Term.dest_const tm
     handle e as HOL_ERR {message = "not a const", ...} =>
            (Parse.print_term tm; print "\n"; raise e)
   val l =
      [
       "cond", "mips_exception", "mips_exceptionSignalled",
       "mips_CP0_Status_RE", "mips_CP0_Status_ERL", "mips_CP0_Status_EXL",
       "mips_CP0_Status_BEV", "mips_CP0_Status_CU1", "mips_CP0_Config_BE",
       "mips_CP0_Count", "mips_CP0_Cause", "mips_CP0_EPC", "mips_CP0_Debug",
       "mips_CP0_ErrCtl", "mips_fcsr_FS", "mips_fcsr_RM", "mips_BranchDelay",
       "mips_BranchTo", "mips_LLbit", "mips_hi", "mips_lo", "mips_PC"
      ]
   val m = ListPair.zip (l, Lib.mapi (fn i => Lib.K i) l)
   fun other_index tm =
      Option.getOpt
        (Option.map snd (Lib.assoc1 (fst (dest_const (boolSyntax.rator tm))) m),
         ~1)
   val total_dest_lit = Lib.total wordsSyntax.dest_word_literal
   fun word_compare (w1, w2) =
      case (total_dest_lit w1, total_dest_lit w2) of
         (SOME x1, SOME x2) => Arbnum.compare (x1, x2)
       | (SOME _, NONE) => General.GREATER
       | (NONE, SOME _) => General.LESS
       | (NONE, NONE) => Term.compare (w1, w2)
   val register = fst o dest_mips_gpr
   val fp_register = fst o dest_mips_FGR
   val address = HolKernel.strip_binop (Lib.total wordsSyntax.dest_word_add) o
                 fst o dest_mips_MEM
in
   fun psort p =
      let
         val (m, rst) = List.partition is_mips_MEM p
         val (r, rst) = List.partition is_mips_gpr rst
         val (f, rst) = List.partition is_mips_FGR rst
      in
         mlibUseful.sort_map other_index Int.compare rst @
         mlibUseful.sort_map register word_compare r @
         mlibUseful.sort_map fp_register word_compare f @
         mlibUseful.sort_map address (mlibUseful.lex_list_order word_compare) m
      end
end

local
   val cp0_status_write_footprint =
      stateLib.write_footprint mips_1 mips_2 [] []
         [("mips$StatusRegister_ERL_fupd", "mips_CP0_Status_ERL"),
          ("mips$StatusRegister_EXL_fupd", "mips_CP0_Status_EXL")]
         []
         (fn (s, l) => s = "mips$CP0_Status" andalso tmleq l [``^st.CP0``])
   val cp0_write_footprint =
      stateLib.write_footprint mips_1 mips_2 []
         [("mips$CP0_Cause_fupd", "mips_CP0_Cause"),
          ("mips$CP0_EPC_fupd", "mips_CP0_EPC"),
          ("mips$CP0_Debug_fupd", "mips_CP0_Debug"),
          ("mips$CP0_LLAddr_fupd", "mips_CP0_LLAddr"),
          ("mips$CP0_ErrCtl_fupd", "mips_CP0_ErrCtl")]
         [("mips$CP0_Count_fupd", "mips_CP0_Count")]
         [("mips$CP0_Status_fupd", cp0_status_write_footprint)]
         (fn (s, l) => s = "mips$mips_state_CP0" andalso tmleq l [st])
   val fcsr_write_footprint =
      stateLib.write_footprint mips_1 mips_2 [] []
         [("mips$FCSR_FCC_fupd", "mips_fcsr_FCC")]
         []
         (fn (s, l) => s = "mips$mips_state_fcsr" andalso tmleq l [st])
in
   val mips_write_footprint =
      stateLib.write_footprint mips_1 mips_2
        [("mips$mips_state_MEM_fupd", "mips_MEM", ``^st.MEM``),
         ("mips$mips_state_gpr_fupd", "mips_gpr", ``^st.gpr``),
         ("mips$mips_state_FGR_fupd", "mips_FGR", ``^st.FGR``)]
        [("mips$mips_state_hi_fupd", "mips_hi"),
         ("mips$mips_state_lo_fupd", "mips_lo"),
         ("mips$mips_state_exceptionSignalled_fupd", "mips_exceptionSignalled"),
         ("mips$mips_state_LLbit_fupd", "mips_LLbit"),
         ("mips$mips_state_BranchTo_fupd", "mips_BranchTo")]
        [("mips$mips_state_PC_fupd", "mips_PC"),
         ("mips$mips_state_BranchDelay_fupd", "mips_BranchDelay")]
        [("mips$mips_state_CP0_fupd", cp0_write_footprint),
         ("mips$mips_state_fcsr_fupd", fcsr_write_footprint)]
        (K false)
end

val mips_mk_pre_post =
   stateLib.mk_pre_post
     mips_progTheory.MIPS_MODEL_def mips_comp_defs mk_mips_code_pool []
     mips_write_footprint psort

(* ------------------------------------------------------------------------ *)

local
   val mips_rmap =
      Lib.total
        (fn "mips_prog$mips_CP0_Count" => K "count"
          | "mips_prog$mips_CP0_Cause" => K "cause"
          | "mips_prog$mips_CP0_EPC" => K "epc"
          | "mips_prog$mips_CP0_ErrorEPC" => K "errorpc"
          | "mips_prog$mips_CP0_Status_ERL" => K "erl"
          | "mips_prog$mips_CP0_Status_EXL" => K "exl"
          | "mips_prog$mips_CP0_Status_BEV" => K "bev"
          | "mips_prog$mips_fcsr_FS" => K "flush_to_zero"
          | "mips_prog$mips_fcsr_RM" => K "rounding_mode"
          | "mips_prog$mips_fcsr_FCC" => K "fcc"
          | "mips_prog$mips_fcsr_ABS2008" => K "abs2008"
          | "mips_prog$mips_LLbit" => K "llbit"
          | "mips_prog$mips_hi" => K "hi"
          | "mips_prog$mips_lo" => K "lo"
          | "mips_prog$mips_gpr" =>
              Lib.curry (op ^) "r" o Int.toString o wordsSyntax.uint_of_word o
              List.hd
          | "mips_prog$mips_FGR" =>
              Lib.curry (op ^) "f" o Int.toString o wordsSyntax.uint_of_word o
              List.hd
          | "mips_prog$mips_MEM" => K "b"
          | _ => fail())
in
   val mips_rename = stateLib.rename_vars (mips_rmap, ["b"])
end

fun spec_BranchTo th =
   let
      val p =
         progSyntax.strip_star (temporal_stateSyntax.dest_pre' (Thm.concl th))
   in
      case List.mapPartial (Lib.total dest_BranchTo) p of
         [v] => if Term.is_var v
                   then let
                           val ty = optionSyntax.dest_option (Term.type_of v)
                        in
                           Thm.INST [v |-> optionSyntax.mk_none ty] th
                        end
                else th
       | _ => th
   end
fun tdistinct tml = HOLset.numItems (listset tml) = length tml
local
   fun check_unique_reg_CONV tm =
      let
         val p = progSyntax.strip_star (temporal_stateSyntax.dest_pre' tm)
         val rp = List.mapPartial (Lib.total (fst o dest_mips_gpr)) p
         val fp = List.mapPartial (Lib.total (fst o dest_mips_FGR)) p
      in
         if tdistinct rp andalso tdistinct fp
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
   val OPT_CONV = REWRITE_CONV [optionTheory.IS_SOME_DEF]
   val OPC_CONV = POOL_CONV o Conv.RATOR_CONV o Conv.RAND_CONV o Conv.RAND_CONV
   exception FalseTerm
   fun NOT_F_CONV tm =
      if Feq tm then raise FalseTerm else Conv.ALL_CONV tm
   val WGROUND_RW_CONV =
      Conv.DEPTH_CONV (utilsLib.cache 10 Term.compare bitstringLib.v2w_n2w_CONV)
      THENC utilsLib.WGROUND_CONV
   val PRE_COND_CONV =
      PRE_CONV
         (DEPTH_COND_CONV
             (WGROUND_RW_CONV
              THENC REWRITE_CONV []
              THENC NOT_F_CONV))
   val cnv =
      check_unique_reg_CONV
      THENC PRE_COND_CONV
      THENC PRE_CONV WGROUND_RW_CONV
      THENC OPC_CONV bitstringLib.v2w_n2w_CONV
      THENC POST_CONV (WGROUND_RW_CONV THENC OPT_CONV)
in
   fun simp_triple_rule thm =
      mips_rename (Conv.CONV_RULE cnv thm)
      handle FalseTerm => raise ERR "simp_triple_rule" "condition false"
end

local
   val rwts =
      List.map bitstringLib.v2w_n2w_CONV
         (List.tabulate
            (32, fn i => bitstringSyntax.padded_fixedwidth_of_num
                           (Arbnum.fromInt i, 5)))
in
   val REG_CONV = Conv.QCONV (REWRITE_CONV rwts)
end

local
   val dest_reg = dest_mips_gpr
   val dest_fp_reg = dest_mips_FGR
   val reg_width = 5
   val proj_reg = NONE
   val reg_conv = REG_CONV
   val ok_conv = ALL_CONV
   fun asm_rule (tm : term) = (raise ERR "" "") : thm
   val model_tm = ``MIPS_MODEL``
   val reg_combinations =
      stateLib.register_combinations
         (dest_reg, reg_width, proj_reg, reg_conv, ok_conv, asm_rule, model_tm)
   val fp_reg_combinations =
      stateLib.register_combinations
         (dest_fp_reg, reg_width, proj_reg, reg_conv, ok_conv, asm_rule,
          model_tm)
in
  fun combinations thm_t =
     case fp_reg_combinations thm_t of
        [_] => reg_combinations thm_t
      | l => l
end

local
   val component_11 = Drule.CONJUNCTS mips_progTheory.mips_component_11
   val mips_rwts = List.drop (utilsLib.datatype_rewrites true "mips"
                                ["mips_state", "CP0", "StatusRegister",
                                 "FCSR"], 1)
   val STATE_TAC = ASM_REWRITE_TAC mips_rwts
in
   val spec =
      stateLib.introduce_triple_definition (false, mips_CONFIG_def) o
      mips_rename o spec_BranchTo o
      stateLib.spec
           mips_progTheory.MIPS_IMP_SPEC
           mips_progTheory.MIPS_IMP_TEMPORAL
           [mips_stepTheory.get_bytes]
           []
           (mips_select_state_pool_thm :: mips_select_state_thms)
           [mips_frame, state_id, CP0_id]
           component_11
           [dword, word5]
           ALL_TAC STATE_TAC
   fun mips_spec_opt be =
      let
         val step = mips_stepLib.mips_eval be
      in
         fn tm =>
            let
               val thms = step tm
               val thm_ts =
                  List.map
                     (fn thm =>
                        let
                           val t = mips_mk_pre_post thm
                        in
                           combinations (thm, t)
                        end) thms
            in
               List.map (fn x => (print "."; spec x)) (List.concat thm_ts)
            end
      end
end

local
   val get_opcode =
      fst o bitstringSyntax.dest_v2w o
      snd o pairSyntax.dest_pair o
      hd o pred_setSyntax.strip_set o
      temporal_stateSyntax.dest_code' o
      Thm.concl
   val the_spec = ref (mips_spec_opt true)
   val spec_label_set = ref (Redblackset.empty String.compare)
   val init_net = utilsLib.mk_rw_net (fn _ => raise ERR "" "") []
   val spec_rwts = ref init_net
   val add1 = utilsLib.add_to_rw_net get_opcode
   val add_specs = List.app (fn thm => spec_rwts := add1 (thm, !spec_rwts))
   fun find_spec opc = Lib.total (utilsLib.find_rw (!spec_rwts)) opc
   fun spec_spec opc thm =
      let
         val thm_opc = get_opcode thm
         val a = fst (Term.match_term thm_opc opc)
      in
         simp_triple_rule (Thm.INST a thm)
      end
   fun err e s = raise ERR "mips_spec_hex" (e ^ ": " ^ s)
   fun reverse_endian tm =
      let
         val (l, ty) = listSyntax.dest_list tm
      in
         listSyntax.mk_list (utilsLib.rev_endian l, ty)
      end
   val rev_endian = ref reverse_endian
   fun thm_eq thm1 thm2 = Term.aconv (Thm.concl thm1) (Thm.concl thm2)
   val mk_thm_set = Lib.op_mk_set thm_eq
in
   fun mips_config be =
      ( the_spec := mips_spec_opt be
      ; spec_label_set := Redblackset.empty String.compare
      ; spec_rwts := init_net
      ; rev_endian := (if be then reverse_endian else Lib.I)
      )
   fun mips_spec s = (!the_spec) s
   fun addInstruction (s, tm) =
      if Redblackset.member (!spec_label_set, s)
         then false
      else ( print s
           ; add_specs (mips_spec tm)
           ; spec_label_set := Redblackset.add (!spec_label_set, s)
           ; true)
   fun mips_spec_hex () =
      (* utilsLib.cache 1000 String.compare *)
        (fn s =>
            let
               val opc = mips_stepLib.hex_to_padded_opcode s
               fun loop e =
                  let
                     val l = mips_stepLib.mips_find_opc opc
                  in
                     if (print "\n"; List.exists addInstruction l)
                        then mips_spec_hex () s
                     else err e s
                  end
               val opc = !rev_endian opc
            in
               case find_spec opc of
                  SOME thms =>
                    let
                       val l = List.mapPartial (Lib.total (spec_spec opc)) thms
                    in
                       if List.null l
                          then loop "failed to find suitable spec"
                       else mk_thm_set l
                    end
                | NONE => loop "failed to add suitable spec"
            end)
   val mips_spec_hex = mips_spec_hex ()
   val mips_spec_code = mips_spec_hex o mips.encodeInstruction
end

local
   val MIPS_PC_INTRO0 =
      MIPS_PC_INTRO |> Q.INST [`p1`|->`emp`, `p2`|->`emp`]
                    |> PURE_REWRITE_RULE [set_sepTheory.SEP_CLAUSES]
   fun MP_MIPS_PC_INTRO th =
      Lib.tryfind (fn thm => MATCH_MP thm th)
         [MIPS_PC_INTRO, MIPS_PC_INTRO0]
in
   val mips_pc_intro_rule =
      Conv.CONV_RULE
         (Conv.LAND_CONV (REWRITE_CONV [alignmentTheory.aligned_numeric])
          THENC (Conv.REWR_CONV
                     (Thm.CONJUNCT1 (Drule.SPEC_ALL boolTheory.IMP_CLAUSES))
                 ORELSEC stateLib.MOVE_COND_CONV)
          THENC helperLib.POST_CONV (stateLib.PC_CONV "mips_prog$MIPS_PC")) o
      MP_MIPS_PC_INTRO o
      Conv.CONV_RULE
         (helperLib.POST_CONV
             (helperLib.MOVE_OUT_CONV ``mips_BranchDelay``
              THENC helperLib.MOVE_OUT_CONV ``mips_PC``)) o
      stateLib.introduce_triple_definition
         (false, mips_progTheory.MIPS_PC_def) o
      Conv.CONV_RULE
        (stateLib.PRE_COND_CONV
           (SIMP_CONV (bool_ss++boolSimps.CONJ_ss)
              [alignmentTheory.aligned_numeric])) o
      helperLib.MERGE_CONDS_RULE
   val spec_join_rule = helperLib.SPEC_COMPOSE_RULE o Lib.list_of_pair
end

val spec_hex =
   List.map
     (REWRITE_RULE [GSYM mips_LE_def, GSYM mips_BE_def] o
      Q.INST [`flush_to_zero` |-> `F`, `rounding_mode` |-> `0w`,
              `abs2008` |-> `T`]) o
   mips_spec_hex

val split_BranchDelay = stateLib.split_cond true dest_BranchDelay
val split_exception = stateLib.split_cond false dest_mips_PC

fun mips_spec_hex2 s =
   List.map mips_pc_intro_rule
   (case String.tokens Char.isSpace s of
      [s1] =>
        (case spec_hex s1 of
            [th, _] => [List.last (split_exception th)]
          | l => raise ERR "mips_spec2_hex" ("Expecting two theorems: " ^ s1))
     | [s1, s2] =>
        (case (spec_hex s1, spec_hex s2) of
            ([th1], [_, th2]) =>
              List.map (fn t => spec_join_rule (t, th2)) (split_BranchDelay th1)
          | _ => raise ERR "mips_spec2_hex" ("Expecting three theorems: " ^ s))
     | _ => raise ERR "mips_spec2_hex" ("More than two strings: " ^ s))

(* ------------------------------------------------------------------------ *)

(* Testing...

open mips_progLib

val imp_spec = MIPS_IMP_SPEC
val imp_temp = mips_progTheory.MIPS_IMP_TEMPORAL
val read_thms = [mips_stepTheory.get_bytes]
val write_thms = []: thm list
val select_state_thms = (mips_select_state_pool_thm :: mips_select_state_thms)
val frame_thms = [mips_frame, state_id, CP0_id]
val map_tys = [dword, word5]
val mk_pre_post = mips_mk_pre_post
val write = mips_write_footprint
val EXTRA_TAC = ALL_TAC

val () = mips_config false
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
      mips_spec_hex s
      handle e as HOL_ERR _ => (print ("\n\n" ^ s ^ "\n\n"); raise e)
end

val () = mips_config false
val be = false
val tst = mips_spec
val tst = Count.apply hex o random_hex
val tst = hex o random_hex
val dec = Conv.CONV_RULE (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV) o
          mips_stepLib.mips_decode_hex

val d = List.filter (fn (s, _) => not (Lib.mem s ["MFC0", "MTC0"]))
           (Redblackmap.listItems mips_stepLib.mips_dict)

val l = List.map (I ## tst) d

mips_stepLib.mips_find_opc (mips_stepLib.hex_to_padded_opcode "000C001E")

val s = random_hex (Redblackmap.find (mips_stepLib.mips_dict, "ERET"))
mips_spec (Redblackmap.find (mips_stepLib.mips_dict, "ERET"))

mips_spec_hex s

dec "9FA0AED9"

*)

(* ------------------------------------------------------------------------ *)

end
