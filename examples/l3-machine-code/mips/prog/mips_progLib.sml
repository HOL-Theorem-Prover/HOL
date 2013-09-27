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

val mips_1 =
   HolKernel.syntax_fns "mips_prog" 2 HolKernel.dest_monop HolKernel.mk_monop
val mips_2 =
   HolKernel.syntax_fns "mips_prog" 3 HolKernel.dest_binop HolKernel.mk_binop
val byte = wordsSyntax.mk_int_word_type 8
val word5 = wordsSyntax.mk_int_word_type 5
val word = wordsSyntax.mk_int_word_type 32
val dword = wordsSyntax.mk_int_word_type 64
val (_, mk_mips_PC, _, _) = mips_1 "mips_PC"
val (_, mk_mips_MEM, dest_mips_MEM, is_mips_MEM) = mips_2 "mips_MEM"
val (_, mk_mips_gpr, dest_mips_gpr, is_mips_gpr) = mips_2 "mips_gpr"

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
         val pc_subst = Term.subst [``s.PC`` |-> pc]
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
       ["CP0", "LLbit", "PC", "gpr"],
       ["CP0", "PC"],
       ["CP0", "HLStatus", "PC"],
       ["CP0", "HLStatus", "PC", "gpr"],
       ["CP0", "HLStatus", "LO", "PC"],
       ["CP0", "HI", "HLStatus", "PC"],
       ["CP0", "HI", "HLStatus", "LO", "PC"],
       ["CP0", "MEM", "PC"],
       ["MEM", "PC"],
       ["gpr"]]

val CP0_id =
   utilsLib.mk_state_id_thm mipsTheory.CP0_component_equality [["Status"]]

val mips_frame =
   update_frame_state_thm mips_proj_def
      [
       (`K mips_c_CP0_Count`,
        `\s:mips_state a w. s with CP0 := cp0 with Count := w`,
        `\s:mips_state. s with CP0 := cp0`),
       (`K mips_c_CP0_Cause`,
        `\s:mips_state a w. s with CP0 := cp0 with Cause := w`,
        `\s:mips_state. s with CP0 := cp0`),
       (`K mips_c_CP0_EPC`,
        `\s:mips_state a w. s with CP0 := cp0 with EPC := w`,
        `\s:mips_state. s with CP0 := cp0`),
       (`K mips_c_CP0_Debug`,
        `\s:mips_state a w. s with CP0 := cp0 with Debug := w`,
        `\s:mips_state. s with CP0 := cp0`),
       (`K mips_c_CP0_ErrCtl`,
        `\s:mips_state a w. s with CP0 := cp0 with ErrCtl := w`,
        `\s:mips_state. s with CP0 := cp0`),
       (`K mips_c_CP0_Status_EXL`,
        `\s:mips_state a w.
            s with CP0 := cp0 with Status := status with EXL := w`,
        `\s:mips_state. s with CP0 := cp0 with Status := status`),
       (`K mips_c_PC`,
        `\s:mips_state a w. s with PC := w`,
        `I: mips_state -> mips_state`),
       (`K mips_c_BranchStatus`,
        `\s:mips_state a w. s with BranchStatus := w`,
        `I: mips_state -> mips_state`),
       (`K mips_c_LLbit`,
        `\s:mips_state a w. s with LLbit := w`,
        `I: mips_state -> mips_state`),
       (`K mips_c_HI`,
        `\s:mips_state a w. s with HI := w`,
        `I: mips_state -> mips_state`),
       (`K mips_c_LO`,
        `\s:mips_state a w. s with LO := w`,
        `I: mips_state -> mips_state`),
       (`K mips_c_HLStatus`,
        `\s:mips_state a w. s with HLStatus := w`,
        `I: mips_state -> mips_state`),
       (`mips_c_gpr`, `\s:mips_state a w. s with gpr := (a =+ w) r`,
        `\s:mips_state. s with gpr := r`),
       (`mips_c_MEM`, `\s:mips_state a w. s with MEM := (a =+ w) r`,
        `\s:mips_state. s with MEM := r`)
      ]

(* -- *)

local
   fun other_index tm =
      case fst (Term.dest_const (boolSyntax.rator tm)) of
         "cond" => 0
       | "mips_exception" => 1
       | "mips_CP0_Status_RE" => 2
       | "mips_CP0_Status_EXL" => 3
       | "mips_CP0_Status_BEV" => 4
       | "mips_CP0_Config_BE" => 5
       | "mips_CP0_Count" => 6
       | "mips_CP0_Cause" => 7
       | "mips_CP0_EPC" => 8
       | "mips_CP0_Debug" => 9
       | "mips_CP0_ErrCtl" => 10
       | "mips_BranchStatus" => 11
       | "mips_LLbit" => 12
       | "mips_HLStatus" => 13
       | "mips_HI" => 14
       | "mips_LO" => 15
       | "mips_PC" => 16
       | _ => ~1
   val total_dest_lit = Lib.total wordsSyntax.dest_word_literal
   fun word_compare (w1, w2) =
      case (total_dest_lit w1, total_dest_lit w2) of
         (SOME x1, SOME x2) => Arbnum.compare (x1, x2)
       | (SOME _, NONE) => General.GREATER
       | (NONE, SOME _) => General.LESS
       | (NONE, NONE) => Term.compare (w1, w2)
   val register = fst o dest_mips_gpr
   val address = HolKernel.strip_binop (Lib.total wordsSyntax.dest_word_add) o
                 fst o dest_mips_MEM
in
   fun psort p =
      let
         val (m, rst) = List.partition is_mips_MEM p
         val (r, rst) = List.partition is_mips_gpr rst
      in
         mlibUseful.sort_map other_index Int.compare rst @
         mlibUseful.sort_map register word_compare r @
         mlibUseful.sort_map address (mlibUseful.lex_list_order word_compare) m
      end
end

local
   val st = Term.mk_var ("s", ``:mips_state``)
   val cp0_status_write_footprint =
      stateLib.write_footprint mips_1 mips_2 [] []
         [("mips$StatusRegister_EXL_fupd", "mips_CP0_Status_EXL")]
         []
         (fn (s, l) => s = "mips$CP0_Status" andalso l = [``^st.CP0``])
   val cp0_write_footprint =
      stateLib.write_footprint mips_1 mips_2 []
         [("mips$CP0_Cause_fupd", "mips_CP0_Cause"),
          ("mips$CP0_EPC_fupd", "mips_CP0_EPC"),
          ("mips$CP0_Debug_fupd", "mips_CP0_Debug"),
          ("mips$CP0_ErrCtl_fupd", "mips_CP0_ErrCtl")]
         [("mips$CP0_Count_fupd", "mips_CP0_Count")]
         [("mips$CP0_Status_fupd", cp0_status_write_footprint)]
         (fn (s, l) => s = "mips$mips_state_CP0" andalso l = [st])
in
   val mips_write_footprint =
      stateLib.write_footprint mips_1 mips_2
         [("mips$mips_state_MEM_fupd", "mips_MEM", ``^st.MEM``),
          ("mips$mips_state_gpr_fupd", "mips_gpr", ``^st.gpr``)]
         [("mips$mips_state_HI_fupd", "mips_HI"),
          ("mips$mips_state_LO_fupd", "mips_LO"),
          ("mips$mips_state_HLStatus_fupd", "mips_HLStatus"),
          ("mips$mips_state_LLbit_fupd", "mips_LLbit")]
         [("mips$mips_state_PC_fupd", "mips_PC"),
          ("mips$mips_state_BranchStatus_fupd", "mips_BranchStatus")]
         [("mips$mips_state_CP0_fupd", cp0_write_footprint)]
         (K false)
end

val mips_mk_pre_post =
   stateLib.mk_pre_post
     mips_progTheory.MIPS_MODEL_def mips_comp_defs mk_mips_code_pool []
     mips_write_footprint psort

(* ------------------------------------------------------------------------ *)

local
   val reg = Lib.total (Int.toString o wordsSyntax.uint_of_word)
   val CauseRegister_ty = ``:CauseRegister``
   val HLStatus_ty = ``:HLStatus``
   val obool_ty = ``:bool option``
   fun rename f =
      fn tm =>
         case boolSyntax.dest_strip_comb tm of
            ("mips_prog$mips_CP0_Count", [v]) => SOME (v |-> f ("count", word))
          | ("mips_prog$mips_CP0_Cause", [v]) =>
               SOME (v |-> f ("cause", CauseRegister_ty))
          | ("mips_prog$mips_CP0_EPC", [v]) => SOME (v |-> f ("epc", dword))
          | ("mips_prog$mips_CP0_Status_BEV", [v]) =>
               SOME (v |-> f ("bev", bool))
          | ("mips_prog$mips_LLbit", [v]) => SOME (v |-> f ("llbit", obool_ty))
          | ("mips_prog$mips_HLStatus", [v]) =>
               SOME (v |-> f ("hlstatus", HLStatus_ty))
          | ("mips_prog$mips_HI", [v]) => SOME (v |-> f ("hi", dword))
          | ("mips_prog$mips_LO", [v]) => SOME (v |-> f ("lo", dword))
          | ("mips_prog$mips_gpr", [x, v]) =>
               Option.map (fn n => v |-> f ("r" ^ n, dword)) (reg x)
          | ("mips_prog$mips_MEM", [_, v]) => SOME (v |-> f ("b", byte))
          | _ => NONE
in
   fun rename_vars thm =
      let
         val (_, p, _, _) = progSyntax.dest_spec (Thm.concl thm)
         val () = stateLib.varReset()
         val _ = stateLib.gvar "b" Type.bool
         val avoid = utilsLib.avoid_name_clashes p o Lib.uncurry stateLib.gvar
         val p = progSyntax.strip_star p
      in
         Thm.INST (List.mapPartial (rename avoid) p) thm
      end
      handle e as HOL_ERR _ => Raise e
end

local
   fun check_unique_reg_CONV tm =
      let
         val (_, p, _, _) = progSyntax.dest_spec tm
         val p = progSyntax.strip_star p
         val rp = List.mapPartial (Lib.total (fst o dest_mips_gpr)) p
      in
         if Lib.mk_set rp = rp
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
      THENC POST_CONV WGROUND_RW_CONV
in
   fun simp_triple_rule thm =
      rename_vars (Conv.CONV_RULE cnv thm)
      handle FalseTerm => raise ERR "simp_triple_rule" "condition false"
end

local
   val ty5 = ``:5``
   fun REG_CONV tm =
      if Lib.total wordsSyntax.dim_of tm = SOME ty5
         then bitstringLib.v2w_n2w_CONV tm
      else raise ERR "REG_CONV" ""
   fun is_reg_neq tm =
      case Lib.total boolSyntax.dest_neg tm of
         SOME etm =>
            (case Lib.total (fst o boolSyntax.dest_eq) etm of
               SOME r => (case Lib.total (snd o bitstringSyntax.dest_v2w) r of
                            SOME ty => ty = ty5
                          | NONE => false)
             | NONE => false)
       | NONE => false
   val dest_v2w_reg =
      fst o listSyntax.dest_list o fst o bitstringSyntax.dest_v2w
   fun dest_reg tm =
      case Lib.total dest_v2w_reg tm of
         SOME l => l
       | NONE => dest_reg (bitstringSyntax.padded_fixedwidth_of_int
                              (wordsSyntax.uint_of_word tm, 5))
   val join =
      fn ([(s1 as {redex = r1, residue = d1} :: l1, l2)],
          [(s2 as {redex = r2, residue = d2} :: l3, l4)]) =>
             [([{redex = r1, residue = Term.subst s2 d1},
                {redex = r2, residue = Term.subst s1 d2}] @ l1 @ l3,
              l2 @ l4)]
       | _ => []
   fun match_reg ((r1, b1, a1), (r2, b2, a2)) =
      let
         val l1 = dest_reg r1
         val l2 = dest_reg r2
      in
         if List.all Term.is_var l1 andalso b1 = a1
            then [((b1 |-> b2) :: List.map (op |->) (ListPair.zip (l1, l2)),
                   [r1])]
         else if List.all Term.is_var l2 andalso b2 = a2
            then [((b1 |-> b2) :: List.map (op |->) (ListPair.zip (l2, l1)),
                   [r2])]
         else []
      end
   fun delete_regs ds =
      List.filter (fn tm => case Lib.total dest_mips_gpr tm of
                               SOME (a, _) => not (Lib.mem a ds)
                             | NONE => true)
   fun subst_delete f ds = progSyntax.list_mk_star o List.map f o delete_regs ds
   val regs = List.mapPartial (Lib.total dest_mips_gpr)
   fun mk_assign (p, q) =
      List.map
         (fn ((r1, a), (r2, b)) => (Lib.assert (op =) (r1, r2); (r1, a, b)))
         (ListPair.zip (regs p, regs q))
   val x = Term.mk_var ("x", Type.alpha)
   val y = Term.mk_var ("y", Type.alpha)
   fun cond_neq_conv l =
      let
         val thms = List.map Thm.ASSUME l
         val cnv = REWRITE_CONV thms
         fun mk_neq_cond tm = boolSyntax.mk_cond (boolSyntax.dest_neg tm, x, y)
      in
         Conv.QCONV
            (Conv.DEPTH_CONV REG_CONV
             THENC Conv.DEPTH_CONV wordsLib.word_EQ_CONV
             THENC REWRITE_CONV (List.map (cnv o mk_neq_cond) l))
      end
in
   fun combinations (thm, t) =
      let
         val (m, p, c, q) = progSyntax.dest_spec t
         val pl = progSyntax.strip_star p
         val ql = progSyntax.strip_star q
         val rs = mk_assign (pl, ql)
         val rh = Lib.filter is_reg_neq (Thm.hyp thm)
         val groups =
            case rs of
               [r1, r2] => match_reg (r1, r2)
             | [r1 as (_, b1, a1), r2 as (_, b2, a2), r3 as (_, b3, a3)] =>
                  let
                     val m12 = match_reg (r1, r2)
                     val m23 = match_reg (r2, r3)
                     val m13 = match_reg (r1, r3)
                  in
                     m12 @ m23 @ m13 @
                     (if b1 <> a1
                         then join (m12, m13)
                      else if b2 <> a2
                         then join (m12, m23)
                      else if b3 <> a3
                         then join (m13, m23)
                      else [])
                  end
             | _ => []
      in
         List.map
            (fn (s, ds) =>
               let
                  val sbst = Term.subst s
                  val l = List.map sbst rh
                  val cnv = cond_neq_conv l
                  val f = utilsLib.rhsc o cnv o sbst
                  val p' = subst_delete f ds pl
                  val q' = subst_delete f ds ql
               in
                  (thm |> Thm.INST s
                       |> Drule.DISCH_ALL
                       |> Conv.CONV_RULE cnv
                       |> Drule.UNDISCH_ALL,
                   progSyntax.mk_spec (m, p', sbst c, q'))
               end) groups
      end
end

local
   val component_11 =
      (case Drule.CONJUNCTS mips_progTheory.mips_component_11 of
          [r, m] => [r, m]
        | _ => raise ERR "component_11" "")
   val mips_rwts = List.drop (utilsLib.datatype_rewrites "mips"
                                ["mips_state", "CP0", "StatusRegister"], 1)
   val STATE_TAC = ASM_REWRITE_TAC mips_rwts
in
   val spec =
      stateLib.spec
           mips_progTheory.MIPS_IMP_SPEC
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
                           (thm, t) :: combinations (thm, t)
                        end) thms
            in
               List.map (fn x => (print "."; spec x)) (List.concat thm_ts)
            end
      end
end

local
   fun get_opcode thm =
      let
         val (_, _, c, _) = progSyntax.dest_spec (Thm.concl thm)
      in
         c |> pred_setSyntax.strip_set |> hd
           |> pairSyntax.dest_pair |> snd
           |> bitstringSyntax.dest_v2w |> fst
      end
   val the_spec = ref (mips_spec_opt false)
   val spec_label_set = ref (Redblackset.empty String.compare)
   val spec_rwts = ref (utilsLib.mk_rw_net get_opcode [])
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
in
   fun mips_config be =
      (the_spec := mips_spec_opt be
       ; spec_label_set := Redblackset.empty String.compare
       ; spec_rwts := utilsLib.mk_rw_net get_opcode [])
   fun mips_spec s = (!the_spec) s
   fun addInstruction (s, tm) =
      if Redblackset.member (!spec_label_set, s)
         then false
      else (print s
            ; add_specs (mips_spec tm)
            ; print "\n"
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
                     if List.exists addInstruction l
                        then mips_spec_hex () s
                     else err e s
                  end
            in
               case find_spec opc of
                  SOME thms =>
                    (case List.mapPartial (Lib.total (spec_spec opc)) thms of
                       [] => loop "failed to find suitable spec"
                      | l as [_] => l
                      | l as [_, _] => l
                      | _ => err "more than two specs" s)
                | NONE => loop "failed to add suitable spec"
            end)
    val mips_spec_hex = mips_spec_hex ()
end

(* ------------------------------------------------------------------------ *)

(* Testing...

val imp_spec = MIPS_IMP_SPEC
val read_thms = [mips_stepTheory.get_bytes]
val write_thms = []: thm list
val select_state_thms = (mips_select_state_pool_thm :: mips_select_state_thms)
val frame_thms = [mips_frame, state_id, CP0_id]
val map_tys = [dword, word5]
val mk_pre_post = mips_mk_pre_post
val write = mips_write_footprint
val EXTRA_TAC = ALL_TAC

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

val () = mips_config false
val be = false
val tst = mips_spec
val tst = Count.apply mips_spec_hex o random_hex
val tst = mips_spec_hex o random_hex
val dec = Conv.CONV_RULE (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV) o
          mips_stepLib.mips_decode_hex

val d = List.filter (fn (s, _) => not (Lib.mem s ["MFC0", "MTC0"]))
           (Redblackmap.listItems mips_stepLib.mips_dict)

val l = List.map (I ## tst) d

mips_stepLib.mips_find_opc (mips_stepLib.hex_to_padded_opcode "9FA0AED9")

dec "9FA0AED9"

*)

(* ------------------------------------------------------------------------ *)

end
