structure m0_progLib :> m0_progLib =
struct

open HolKernel boolLib bossLib
open stateLib m0_progTheory

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
in
   val m0_1 =
      HolKernel.syntax_fns "m0_prog" 2 HolKernel.dest_monop HolKernel.mk_monop
   val m0_2 =
      HolKernel.syntax_fns "m0_prog" 3 HolKernel.dest_binop HolKernel.mk_binop
   val byte = wordsSyntax.mk_int_word_type 8
   val half = wordsSyntax.mk_int_word_type 16
   val word = wordsSyntax.mk_int_word_type 32
   val (_, mk_m0_MEM, dest_m0_MEM, is_m0_MEM) = m0_2 "m0_MEM"
   val (_, mk_m0_REG, dest_m0_REG, is_m0_REG) = m0_2 "m0_REG"
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
      [(`K m0_c_PSR_N`,
        `\s:m0_state a w. s with PSR := psr with N := w`,
        `\s:m0_state. s with PSR := psr`),
       (`K m0_c_PSR_Z`,
        `\s:m0_state a w. s with PSR := psr with Z := w`,
        `\s:m0_state. s with PSR := psr`),
       (`K m0_c_PSR_C`,
        `\s:m0_state a w. s with PSR := psr with C := w`,
        `\s:m0_state. s with PSR := psr`),
       (`K m0_c_PSR_V`,
        `\s:m0_state a w. s with PSR := psr with V := w`,
        `\s:m0_state. s with PSR := psr`),
       (`K m0_c_count`,
        `\s:m0_state a w. s with count := c`,
        `\s:m0_state. s`),
       (`m0_c_REG`, `\s:m0_state a w. s with REG := (a =+ w) r`,
        `\s:m0_state. s with REG := r`),
       (`m0_c_MEM`, `\s:m0_state a w. s with MEM := (a =+ w) r`,
        `\s:m0_state. s with MEM := r`)
      ]

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
   stateLib.mk_pre_post m0_stepTheory.NextStateARM_def m0_instr_def
     m0_proj_def m0_comp_defs mk_m0_code_pool [] m0_write_footprint psort

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
in
   val REG_CONV = Conv.QCONV (REWRITE_CONV [R_main, m0_stepTheory.v2w_ground4])
   val REG_RULE = Conv.CONV_RULE REG_CONV o utilsLib.ALL_HYP_CONV_RULE REG_CONV
end

local
   fun concat_unzip l = (List.concat ## List.concat) (ListPair.unzip l)
   val regs = List.mapPartial (Lib.total dest_m0_REG)
   fun instantiate (a, b) =
      if Term.is_var a then SOME (a |-> b)
      else if a = b then NONE
           else raise ERR "instantiate" "bad constant match"
   fun bits i =
      List.map bitstringSyntax.mk_b
         (utilsLib.padLeft false 4 (bitstringSyntax.int_to_bitlist i))
   fun dest_reg r =
      let
         val t = Term.rand r
         val l = case Lib.total bitstringSyntax.dest_v2w t of
                    SOME (l, _) => fst (listSyntax.dest_list l)
                  | NONE => bits (wordsSyntax.uint_of_word t)
      in
         List.length l = 4 orelse raise ERR "dest_reg" "assertion failed"
         ; l
      end
      handle HOL_ERR {message = s, ...} => raise ERR "dest_reg" s
   fun match_register (tm1, v1, _) (tm2, v2, v3) =
      let
         val _ = v3 = v2 orelse raise ERR "match_register" "changed"
         val l = case Lib.total reg_index tm1 of
                    SOME i => bits i
                  | NONE => dest_reg tm1
      in
         ((v2 |-> v1) ::
          List.mapPartial instantiate (ListPair.zip (dest_reg tm2, l)),
          [tm2])
      end
   fun exists_free l =
      List.exists (fn (t, _, _) => not (List.null (Term.free_vars t))) l
   fun groupings ok rs =
     rs |> utilsLib.partitions
        |> List.map
              (List.mapPartial
                  (fn l =>
                     let
                        val (unchanged, changed) =
                           List.partition (fn (_, a, b) => a = b) l
                     in
                        if 1 < List.length l andalso List.length changed < 2
                           andalso exists_free l
                           then SOME (changed @ unchanged)
                        else NONE
                     end))
        |> Lib.mk_set
        |> Lib.mapfilter
             (fn p =>
                concat_unzip
                  (List.map
                     (fn l =>
                        let
                           val (h, t) =
                              Lib.pluck
                                 (fn (tm, _, _) =>
                                    List.null (Term.free_vars tm)) l
                              handle
                                 HOL_ERR
                                   {message = "predicate not satisfied", ...} =>
                                   (hd l, tl l)
                           fun mtch x =
                              let
                                 val s = match_register h x
                              in
                                 Lib.assert ok (fst s); s
                              end
                        in
                           concat_unzip (List.map mtch t)
                        end) p))
   (* check that the pre-condition predictate (from "cond P" terms) is not
      violated *)
   fun assign_ok p =
      let
         val l = List.mapPartial (Lib.total progSyntax.dest_cond) p
         val c = boolSyntax.list_mk_conj l
      in
         fn s => utilsLib.rhsc (REG_CONV (Term.subst s c)) <> boolSyntax.F
      end
   val r15 = wordsSyntax.mk_wordii (15, 4)
   fun assume_not_pc r =
      Thm.ASSUME (boolSyntax.mk_neg (boolSyntax.mk_eq (r, r15)))
   fun star_subst s = List.map (utilsLib.rhsc o REG_CONV o Term.subst s)
   fun mk_assign f (p, q) =
      List.map
         (fn ((r1, a), (r2, b)) => (Lib.assert (op =) (r1, r2); (r1, a, b)))
         (ListPair.zip (f p, f q))
in
   fun combinations (thm, t) =
      let
         val (m, p, c, q) = progSyntax.dest_spec t
         val pl = progSyntax.strip_star p
         val ql = progSyntax.strip_star q
         val rs = mk_assign regs (pl, ql)
         val groups = groupings (assign_ok pl) rs
      in
         List.map
            (fn (s, d) =>
                let
                   val do_reg =
                      star_subst s o
                      List.filter
                         (fn tm => case Lib.total dest_m0_REG tm of
                                      SOME (a, _) => not (Lib.mem a d)
                                    | NONE => true)
                   val pl' = do_reg pl
                   val p' = progSyntax.list_mk_star pl'
                   val q' = progSyntax.list_mk_star (do_reg ql)
                   val rwts =
                      Lib.mapfilter (assume_not_pc o Term.rand o fst) (regs pl')
                   val NPC_CONV = Conv.QCONV (REWRITE_CONV rwts)
                in
                   (Conv.CONV_RULE NPC_CONV (REG_RULE (Thm.INST s thm)),
                    progSyntax.mk_spec
                       (m, p', Term.subst s c, utilsLib.rhsc (NPC_CONV q')))
                end) groups
      end
end

(* ------------------------------------------------------------------------ *)

local
   val aircr_ty = Type.mk_thy_type {Thy = "m0", Args = [], Tyop = "AIRCR"}
   fun rename f =
      let
         fun g (v, s, t) =
            case Lib.total (fst o Term.dest_var) v of
               SOME q => if String.sub (q, 0) = #"%"
                            then SOME (v |-> (f (s, t): term))
                         else NONE
             | NONE => NONE
      in
         fn tm =>
            case boolSyntax.dest_strip_comb tm of
               ("m0_prog$m0_PSR_N", [v]) => g (v, "n", Type.bool)
             | ("m0_prog$m0_PSR_Z", [v]) => g (v, "z", Type.bool)
             | ("m0_prog$m0_PSR_C", [v]) => g (v, "c", Type.bool)
             | ("m0_prog$m0_PSR_V", [v]) => g (v, "v", Type.bool)
             | ("m0_prog$m0_AIRCR", [v]) => g (v, "aircr", aircr_ty)
             | ("m0_prog$m0_count", [v]) => g (v, "count", numSyntax.num)
             | ("m0_prog$m0_REG", [x, v]) =>
                  let
                     val n = reg_index x
                  in
                     if n = 15 then NONE else g (v, "r" ^ Int.toString n, word)
                  end
             | ("m0_prog$m0_MEM", [_, v]) => SOME (v |-> f ("b", byte))
             | _ => NONE
      end
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
         val rp = List.mapPartial (Lib.total (fst o dest_m0_REG)) p
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
              THENC REWRITE_CONV [m0_stepTheory.Aligned_numeric]
              THENC NOT_F_CONV))
   val cnv =
      REG_CONV
      THENC check_unique_reg_CONV
      THENC PRE_COND_CONV
      THENC PRE_CONV WGROUND_RW_CONV
      THENC OPC_CONV (Conv.RAND_CONV bitstringLib.v2w_n2w_CONV)
      THENC POST_CONV WGROUND_RW_CONV
in
   fun simp_triple_rule thm =
      rename_vars (Conv.CONV_RULE cnv thm)
      handle FalseTerm => raise ERR "simp_triple_rule" "condition false"
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
   val m0_rwts =
      List.drop (utilsLib.datatype_rewrites "m0" ["m0_state", "PSR"], 1)
   val STATE_TAC = ASM_REWRITE_TAC m0_rwts
   val spec =
      stateLib.spec
           m0_progTheory.M0_IMP_SPEC
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
   fun m0_spec_opt opt =
      let
         val step = m0_stepLib.thumb_step opt
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
              List.map (fn x => (print "."; spec x)) thms_ts
           end
           before print (!newline)
      end
   val bigend = ref false
   val the_spec = ref (m0_spec_opt (!bigend, false))
   fun mk_bool_list l = listSyntax.mk_list (l, Type.bool)
   fun reverse_end b l =
      mk_bool_list (if b then List.drop (l, 8) @ List.take (l, 8) else l)
   fun mk_thumb2_pair tm =
      let
         val l = fst (listSyntax.dest_list tm)
         val r = reverse_end (!bigend)
      in
         if 16 < List.length l
            then let
                    val l1 = List.take (l, 16)
                    val l2 = List.drop (l, 16)
                 in
                    pairSyntax.mk_pair (r l1, r l2)
                 end
         else if !bigend
            then r l
         else tm
      end
   fun get_opcode thm =
      let
         val (_, _, c, _) = progSyntax.dest_spec (Thm.concl thm)
      in
         c |> pred_setSyntax.strip_set |> hd
           |> pairSyntax.dest_pair |> snd
           |> boolSyntax.rand
           |> bitstringSyntax.dest_v2w |> fst
           |> mk_thumb2_pair
      end
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
in
   fun set_newline s = newline := s
   fun m0_config opt =
      (the_spec := m0_spec_opt opt
       ; bigend := fst opt
       ; spec_rwts := utilsLib.mk_rw_net get_opcode [])
   fun m0_spec s = (!the_spec) s
   fun addInstructionClass s =
      if Redblackset.member (!spec_label_set, s)
         then false
      else (print s
            ; add_specs (m0_spec s)
            ; spec_label_set := Redblackset.add (!spec_label_set, s)
            ; true)
   fun m0_spec_hex looped =
      (* utilsLib.cache 1000 String.compare *)
        (fn s =>
            let
               val opc = m0_stepLib.hex_to_bits s
            in
               case find_spec opc of
                  SOME thms =>
                    let
                       val l = List.mapPartial (Lib.total (spec_spec opc)) thms
                    in
                       if List.null l
                          then loop looped opc "failed to find suitable spec" s
                       else l
                    end
                | NONE => loop looped opc "failed to add suitable spec" s
            end)
    and loop looped opc e s =
       if looped orelse
          not (addInstructionClass (m0_stepLib.thumb_instruction opc))
          then raise ERR "m0_spec_hex" (e ^ ": " ^ s)
       else m0_spec_hex true s
    val m0_spec_hex = m0_spec_hex false
end

(* ------------------------------------------------------------------------ *)

(* Testing...

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
