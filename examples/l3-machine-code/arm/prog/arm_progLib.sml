structure arm_progLib :> arm_progLib =
struct

open HolKernel boolLib bossLib
open stateLib arm_progTheory

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
   val arm_1 =
      HolKernel.syntax_fns "arm_prog" 2 HolKernel.dest_monop HolKernel.mk_monop
   val arm_2 =
      HolKernel.syntax_fns "arm_prog" 3 HolKernel.dest_binop HolKernel.mk_binop
   val word2 = wordsSyntax.mk_int_word_type 2
   val word5 = wordsSyntax.mk_int_word_type 5
   val byte = wordsSyntax.mk_int_word_type 8
   val word = wordsSyntax.mk_int_word_type 32
   val dword = wordsSyntax.mk_int_word_type 64
   val (_, _, dest_arm_instr, _) = arm_1 "arm_instr"
   val (_, _, dest_arm_CPSR_E, _) = arm_1 "arm_CPSR_E"
   val (_, _, dest_arm_MEM, is_arm_MEM) = arm_2 "arm_MEM"
   val (_, mk_arm_REG, dest_arm_REG, is_arm_REG) = arm_2 "arm_REG"
   val (_, _, dest_arm_FP_REG, is_arm_FP_REG) = arm_2 "arm_FP_REG"
   val (_, _, dest_arm_Extensions, is_arm_Extensions) = arm_2 "arm_Extensions"
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
      [["FPSCR"]]

val arm_frame =
   stateLib.update_frame_state_thm arm_proj_def
      [(`K arm_c_CPSR_N`,
        `\s:arm_state a w. s with CPSR := cpsr with N := w`,
        `\s:arm_state. s with CPSR := cpsr`),
       (`K arm_c_CPSR_Z`,
        `\s:arm_state a w. s with CPSR := cpsr with Z := w`,
        `\s:arm_state. s with CPSR := cpsr`),
       (`K arm_c_CPSR_C`,
        `\s:arm_state a w. s with CPSR := cpsr with C := w`,
        `\s:arm_state. s with CPSR := cpsr`),
       (`K arm_c_CPSR_V`,
        `\s:arm_state a w. s with CPSR := cpsr with V := w`,
        `\s:arm_state. s with CPSR := cpsr`),
       (`K arm_c_CPSR_J`,
        `\s:arm_state a w. s with CPSR := cpsr with J := w`,
        `\s:arm_state. s with CPSR := cpsr`),
       (`K arm_c_CPSR_T`,
        `\s:arm_state a w. s with CPSR := cpsr with T := w`,
        `\s:arm_state. s with CPSR := cpsr`),
       (`K arm_c_CPSR_E`,
        `\s:arm_state a w. s with CPSR := cpsr with E := w`,
        `\s:arm_state. s with CPSR := cpsr`),
       (`K arm_c_FP_FPSCR_N`,
        `\s:arm_state a w. s with FP := fp with FPSCR := fpscr with N := w`,
        `\s:arm_state. s with FP := fp with FPSCR := fpscr`),
       (`K arm_c_FP_FPSCR_Z`,
        `\s:arm_state a w. s with FP := fp with FPSCR := fpscr with Z := w`,
        `\s:arm_state. s with FP := fp with FPSCR := fpscr`),
       (`K arm_c_FP_FPSCR_C`,
        `\s:arm_state a w. s with FP := fp with FPSCR := fpscr with C := w`,
        `\s:arm_state. s with FP := fp with FPSCR := fpscr`),
       (`K arm_c_FP_FPSCR_V`,
        `\s:arm_state a w. s with FP := fp with FPSCR := fpscr with V := w`,
        `\s:arm_state. s with FP := fp with FPSCR := fpscr`),
       (`arm_c_REG`, `\s:arm_state a w. s with REG := (a =+ w) r`,
        `\s:arm_state. s with REG := r`),
       (`arm_c_MEM`, `\s:arm_state a w. s with MEM := (a =+ w) r`,
        `\s:arm_state. s with MEM := r`),
       (`arm_c_FP_REG`,
        `\s:arm_state a w. s with FP := fp with REG := (a =+ w) fp.REG`,
        `\s:arm_state. s with FP := fp`)
      ]

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

   val list_mk_add_or_sub =
      List.foldl
         (fn ((b, t1), t2) =>
            if b then wordsSyntax.mk_word_add (t2, t1)
            else wordsSyntax.mk_word_sub (t2, t1)) pc_tm

   val strip_add_or_sub =
      let
         fun iter a t =
            case Lib.total wordsSyntax.dest_word_add t of
               SOME (l, r) => iter ((true, r) :: a) l
             | NONE => (case Lib.total wordsSyntax.dest_word_sub t of
                           SOME (l, r) => iter ((false, r) :: a) l
                         | NONE => if t = pc_tm then a else [])
      in
         iter []
      end

   fun is_byte_offset tm =
      case Lib.total wordsSyntax.uint_of_word tm of
         SOME i => 1 <= i andalso i <= 3
       | NONE => false

   val zero_offset = wordsSyntax.mk_wordii (0, 32)

   fun dest_pc_relative tm =
      case Lib.total ((strip_add_or_sub ## Lib.I) o dest_arm_MEM) tm of
         SOME (l as _ :: _, d) =>
            let
               val (b, tm) = List.last l
            in
               SOME (if b andalso is_byte_offset tm
                        then (tm, d, list_mk_add_or_sub (Lib.butlast l))
                     else (zero_offset, d, list_mk_add_or_sub l))
            end
       | _ => NONE

   val part_pc_relative =
      utilsLib.classes (fn ((_, _, a), (_, _, b)) => a = b) o
      (List.foldl (fn (tm, a) => case dest_pc_relative tm of
                                    SOME x => x :: a
                                  | NONE => a) [])

   fun get i =
      let
         val tm = wordsSyntax.mk_wordii (i, 32)
      in
         fn l =>
            case List.find (fn (j, _, _: term) => j = tm) l of
               SOME (_, d, _) => d
             | NONE => raise ERR "extend_arm_code_pool"
                                 ("missing byte: " ^ Int.toString i)
      end

   val CONCAT_BYTE_RULE = PURE_REWRITE_RULE [arm_stepTheory.concat_bytes]

   fun mk_w i = Term.mk_var ("w" ^ Int.toString i, word)
   val i8 = fcpSyntax.mk_int_numeric_type 8

   fun mk_byte (h, l) =
      let
         val hi = numSyntax.term_of_int h
         val li = numSyntax.term_of_int l
      in
         fn w => wordsSyntax.mk_word_extract (hi, li, w, i8)
      end

   val b0 = mk_byte (31, 24)
   val b1 = mk_byte (23, 16)
   val b2 = mk_byte (15, 8)
   val b3 = mk_byte (7, 0)

   val reverse_endian_tm =
      Term.prim_mk_const {Thy = "arm_step", Name = "reverse_endian"}
   fun mk_reverse_endian e tm =
      if e then Term.mk_comb (reverse_endian_tm, tm) else tm
   fun is_big_end tm =
      case Lib.total dest_arm_CPSR_E tm of
         SOME t => t = boolSyntax.T
       | NONE => false

   fun gen_words e =
      (List.rev ## List.concat) o ListPair.unzip o
      Lib.mapi
         (fn i => fn l =>
             let
                val a = case hd l of (_, _:term, a) => a
                val w = mk_reverse_endian e (mk_w i)
                val x = List.tabulate (4, fn j => get (3 - j) l)
             in
                ((a, w),
                 [List.nth (x, 3) |-> b3 w,
                  List.nth (x, 2) |-> b2 w,
                  List.nth (x, 1) |-> b1 w,
                  List.nth (x, 0) |-> b0 w])
             end)

   fun move_to_code ((a, w), thm) =
      REWRITE_RULE
        [stateTheory.BIGUNION_IMAGE_1, stateTheory.BIGUNION_IMAGE_2,
         set_sepTheory.STAR_ASSOC, set_sepTheory.SEP_CLAUSES,
         Drule.SPECL [a, w] arm_progTheory.MOVE_TO_ARM_CODE_POOL,
         arm_progTheory.disjoint_arm_instr_thms] thm

   val err = ERR "DISJOINT_CONV" ""
   val cnv =
      LAND_CONV wordsLib.WORD_EVAL_CONV
      THENC REWRITE_CONV [arm_progTheory.sub_intro]
   fun split_arm_instr tm =
      Lib.with_exn (pairSyntax.dest_pair o dest_arm_instr) tm err
in
   fun DISJOINT_CONV tm =
      let
         val (l, r) = Lib.with_exn pred_setSyntax.dest_disjoint tm err
         val (a, x) = split_arm_instr l
         val y = snd (split_arm_instr r)
         val a = case strip_add_or_sub a of
                    [(false, w)] => wordsSyntax.mk_word_2comp w
                  | [(false, w), (true, x)] =>
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
         val (spc, p, c, q) = progSyntax.dest_spec (Thm.concl thm)
         val lp = progSyntax.strip_star p
         val p_pc = part_pc_relative lp
      in
         if not (List.null p_pc) andalso
            List.all (Lib.equal 4 o List.length) p_pc andalso
            List.all (op =)
              (ListPair.zip (p_pc, part_pc_relative (progSyntax.strip_star q)))
            then let (* it's a well-formed load *)
                    val e = List.exists is_big_end lp
                    val (c_w, s) = gen_words e p_pc
                    val thm' = CONCAT_BYTE_RULE (Thm.INST s thm)
                 in
                    List.foldl move_to_code thm' c_w
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
       | "arm_CPSR_J" => 5
       | "arm_CPSR_E" => 6
       | "arm_CPSR_T" => 7
       | "arm_CPSR_M" => 8
       | "arm_CPSR_N" => 9
       | "arm_CPSR_Z" => 10
       | "arm_CPSR_C" => 11
       | "arm_CPSR_V" => 12
       | "arm_FP_FPSCR_N" => 13
       | "arm_FP_FPSCR_Z" => 14
       | "arm_FP_FPSCR_C" => 15
       | "arm_FP_FPSCR_V" => 16
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
         ("arm$PSR_E_fupd", "arm_CPSR_E")] [] []
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
   stateLib.mk_pre_post arm_stepTheory.NextStateARM_def arm_instr_def
     arm_proj_def arm_comp_defs mk_arm_code_pool [] arm_write_footprint psort

(* ------------------------------------------------------------------------ *)

val REG_CONV =
   Conv.QCONV
     (REWRITE_CONV
        [EVAL ``R_mode mode 15w``,
         arm_stepTheory.v2w_ground4, arm_stepTheory.v2w_ground5])

val REG_RULE = Conv.CONV_RULE REG_CONV o utilsLib.ALL_HYP_CONV_RULE REG_CONV

local
   fun concat_unzip l = (List.concat ## List.concat) (ListPair.unzip l)
   val regs = List.mapPartial (Lib.total dest_arm_REG)
   val fp_regs = List.mapPartial (Lib.total dest_arm_FP_REG)
   fun instantiate (a, b) =
      if Term.is_var a then SOME (a |-> b)
      else if a = b then NONE
           else raise ERR "instantiate" "bad constant match"
   fun bits n i =
      List.map bitstringSyntax.mk_b
         (utilsLib.padLeft false n (bitstringSyntax.int_to_bitlist i))
   fun dest_reg n r =
      let
         val t = if n = 4 then Term.rand r else r
         val l = case Lib.total bitstringSyntax.dest_v2w t of
                    SOME (l, _) => fst (listSyntax.dest_list l)
                  | NONE => bits n (wordsSyntax.uint_of_word t)
      in
         List.length l = n orelse raise ERR "dest_reg" "assertion failed"
         ; l
      end
      handle HOL_ERR {message = s, ...} => raise ERR "dest_reg" s
   fun match_register n (tm1, v1, _) (tm2, v2, _) =
      let
         val l = case Lib.total reg_index tm1 of
                    SOME i => bits n i
                  | NONE => dest_reg n tm1
      in
         ((v2 |-> v1) ::
          List.mapPartial instantiate (ListPair.zip (dest_reg n tm2, l)),
          [tm2])
      end
   fun exists_free l =
      List.exists (fn (t, _, _) => not (List.null (Term.free_vars t))) l
   fun groupings n ok rs =
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
                                 val s = match_register n h x
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
         val ds = mk_assign fp_regs (pl, ql)
         val (n, dst, rs) =
            if List.length ds < 2
               then (4, dest_arm_REG, mk_assign regs (pl, ql))
            else (5, dest_arm_FP_REG, ds)
         val groups = groupings n (assign_ok pl) rs
      in
         List.map
            (fn (s, d) =>
                let
                   val do_reg =
                      star_subst s o
                      List.filter
                         (fn tm => case Lib.total dst tm of
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
               ("arm_prog$arm_CPSR_N", [v]) => g (v, "n", Type.bool)
             | ("arm_prog$arm_CPSR_Z", [v]) => g (v, "z", Type.bool)
             | ("arm_prog$arm_CPSR_C", [v]) => g (v, "c", Type.bool)
             | ("arm_prog$arm_CPSR_V", [v]) => g (v, "v", Type.bool)
             | ("arm_prog$arm_CPSR_M", [v]) => g (v, "mode", word5)
             | ("arm_prog$arm_FP_FPSCR_N", [v]) => g (v, "fp_n", Type.bool)
             | ("arm_prog$arm_FP_FPSCR_Z", [v]) => g (v, "fp_z", Type.bool)
             | ("arm_prog$arm_FP_FPSCR_C", [v]) => g (v, "fp_c", Type.bool)
             | ("arm_prog$arm_FP_FPSCR_V", [v]) => g (v, "fp_v", Type.bool)
             | ("arm_prog$arm_FP_FPSCR_RMode", [v]) => g (v, "rmode", word2)
             | ("arm_prog$arm_FP_REG", [x, v]) =>
                 (case Lib.total (Int.toString o wordsSyntax.uint_of_word) x of
                     SOME s => g (v, "d" ^ s, dword)
                   | NONE => NONE)
             | ("arm_prog$arm_REG", [x, v]) =>
                  let
                     val n = reg_index x
                  in
                     if n = 15 then NONE else g (v, "r" ^ Int.toString n, word)
                  end
             | ("arm_prog$arm_MEM", [_, v]) => SOME (v |-> f ("b", byte))
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
         val (_, p, _, _) = progSyntax.dest_spec tm
         val p = progSyntax.strip_star p
         val rp = List.mapPartial (Lib.total (fst o dest_arm_REG)) p
         val dp = List.mapPartial (Lib.total (fst o dest_arm_FP_REG)) p
      in
         if Lib.mk_set rp = rp andalso Lib.mk_set dp = dp
            then Conv.ALL_CONV tm
         else raise ERR "check_unique_reg_CONV" "duplicate register"
      end
   val PRE_CONV = Conv.RATOR_CONV o Conv.RATOR_CONV o Conv.RAND_CONV
   fun DEPTH_COND_CONV cnv =
      Conv.ONCE_DEPTH_CONV
         (fn tm => if progSyntax.is_cond tm
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
             (DEPTH_CONV DISJOINT_CONV
              THENC REWRITE_CONV [arm_stepTheory.Aligned_numeric]
              THENC NOT_F_CONV))
   val cnv =
      REG_CONV
      THENC check_unique_reg_CONV
      THENC WGROUND_RW_CONV
      THENC PRE_COND_CONV
      THENC POST_CONV (PURE_REWRITE_CONV spec_rwts)
in
   fun simp_triple_rule thm =
      rename_vars (Conv.CONV_RULE cnv thm)
      handle FalseTerm => raise ERR "simp_triple_rule" "condition false"
end

local
   val a_tm = Term.mk_var ("a", ``:string set``)
   val k_thm =
      Drule.EQT_ELIM (Drule.ISPECL [boolSyntax.T, a_tm] combinTheory.K_THM)
in
   fun mk_strings_thm l =
      let
         val tm = pred_setSyntax.mk_set (List.map stringSyntax.fromMLstring l)
      in
         Thm.INST [a_tm |-> tm] k_thm
      end
   fun dest_strings_thm thm =
      thm |> Thm.concl
          |> combinSyntax.dest_K |> snd
          |> pred_setSyntax.strip_set
          |> List.map stringSyntax.fromHOLstring
end

local
   val component_11 =
      (case Drule.CONJUNCTS arm_progTheory.arm_component_11 of
          [r, m, _, fp] => [r, m, fp]
        | _ => raise ERR "component_11" "")
   val sym_R_x_pc =
      REWRITE_RULE [utilsLib.qm [] ``(a = RName_PC) = (RName_PC = a)``]
         arm_stepTheory.R_x_pc
   val EXTRA_TAC =
      RULE_ASSUM_TAC (REWRITE_RULE [sym_R_x_pc, arm_stepTheory.R_x_pc])
      THEN ASM_REWRITE_TAC [boolTheory.DE_MORGAN_THM]
   val arm_rwts =
      List.drop (utilsLib.datatype_rewrites "arm"
                   ["arm_state", "PSR", "FP", "FPSCR"], 1)
   val STATE_TAC = ASM_REWRITE_TAC arm_rwts
   val spec =
      extend_arm_code_pool o
      stateLib.spec
           arm_progTheory.ARM_IMP_SPEC
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
   val v3 = Term.mk_var ("x3", Type.bool)
   val v4 = Term.mk_var ("x4", Type.bool)
   val v5 = Term.mk_var ("x5", Type.bool)
   val v6 = Term.mk_var ("x6", Type.bool)
   val vn = listSyntax.mk_list ([v3, v4, v5, v6], Type.bool)
   val vn = bitstringSyntax.mk_v2w (vn, fcpSyntax.mk_int_numeric_type 4)
   val newline = ref "\n"
   fun arm_spec_opt opt =
      let
         val step = arm_stepLib.arm_step opt
      in
         fn s =>
           (if is_stm_wb s
               then let
                       val l = step s
                       val thm = hd l
                       val base = s |> utilsLib.splitAtChar (Char.isDigit)
                                    |> snd
                                    |> String.tokens (Lib.equal #",")
                                    |> List.map Arbnum.fromString
                                    |> mlibUseful.min Arbnum.compare
                                    |> fst
                                    |> Arbnum.toInt
                       val (x3, x4, x5, x6) =
                          utilsLib.padLeft false 4
                             (bitstringSyntax.int_to_bitlist base)
                          |> List.map bitstringSyntax.mk_b
                          |> Lib.quadruple_of_list
                       val thm1 =
                          REG_RULE
                            (Thm.INST [v3 |-> x3, v4 |-> x4,
                                       v5 |-> x5, v6 |-> x6] thm)
                       val thm2 =
                          Drule.ADD_ASSUM
                            (boolSyntax.mk_neg
                               (boolSyntax.mk_eq
                                  (vn, wordsSyntax.mk_wordii (base, 4)))) thm
                       val () = print "."
                       val spec1 = spec (thm1, arm_mk_pre_post thm1)
                       val () = print "."
                       val spec2 = spec (thm2, arm_mk_pre_post thm2)
                       val specs =
                          List.map
                             (fn t =>
                                (print "."
                                 ; spec (t, arm_mk_pre_post t))) (tl l)
                    in
                       [spec1, spec2] @ specs
                    end
            else let
                    val thms = step s
                    val ts = List.map arm_mk_pre_post thms
                    val thms_ts =
                       List.concat
                          (List.map combinations (ListPair.zip (thms, ts)))
                 in
                    List.map (fn x => (print "."; spec x)) thms_ts
                 end)
           before print (!newline)
      end
   val the_spec = ref (arm_spec_opt "")
   fun get_opcode thm =
      let
         val (_, _, c, _) = progSyntax.dest_spec (Thm.concl thm)
      in
         c |> pred_setSyntax.strip_set |> List.last
           |> pairSyntax.dest_pair |> snd
           |> bitstringSyntax.dest_v2w |> fst
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
   val mk_thm_set =
      Lib.op_mk_set (fn t1 => fn t2 => Term.aconv (Thm.concl t1) (Thm.concl t2))
   val reverse_endian =
      fn [a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, b8,
          c1, c2, c3, c4, c5, c6, c7, c8, d1, d2, d3, d4, d5, d6, d7, d8] =>
         [d1, d2, d3, d4, d5, d6, d7, d8, c1, c2, c3, c4, c5, c6, c7, c8,
          b1, b2, b3, b4, b5, b6, b7, b8, a1, a2, a3, a4, a5, a6, a7, a8]
       | _ => raise ERR "reverse_endian" ""
   val rev_endian = ref (Lib.I : term list -> term list)
   val is_be_tm = Term.aconv ``s.CPSR.E``
   fun set_endian opt =
      let
         val l = arm_configLib.mk_config_terms opt
      in
         if List.exists is_be_tm l
            then rev_endian := reverse_endian
         else rev_endian := Lib.I
      end
in
   fun set_newline s = newline := s
   fun arm_config opt =
      (the_spec := arm_spec_opt opt
       ; set_endian opt
       ; spec_label_set := Redblackset.empty String.compare
       ; spec_rwts := utilsLib.mk_rw_net get_opcode [])
   fun arm_spec s = (!the_spec) s
   fun saveSpecs name =
      Theory.save_thm (name,
         Drule.LIST_CONJ
            (mk_strings_thm (Redblackset.listItems (!spec_label_set)) ::
             List.map snd (LVTermNet.listItems (!spec_rwts))))
      handle HOL_ERR {message = "empty set", ...} =>
         raise ERR "saveSpecs" "there are no spec theorems to save"
   fun loadSpecs thm =
      let
         val l = Drule.CONJUNCTS thm
      in
         spec_label_set :=
            Redblackset.fromList String.compare (dest_strings_thm (hd l))
         ; add_specs (tl l)
      end
   fun addInstructionClass s =
      (print (" " ^ s)
       ; if Redblackset.member (!spec_label_set, s)
            then print (!newline)
         else (add_specs (arm_spec s)
               ; spec_label_set := Redblackset.add (!spec_label_set, s)))
   fun arm_spec_hex looped =
      (* utilsLib.cache 1000 String.compare *)
        (fn s =>
            let
               val i = arm_stepLib.hex_to_bits_32 s
               val opc = listSyntax.mk_list (!rev_endian i, Type.bool)
            in
               case find_spec opc of
                  SOME thms =>
                    let
                       val l = List.mapPartial (Lib.total (spec_spec opc)) thms
                    in
                       if List.null l
                          then loop looped i "failed to find suitable spec" s
                       else mk_thm_set l
                    end
                | NONE => loop looped i "failed to add suitable spec" s
            end)
    and loop looped i e s =
       if looped
          then raise ERR "arm_spec_hex" (e ^ ": " ^ s)
       else (List.app addInstructionClass (arm_stepLib.arm_instruction i);
             arm_spec_hex true s)
    val arm_spec_hex = arm_spec_hex false
end

(* ------------------------------------------------------------------------ *)

(* Testing...

fun opc_class s =
   let
      val i = arm_stepLib.hex_to_bits_32 s
   in
      (listSyntax.mk_list (i, Type.bool), arm_stepLib.arm_instruction i)
   end

val step = hd o arm_stepLib.arm_step "vfp"

val s = "VADD (double)"
val s = "e1c44013"
val s = List.nth (hex_list, 0)
val (opc, l) = opc_class s
val thm = step s
val t = arm_mk_pre_post thm
val thms = List.map spec (combinations (thm, t))
spec (thm, t)

val thm = saveSpecs "specs"

val () = arm_config "vfp"
val () = arm_config "vfp,be"
val () = arm_config ""

val arm_spec = Count.apply arm_spec
val arm_spec_hex = Count.apply arm_spec_hex

arm_spec_hex "eeb65a00"
set_trace "stateLib.spec" 1

  Count.apply arm_spec_hex "1ddf7a04"

val thm = hd (arm_spec_hex "E51F000C")

  Count.apply arm_spec_hex "E79F2003"  (* ldr r2, [pc, r3] *)
  Count.apply arm_spec_hex "E18F20D4"  (* ldrd r2, r3, [pc, r4] *)
  Count.apply arm_spec_hex "E51F2018"  (* ldr r2, [pc, #-24] *)
  Count.apply arm_spec_hex "E14F21D8"  (* ldrd r2, r3, [pc, #-24] *)

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

*)

(* ------------------------------------------------------------------------ *)

end
