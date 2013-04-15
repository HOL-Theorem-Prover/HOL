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

infix \\
val op \\ = op THEN;

val ERR = Feedback.mk_HOL_ERR "arm_progLib"

(* ------------------------------------------------------------------------ *)

val arm_proj_def = arm_progTheory.arm_proj_def
val arm_comp_defs = arm_progTheory.component_defs

local
   val arm_1 =
      (fn (_, mk, _, _) => mk) o
      HolKernel.syntax_fns "arm_prog" 2 HolKernel.dest_monop HolKernel.mk_monop
   val arm_2 =
      HolKernel.syntax_fns "arm_prog" 3 HolKernel.dest_binop HolKernel.mk_binop
   val pc = Term.prim_mk_const {Thy = "arm", Name = "RName_PC"}
in
   val word2 = wordsSyntax.mk_int_word_type 2
   val word4 = wordsSyntax.mk_int_word_type 4
   val word5 = wordsSyntax.mk_int_word_type 5
   val byte = wordsSyntax.mk_int_word_type 8
   val word = wordsSyntax.mk_int_word_type 32
   val dword = wordsSyntax.mk_int_word_type 64
   val mk_arm_CurrentCondition = arm_1 "arm_CurrentCondition"
   val mk_arm_Encoding = arm_1 "arm_Encoding"
   val mk_arm_undefined = arm_1 "arm_undefined"
   val mk_arm_CPSR_N = arm_1 "arm_CPSR_N"
   val mk_arm_CPSR_Z = arm_1 "arm_CPSR_Z"
   val mk_arm_CPSR_C = arm_1 "arm_CPSR_C"
   val mk_arm_CPSR_V = arm_1 "arm_CPSR_V"
   val mk_arm_CPSR_J = arm_1 "arm_CPSR_J"
   val mk_arm_CPSR_T = arm_1 "arm_CPSR_T"
   val mk_arm_CPSR_E = arm_1 "arm_CPSR_E"
   val (_, mk_arm_MEM, dest_arm_MEM, is_arm_MEM) = arm_2 "arm_MEM"
   val (_, mk_arm_REG, dest_arm_REG, is_arm_REG) = arm_2 "arm_REG"
   val (_, mk_arm_FP_REG, dest_arm_FP_REG, is_arm_FP_REG) = arm_2 "arm_FP_REG"
   val (_, mk_arm_Extensions, dest_arm_Extensions, is_arm_Extensions) =
      arm_2 "arm_Extensions"
   fun mk_arm_PC v = mk_arm_REG (pc, v)
end

(* -- *)

val arm_select_state_thms =
   List.map (fn t => star_select_state_thm arm_proj_def [] ([], t))
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
       ["MEM", "REG", "undefined"]
      ]

val arm_frame =
   update_frame_state_thm arm_proj_def
      [(`K arm_c_CurrentCondition`,
        `\s a w. s with CurrentCondition := w`,
        `I: arm_state -> arm_state`),
       (`K arm_c_Encoding`,
        `\s a w. s with Encoding := w`,
        `I: arm_state -> arm_state`),
       (`K arm_c_undefined`,
        `\s a w. s with undefined := w`,
        `I: arm_state -> arm_state`),
       (`K arm_c_CPSR_N`,
        `\s a w. s with CPSR := cpsr with N := w`,
        `\s. s with CPSR := cpsr`),
       (`K arm_c_CPSR_Z`,
        `\s a w. s with CPSR := cpsr with Z := w`,
        `\s. s with CPSR := cpsr`),
       (`K arm_c_CPSR_C`,
        `\s a w. s with CPSR := cpsr with C := w`,
        `\s. s with CPSR := cpsr`),
       (`K arm_c_CPSR_V`,
        `\s a w. s with CPSR := cpsr with V := w`,
        `\s. s with CPSR := cpsr`),
       (`K arm_c_CPSR_J`,
        `\s a w. s with CPSR := cpsr with J := w`,
        `\s. s with CPSR := cpsr`),
       (`K arm_c_CPSR_T`,
        `\s a w. s with CPSR := cpsr with T := w`,
        `\s. s with CPSR := cpsr`),
       (`K arm_c_CPSR_E`,
        `\s a w. s with CPSR := cpsr with E := w`,
        `\s. s with CPSR := cpsr`),
       (`arm_c_REG`, `\s:arm_state a w. s with REG := (a =+ w) r`,
        `\s:arm_state. s with REG := r`),
       (`arm_c_MEM`, `\s:arm_state a w. s with MEM := (a =+ w) r`,
        `\s:arm_state. s with MEM := r`),
       (`arm_c_FP_REG`,
        `\s:arm_state a w. s with FP := fp with REG := (a =+ w) fp.REG`,
        `\s. s with FP := fp`)
      ]

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
         val r15 = stateLib.gvar "pc" (wordsSyntax.mk_int_word_type 32)
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

(* -- *)

fun reg_index tm =
   case Term.dest_thy_const tm of
      {Thy = "arm", Name = "RName_0usr", ...} => 0
    | {Thy = "arm", Name = "RName_1usr", ...} => 1
    | {Thy = "arm", Name = "RName_2usr", ...} => 2
    | {Thy = "arm", Name = "RName_3usr", ...} => 3
    | {Thy = "arm", Name = "RName_4usr", ...} => 4
    | {Thy = "arm", Name = "RName_5usr", ...} => 5
    | {Thy = "arm", Name = "RName_6usr", ...} => 6
    | {Thy = "arm", Name = "RName_7usr", ...} => 7
    | {Thy = "arm", Name = "RName_8usr", ...} => 8
    | {Thy = "arm", Name = "RName_8fiq", ...} => 8
    | {Thy = "arm", Name = "RName_9usr", ...} => 9
    | {Thy = "arm", Name = "RName_9fiq", ...} => 9
    | {Thy = "arm", Name = "RName_10usr", ...} => 10
    | {Thy = "arm", Name = "RName_10fiq", ...} => 10
    | {Thy = "arm", Name = "RName_11usr", ...} => 11
    | {Thy = "arm", Name = "RName_11fiq", ...} => 11
    | {Thy = "arm", Name = "RName_12usr", ...} => 12
    | {Thy = "arm", Name = "RName_12fiq", ...} => 12
    | {Thy = "arm", Name = "RName_SPusr", ...} => 13
    | {Thy = "arm", Name = "RName_SPfiq", ...} => 13
    | {Thy = "arm", Name = "RName_SPirq", ...} => 13
    | {Thy = "arm", Name = "RName_SPsvc", ...} => 13
    | {Thy = "arm", Name = "RName_SPabt", ...} => 13
    | {Thy = "arm", Name = "RName_SPund", ...} => 13
    | {Thy = "arm", Name = "RName_SPmon", ...} => 13
    | {Thy = "arm", Name = "RName_SPhyp", ...} => 13
    | {Thy = "arm", Name = "RName_LRusr", ...} => 14
    | {Thy = "arm", Name = "RName_LRfiq", ...} => 14
    | {Thy = "arm", Name = "RName_LRirq", ...} => 14
    | {Thy = "arm", Name = "RName_LRsvc", ...} => 14
    | {Thy = "arm", Name = "RName_LRabt", ...} => 14
    | {Thy = "arm", Name = "RName_LRund", ...} => 14
    | {Thy = "arm", Name = "RName_LRmon", ...} => 14
    | {Thy = "arm", Name = "RName_LRhyp", ...} => 14
    | {Thy = "arm", Name = "RName_PC", ...} => 15
    | _ => raise ERR "reg_index" ""

local
   fun other_index tm =
      case fst (Term.dest_const (boolSyntax.rator tm)) of
         "cond" => 0
       | "arm_exception" => 1
       | "arm_undefined" => 2
       | "arm_CurrentCondition" => 3
       | "arm_Encoding" => 4
       | "arm_CPSR_J" => 5
       | "arm_CPSR_E" => 6
       | "arm_CPSR_T" => 7
       | "arm_CPSR_M" => 8
       | "arm_CPSR_N" => 9
       | "arm_CPSR_Z" => 10
       | "arm_CPSR_C" => 11
       | "arm_CPSR_V" => 12
       | _ => ~1
   val int_of_v2w = bitstringSyntax.int_of_term o fst o bitstringSyntax.dest_v2w
   fun write_err s = raise ERR "arm_write_footprint" s
   fun strip_assign (a, b) =
      let
         val (x, y) = combinSyntax.strip_update (combinSyntax.dest_K_1 a)
      in
         b = y orelse write_err "strip_assign"; x
      end
   fun not_in_asserts p =
      fn (dst: term -> term) =>
         List.filter
            (fn x =>
               let
                  val d = dst x
               in
                  not (Lib.exists
                          (fn y => case Lib.total dst y of
                                      SOME c => c = d
                                    | NONE => false) p)
               end)
   fun prefix tm = case boolSyntax.strip_comb tm of
                      (a, [_]) => a
                    | (a, [b, _]) => Term.mk_comb (a, b)
                    | _ => raise ERR "prefix" ""
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
   val register = reg o fst o dest_arm_REG
   fun fp_reg tm =
      case Lib.total int_of_v2w tm of
         SOME i => mlibUseful.INL i
       | NONE => mlibUseful.INR tm
   val fp_register = fp_reg o fst o dest_arm_FP_REG
   val address = HolKernel.strip_binop (Lib.total wordsSyntax.dest_word_add) o
                 fst o dest_arm_MEM
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
   fun fillIn f ty =
      fn []: term list => []
       | _ => [f (stateLib.vvar ty)]: term list
   fun augment1 dst ty mk (p, q, tm, rst) =
      let
         val x = mk (combinSyntax.dest_K_1 tm)
         val l = fillIn mk ty (not_in_asserts p dst [x])
      in
         (l @ p, x :: q, rst)
      end
   val flag = augment1 Term.rator Type.bool
   val s = Term.mk_var ("s", ``:arm_state``)
   val FP_REG_tm = ``^s.FP.REG``
   val REG_tm = ``^s.REG``
   val MEM_tm = ``^s.MEM``
   val c_FP_REG = fst o dest_arm_FP_REG
   val c_REG = fst o dest_arm_REG
   val c_MEM = fst o dest_arm_MEM
   fun d_FP_REG tm = mk_arm_FP_REG (c_FP_REG tm, stateLib.vvar dword)
   fun d_REG tm = mk_arm_REG (c_REG tm, stateLib.vvar word)
   fun d_MEM tm = mk_arm_MEM (c_MEM tm, stateLib.vvar byte)
   fun cpsr_footprint (p, q, tm) =
      (case boolSyntax.dest_strip_comb tm of
          ("arm$PSR_N_fupd", [b, rst]) =>
              cpsr_footprint (flag mk_arm_CPSR_N (p, q, b, rst))
        | ("arm$PSR_Z_fupd", [b, rst]) =>
              cpsr_footprint (flag mk_arm_CPSR_Z (p, q, b, rst))
        | ("arm$PSR_C_fupd", [b, rst]) =>
              cpsr_footprint (flag mk_arm_CPSR_C (p, q, b, rst))
        | ("arm$PSR_V_fupd", [b, rst]) =>
              cpsr_footprint (flag mk_arm_CPSR_V (p, q, b, rst))
        | ("arm$PSR_J_fupd", [b, rst]) =>
              cpsr_footprint (flag mk_arm_CPSR_J (p, q, b, rst))
        | ("arm$PSR_T_fupd", [b, rst]) =>
              cpsr_footprint (flag mk_arm_CPSR_T (p, q, b, rst))
        | ("arm$PSR_E_fupd", [b, rst]) =>
              cpsr_footprint (flag mk_arm_CPSR_E (p, q, b, rst))
        | ("arm$arm_state_CPSR", [cpsr_s]) =>
              (cpsr_s = s orelse raise ERR "cpsr_footprint" "mismatch"
               ; (p, q))
        | (s, _) => raise ERR "cpsr_footprint" s)
      handle HOL_ERR {message = "not a const", ...} => (p, q)
in
   fun arm_write_footprint (p, q, tm) =
      (case boolSyntax.dest_strip_comb tm of
          ("arm$arm_state_MEM_fupd", [m, rst]) =>
              let
                 val l = List.map mk_arm_MEM (strip_assign (m, MEM_tm))
                 val l2 = List.map d_MEM (not_in_asserts p c_MEM l)
              in
                 arm_write_footprint (l2 @ p, l @ q, rst)
              end
        | ("arm$arm_state_REG_fupd", [r, rst]) =>
              let
                 val l = List.map mk_arm_REG (strip_assign (r, REG_tm))
                 val l2 = List.map d_REG (not_in_asserts p c_REG l)
              in
                 arm_write_footprint (l2 @ p, l @ q, rst)
              end
        | ("arm$arm_state_FP_fupd", [r, rst]) =>
             (case Lib.total
                     (boolSyntax.dest_strip_comb o combinSyntax.dest_K_1) r of
                 SOME ("arm$FP_REG_fupd", [r, _]) =>
                    let
                       val l =
                          List.map mk_arm_FP_REG (strip_assign (r, FP_REG_tm))
                       val l2 = List.map d_FP_REG (not_in_asserts p c_FP_REG l)
                    in
                       arm_write_footprint (l2 @ p, l @ q, rst)
                    end
               | _ => write_err "VFP registers")
        | ("arm$arm_state_Encoding_fupd", [e, rst]) =>
              arm_write_footprint
                 (augment1 Term.rator ``:Encoding`` mk_arm_Encoding
                           (p, q, e, rst))
        | ("arm$arm_state_CurrentCondition_fupd", [c, rst]) =>
              arm_write_footprint
                 (augment1 Term.rator word4 mk_arm_CurrentCondition
                           (p, q, c, rst))
        | ("arm$arm_state_undefined_fupd", [u, rst]) =>
              arm_write_footprint (flag mk_arm_undefined (p, q, u, rst))
        | ("arm$arm_state_CPSR_fupd", [c, rst]) =>
              let
                 val (p', q') = cpsr_footprint (p, q, combinSyntax.dest_K_1 c)
              in
                 arm_write_footprint (p', q', rst)
              end
        | (s, _) => write_err s)
      handle HOL_ERR {message = "not a const", ...} =>
         let
            val q = psort (q @ not_in_asserts q prefix p)
            val p = psort p
         in
            (progSyntax.list_mk_star p, progSyntax.list_mk_star q)
         end
end

val arm_mk_pre_post =
   stateLib.mk_pre_post arm_stepTheory.NextStateARM_def arm_instr_def
     arm_proj_def arm_comp_defs mk_arm_code_pool [] arm_write_footprint

(* ------------------------------------------------------------------------ *)

local
   val registers = List.tabulate (16, fn i => wordsSyntax.mk_wordii (i, 4))
   val R_usr_tm = Term.prim_mk_const {Thy = "arm_step", Name = "R_usr"}
   val mk_R_usr = Lib.curry Term.mk_comb R_usr_tm
   val R_usr =
      utilsLib.map_conv
         (SIMP_CONV (srw_ss()) [arm_stepTheory.R_usr_def])
         (List.map mk_R_usr registers)
in
   val REG_CONV =
      Conv.QCONV
        (REWRITE_CONV
           [R_usr, arm_stepTheory.v2w_ground4, arm_stepTheory.v2w_ground5])
   val REG_RULE = Conv.CONV_RULE REG_CONV o utilsLib.ALL_HYP_CONV_RULE REG_CONV
end

local
   fun concat_unzip l = (List.concat ## List.concat) (ListPair.unzip l)
   val regs = List.mapPartial (Lib.total dest_arm_REG)
   val fp_regs = List.mapPartial (Lib.total dest_arm_FP_REG)
   val pc_tm = Term.prim_mk_const {Thy = "arm", Name = "RName_PC"}
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
               ("arm_prog$arm_undefined", [v]) => g (v, "und", Type.bool)
             | ("arm_prog$arm_CurrentCondition", [v]) => g (v, "cond", word4)
             | ("arm_prog$arm_Encoding", [v]) => g (v, "enc", ``:Encoding``)
             | ("arm_prog$arm_CPSR_N", [v]) => g (v, "n", Type.bool)
             | ("arm_prog$arm_CPSR_Z", [v]) => g (v, "z", Type.bool)
             | ("arm_prog$arm_CPSR_C", [v]) => g (v, "c", Type.bool)
             | ("arm_prog$arm_CPSR_V", [v]) => g (v, "v", Type.bool)
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
              THENC REWRITE_CONV [arm_stepTheory.Aligned_numeric]
              THENC NOT_F_CONV))
   val cnv =
      REG_CONV
      THENC check_unique_reg_CONV
      THENC PRE_COND_CONV
      THENC PRE_CONV WGROUND_RW_CONV
      THENC OPC_CONV bitstringLib.v2w_n2w_CONV
      THENC POST_CONV (WGROUND_RW_CONV THENC PURE_REWRITE_CONV spec_rwts)
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
      \\ ASM_REWRITE_TAC [boolTheory.DE_MORGAN_THM]
   val arm_rwts =
      List.drop (utilsLib.datatype_rewrites "arm" ["arm_state", "PSR", "FP"], 1)
   val STATE_TAC = ASM_REWRITE_TAC arm_rwts
   val spec =
      stateLib.spec
           arm_progTheory.ARM_IMP_SPEC
           [arm_stepTheory.get_bytes]
           []
           (arm_select_state_pool_thm :: arm_select_state_thms)
           [arm_frame, state_id]
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
           before print "\n"
      end
   val the_spec = ref (arm_spec_opt "")
   fun get_opcode thm =
      let
         val (_, _, c, _) = progSyntax.dest_spec (Thm.concl thm)
      in
         c |> pred_setSyntax.strip_set |> hd
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
in
   fun arm_config opt =
      (the_spec := arm_spec_opt opt
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
      (print s
       ; if Redblackset.member (!spec_label_set, s)
            then print "\n"
         else (add_specs (arm_spec s)
               ; spec_label_set := Redblackset.add (!spec_label_set, s)))
   fun arm_spec_hex looped =
      (* utilsLib.cache 1000 String.compare *)
        (fn s =>
            let
               val i = arm_stepLib.hex_to_bits_32 s
               val opc = listSyntax.mk_list (i, Type.bool)
            in
               case find_spec opc of
                  SOME thms =>
                    let
                       val l = List.mapPartial (Lib.total (spec_spec opc)) thms
                    in
                       if List.null l
                          then loop looped i "failed to find suitable spec" s
                       else l
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
val s = "ed817a00"
val s = List.nth (hex_list, 0)
val (opc, l) = opc_class s
val thm = step s
val t = arm_mk_pre_post thm
val thms = List.map spec (combinations (thm, t))
spec (thm, t)

val thm = saveSpecs "specs"

  arm_config "vfp"

val arm_spec_hex = Count.apply arm_spec_hex

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

val () = arm_config ""

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

         (List.take (hex_list, 10))

val tm = rst
val SOME ("arm$FP_REG_fupd", [r, _]) =
   Lib.total
      (boolSyntax.dest_strip_comb o combinSyntax.dest_K_1) r
val ("arm$arm_state_FP_fupd", [r, rst]) =
   boolSyntax.dest_strip_comb tm
val ("arm$arm_state_CPSR_fupd", [c, rst]) =
   boolSyntax.dest_strip_comb tm
val ("arm$arm_state_MEM_fupd", [m, rst]) =
   boolSyntax.dest_strip_comb tm
val ("arm$arm_state_REG_fupd", [r, rst]) =
   boolSyntax.dest_strip_comb tm
val ("arm$arm_state_CurrentCondition_fupd", [c, rst]) =
   boolSyntax.dest_strip_comb tm
val ("arm$arm_state_Encoding_fupd", [e, rst]) =
   boolSyntax.dest_strip_comb tm
val ("arm$arm_state_undefined_fupd", [u, rst]) =
   boolSyntax.dest_strip_comb tm

val next_def = arm_stepTheory.NextStateARM_def
val instr_def = arm_instr_def
val proj_def = arm_proj_def
val comp_defs = arm_comp_defs
val cpool = mk_arm_code_pool
val extras = [] : stateLib.footprint_extra list
val q = [] : term list

val imp_spec = ARM_IMP_SPEC
val read_thms = [arm_stepTheory.get_bytes]
val write_thms = []: thm list
val select_state_thms = (arm_select_state_pool_thm :: arm_select_state_thms)
val frame_thms = [arm_frame, state_id]
val map_tys = [word, word5, ``:RName``]
val mk_pre_post = arm_mk_pre_post
val write = arm_write_footprint

fun exclude s = List.exists (fn e => String.isPrefix e s) ["LDM", "STM"]

val l = List.filter (not o exclude) (arm_stepLib.list_instructions ())

val pos = ref 0;

val () = List.app (fn s => (addInstructionClass s; Portable.inc pos))
                  (List.drop (l, !pos))

use "arm_tests.sml";
val l = Lib.mk_set arm_tests
length arm_tests
length l

val stp = arm_stepLib.arm_step_hex ""
val dec = arm_stepLib.decode_arm_hex (arm_configLib.mk_config_terms "")
List.length (!fails)
val fs = List.map (fn s => (s, Lib.total dec s)) (!fails)

val s = "e8bd85f8"
val s = fst (List.nth (fs, 10))

dec s
stp s
arm_spec_hex s

val fails = ref ([]:string list)
val pos = ref 0;

val () = List.app (fn s => (arm_spec_hex s
                            handle HOL_ERR _ => (fails := s::(!fails); TRUTH)
                            ; Portable.inc pos))
                  (List.drop (l, !pos))

fails
pos
List.length l
val s = List.nth (l, !pos)
val thm = step (List.nth (l, !pos))
val thm = Count.apply arm_spec (List.nth (l, !pos))

val ce = Count.apply e

*)

(* ------------------------------------------------------------------------ *)

end
