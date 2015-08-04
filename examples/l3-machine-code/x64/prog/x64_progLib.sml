structure x64_progLib :> x64_progLib =
struct

open HolKernel boolLib bossLib
open stateLib x64_stepLib x64_progTheory

structure Parse =
struct
   open Parse
   val (Type, Term) = parse_from_grammars x64_progTheory.x64_prog_grammars
end

open Parse

val ERR = Feedback.mk_HOL_ERR "x64_progLib"

(* ------------------------------------------------------------------------ *)

val x64_proj_def = x64_progTheory.x64_proj_def
val x64_comp_defs = x64_progTheory.component_defs

fun syn n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "x64_prog"
val x64_1 = syn 2 HolKernel.dest_monop HolKernel.mk_monop
val x64_2 = syn 3 HolKernel.dest_binop HolKernel.mk_binop
val byte = wordsSyntax.mk_int_word_type 8
val word = wordsSyntax.mk_int_word_type 16
val dword = wordsSyntax.mk_int_word_type 32
val qword = wordsSyntax.mk_int_word_type 64
val (_, mk_x64_RIP, _, _) = x64_1 "x64_RIP"
val (_, mk_x64_EFLAGS, dest_x64_EFLAGS, _) = x64_2 "x64_EFLAGS"
val (_, mk_x64_MEM, dest_x64_MEM, _) = x64_2 "x64_MEM"
val (_, mk_x64_REG, dest_x64_REG, _) = x64_2 "x64_REG"
val (_, mk_x64_mem16, dest_x64_mem16, _) = x64_2 "x64_mem16"
val (_, mk_x64_mem32, dest_x64_mem32, _) = x64_2 "x64_mem32"
val (_, mk_x64_mem64, dest_x64_mem64, _) = x64_2 "x64_mem64"

(* -- *)

val x64_select_state_thms =
   List.map (fn t => star_select_state_thm x64_proj_def [] ([], t))
            (x64_comp_defs @ [x64_mem16_def, x64_mem32_def, x64_mem64_def])

local
   val opcs =
      List.tabulate (20, fn i => Term.mk_var ("opc" ^ Int.toString i, byte))
   val cnv =
      utilsLib.SRW_CONV
         [pred_setTheory.INSERT_UNION_EQ, stateTheory.CODE_POOL,
          x64_instr_def, x64_mem_def]
   fun x64_pool i =
      cnv (stateLib.list_mk_code_pool
              (``x64_instr``, ``v: word64``, List.take (opcs, i)))
   val select_state_pool_thm =
      stateLib.pool_select_state_thm x64_proj_def [] o
      x64_pool o (fn i => i + 1)
in
   val x64_select_state_pool_thms = List.tabulate (20, select_state_pool_thm)
end

(* -- *)

val state_id =
   utilsLib.mk_state_id_thm x64Theory.x64_state_component_equality
      [["EFLAGS", "REG", "RIP"],
       ["EFLAGS", "MEM", "RIP"],
       ["EFLAGS", "RIP"],
       ["MEM", "REG", "RIP"],
       ["MEM", "RIP"],
       ["REG", "RIP"]
      ]

val x64_frame =
   stateLib.update_frame_state_thm x64_proj_def ["RIP", "REG", "MEM", "EFLAGS"]

(* -- *)

local
   fun is_imm_var tm =
      case Lib.total Term.dest_var tm of
         SOME ("imm", _) => true
       | _ => false
   fun is_opc_byte tm =
      case Lib.total wordsSyntax.dest_word_extract tm of
         SOME (_, _, i, _) => is_imm_var i
       | NONE => (case Lib.total combinSyntax.dest_I tm of
                     SOME i => is_imm_var i
                   | NONE => wordsSyntax.is_n2w tm)
   fun is_mem_access v tm =
      case Lib.total boolSyntax.dest_eq tm of
         SOME (l, r) =>
            stateLib.is_code_access ("x64$x64_state_MEM", v) l andalso
            is_opc_byte r
       | NONE => false
in
   fun mk_x64_code_pool thm =
      let
         val rip = stateLib.gvar "rip" (wordsSyntax.mk_int_word_type 64)
         val rip_a = mk_x64_RIP rip
         val (a, tm) = Thm.dest_thm thm
         val rip_subst = Term.subst [``s.RIP`` |-> rip]
         val a = List.map rip_subst a
         val (m, a) = List.partition (is_mem_access rip) a
         val m = List.map dest_code_access m
         val m = mlibUseful.sort_map fst Int.compare m
      in
         (rip_a,
          boolSyntax.rand
            (stateLib.list_mk_code_pool (``x64_instr``, rip, List.map snd m)),
          list_mk_imp (a, rip_subst tm))
      end
end

(* -- *)

local
   fun prefix tm = case boolSyntax.strip_comb tm of
                      (a, [_]) => a
                    | (a, [b, _]) => Term.mk_comb (a, b)
                    | _ => raise ERR "prefix" ""
in
   val psort = mlibUseful.sort_map prefix Term.compare
end

local
   val st = Term.mk_var ("s", ``:x64_state``)
   val MEM_tm = ``^st.MEM``
   fun err () = raise ERR "x64_write_footprint" "mem"
in
   val x64_write_footprint =
      stateLib.write_footprint x64_1 x64_2
         [("x64$x64_state_REG_fupd", "x64_REG", ``^st.REG``),
          ("x64$x64_state_EFLAGS_fupd", "x64_EFLAGS", ``^st.EFLAGS``)]
         []
         [("x64$x64_state_RIP_fupd", "x64_RIP")]
         [("x64$x64_state_MEM_fupd",
             fn (p, q, m) =>
                let
                   val l =
                      case combinSyntax.strip_update m of
                         ([], t) =>
                            (case boolSyntax.dest_strip_comb t of
                                ("x64_step$write_mem16", [_, a, d]) =>
                                      [mk_x64_mem16 (a, d)]
                              | ("x64_step$write_mem32", [_, a, d]) =>
                                      [mk_x64_mem32 (a, d)]
                              | ("x64_step$write_mem64", [_, a, d]) =>
                                      [mk_x64_mem64 (a, d)]
                              |  _ => err ()
                            )
                       | (l, t) => (t = MEM_tm orelse err ()
                                    ; List.map mk_x64_MEM l)
                in
                   (p, l @ q)
                end)]
         (K false)
end

val x64_extras =
   [((``x64_mem16 v``, ``read_mem16 s.MEM v``), I, I),
    ((``x64_mem32 v``, ``read_mem32 s.MEM v``), I, I),
    ((``x64_mem64 v``, ``read_mem64 s.MEM v``), I, I)]
   : footprint_extra list

val x64_mk_pre_post =
   stateLib.mk_pre_post x64_progTheory.X64_MODEL_def x64_comp_defs
     mk_x64_code_pool x64_extras x64_write_footprint psort

(* ------------------------------------------------------------------------ *)

local
   val lowercase_const = utilsLib.lowercase o fst o Term.dest_const
   val x64_rename2 =
      fn "x64_prog$x64_REG" => SOME lowercase_const
       | "x64_prog$x64_EFLAGS" => SOME lowercase_const
       | _ => NONE
   val x64_rename = stateLib.rename_vars (K NONE, x64_rename2, [])
   val byte_mem_intro =
      stateLib.introduce_map_definition
          (x64_progTheory.x64_BYTE_MEMORY_INSERT, Conv.ALL_CONV)
   val mem_intro =
      Conv.BETA_RULE o
      stateLib.introduce_map_definition
          (x64_progTheory.x64_MEMORY_INSERT, Conv.ALL_CONV)
   val match_mem32 = fst o match_term ``pp * x64_prog$x64_mem32 a w``
   val w = ``w:word32``
   val w2w_w = ``(w2w: word64 -> word32) w``
   fun try_to_remove_mem32 th =
      let
         val i = match_mem32 (temporal_stateSyntax.dest_pre' (Thm.concl th))
         val th = INST [subst i w |-> w2w_w] th
      in
         Lib.tryfind (fn thm => MATCH_MP thm th)
            [x64_mem32_READ_EXTEND, x64_mem32_WRITE_EXTEND,
             x64_mem32_TEMPORAL_READ_EXTEND, x64_mem32_TEMPORAL_WRITE_EXTEND]
      end
      handle HOL_ERR _ => th
in
   val x64_rule =
      x64_rename o
      byte_mem_intro o
      mem_intro o
      try_to_remove_mem32 o
      helperLib.PRE_POST_RULE
        (wordsLib.WORD_SUB_CONV
         THENC helperLib.EVERY_MATCH_MOVE_OUT_CONV ``x64_prog$x64_mem32 a b``) o
      Conv.CONV_RULE
         (helperLib.POST_CONV (stateLib.PC_CONV "x64_prog$x64_PC")) o
      stateLib.introduce_triple_definition (false, x64_PC_def)
end

(* ------------------------------------------------------------------------ *)

local
   val component_11 = Drule.CONJUNCTS x64_progTheory.x64_component_11
   val x64_rwts =
      Thm.INST_TYPE [Type.alpha |-> ``:Zreg``] boolTheory.COND_RATOR ::
      List.drop (utilsLib.datatype_rewrites true "x64" ["x64_state"], 1)
   val STATE_TAC = ASM_REWRITE_TAC x64_rwts
   val spec =
      x64_rule o
      stateLib.spec
           x64_progTheory.X64_IMP_SPEC
           x64_progTheory.X64_IMP_TEMPORAL
           [x64_stepTheory.read_mem16, x64_stepTheory.read_mem32,
            x64_stepTheory.read_mem64, combinTheory.I_THM]
           [x64_stepTheory.write_mem16_def, x64_stepTheory.write_mem32_def,
            x64_stepTheory.write_mem64_def]
           (x64_select_state_thms @ x64_select_state_pool_thms)
           [x64_frame, state_id]
           component_11
           [qword, ``:Zreg``, ``:Zeflags``]
           NO_TAC STATE_TAC
   val disassemble1 =
      hd o x64AssemblerLib.x64_disassemble o Lib.list_of_singleton o QUOTE
   val x64_spec_trace = ref 0
   val () = Feedback.register_trace ("x64 spec", x64_spec_trace, 2)
in
   val x64_spec =
      (* utilsLib.cache 2000 String.compare *)
         (fn s =>
             let
                val thm = x64_stepLib.x64_step_hex s
                val t = x64_mk_pre_post thm
             in
                case !x64_spec_trace of
                   1 => assemblerLib.printn (s ^ " ; " ^ disassemble1 s)
                 | 2 => print (" " ^ disassemble1 s)
                 | _ => ()
              ; spec (thm, t)
             end)
end

val x64_spec_code = List.map x64_spec o x64AssemblerLib.x64_code_no_spaces

(* ------------------------------------------------------------------------ *)

(*

open x64_progLib

val () = Feedback.set_trace "x64 spec" 1

val thms = x64_spec_code
  `ret                          ; c3
   cmovb r8d, ecx               ; 44 0f 42 c1
   push rdx                     ; 52
   mul r8d                      ; 41 f7 e0
   cmp r8d, edx                 ; 41 39 d0
   mov [rsp+rax], al            ; 88 04 04
   mov [rip+0x4], al            ; 88 05 04 00 00 00
   add r8, 0x30                 ; 49 83 c0 30
   mov dword [rax], 0x504D4F54  ; c7 00 54 4f 4d 50
   mov r15, [rdi-0xF0]          ; 4c 8b bf 10 ff ff ff
   mov ecx, [rsi+rax*4+0x4]     ; 8b 4c 86 04`

x64AssemblerLib.print_x64_code `mov [rsp+rax], ax`

x64AssemblerLib.print_x64_disassemble
  `48C3
   440F42C1
   4852
   41F7E0
   4139D0
   880404
   880504000000
   4983C030
   C700544F4D50
   4C8BBF10FFFFFF
   8B4C8604`

val () = stateLib.set_temporal false
val () = stateLib.set_temporal true

val thm = Count.apply x64_spec "48C3"
val thm = Count.apply x64_spec "440F42C1"
val thm = Count.apply x64_spec "4852"
val thm = Count.apply x64_spec "41F7E0"
val thm = Count.apply x64_spec "4139D0"
val thm = Count.apply x64_spec "880404"
val thm = Count.apply x64_spec "880504000000"
val thm = Count.apply x64_spec "4983C030"
val thm = Count.apply x64_spec "C700544F4D50"
val thm = Count.apply x64_spec "4C8BBF10FFFFFF"
val thm = Count.apply x64_spec "8B4C8604"

val thm = Count.apply x64_spec "8345F8__"
val thm = Count.apply x64_spec "41B8________"
val thm = Count.apply x64_spec "48BA________________"

val pos = ref 1;

val () = List.app (fn s => (Count.apply x64_spec s; Portable.inc pos))
                  (List.drop (hex_list, !pos))

val () =
  Count.apply (List.app (fn s => General.ignore (x64_spec s))) (tl hex_list)

val next_def = x64_stepTheory.NextStateX64_def
val instr_def = x64_instr_def
val proj_def = x64_proj_def
val model_def = x64_progTheory.X64_MODEL_def
val comp_defs = x64_comp_defs
val cpool = mk_x64_code_pool
val extras = x64_extras
val write_fn = x64_write_footprint
val q = [] : term list

val imp_spec = X64_IMP_SPEC
val imp_temp = x64_progTheory.X64_IMP_TEMPORAL
val read_thms =
   [x64_stepTheory.read_mem16, x64_stepTheory.read_mem32,
    x64_stepTheory.read_mem64, combinTheory.I_THM]
val write_thms =
   [x64_stepTheory.write_mem16_def, x64_stepTheory.write_mem32_def,
    x64_stepTheory.write_mem64_def]
val select_state_thms = x64_select_state_thms @ x64_select_state_pool_thms
val frame_thms = [x64_frame, state_id]
val map_tys = [qword, ``:Zreg``, ``:Zeflags``]
val EXTRA_TAC = NO_TAC
val step = x64_stepLib.x64_step
val mk_pre_post = x64_mk_pre_post

*)

(* ------------------------------------------------------------------------ *)

end
