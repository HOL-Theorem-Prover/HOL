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

infix \\
val op \\ = op THEN;

val ERR = Feedback.mk_HOL_ERR "x64_progLib"

(* ------------------------------------------------------------------------ *)

val x64_proj_def = x64_progTheory.x64_proj_def
val x64_comp_defs = x64_progTheory.component_defs

local
   val x64_1 =
      HolKernel.syntax_fns "x64_prog" 2 HolKernel.dest_monop HolKernel.mk_monop
   val x64_2 =
      HolKernel.syntax_fns "x64_prog" 3 HolKernel.dest_binop HolKernel.mk_binop
in
   val byte = wordsSyntax.mk_int_word_type 8
   val word = wordsSyntax.mk_int_word_type 16
   val dword = wordsSyntax.mk_int_word_type 32
   val qword = wordsSyntax.mk_int_word_type 64
   val (_, mk_x64_RIP, dest_x64_RIP, _) = x64_1 "x64_RIP"
   val (_, mk_x64_EFLAGS, dest_x64_EFLAGS, _) = x64_2 "x64_EFLAGS"
   val (_, mk_x64_MEM, dest_x64_MEM, _) = x64_2 "x64_MEM"
   val (_, mk_x64_REG, dest_x64_REG, _) = x64_2 "x64_REG"
   val (_, mk_x64_mem16, dest_x64_mem16, _) = x64_2 "x64_mem16"
   val (_, mk_x64_mem32, dest_x64_mem32, _) = x64_2 "x64_mem32"
   val (_, mk_x64_mem64, dest_x64_mem64, _) = x64_2 "x64_mem64"
end

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
   update_frame_state_thm x64_proj_def
      [(`K x64_c_RIP`,
        `\s a w. s with RIP := w`,
        `I : x64_state -> x64_state`),
       (`x64_c_REG`, `\s a w. s with REG := (a =+ w) r`,
        `\s. s with REG := r`),
       (`x64_c_MEM`, `\s a w. s with MEM := (a =+ w) r`,
        `\s. s with MEM := r`),
       (`x64_c_ICACHE`, `\s a w. s with ICACHE := (a =+ w) r`,
        `\s. s with ICACHE := r`),
       (`x64_c_EFLAGS`, `\s a w. s with EFLAGS := (a =+ w) r`,
        `\s. s with EFLAGS := r`)]

(* -- *)

local
   fun is_mem_access v tm =
      case Lib.total boolSyntax.dest_eq tm of
         SOME (l, r) =>
            is_code_access ("x64$x64_state_MEM", v) l andalso
            (case Lib.total optionSyntax.dest_some r of
                SOME w => wordsSyntax.is_word_literal w
              | NONE => false)
       | NONE => false
   fun is_icache_access v tm =
      case Lib.total boolSyntax.dest_eq tm of
         SOME (l, r) =>
            is_code_access ("x64$x64_state_ICACHE", v) l andalso
            is_code_access ("x64$x64_state_MEM", v) r
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
         val (i, a) = List.partition (is_icache_access rip) a
         val _ = List.length m = List.length i orelse
                 raise ERR "mk_x64_code_pool" "icache mismatch"
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
   fun write_err s = raise ERR "x64_write_footprint" s
   fun write_assert s a b = General.ignore (a = b orelse write_err s)
   val strip = combinSyntax.strip_update o combinSyntax.dest_K_1
   fun strip_assign (a, b) =
      let
         val (x, y) = strip a
      in
         write_assert "strip_assign" b y; x
      end
   fun not_in_asserts p =
      fn (dst: term -> term) =>
         List.filter
            (fn x => not (Option.isSome
                            (List.find (fn y => case Lib.total dst y of
                                           SOME c => c = dst x
                                         | NONE => false) p)))
   fun prefix tm = case boolSyntax.strip_comb tm of
                      (a, [_]) => a
                    | (a, [b, _]) => Term.mk_comb (a, b)
                    | _ => raise ERR "prefix" ""
   val psort = mlibUseful.sort_map prefix Term.compare
   val s = Term.mk_var ("s", ``:x64_state``)
   val EFLAGS_tm = ``^s.EFLAGS``
   val REG_tm = ``^s.REG``
   val MEM_tm = ``^s.MEM``
   val c_EFLAGS = fst o dest_x64_EFLAGS
   fun d_EFLAGS tm = mk_x64_EFLAGS (c_EFLAGS tm, stateLib.vvar ``:bool option``)
   val c_REG = fst o dest_x64_REG
   fun d_REG tm = mk_x64_REG (c_REG tm, stateLib.vvar qword)
   val c_MEM = fst o dest_x64_MEM
   fun d_MEM tm = mk_x64_MEM (c_MEM tm, stateLib.vvar qword)
   val c_mem16 = fst o dest_x64_mem16
   fun d_mem16 tm = mk_x64_mem16 (c_mem16 tm, stateLib.vvar word)
   val c_mem32 = fst o dest_x64_mem32
   fun d_mem32 tm = mk_x64_mem32 (c_mem32 tm, stateLib.vvar dword)
   val c_mem64 = fst o dest_x64_mem64
   fun d_mem64 tm = mk_x64_mem64 (c_mem64 tm, stateLib.vvar qword)
in
   fun x64_write_footprint (p, q, tm) =
      let
         val not_in_p = not_in_asserts p
      in
         case boolSyntax.dest_strip_comb tm of
            ("x64$x64_state_MEM_fupd", [m, rst]) =>
                let
                   val l =
                      case strip m of
                         ([], t) =>
                            (case boolSyntax.dest_strip_comb t of
                                ("x64_step$write_mem16", [_, a, d]) =>
                                      [mk_x64_mem16 (a, d)]
                              | ("x64_step$write_mem32", [_, a, d]) =>
                                      [mk_x64_mem32 (a, d)]
                              | ("x64_step$write_mem64", [_, a, d]) =>
                                      [mk_x64_mem64 (a, d)]
                              |  _ => write_err "mem"
                            )
                       | (l, t) =>
                           (write_assert "mem" t MEM_tm; List.map mk_x64_MEM l)
                in
                   x64_write_footprint (p, l @ q, rst)
                end
          | ("x64$x64_state_EFLAGS_fupd", [e, rst]) =>
                let
                   val l = List.map mk_x64_EFLAGS (strip_assign (e, EFLAGS_tm))
                   val l2 = List.map d_EFLAGS (not_in_p c_EFLAGS l)
                in
                   x64_write_footprint (l2 @ p, l @ q, rst)
                end
          | ("x64$x64_state_REG_fupd", [r, rst]) =>
                let
                   val reg_assert = write_assert "reg" REG_tm
                   val (l2, l) =
                      case strip r of
                         ([], t) =>
                          (let
                              val (b, t, e) = boolSyntax.dest_cond t
                              val () = reg_assert e
                              val ((a, d), f) = combinSyntax.dest_update_comb t
                              val () = reg_assert f
                              fun is_a c = Lib.total c_REG c = SOME a
                              val (new, pa) =
                                 case List.find is_a p of
                                    SOME pa => (false, pa)
                                  | NONE =>
                                     (true,
                                      mk_x64_REG (a, stateLib.vvar qword))
                              val v = snd (dest_x64_REG pa)
                           in
                             (if new then [pa] else [],
                              [mk_x64_REG (a, boolSyntax.mk_cond (b, d, v))])
                           end
                           handle HOL_ERR _ => write_err "reg")
                       | (l, t) =>
                           let
                              val () = reg_assert t
                              val l = List.map mk_x64_REG l
                           in
                              (List.map d_REG (not_in_p c_REG l), l)
                           end
                in
                   x64_write_footprint (l2 @ p, l @ q, rst)
                end
          | ("x64$x64_state_RIP_fupd", [r, rst]) =>
                let
                   val rip = mk_x64_RIP (combinSyntax.dest_K_1 r)
                in
                   x64_write_footprint (p, rip :: q, rst)
                end
          | (s, _) => write_err s
      end
      handle HOL_ERR {message = "not a const", ...} =>
         let
            val q = psort (q @ not_in_asserts q prefix p)
            val p = psort p
         in
            (progSyntax.list_mk_star p, progSyntax.list_mk_star q)
         end
end

val x64_extras =
   [((``x64_mem16 v``, ``read_mem16 s.MEM v``), I, optionSyntax.mk_some),
    ((``x64_mem32 v``, ``read_mem32 s.MEM v``), I, optionSyntax.mk_some),
    ((``x64_mem64 v``, ``read_mem64 s.MEM v``), I, optionSyntax.mk_some)]
   : footprint_extra list

val x64_mk_pre_post =
   stateLib.mk_pre_post x64_stepTheory.NextStateX64_def x64_instr_def
     x64_proj_def x64_comp_defs mk_x64_code_pool x64_extras x64_write_footprint

(* ------------------------------------------------------------------------ *)

local
   val component_11 =
      case Drule.CONJUNCTS x64_progTheory.x64_component_11 of
        [r, m, _, e] => [r, m, e]
      | _ => raise ERR "component_11" ""
   val x64_rwts =
      Thm.INST_TYPE [Type.alpha |-> ``:Zreg``] boolTheory.COND_RATOR ::
      List.drop (utilsLib.datatype_rewrites "x64" ["x64_state"], 1)
   val STATE_TAC = ASM_REWRITE_TAC x64_rwts
   val spec =
      stateLib.spec
           x64_progTheory.X64_IMP_SPEC
           [x64_stepTheory.read_mem16, x64_stepTheory.read_mem32,
            x64_stepTheory.read_mem64]
           [x64_stepTheory.write_mem16_def, x64_stepTheory.write_mem32_def,
            x64_stepTheory.write_mem64_def]
           (x64_select_state_thms @ x64_select_state_pool_thms)
           [x64_frame, state_id]
           component_11
           [qword, ``:Zreg``, ``:Zeflags``]
           NO_TAC STATE_TAC
in
   val x64_spec =
      utilsLib.cache 2000 String.compare
         (fn s =>
             let
                val thm = x64_stepLib.x64_step s
             in
                spec (thm, x64_mk_pre_post thm)
             end)
end

(* ------------------------------------------------------------------------ *)

(*

val next_def = x64_stepTheory.NextStateX64_def
val instr_def = x64_instr_def
val proj_def = x64_proj_def
val comp_defs = x64_comp_defs
val cpool = mk_x64_code_pool
val extras = x64_extras
val q = [] : term list

val imp_spec = X64_IMP_SPEC
val read_thms =
   [x64_stepTheory.read_mem16, x64_stepTheory.read_mem32,
    x64_stepTheory.read_mem64]
val write_thms =
   [x64_stepTheory.write_mem16_def, x64_stepTheory.write_mem32_def,
   x64_stepTheory.write_mem64_def]
val select_state_thms = x64_select_state_thms @ x64_select_state_pool_thms
val frame_thms = [x64_frame, x64_stepTheory.x64_ID]
val map_tys = [qword, ``:Zreg``, ``:Zeflags``]
val step = x64_stepLib.x64_step
val mk_pre_post = x64_mk_pre_post


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

val pos = ref 1;

val () = List.app (fn s => (Count.apply x64_spec s; Portable.inc pos))
                  (List.drop (hex_list, !pos))

val () =
  Count.apply (List.app (fn s => General.ignore (x64_spec s))) (tl hex_list)

val s = List.nth (hex_list, !pos)

val ce = Count.apply e

val dec = Count.apply x64_stepLib.x64_decode s

val thm = Count.apply x64_stepLib.x64_step "48FF47D0"
val thm = Count.apply x64_stepLib.x64_step "418803"
val thm = Count.apply x64_stepLib.x64_step "488347A013"
val thm = Count.apply x64_stepLib.x64_step "48FF47D0"
val thm = Count.apply x64_stepLib.x64_step "48C3"
val thm = Count.apply x64_stepLib.x64_step "440F42C1"
val thm = Count.apply x64_stepLib.x64_step "4852"
val thm = Count.apply x64_stepLib.x64_step "41F7E0"
val thm = Count.apply x64_stepLib.x64_step "880404"
val thm = Count.apply x64_stepLib.x64_step "880504000000"
val thm = Count.apply x64_stepLib.x64_step "4983C030"
val thm = Count.apply x64_stepLib.x64_step "C700544F4D50"
val thm = Count.apply x64_stepLib.x64_step "4C8BBF10FFFFFF"
val thm = Count.apply x64_stepLib.x64_step "8B4C8604"

*)

(* ------------------------------------------------------------------------ *)

end
