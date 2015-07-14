structure m0_core_decompLib :> m0_core_decompLib =
struct

open HolKernel Parse boolLib bossLib
open m0_core_decompTheory core_decompilerLib tripleLib m0_decompLib

val ERR = Feedback.mk_HOL_ERR "m0_core_decompLib"

val _ = Parse.hide "cond"

(* ------------------------------------------------------------------------ *)

local
   val count_INTRO_rule =
      stateLib.introduce_triple_definition
         (false, m0_decompTheory.m0_COUNT_def) o
      Thm.INST [``endianness:bool`` |-> boolSyntax.F,
                ``spsel:bool`` |-> boolSyntax.F]
in
   val spec =
      List.map (count_INTRO_rule o
                m0_progLib.memory_introduction o
                m0_progLib.register_introduction o
                m0_progLib.m0_introduction) o
      m0_progLib.m0_spec
end

(* ------------------------------------------------------------------------ *)

val get_cond' =
   tripleSyntax.get_component (Lib.equal (Term.mk_var ("cond'", Type.bool)))

local
   val ARITH_SUB_CONV =
      Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV
      THENC wordsLib.WORD_ARITH_CONV
      THENC wordsLib.WORD_SUB_CONV
   fun is_reducible tm =
      case Lib.total wordsSyntax.dest_word_add tm of
         SOME (v, _) => not (Term.is_var v)
       | _ => not (boolSyntax.is_cond tm)
   fun PC_CONV tm = if is_reducible tm then ARITH_SUB_CONV tm else ALL_CONV tm
   val WGROUND_RW_CONV =
      Conv.DEPTH_CONV (utilsLib.cache 10 Term.compare bitstringLib.v2w_n2w_CONV)
      THENC utilsLib.WALPHA_CONV
      THENC utilsLib.WGROUND_CONV
      THENC utilsLib.WALPHA_CONV
   val cnv1 = m0_progLib.REG_CONV
              THENC WGROUND_RW_CONV
              THENC REWRITE_CONV [alignmentTheory.aligned_numeric]
   val cnv2 =
      tripleLib.CODE_CONV (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV)
      THENC tripleLib.POST_CONV (Conv.RAND_CONV PC_CONV)
in
   fun simp_triple_rule thm =
      let
         val thm1 = utilsLib.ALL_HYP_CONV_RULE cnv1 thm
         val _ = get_cond' thm1 <> boolSyntax.F orelse
                 raise ERR "simp_triple_rule" "condition false"
      in
         Conv.CONV_RULE cnv2 thm1
      end
end

val pc = Term.mk_var ("pc", ``:word32``)

val get_code =
   snd o pairSyntax.dest_pair o
   hd o pred_setSyntax.strip_set o
   tripleSyntax.dest_code o Thm.concl

local
   val get_opcode = m0_progLib.mk_thumb2_pair false o Term.rand o get_code
   val spec_label_set = ref (Redblackset.empty String.compare)
   val triple_rwts = ref (LVTermNet.empty: thm LVTermNet.lvtermnet)
   fun add1 thm =
      triple_rwts := utilsLib.add_to_rw_net get_opcode (thm, !triple_rwts)
   val rule = tripleLib.spec_to_triple_rule (pc, M0_ASSERT_def, L3_M0_def)
   val add_triples = List.app (add1 o rule)
   fun find_triple opc = Lib.total (utilsLib.find_rw (!triple_rwts)) opc
   fun spec_spec opc thm =
      let
         val thm_opc = get_opcode thm
         val a = fst (Term.match_term thm_opc opc)
      in
         simp_triple_rule (Thm.INST a thm)
      end
in
   fun addInstructionClass s =
      if Redblackset.member (!spec_label_set, s)
         then false
      else (print (" " ^ s)
            ; add_triples (spec s)
            ; spec_label_set := Redblackset.add (!spec_label_set, s)
            ; true)
   fun m0_triple_hex looped s =
      let
         val opc = m0_stepLib.hex_to_bits s
      in
         case find_triple opc of
            SOME thms =>
              let
                 val l = List.mapPartial (Lib.total (spec_spec opc)) thms
              in
                 if List.null l
                    then loop looped opc "failed to find suitable spec" s
                 else l
              end
          | NONE => loop looped opc "failed to add suitable spec" s
      end
    and loop looped opc e s =
       if looped orelse
          not (addInstructionClass (m0_stepLib.thumb_instruction opc))
          then raise ERR "m0_triple_hex" (e ^ ": " ^ s)
       else m0_triple_hex true s
    val m0_triple_hex = m0_triple_hex false
end

(* ------------------------------------------------------------------------ *)

local
   val sym_abbr_thm = GSYM markerTheory.Abbrev_def
   val swap_disj_abbr_thm = Q.prove(
      `!x y. x \/ y = Abbrev (y \/ x)`,
      utilsLib.qm_tac [markerTheory.Abbrev_def])
   val swap_conj_abbr_thm = Q.prove(
      `!x y. x /\ y = Abbrev (y /\ x)`,
      utilsLib.qm_tac [markerTheory.Abbrev_def])
in
   fun abbrev_into_conv c =
      case Lib.total boolSyntax.dest_disj c of
         SOME (a, b) =>
           let
              val d = boolSyntax.mk_disj (b, a)
           in
              ONCE_DEPTH_CONV
                 (fn t => if t = c
                             then Thm.SPEC c sym_abbr_thm
                          else if t = d
                             then Drule.SPECL [b, a] swap_disj_abbr_thm
                          else NO_CONV t)
           end
       | NONE =>
           (case Lib.total boolSyntax.dest_conj c of
               SOME (a, b) =>
                 let
                    val d = boolSyntax.mk_conj (b, a)
                 in
                    ONCE_DEPTH_CONV
                       (fn t => if t = c
                                   then Thm.SPEC c sym_abbr_thm
                                else if t = d
                                   then Drule.SPECL [b, a] swap_conj_abbr_thm
                                else NO_CONV t)
                 end
             | NONE =>
                    ONCE_DEPTH_CONV
                          (fn t => if t = c
                                      then Thm.SPEC c sym_abbr_thm
                                   else NO_CONV t))
end

local
   fun get_length th = if sumSyntax.is_inl (get_code th) then 2 else 4
   val get_pc = Term.rand o Term.rand
   fun find_exit thm =
      let
         val (_, p, _, q) = tripleSyntax.dest_triple (Thm.concl thm)
      in
         stateLib.get_delta (get_pc p) (get_pc q)
      end
   fun format_thm th = (th, get_length th, find_exit th)
   val fix_precond =
      fn [th1, th2] =>
            let
               val c = snd (boolSyntax.dest_conj (get_cond' th2))
               val c = utilsLib.mk_negation c
            in
               [utilsLib.ALL_HYP_CONV_RULE (abbrev_into_conv c) th1, th2]
            end
       | thms as [_] => thms
       | _ => raise ERR "fix_precond" ""
   val finalise = List.map format_thm o fix_precond
in
   fun m0_triple hex =
      case finalise (m0_triple_hex hex) of
         [x] => (x, NONE)
       | [x1, x2] => (x1, SOME x2)
       | _ => raise ERR "m0_triple" ""
    val m0_triple_code =
       List.map m0_triple o
       (m0AssemblerLib.m0_code: string quotation -> string list)
end

val vars = Term.mk_var ("cond", Type.bool) ::
           fst (boolSyntax.strip_forall (Thm.concl M0_ASSERT_def))

fun config_for_m0 () =
   core_decompilerLib.configure
     { pc_tm = pc,
       init_fn = Lib.I,
       pc_conv = RAND_CONV,
       triple_fn = m0_triple,
       component_vars = vars }

val () = config_for_m0 ()

fun m0_core_decompile name qcode =
   ( config_for_m0 ()
   ; core_decompilerLib.code_parser := NONE
   ; core_decompilerLib.core_decompile name qcode
   )

fun m0_core_decompile_code name qcode =
   ( config_for_m0 ()
   ; core_decompilerLib.code_parser := SOME (m0AssemblerLib.m0_code)
   ; core_decompilerLib.core_decompile name qcode
   )

(* ------------------------------------------------------------------------ *)

(* Testing...

open m0_core_decompLib

val (test_cert, test_def) = m0_core_decompLib.m0_core_decompile "test"`
   2100  (*     movs r1, #0 *)
   0003  (*     mov  r3, r0 *)
   3328  (*     adds r3, #40 *)
   6842  (* l1: ldr  r2, [r0, #4] *)
   3004  (*     adds r0, #4 *)
   4411  (*     add  r1, r2 *)
   4298  (*     cmp  r0, r3 *)
   DBFA  (*     blt  l1 *)`

val (test2_cert, test2_def) = m0_core_decompLib.m0_core_decompile_code "test2"
   `movs r1, #0        ; accumulator
    mov  r3, r0        ; first address
    adds r3, #40       ; last address (10 loads)
l1: ldr  r2, [r0, #4]  ; load data
    adds r0, #4        ; increment address
    add  r1, r2        ; add to accumulator
    cmp  r0, r3        ; test if done
    blt  l1            ; loop if not done`

val () = utilsLib.add_datatypes [``:RName``] computeLib.the_compset
val () = computeLib.add_funs
           [test_def, alignmentTheory.aligned_def, alignmentTheory.align_def]
val eval =
   EVAL THENC ONCE_DEPTH_CONV (updateLib.SORT_ENUM_UPDATES_CONV ``:RName``)

eval ``test (T, (\a. if a && 3w = 0w then 4w else 0w), dmem,
                (\x. 12w), UNIV, 0, F, F, F, F)``

val test = Count.apply m0_triple

test "D000";
test "D100";
test "D200";
test "D300";
test "D400";
test "D500";
test "D600";
test "D700";
test "D800";
test "D900";
test "DA00";
test "DB00";
test "DC00";
test "DD00";

*)

(* ------------------------------------------------------------------------ *)

end
