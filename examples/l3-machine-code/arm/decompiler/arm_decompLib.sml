structure arm_decompLib :> arm_decompLib =
struct

open HolKernel Parse boolLib bossLib;
open helperLib set_sepTheory addressTheory progTheory;
open pred_setTheory combinTheory;
open arm_decompTheory decompilerLib;

val ERR = Feedback.mk_HOL_ERR "arm_decompLib"

val () = arm_progLib.arm_config "vfp"
val () = arm_progLib.set_newline ""

(* automation *)

(*** TODO
val v1 = mk_var ("%v1", ``:word5``)
val GoodMode_tm = ``GoodMode ^v1``
*)

local
   val bit_0_14_tm = ``~word_bit 0 (r14:word32)``
   val GoodMode_tm = ``GoodMode mode``
   val arm_REG_RName_PC_tm = ``arm_REG RName_PC``
   val AlignedPC_tm = ``Aligned (pc:word32,4)``
   val arm_PC_INTRO3 =
      arm_PC_INTRO2 |> Q.INST [`p1`|->`emp`, `p2`|->`emp`]
                    |> PURE_REWRITE_RULE [SEP_CLAUSES]
   fun TRY_MATCH_MP [] lemma = raise ERR "intro_arm_PC" "TRY_MATCH_MP"
     | TRY_MATCH_MP (x::xs) lemma =
         MATCH_MP x lemma handle HOL_ERR _ => TRY_MATCH_MP xs lemma
   val targets =
      arm_decompTheory.arm_OK_def
      |> Thm.concl
      |> boolSyntax.dest_forall |> snd
      |> boolSyntax.rhs
      |> progSyntax.strip_star
      |> List.map get_sep_domain
      |> Lib.butlast
   val arm_ok_cnv =
      PURE_REWRITE_CONV
        [GSYM STAR_ASSOC, PURE_REWRITE_RULE [GSYM STAR_ASSOC] (GSYM arm_OK_def)]
      THENC PURE_REWRITE_CONV [STAR_ASSOC]
      THENC MOVE_OUT_CONV arm_REG_RName_PC_tm
   val aligned_rule =
      CONV_RULE
         ((RATOR_CONV o RAND_CONV)
             (SIMP_CONV bool_ss [Aligned_EQ_ALIGNED, ALIGNED_CLAUSES]))
   val frame_rule =
      SPECL_FRAME_RULE  [``arm_Extensions Extension_VFP T``,
                         ``arm_Extensions Extension_Security F``,
                         ``arm_Architecture ARMv7_A``]
in
   fun intro_arm_PC th =
      th
      |> frame_rule
      |> MOVE_COND_RULE bit_0_14_tm
      |> PRE_POST_RULE (LIST_MOVE_OUT_CONV false targets)
      |> MOVE_COND_RULE GoodMode_tm
      |> MATCH_MP progTheory.SPEC_DUPLICATE_COND
      |> PRE_POST_RULE arm_ok_cnv
      |> MOVE_COND_RULE AlignedPC_tm
      |> PURE_REWRITE_RULE [arm_PC_INTRO1, SEP_CLAUSES]
      |> TRY_MATCH_MP [arm_PC_INTRO2, arm_PC_INTRO3]
      |> aligned_rule
      |> PURE_REWRITE_RULE [GSYM SPEC_MOVE_COND, SEP_CLAUSES]
end

local
   val cnv =
      SIMP_CONV (pure_ss++wordsLib.WORD_ARITH_ss++wordsLib.WORD_ARITH_EQ_ss) []
in
   fun WORD_NOT_EQ_CONV tm =
      if boolSyntax.is_eq (boolSyntax.dest_neg tm)
         then cnv tm
      else raise ERR "WORD_NOT_EQ_CONV" ""
end

local
   fun is_mem tm = fst (boolSyntax.dest_strip_comb tm) = "arm_prog$arm_MEM"
   val get_mems =
      List.filter is_mem o progSyntax.strip_star o progSyntax.dest_pre o
      Thm.concl
   val MEMORY_INSERT = SPEC_ALL arm_MEMORY_INSERT
   val fff = match_term ((fst o dest_eq o concl o UNDISCH_ALL) MEMORY_INSERT)
   val f = mk_var ("m", ``:word32->word8``)
   fun f_intro tm = cdr tm |-> mk_comb (f, cdr (car tm))
   fun df_intro [] = mk_var ("dm", ``:word32 set``)
     | df_intro (v::vs) = pred_setSyntax.mk_delete (df_intro vs, v)
   fun mk_frame ys = mk_comb (mk_comb (``arm_MEMORY``, df_intro ys), f)
   fun compact th =
      let
         val (p, q) = progSyntax.dest_pre_post (Thm.concl th)
         val x1 = find_term (can fff) p
         val x2 = find_term (can fff) q
         val rw1 = UNDISCH (INST (fst (fff x1)) MEMORY_INSERT)
         val rw2 = UNDISCH (INST (fst (fff x2)) MEMORY_INSERT)
      in
         PURE_REWRITE_RULE [rw1, rw2] th
      end
   val rule =
      SIMP_RULE (bool_ss++sep_cond_ss) [] o
      Conv.CONV_RULE
        (LAND_CONV (PURE_REWRITE_CONV [IN_DELETE, WORD_EQ_ADD_CANCEL]
                    THENC Conv.DEPTH_CONV WORD_NOT_EQ_CONV
                    THENC REWRITE_CONV [])
         THENC Conv.REWR_CONV (GSYM SPEC_MOVE_COND)) o
      PURE_REWRITE_RULE
         [STAR_ASSOC, AND_IMP_INTRO, GSYM CONJ_ASSOC, APPLY_UPDATE_ID] o
      DISCH_ALL o
      Lib.repeat compact o
      PURE_REWRITE_RULE [GSYM STAR_ASSOC]
(* testing
   thm
   |> PURE_REWRITE_RULE [GSYM STAR_ASSOC]
   |> Lib.repeat compact
   |> DISCH_ALL
   |> PURE_REWRITE_RULE
        [STAR_ASSOC, AND_IMP_INTRO, GSYM CONJ_ASSOC, APPLY_UPDATE_ID]
   |> Conv.CONV_RULE
        (LAND_CONV (PURE_REWRITE_CONV [IN_DELETE, WORD_EQ_ADD_CANCEL]
                    THENC Conv.DEPTH_CONV WORD_NOT_EQ_CONV
                    THENC REWRITE_CONV [])
         THENC Conv.REWR_CONV (GSYM SPEC_MOVE_COND))
   |> SIMP_RULE (bool_ss++sep_cond_ss) []
*)
in
   fun introduce_arm_MEMORY th =
      let
         val xs = get_mems th
      in
         if List.null xs
            then th
         else let
                 val ts = List.map rator xs
                 val th = th |> PRE_POST_RULE (LIST_MOVE_OUT_CONV false ts)
                             |> Thm.INST (List.map f_intro xs)
                 val ys = List.rev (List.map (cdr o car) (get_mems th))
              in
                 rule (SPECC_FRAME_RULE (mk_frame ys) th)
              end
      end
end

val intro_arm_mem_and_pc =
   introduce_arm_MEMORY o intro_arm_PC o
   PURE_REWRITE_RULE [GSYM L3_ARM_MODEL_def]

local
   val arm_CPSR_T_F = prove(
     ``( n ==> (arm_CPSR_N T = arm_CPSR_N n)) /\
       (~n ==> (arm_CPSR_N F = arm_CPSR_N n)) /\
       ( z ==> (arm_CPSR_Z T = arm_CPSR_Z z)) /\
       (~z ==> (arm_CPSR_Z F = arm_CPSR_Z z)) /\
       ( c ==> (arm_CPSR_C T = arm_CPSR_C c)) /\
       (~c ==> (arm_CPSR_C F = arm_CPSR_C c)) /\
       ( v ==> (arm_CPSR_V T = arm_CPSR_V v)) /\
       (~v ==> (arm_CPSR_V F = arm_CPSR_V v))``,
     SIMP_TAC std_ss []) |> CONJUNCTS |> map UNDISCH;

   val cnv =
      SIMP_CONV std_ss [word_arith_lemma1, word_arith_lemma3,word_arith_lemma4]

   val arm_PC_SIMP =
     [addressTheory.ALIGNED_ADD_EQ, addressTheory.ALIGNED, SEP_CLAUSES,
      utilsLib.map_conv cnv
         [``arm_PC (pc + n2w m + n2w n)``,
          ``arm_PC (pc + n2w m - n2w n)``,
          ``ALIGNED (pc + n2w m + n2w n)``,
          ``ALIGNED (pc + n2w m - n2w n)``]]

   val rule =
      SIMP_RULE (std_ss++sep_cond_ss) arm_PC_SIMP o
      PURE_REWRITE_RULE [GSYM SPEC_MOVE_COND] o
      DISCH_ALL o
      PURE_REWRITE_RULE arm_CPSR_T_F o
      intro_arm_mem_and_pc

   fun is_pc tm = fst (boolSyntax.dest_strip_comb tm) = "arm_decomp$arm_PC"
   val get_pc =
      Term.rand o Option.valOf o List.find is_pc o progSyntax.strip_star
in
   fun format_thm th =
      let
         val th = rule th
         val (p, q) = progSyntax.dest_pre_post (Thm.concl th)
         val pc_var = get_pc p
         val pc = get_pc q
         val next =
            case Lib.total wordsSyntax.dest_word_add pc of
               SOME (x, n) =>
                  if x = pc_var
                     then Lib.total wordsSyntax.uint_of_word n
                  else NONE
             | NONE =>
                 (case Lib.total wordsSyntax.dest_word_sub pc of
                     SOME (x, n) =>
                        if x = pc_var
                           then Lib.total (Int.~ o wordsSyntax.uint_of_word) n
                        else NONE
                   | NONE => if pc = pc_var then SOME 0 else NONE)
      in
         (th, 4, next)
      end
end

local
   val pecond_rule =
      Conv.CONV_RULE
         (Conv.TRY_CONV
            (PRE_CONV
               (Conv.RAND_CONV
                  (Conv.RATOR_CONV (Conv.REWR_CONV (GSYM precond_def))))))
   fun mk_rw_neg tm =
      utilsLib.rhsc
        (Conv.QCONV (REWRITE_CONV [boolTheory.DE_MORGAN_THM])
           (boolSyntax.mk_neg tm))
in
   fun fix_precond [(th1,x1,y1),(th2,x2,y2)] =
      let
         val c = th2 |> SIMP_RULE (pure_ss++sep_cond_ss) []
                     |> PURE_REWRITE_RULE [SPEC_MOVE_COND, AND_IMP_INTRO]
                     |> Thm.concl
                     |> boolSyntax.dest_imp
                     |> fst
         val th1 = pecond_rule (MOVE_COND_RULE (mk_rw_neg c) th1)
         val th2 = pecond_rule (MOVE_COND_RULE c th2)
      in
         [(th1,x1,y1),(th2,x2,y2)]
      end
     | fix_precond res = res
end

val l3_arm_triples = List.map intro_arm_mem_and_pc o arm_progLib.arm_spec_hex

local
   val w0_var = mk_var ("w0", ``:word32``)
in
   fun l3_arm_spec hex =
      let
         val hs = String.tokens (fn c => c = #" ") hex
         val xs = arm_progLib.arm_spec_hex (hd hs)
         val _ = mem (length xs) [1, 2] orelse
                 raise ERR "l3_arm_spec" "unexpected result from arm_spec_hex"
         val w0 = wordsSyntax.mk_wordi (Arbnum.fromHexString (last hs), 32)
         val ys = List.map (format_thm o INST [w0_var |-> w0]) xs
         val ys = fix_precond ys
     in
        if length ys = 1
           then (hd ys, NONE)
        else (hd ys, SOME (el 2 ys))
     end
end

val arm_pc = ``arm_PC``

val (arm_jump:(term -> term -> int -> bool -> string * int)) =
  fn x => fail()

val l3_arm_tools = (l3_arm_spec, arm_jump, aS_HIDE, arm_pc):decompiler_tools;

fun l3_arm_decompile name qcode =
   let
      val (result, func) = decompile l3_arm_tools name qcode
      val result = UNABBREV_CODE_RULE result
   in
      (result,func)
   end

(* testing

open rel_decompilerLib

l3_arm_spec hex

val [(th1,x1,y1),(th2,x2,y2)] = ys

val hex = "B0821003"

val hex = "07921003"

  l3_arm_spec "00821003"

  l3_arm_spec "07921003";
  l3_arm_spec "17921003";
  l3_arm_spec "27921003";
  l3_arm_spec "37921003";
  l3_arm_spec "47921003";
  l3_arm_spec "57921003";
  l3_arm_spec "67921003";
  l3_arm_spec "77921003";
  l3_arm_spec "87921003";
  l3_arm_spec "97921003";
  l3_arm_spec "A7921003";
  l3_arm_spec "B7921003";
  l3_arm_spec "C7921003";
  l3_arm_spec "D7921003";
  l3_arm_spec "E7921003";

fast_decompile "test" `e59f322c  00012f94`

l3_arm_spec "e59f322c  00012f94"

l3_arm_decompile "test" `e59f322c  00012f94`

val th = hd (arm_progLib.arm_spec_hex "E1A01002")
val th = hd (arm_progLib.arm_spec_hex "E1C200D4")
val th = hd (arm_progLib.arm_spec_hex "E891003C")
val th = hd (arm_progLib.arm_spec_hex "E881003C")
val th = hd (arm_progLib.arm_spec_hex "E59F100C")
val th = hd (arm_progLib.arm_spec_hex "EA000001")

val th = hd (arm_progLib.arm_spec "LDR (+imm,pre)")
val th = hd (arm_progLib.arm_spec "STR (+imm,pre)")

val th' = Count.apply intro_arm_PC th
val th' = Count.apply intro_arm_mem_and_pc th
val th' = Count.apply format_thm th
val th = th'

*)

end
