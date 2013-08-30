structure arm_decompLib :> arm_decompLib =
struct

open HolKernel Parse boolLib bossLib;
open helperLib set_sepTheory addressTheory progTheory;
open pred_setTheory combinTheory;
open arm_decompTheory decompilerLib;

infix \\
val op \\ = op THEN;

val _ = arm_progLib.arm_config "vfp";
val _ = arm_progLib.set_newline "";

(* automation *)

fun HIDE_PRE_POST_RULE tm th =
  th |> HIDE_POST_RULE tm |> HIDE_PRE_RULE tm;

fun intro_arm_OK th = let
  val th = if can (find_term (can (match_term ``arm_Extensions Extension_VFP``)))
                  (concl th)
           then th else SPEC_FRAME_RULE th ``arm_Extensions Extension_VFP T``
  val th = if can (find_term (can (match_term ``arm_Architecture ARMv7_A``)))
                  (concl th)
           then th else SPEC_FRAME_RULE th ``arm_Architecture ARMv7_A``
  val pat = ``word_bit 0 (r14:word32)``
  val th = if not (can (find_term (can (match_term pat))) (concl th)) then th else
    let val tm = find_term (can (match_term pat)) (concl th)
        in REWRITE_RULE [ASSUME (mk_neg tm)] th
               |> DISCH (mk_neg tm)
               |> REWRITE_RULE [GSYM SPEC_MOVE_COND] end
  val xs = arm_OK_def |> concl |> rand |> list_dest dest_star |> map get_sep_domain
  val move = foldr (fn (x,c) => MOVE_OUT_CONV x THENC c) ALL_CONV xs
             THENC REWRITE_CONV [GSYM STAR_ASSOC,
                     RW [GSYM STAR_ASSOC] (GSYM arm_OK_def)]
             THENC REWRITE_CONV [STAR_ASSOC]
  in CONV_RULE (PRE_CONV move THENC POST_CONV move) th end

val arm_PC_INTRO3 =
  arm_PC_INTRO2 |> Q.INST [`p1`|->`emp`,`p2`|->`emp`]
                |> RW [SEP_CLAUSES]

fun TRY_MATCH_MP [] lemma = fail()
  | TRY_MATCH_MP (x::xs) lemma =
      MATCH_MP x lemma handle HOL_ERR _ => TRY_MATCH_MP xs lemma

fun intro_arm_PC th =
  th |> intro_arm_OK
     |> CONV_RULE (PRE_CONV (MOVE_OUT_CONV ``arm_REG RName_PC``))
     |> CONV_RULE (POST_CONV (MOVE_OUT_CONV ``arm_REG RName_PC``))
     |> DISCH ``Aligned (pc:word32,4)`` |> SIMP_RULE bool_ss []
     |> ONCE_REWRITE_RULE [GSYM SPEC_MOVE_COND]
     |> PURE_REWRITE_RULE [arm_PC_INTRO1,SEP_CLAUSES]
     |> TRY_MATCH_MP [arm_PC_INTRO2,arm_PC_INTRO3]
     |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV bool_ss
          [Aligned_EQ_ALIGNED,ALIGNED_CLAUSES]))
     |> PURE_REWRITE_RULE [GSYM SPEC_MOVE_COND,SEP_CLAUSES]

fun introduce_arm_MEMORY th = if
  not (can (find_term (can (match_term ``arm_MEM``))) (concl th))
  then th else let
  val (_,p,_,q) = dest_spec(concl th)
  val xs = (rev o list_dest dest_star) p
  val tm = (fst o dest_eq o concl o SPEC_ALL) arm_progTheory.arm_MEM_def
  val xs = filter (can (match_term tm)) xs
  val ts = map rator xs
  val move = foldr (fn (tm,c) => MOVE_OUT_CONV tm THENC c) ALL_CONV ts
  val th = CONV_RULE (PRE_CONV move THENC POST_CONV move) th
  fun foo tm = cdr tm |-> mk_comb(mk_var("f",``:word32->word8``),(cdr o car) tm)
  val th = INST (map foo xs) th
  in if xs = [] then th else let
    val (_,p,_,q) = dest_spec(concl th)
    val xs = (rev o list_dest dest_star) p
    val tm = (fst o dest_eq o concl o SPEC_ALL) arm_progTheory.arm_MEM_def
    val xs = filter (can (match_term tm)) xs
    val ys = (map (cdr o car) xs)
    fun foo [] = mk_var("df",``:word32 set``)
      | foo (v::vs) = pred_setSyntax.mk_delete(foo vs,v)
    val frame = mk_comb(mk_comb(``arm_MEMORY``,foo ys),
                        mk_var("f",``:word32->word8``))
    val th = SPEC frame (MATCH_MP progTheory.SPEC_FRAME th)
    val th = RW [GSYM STAR_ASSOC] th
    val fff = (fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) arm_MEMORY_INSERT
    fun compact th = let
      val x = find_term (can (match_term fff)) ((car o car o concl o UNDISCH_ALL) th)
      val rw = (INST (fst (match_term fff x)) o SPEC_ALL) arm_MEMORY_INSERT
      val th = DISCH ((fst o dest_imp o concl) rw) th
      val th = SIMP_RULE bool_ss [arm_MEMORY_INSERT] th
      in th end
    val th = repeat compact th
    val th = RW [STAR_ASSOC,AND_IMP_INTRO,GSYM CONJ_ASSOC] th
    val th = RW [APPLY_UPDATE_ID] th
    val th = SIMP_RULE std_ss [IN_DELETE,WORD_EQ_ADD_CANCEL] th
             |> SIMP_RULE (std_ss++wordsLib.SIZES_ss) [wordsTheory.n2w_11]
             |> PURE_REWRITE_RULE [GSYM SPEC_MOVE_COND]
    val th = SIMP_RULE (bool_ss++sep_cond_ss) [] th
    val th = Q.INST [`df`|->`dm`,`f`|->`m`] th
    in th end end

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

fun format_thm th = let
  val th = th |> PURE_REWRITE_RULE [GSYM L3_ARM_MODEL_def]
              |> intro_arm_PC |> introduce_arm_MEMORY
              |> PURE_REWRITE_RULE arm_CPSR_T_F
              |> DISCH_ALL |> PURE_REWRITE_RULE [GSYM SPEC_MOVE_COND]
(*
              |> SIMP_RULE (std_ss ++ sep_cond_ss) [word_arith_lemma1,
                   word_arith_lemma3,word_arith_lemma4]
*)
  val pc_var = th |> concl |> rator
                  |> find_term (can (match_term ``arm_PC pc``)) |> rand
  val pc = th |> concl |> rand
              |> find_term (can (match_term ``arm_PC pc``)) |> rand
  val next = (let val (i,s) = match_term ``(pc:word32) + n2w n`` pc
                  val _ = (subst i pc_var = pc_var) orelse fail()
                  val n = subst i ``n:num`` |> numSyntax.int_of_term
                  in SOME n end handle HOL_ERR _ =>
              let val (i,s) = match_term ``(pc:word32) - n2w n`` pc
                  val _ = (subst i pc_var = pc_var) orelse fail()
                  val n = subst i ``n:num`` |> numSyntax.int_of_term
                  in SOME (0 - n) end handle HOL_ERR _ =>
              if pc = pc_var then SOME 0 else NONE)
  in (th,4,next) end

fun fix_precond [(th1,x1,y1),(th2,x2,y2)] = let
  val th = PURE_REWRITE_RULE [SPEC_MOVE_COND,AND_IMP_INTRO] th2
  val c = th |> concl |> dest_imp |> fst
  val not_c = mk_neg c
  val th1 = PURE_REWRITE_RULE [SPEC_MOVE_COND,AND_IMP_INTRO] th1
  val ss = SIMP_CONV std_ss [ASSUME not_c]
  val th1 = CONV_RULE ((RATOR_CONV o RAND_CONV) ss) th1
            |> RW [] |> RW [GSYM SPEC_MOVE_COND]
  val th1 = th1 |> DISCH not_c
  val ss = SIMP_CONV std_ss []
  val th1 = CONV_RULE ((RATOR_CONV o RAND_CONV) ss) th1
            |> RW [] |> RW [GSYM (SPEC_MOVE_COND |> RW [GSYM precond_def])]
  val th2 = RW [GSYM precond_def] th2
  in [(th1,x1,y1),(th2,x2,y2)] end
  | fix_precond res = res

fun l3_arm_triples hex = let
  val xs = arm_progLib.arm_spec_hex hex
  fun f th = th |> PURE_REWRITE_RULE [GSYM L3_ARM_MODEL_def]
                |> intro_arm_PC |> introduce_arm_MEMORY
  in map f xs end;

val hex = arm_progLib.arm_spec_hex "eef1fa10"

fun l3_arm_spec hex = let
  val hs = String.tokens (fn c => c = #" ") hex
  val xs = arm_progLib.arm_spec_hex (hd hs)
  val n = Arbnum.fromHexString (last hs) |> numSyntax.mk_numeral
  val w0 = wordsSyntax.mk_n2w(n,``:32``)
  val w0_var = mk_var("w0",``:word32``)
  val xs = map (INST [w0_var|->w0]) xs
  val _ = mem (length xs) [1,2] orelse failwith "unexpected result from arm_spec_hex"
  val ys = map format_thm xs
  val ys = fix_precond ys
  in if length ys = 1 then (hd ys, NONE) else (hd ys, SOME (el 2 ys)) end

val arm_pc = ``arm_PC``

val (arm_jump:(term -> term -> int -> bool -> string * int)) =
  fn x => fail()

val l3_arm_tools = (l3_arm_spec, arm_jump, aS_HIDE, arm_pc):decompiler_tools;

fun l3_arm_decompile name qcode = let
  val tools = l3_arm_tools
  val (result,func) = decompile tools name qcode
  val result = UNABBREV_CODE_RULE result
  in (result,func) end;

end
