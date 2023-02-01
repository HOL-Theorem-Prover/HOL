structure derive_specsLib :> derive_specsLib =
struct

open HolKernel boolLib bossLib Parse;
open wordsTheory pred_setTheory arithmeticTheory pairSyntax;
open set_sepTheory progTheory addressTheory;
open helperLib backgroundLib file_readerLib stack_introLib stack_analysisLib
open writerLib;
open GraphLangTheory

fun spec_rule x =
  case !arch_name of
    ARM   => arm_spec x
  | ARM8  => arm8_spec x
  | M0    => m0_spec x
  | RISCV => riscv_spec x;

(* code abbrevs *)

val code_abbreviations = ref ([]:thm list);
fun add_code_abbrev thms = (code_abbreviations := thms @ !code_abbreviations);

(* formatting *)

fun DISCH_ALL_AS_SINGLE_IMP th = let
  val th = RW [AND_IMP_INTRO] (DISCH_ALL th)
  in if is_imp (concl th) then th else DISCH ``T`` th end

(* thm traces *)

fun next_possible_pcs f (th,i,SOME j,p) =
     if can (find_term (fn tm => aconv tm ``GUARD``)) (concl th)
     then all_distinct [j,p+i] else [j]
  | next_possible_pcs f (th,i,NONE,p) =
    ((th |> concl |> cdr |> find_terms (can (match_term ``p+(n2w n):word32``))
         |> filter (fn tm => wordsSyntax.is_word_add tm)
         |> filter (fn tm => wordsSyntax.is_n2w (cdr tm))
         |> filter (fn tm => aconv (cdr (car tm)) (mk_var("p",``:word32``)))
         |> map (numSyntax.int_of_term o cdr o cdr)
         |> map f
         |> sort (fn x => fn y => x <= y))
      handle HOL_ERR _ => fail())

datatype 'a thm_trace =
    TRACE_CUT of int (* cut because a different branch describes the rest *)
  | TRACE_END of 'a (* normal end *)
  | TRACE_STEP of int * 'a * thm * ('a thm_trace)
  | TRACE_SPLIT of ('a thm_trace) list;

fun print_cfg t = let
  fun cfg2str prefix (TRACE_CUT p) = "repeat from " ^ (int_to_string p) ^ "\n" ^ prefix
    | cfg2str prefix (TRACE_END _) = "return\n" ^ prefix
    | cfg2str prefix (TRACE_STEP (p,_,th,t)) = int_to_string p ^ " " ^ cfg2str prefix t
    | cfg2str prefix (TRACE_SPLIT qs) = let
        val s = "\n" ^ prefix ^ ". " ^ concat (map (cfg2str (prefix ^ ". ")) qs)
        in String.substring(s,0,size(s)-2) end
  in print ("\n\nCFG:\n  " ^ cfg2str "  " t ^ "\n\n") end;

(*

There's a bug in the trace generation to do with guards that are not
just one variable. The following code shows how this happens:

  val code = ["e92d47f0", "e3520003", "959ac000", "97de9002",
              "979cc109", "8590c00c", "e8bd87f0"]

print_cfg (construct_thm_trace thms)

*)

fun bool_normal_form tm = let
  val vars = free_vars tm
  val vsort = sort (fn v1 => fn v2 => fst (dest_var v1) <= fst (dest_var v2))
  val vs = vsort vars
  fun aux t [] = t
    | aux t (v::vs) =
        mk_cond(v,aux (subst [v|->T] t) vs,aux (subst [v|->F] t) vs)
  in SIMP_CONV std_ss [] (aux tm vs) |> concl |> dest_comb |> snd end

fun construct_thm_trace thms = let
  fun list_lookup i [] = fail()
    | list_lookup i ((j,x,NONE)::xs) = if i = j then [x] else list_lookup i xs
    | list_lookup i ((j,x,SOME y)::xs) = if i = j then [x,y] else list_lookup i xs
  fun extract_pre (th,i,j) = let
    val th = RW [] th
    val guard = cdr (find_term (can (match_term ``GUARD n b``)) (concl th))
    in (th,bool_normal_form guard) end handle HOL_ERR _ => (th,T)
  fun resets_status_bits th = let
    val (_,p,_,q) = dest_spec (concl th)
    val pv = free_vars p |> filter (fn tm => type_of tm = ``:bool``)
    val qv = free_vars q |> filter (fn tm => type_of tm = ``:bool``)
    in not (null (term_diff pv qv)) end
  fun guard_conj guard (th,pre) =
    (th,if resets_status_bits th then pre else bool_normal_form (mk_conj(pre,guard)))
  fun next_directions th =
    ((th |> concl |> cdr |> find_terms (can (match_term ``p+(n2w n):word32``))
         |> filter (fn tm => wordsSyntax.is_word_add tm)
         |> filter (fn tm => wordsSyntax.is_n2w (cdr tm))
         |> filter (fn tm => aconv (cdr (car tm)) (mk_var("p",``:word32``)))
         |> map (numSyntax.int_of_term o cdr o cdr)
         |> sort (fn x => fn y => x <= y)))
  fun mk_TRACE_SPLIT [] = TRACE_END T
    | mk_TRACE_SPLIT [x] = x
    | mk_TRACE_SPLIT xs = TRACE_SPLIT xs
  val aux_calls = ref (tl [(0,T)])
  fun int_term_mem (p,tm) [] = false
    | int_term_mem (p,tm) ((x,y)::xs) =
        (p = x andalso aconv tm y) orelse int_term_mem (p,tm) xs
  (* warning: the handling of guards is not perfect, but maybe good enough *)
  fun aux (p:int) (seen:int list) (guard:term) =
    if int_term_mem (p,guard) (!aux_calls) then TRACE_CUT p else
    (aux_calls := (p,guard)::(!aux_calls);
     if mem p seen then TRACE_CUT p else let
       (* finds theorems describing program point p *)
       val xs = list_lookup p thms
       (* extract boolean precondition *)
       val xs = map extract_pre xs
       (* combine with current guard if theorem does not reset status bits *)
       val xs = map (guard_conj guard) xs
       (* remove dead paths *)
       val xs = filter (fn (_,pre) => not (aconv pre F)) xs
       (* reads the next pcs *)
       val ys = map (fn (th,gg) => (th,gg,next_directions th)) xs
       in mk_TRACE_SPLIT (map (fn (th,gs,nexts) =>
            TRACE_STEP (p, gs, th, mk_TRACE_SPLIT (map
              (fn n => aux (n:int) (p::seen) (gs:term)) nexts))) ys) end)
  fun is_nop th = (null (hyp th)) andalso
                  can (find_term (fn tm => aconv tm ``GUARD``)) (concl th)
  fun filter_nops (TRACE_CUT p) = TRACE_CUT p
    | filter_nops (TRACE_END d) = TRACE_END d
    | filter_nops (TRACE_SPLIT ts) = TRACE_SPLIT (map filter_nops ts)
    | filter_nops (TRACE_STEP (p,x,th,t)) =
        if is_nop th then filter_nops t else TRACE_STEP (p,x,th,filter_nops t)
  val result = aux 0 [] T
  in result end


(* derive SPEC theorems *)

fun pair_apply f ((th1,x1:int,x2:int option),NONE) = ((f th1,x1,x2),NONE)
  | pair_apply f ((th1,x1,x2),SOME (th2,y1:int,y2:int option)) =
      ((f th1,x1,x2),SOME (f th2,y1,y2))

fun jump_apply f NONE = NONE | jump_apply f (SOME x) = SOME (f x);

fun pair_jump_apply (f:int->int) ((th1,x1:int,x2:int option),NONE) = ((th1,x1,jump_apply f x2),NONE)
  | pair_jump_apply f ((th1:thm,x1,x2),SOME (th2:thm,y1:int,y2:int option)) =
      ((th1,x1,jump_apply f x2),SOME (th2,y1,jump_apply f y2));

val switch_input = ref (0:int ,[]:string list);

val CARRY_OUT_LEMMA =
  ``CARRY_OUT (x : 'a word) y T``
  |> ONCE_REWRITE_CONV [GSYM WORD_NOT_NOT]
  |> RW [ADD_WITH_CARRY_SUB]
  |> RW [WORD_NOT_NOT]

val OVERFLOW_LEMMA =
  ``OVERFLOW (x : 'a word) y T``
  |> ONCE_REWRITE_CONV [GSYM WORD_NOT_NOT]
  |> RW [ADD_WITH_CARRY_SUB]
  |> RW [WORD_NOT_NOT]

val WORD_NOT_EQ_LESS_EQ = blastLib.BBLAST_PROVE
  ``v <> w /\ v <=+ w <=> v <+ w:word32``
  |> (fn th => CONJ th (RW1 [CONJ_COMM] th))
  |> (fn th => CONJ th (RW1 [NEQ_SYM] th))
  |> RW [GSYM CONJ_ASSOC] |> GEN_ALL

local
  val cond_pat = cond_def |> SPEC_ALL |> concl |> dest_eq |> fst
in
  fun STAR_cond_CONV c tm = let
    val (x,y) = dest_star tm
    val _ = match_term cond_pat y
    in RAND_CONV (RAND_CONV c) tm end
end

local
  val d32 = CONJ (EVAL ``dimindex (:32)``) (EVAL ``dimword (:32)``)
  val d64 = CONJ (EVAL ``dimindex (:64)``) (EVAL ``dimword (:64)``)
  val word32_mem_pat = ``word32 (READ8 w1 m) (READ8 w2 m) (READ8 w3 m) (READ8 w4 m)``
  val word64_mem_pat = ``word64 (READ8 w1 m) (READ8 w2 m) (READ8 w3 m) (READ8 w4 m)
                                (READ8 w5 m) (READ8 w6 m) (READ8 w7 m) (READ8 w8 m)``
  val Align_pat1 = ``arm$Align (w:'a word,n)``
  val Align_pat2 = ``m0$Align (w:'a word,n)``
  (* ``b /\ ~(w ' 0) /\ b2 /\ (b3 ==> ALIGNED w) /\ ~(w ' 1)`` *)
  val clean_ALIGNED_CONV =
    SIMP_CONV (bool_ss++boolSimps.CONJ_ss) [BITS_01_IMP_ALIGNED] THENC
    SIMP_CONV (bool_ss++boolSimps.CONJ_ss) [ALIGNED_IMP_BITS_01]
  val n2w_64 =
    n2w_11 |> INST_TYPE [alpha|->``:64``] |> REWRITE_RULE [EVAL ``dimword (:64)``]
  val word_arith_lemma_CONV =
    SIMP_CONV std_ss [word_arith_lemma1] THENC
    SIMP_CONV std_ss [word_arith_lemma3,word_arith_lemma4,WORD_EQ_SUB_ZERO,n2w_64]
  val flag_conv =
    SIMP_CONV std_ss
      [OVERFLOW_EQ,WORD_MSB_1COMP,WORD_NOT_NOT,
       GSYM carry_out_def,WORD_0_POS,WORD_SUB_RZERO,
       GSYM (EVAL ``~(0w:word32)``),d32,
       GSYM (EVAL ``~(0w:word64)``),d64] THENC
    ONCE_REWRITE_CONV [word_1comp_n2w,word32_msb_n2w] THENC
    SIMP_CONV std_ss [d32,d64]
  val finalise_pre_cond =
    PRE_CONV (SIMP_CONV (pure_ss++sep_cond_ss) [] THENC
              TRY_CONV (STAR_cond_CONV wordsLib.WORD_SUB_CONV))
  val final_conv = clean_ALIGNED_CONV THENC word_arith_lemma_CONV
                   THENC flag_conv THENC finalise_pre_cond
  fun is_Align tm = can (match_term Align_pat1) tm orelse
                    can (match_term Align_pat2) tm
  fun remove_Align th =
    if not (can (find_term is_Align) (concl th)) then th else let
      val tms = find_terms is_Align (concl th)
      val rws = map (fn tm => SPEC (tm |> rand |> pairSyntax.dest_pair |> fst)
                       REMOVE_Align |> UNDISCH) tms
      in PURE_REWRITE_RULE rws th |> DISCH_ALL
         |> PURE_REWRITE_RULE [GSYM SPEC_MOVE_COND]
         |> SIMP_RULE (pure_ss++sep_cond_ss) [] end
  fun READ8_INTRO_CONV tm =
    (if tm |> rator |> is_var then REWR_CONV (GSYM READ8_def) tm
     else NO_CONV tm)
    handle HOL_ERR _ => NO_CONV tm
  val lemma31 = blastLib.BBLAST_PROVE
    ``(((((31 >< 1) (w:word32)):31 word) @@ (0w:1 word)) : word32) =
      w && 0xFFFFFFFEw``
  val fix_sub_word64 = prove(
    ``(n2w n + w = if n < dimword (:'a) DIV 2 then n2w n + (w:'a word)
                   else w - n2w (dimword (:'a) - n MOD dimword (:'a))) /\
      (w + n2w n = if n < dimword (:'a) DIV 2 then w + n2w n
                   else w - n2w (dimword (:'a) - n MOD dimword (:'a)))``,
    simp [Once WORD_ADD_COMM] \\ rw []
    \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [GSYM WORD_NEG_NEG]))
    \\ rewrite_tac [WORD_EQ_NEG,word_2comp_n2w])
    |> INST_TYPE [alpha|->``:64``]
    |> SIMP_RULE std_ss [EVAL ``dimword (:64)``]
  val riscv_mask_byte =
    blastLib.BBLAST_PROVE ``w2w (w && 2w ≪ 7 − 1w) = (w2w (w:word64)) : word8``
in
  fun clean_spec_thm th = let
    val th = th |> REWRITE_RULE [GSYM word32_def, GSYM word64_def,
                     decomp_simp1,GSYM READ32_def,GSYM READ64_def,
                     GSYM WRITE32_def,GSYM WRITE64_def,WRITE64_intro,riscv_mask_byte,
                     word_extract_thm,GSYM word_add_with_carry_def]
                |> CONV_RULE (DEPTH_CONV READ8_INTRO_CONV)
                |> REWRITE_RULE [GSYM WRITE8_def]
                |> SIMP_RULE std_ss [AC CONJ_COMM CONJ_ASSOC,word_bit_def,d32,d64,
                     SHIFT_ZERO(*,WORD_MUL_LSL,word_mul_n2w*),
                     GSYM ADD_ASSOC,lemma31,count_leading_zero_bits_thm]
    val tms32 = find_terms (can (match_term word32_mem_pat)) (concl th)
    val tms64 = find_terms (can (match_term word64_mem_pat)) (concl th)
    fun READ32_RW tm = let
      val (y,x) = tm |> rand |> dest_comb
      val goal = mk_eq(tm,``READ32 ^(rand y) ^x``)
      val c =
        SIMP_CONV std_ss [READ32_def,word_arith_lemma1,READ8_def] THENC
        SIMP_CONV std_ss [word_arith_lemma2,word_arith_lemma3,word_arith_lemma4]
      in MATCH_MP EQ_T (c goal) end handle HOL_ERR _ => TRUTH;
    fun READ64_RW tm = let
      val (y,x) = tm |> rand |> dest_comb
      val goal = mk_eq(tm,``READ64 ^(rand y) ^x``)
      val c =
        SIMP_CONV std_ss [READ64_def,word_arith_lemma1,READ8_def] THENC
        SIMP_CONV std_ss [word_arith_lemma2,word_arith_lemma3,word_arith_lemma4]
      in MATCH_MP EQ_T (c goal) end handle HOL_ERR _ => TRUTH;
    val th = th |> PURE_REWRITE_RULE ([ALIGNED_Align] @ map READ32_RW tms32
                                                      @ map READ64_RW tms64)
    val th = remove_Align th
    val th = CONV_RULE final_conv th
    val th = SIMP_RULE std_ss [word_cancel_extra] th
             |> CONV_RULE word_arith_lemma_CONV
    val th = th |> ONCE_REWRITE_RULE [fix_sub_word64]
                |> SIMP_RULE std_ss [m0_preprocessing]
    in th end
end

fun remove_arm_CONFIGURE th =
  if can (find_term (fn tm => aconv tm ``arm_CONFIG``)) (concl th) then let
    val var = ``var:bool``
    val pat = ``arm_CONFIG (VFPv3,ARMv7_A,F,^var,mode)``
    val m = match_term pat
    val n = subst (fst (m (find_term (can m) (concl th)))) var
    val th = DISCH (mk_neg n) th |> SIMP_RULE bool_ss []
       |> SIMP_RULE (bool_ss++sep_cond_ss) [GSYM SPEC_MOVE_COND,
            GSYM arm_decompTheory.arm_OK_def]
    val _ = if can m (concl th)
            then failwith "unable to remove arm_CONFIGURE" else ()
    in th end
  else th

(*
val (pos,switch_code) = !switch_input
*)

fun get_spec_for_switch (pos,switch_code) = let
  val _ = (switch_input := (pos,switch_code))
  fun remove_colon_prefix s = last (String.tokens (fn x => x = #":") s)
  val raw_code = map remove_colon_prefix switch_code
  val ((th1,_,_),_) = spec_rule (el 1 raw_code)
  val ((th2,_,_),th2a) = spec_rule (el 2 raw_code)
  val ((th3,_,_),_) = spec_rule (el 3 raw_code)
  val (th2a,_,_) = the th2a
  val (_,_,sts,_) = get_tools()
  val (reg,case_count) = let
    val thB = SPEC_COMPOSE_RULE [th1,th2a,th3]
    val thB = thB |> SIMP_RULE (std_ss++sep_cond_ss) [precond_def,
                      SPEC_MOVE_COND,CARRY_OUT_LEMMA,WORD_EQ_SUB_ZERO]
                |> CONV_RULE (BINOP1_CONV (SIMP_CONV (srw_ss()) []))
                |> RW [WORD_NOT_EQ_LESS_EQ]
                |> Q.INST [`pc`|->`n2w ^(numLib.term_of_int pos)`]
                |> SIMP_RULE (srw_ss()) [word_add_n2w,OVERFLOW_LEMMA]
                |> CONV_RULE (SIMP_CONV (pure_ss++star_ss) [] THENC
                              REWRITE_CONV [STAR_ASSOC])
    val reg = thB |> concl |> find_term (can (match_term ``arm_REG x y``))
    in (reg,thB |> concl |> dest_imp |> fst |> rator |> rand |> rand
                         |> numLib.int_of_term |> (curry (op +) 1)) end
  fun genlist f 0 k = []
    | genlist f n k = f k :: genlist f (n-1) (k+1)
  val targets = zip (genlist I case_count 0) (take case_count (drop 3 raw_code))
  val thA = th2
  val thA = RW [WORD_CMP_NORMALISE,precond_def] thA
  val thA = thA |> DISCH ``arm$Aligned (w0:word32,2)``
                |> SIMP_RULE std_ss [Aligned_Align]
  val thA = remove_arm_CONFIGURE thA
  val thA = thA |> Q.INST [`pc`|->`n2w ^(numLib.term_of_int (pos+4))`]
  val thA = thA |> Q.INST [`w0`|->`n2w target`]
  val thA = thA |> INST [reg |> rand|->``n2w n:word32``]
  fun eval_case (c,p) = let
    val n = p |> Arbnum.fromHexString |> Arbnum.toInt |> numLib.term_of_int
    val cnv = PRE_CONV (MOVE_OUT_CONV (rator reg)) THENC
              POST_CONV (MOVE_OUT_CONV (rator reg))
    val th = thA |> INST [``target:num``|->n,``n:num``|->numSyntax.term_of_int c]
    val th = th |> SIMP_RULE (srw_ss()) [armTheory.Aligned_def,armTheory.Align_def,
                      CARRY_OUT_LEMMA,OVERFLOW_LEMMA]
                |> CONV_RULE (PRE_CONV ((RAND_CONV o RAND_CONV)
                     (REWRITE_CONV [armTheory.Aligned_def,armTheory.Align_def]
                      THENC EVAL))) |> RW [SEP_CLAUSES]
                |> CONV_RULE cnv |> RW1 [SWITCH_LEMMA] |> SPEC (rand reg)
                |> CONV_RULE (SIMP_CONV (pure_ss++star_ss) [] THENC
                              REWRITE_CONV [STAR_ASSOC])
    in th end
  val xs = map eval_case targets
  fun combine (x,th) = MATCH_MP SWITCH_COMBINE (CONJ x th)
  val th = foldr combine (last xs) (butlast xs)
  val assum = th |> concl |> dest_imp |> fst
  val (w,n) = dest_eq(repeat (snd o dest_imp) assum)
  val new_assum = ``^w <+ ^n + 1w``
  val lemma = blastLib.BBLAST_PROVE (mk_imp(new_assum,assum))
  val th =
    MP th (UNDISCH lemma)
       |> DISCH_ALL
       |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss [word_add_n2w]))
       |> RW [GSYM SPEC_MOVE_COND]
  val (_,_,c,_) = dest_spec (concl th)
  val code_list = find_terms pairSyntax.is_pair c |> term_all_distinct
  val code_set = code_list |> pred_setSyntax.mk_set
  val th = MATCH_MP SPEC_SUBSET_CODE th |> SPEC code_set
     |> CONV_RULE (BINOP1_CONV (REWRITE_CONV [UNION_SUBSET,
          INSERT_SUBSET,EMPTY_SUBSET,IN_INSERT]))
  val th = MP th TRUTH
  val th2a = th2a |> Q.INST [`pc`|->`n2w ^(numLib.term_of_int (pos+4))`]
  val (_,_,c,_) = dest_spec (concl th)
  val th2a = MP (MATCH_MP SPEC_SUBSET_CODE th2a |> SPEC c
                 |> CONV_RULE (BINOP1_CONV (EVAL))) TRUTH
  in (th1,th,th2a,th3, (length code_list)) end

fun inst_pc_var tools thms = let
  fun triple_apply f (y,(th1,x1:int,x2:int option),NONE) = (y,(f y th1,x1,x2),NONE)
    | triple_apply f (y,(th1,x1,x2),SOME (th2,y1:int,y2:int option)) =
        (y,(f y th1,x1,x2),SOME (f y th2,y1,y2))
  val i = [mk_var("eip",``:word32``) |-> mk_var("p",``:word32``),
           mk_var("rip",``:word64``) |-> mk_var("p",``:word64``)]
  val (_,_,_,pc) = tools
  val ty = (hd o snd o dest_type o type_of) pc
  fun f y th = let
    val aa = (hd o tl o snd o dest_type) ty
    val th = INST i th
    val (_,p,_,_) = dest_spec (concl th)
    val pattern = inst [``:'a``|->aa] ``(p:'a word) + n2w n``
    val new_p = subst [mk_var("n",``:num``)|-> numSyntax.mk_numeral (Arbnum.fromInt y)] pattern
    val th = INST [mk_var("p",type_of new_p)|->new_p] th
    val (_,_,_,q) = dest_spec (concl th)
    val tm = find_term (fn tm => aconv (car tm) pc handle HOL_ERR e => false) q handle HOL_ERR _ => ``T``
    val cc = SIMP_CONV std_ss [word_arith_lemma1,word_arith_lemma3,word_arith_lemma4]
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV) cc) th
    val thi = QCONV cc tm
    in PURE_ONCE_REWRITE_RULE [thi,WORD_ADD_0] th end;
  in map (triple_apply f) thms end

fun pull_let_wider_CONV tm = let
  val x = find_term (can (pairSyntax.dest_anylet)) tm
  val (y,d) = pairSyntax.dest_anylet x
  val tm2 = pairSyntax.mk_anylet(y,subst [x|->d] tm)
  val goal = mk_eq(tm,tm2)
  val lemma = auto_prove "pull_let_wider_CONV" (goal,
    SIMP_TAC std_ss [LET_DEF]
    THEN CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
    THEN REWRITE_TAC [])
  in lemma end handle HOL_ERR _ => NO_CONV tm;

local
  val pc_var1_32 = mk_var("pc",``:word32``)
  val pc_var2_32 = mk_var("p",``:word32``)
  val pc_var1_64 = mk_var("pc",``:word64``)
  val pc_var2_64 = mk_var("p",``:word64``)
  fun get_pc_pat () = let
    val (_,_,_,pc) = get_tools ()
    in ``^pc w`` end
in
  fun inst_pc pos th = let
    val new_pc_32 = ``n2w ^(numSyntax.term_of_int pos):word32``
    val new_pc_64 = ``n2w ^(numSyntax.term_of_int pos):word64``
    val th = INST [pc_var1_32 |-> new_pc_32, pc_var2_32 |-> new_pc_32,
                   pc_var1_64 |-> new_pc_64, pc_var2_64 |-> new_pc_64] th
    val pc_pat = get_pc_pat ()
    val tms = find_terms (can (match_term pc_pat)) (rand (concl th))
    val rws = map (QCONV (RAND_CONV EVAL)) tms
    val th = ONCE_REWRITE_RULE rws th
    in th end
end

fun mk_call_tag fname is_tail_call = let
  val b = if is_tail_call then T else F
  val fname_tm = stringSyntax.fromMLstring fname
  in mk_comb(mk_comb(``CALL_TAG``,fname_tm),b) end

fun dest_call_tag tm = let
  val (xy,z) = dest_comb tm
  val (x,y) = dest_comb xy
  val _ = (aconv x ``CALL_TAG``) orelse fail()
  in (stringSyntax.fromHOLstring y,
      if aconv z T then true else
      if aconv z F then false else fail()) end

exception NoInstructionSpec

fun wrap_get_spec f asm = f asm
  handle HOL_ERR e => if #origin_structure e = "arm_progLib"
  then raise NoInstructionSpec
  else failwith ("Unable to derive spec for " ^ asm ^ ": " ^ format_ERR e)

fun derive_individual_specs code = let
  val tools = get_tools()
  fun mk_new_var prefix v = let
    val (n,ty) = dest_var v
    in mk_var (prefix ^ "@" ^ n, ty) end
  val (f,_,hide_th,pc) = tools
  fun get_model_status_list th =
    (map dest_sep_hide o list_dest dest_star o snd o dest_eq o concl) th handle HOL_ERR e => []
  val delete_spaces = (implode o filter (fn x => not(x = #" ")) o explode)
  fun list_find name [] = fail ()
    | list_find name ((x,y)::xs) = if name = x then y else list_find name xs
  val prefix_len = size "switch:"
  fun remove_switch_prefix s =
    if String.isPrefix "switch:" s
    then remove_switch_prefix (String.substring(s,prefix_len,size s - prefix_len)) else s
  val bad_insts = ["rfeia","mrc","mcr","mcrr","strex","cpsid","svc"]
  fun bad_instruction asm_name =
    length (filter (fn s => String.isPrefix s asm_name) bad_insts) <> 0
  val white_chars = explode " \t\n"
  fun get_asm_name asm = asm |> String.tokens (fn c => mem c white_chars) |> hd

(*
  val ((th,_,_),_) = res
  val th = (inst_pc pos o RW [precond_def]) th
*)

  fun get_local_const pos = let
    val (_,c,_) = first (fn (p,_,_) => p = pos) code
    val _ = String.isPrefix "const:" c orelse failwith "const load from non-const"
    val hex = String.tokens (fn c => c = #":") c |> el 2
    val tm = Arbnum.fromHexString hex |> numSyntax.mk_numeral
    in ``n2w (^tm):word32`` end
  fun has_free_vars tm = length (free_vars tm) <> 0
  fun inst_pc_rel_const th = let
    val (_,_,c,_) = dest_spec (concl th)
    in if not (has_free_vars c) then th else let
         fun do_inst tm = let
           val (pos_tm,v) = pairSyntax.dest_pair tm
           in v |-> get_local_const (pos_tm |> rand
                                            |> numSyntax.int_of_term) end
         val i = find_terms (fn tm => pairSyntax.is_pair tm andalso
                                      is_var (rand tm)) c
                 |> map (do_inst o rand o concl o QCONV EVAL)
         val th = INST i th |> CONV_RULE (RATOR_CONV (RAND_CONV EVAL))
         in th end end

  fun remove_tab s =
    s |> explode |> map (fn c => if c = #"\t" then #" " else c) |> implode
  fun placeholder_spec asm len = let
    val t = String.tokens (fn x => x = #":") asm |> last |> remove_tab
    in (SPECL [stringSyntax.fromMLstring t, numSyntax.term_of_int len]
          (case !arch_name of
             ARM   => SKIP_SPEC_ARM
           | ARM8  => SKIP_SPEC_ARM8
           | M0    => SKIP_SPEC_M0
           | RISCV => SKIP_SPEC_RISCV), len, SOME len) end

(*
  val ((pos,instruction,asm)::code) = code
  val ((pos,instruction,asm)::code) = drop 1 code
  val ((pos,instruction,asm)::code) = drop 17 code
*)
  fun get_specs [] = []
    | get_specs ((pos,instruction,asm)::code) = let
      val instruction = delete_spaces instruction
      in
        if String.isPrefix "call:" instruction then let
          val ts = String.tokens (fn x => x = #":") instruction
          val fname = ts |> el 2
          val instruction = ts |> el 3
          fun add_call_tag th =
            th |> DISCH (mk_call_tag fname false) |> UNDISCH
          val g = add_call_tag o
                  clean_spec_thm o
                  remove_arm_CONFIGURE o
                  inst_pc_rel_const o
                  inst_pc pos o RW [precond_def]
          val res = wrap_get_spec f instruction
          val (x,y) = pair_apply g res
          in (pos,x,y) :: get_specs code end
        else if String.isPrefix "const:" instruction then
          get_specs code
        else if not (code = []) andalso
                String.isPrefix "switch:" ((fn (_,x,_) => x) (hd code)) then let
          val switch_code = instruction :: map (fn (_,x,_) => x) code
          val _ = write_line "Switch found."
          val (th1,th2,th2a,th3,l) = get_spec_for_switch (pos,switch_code)
          val code = drop (l-1) code
          val th2 = th2 |> RW [SPEC_MOVE_COND]
                        |> SIMP_RULE std_ss [] |> UNDISCH_ALL
          fun g pos = clean_spec_thm o
                      remove_arm_CONFIGURE o
                      inst_pc_rel_const o
                      inst_pc pos o RW [precond_def]
          in (pos,(g pos th1,4,SOME 4),NONE) ::
             (pos+4,(g (pos+4) th2,4,NONE),SOME (g (pos+4) th2a,4,SOME 4)) ::
             (pos+8,(g (pos+8) th3,4*l-8,SOME 4),NONE) ::
               get_specs code end
        else if String.isPrefix "dmb" asm then raise NoInstructionSpec
        else let
          val g = clean_spec_thm o
                  remove_arm_CONFIGURE o
                  inst_pc_rel_const o
                  inst_pc pos o RW [precond_def]
          val res = wrap_get_spec f instruction
                    handle HOL_ERR _ => raise NoInstructionSpec
          val (x,y) = pair_apply g res
          in (pos,x,y) :: get_specs code end
      end handle NoInstructionSpec => let
        val asm = String.translate (fn c =>
                      if c = #"\r" then "" else
                      if c = #"\t" then " " else implode [c]) asm
        val _ = write_line ("\n\nWarning: deriving placeholder spec for skipped " ^ instruction ^ " " ^ asm)
        val len = if size instruction (* in hex *) < 8 then 2 else 4 (* bytes *)
        val (thi,x1,x2) = (placeholder_spec asm len)
        in (pos,(inst_pc pos thi,x1,x2),NONE) :: get_specs code end

(*
  val (pos,instruction,asm) = hd code
  val n = 8
  val instruction = hd (drop 22 code)
  val iss = drop 13 code
  val ((th,_,_),_) = f instruction
  val th = renamer th
  val prefix = "foo@"
*)
  val res = get_specs code
  val has_bad_insts = exists bad_instruction
                        (map (fn (_,_,asm) => get_asm_name asm) code)
  fun calc_addresses i [] = []
    | calc_addresses i ((n:int,(th1:thm,l1,j1),y)::xs)  = let
    val (x,y) = pair_jump_apply (fn j => i+j) ((th1,l1,j1),y)
    in (i,x,y) :: calc_addresses (i+l1) xs end
  val res = calc_addresses 0 res
  val res = inst_pc_var tools res
  (* deal with silly blx instructions that call a constant pointer *)
  val pc_rel_var = mk_var("pc_rel",``:word32``)
  fun basic_find_pc_rel_load v =
    first (fn (n,(th,i,k),y) => let
      val vs = free_vars (concl th)
      in term_mem pc_rel_var vs andalso term_mem (mk_new_var "new" v) vs end) res
  fun find_pc_rel_load nn v = let
    fun exit_pc_is_var th = let
      val v = cdr (find_term (can (match_term ``arm_PC w``)) (cdr (concl th)))
      in is_var v end;
    val res2 = map (fn (nn,(th,i,x),y) =>
      if (x = NONE) andalso exit_pc_is_var th
      then hd (inst_pc_var tools [(nn,(fake_spec,i,SOME 4),y)])
      else (nn,(th,i,x),y)) (butlast res) @ [last res]
    fun is_assign th = let
      val vs = free_vars (concl th)
      in term_mem pc_rel_var vs andalso term_mem (mk_new_var "new" v) vs end
    fun assign curr (TRACE_CUT p) = []
      | assign curr (TRACE_END _) = []
      | assign curr (TRACE_SPLIT qs) = append_lists (map (assign curr) qs)
      | assign curr (TRACE_STEP (p,_,th,t)) =
          if p = nn then [curr] else
            assign (if is_assign th then p else curr) t
    val xs = (diff (assign ~1 (construct_thm_trace res2)) [~1])
    val _ = length xs > 0 orelse failwith("can't find assignment")
    val i = hd xs
    fun thms_lookup n [] = fail()
      | thms_lookup n ((nn,x,y)::xs) = if n = nn then (nn,x,y) else thms_lookup n xs
    in thms_lookup i res end handle HOL_ERR _ => basic_find_pc_rel_load v
  fun delete_long_jump (nn,(th,i,SOME k),y) = (nn,(th,i,SOME k),y)
    | delete_long_jump (nn,(th,i,NONE),y) = let
    val v = cdr (find_term (can (match_term ``arm_PC w``)) (cdr (concl th)))
    val (n,(r,_,_),_) = find_pc_rel_load nn v
    val (_,_,c,_) = dest_spec (concl r)
    val k = el 2 (list_dest pred_setSyntax.dest_insert c)
            |> dest_pair |> fst |> cdr |> cdr |> numSyntax.int_of_term
    val xs = String.tokens (fn c => c = #":") ((fn (_,x,_) => x) (el (k div 4 + 1) code))
    val a = el 2 xs |> Arbnum.fromHexString |> numSyntax.mk_numeral
            |> (fn n => wordsSyntax.mk_n2w(n,``:32``))
    val name = el 3 xs
    val rw = GSYM (ASSUME (mk_eq(a,v)))
    val th = CONV_RULE (POST_CONV (MOVE_OUT_CONV ``arm_PC``)) th
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (REWRITE_CONV [rw])) th
    val th = CONV_RULE ((POST_CONV o RAND_CONV) (REWRITE_CONV [rw])) th
    val th = DISCH_ALL_AS_SINGLE_IMP th
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (REWRITE_CONV [rw] THENC EVAL)) th
    val th = UNDISCH_ALL th
    val (th1,_,_) = (print "Not found in memory.\n\n"; fail())
    val th = RW [hide_th] th
    val th = CONV_RULE (POST_CONV (MOVE_OUT_CONV ``aR 14w``)) th
    val th = CONV_RULE (PRE_CONV (MOVE_OUT_CONV ``arm_PC``)) th
    val th = SPEC_COMPOSE_RULE [th,th1]
    val th = DISCH_ALL th |> REWRITE_RULE [GSYM SPEC_MOVE_COND]
    val th = RW [sidecond_def,hide_th,STAR_ASSOC] th
    val th = CONV_RULE (POST_CONV pull_let_wider_CONV) th
    in (nn,(th,i,SOME (nn+i)),y) end handle HOL_ERR _ => (nn,(th,i,NONE),y)
  val res = map delete_long_jump res
  in (has_bad_insts, res) end;

fun inst_pc_rel_const tools thms code = let
  fun triple_apply f (y,(th1,x1:int,x2:int option),NONE) = (y,(f y th1,x1,x2),NONE)
    | triple_apply f (y,(th1,x1,x2),SOME (th2,y1:int,y2:int option)) =
        (y,(f y th1,x1,x2),SOME (f y th2,y1,y2))
  fun find_instr [] p = hd []
    | find_instr (x::xs) p = if p < 4 then x else find_instr xs (p-4)
  val pc_rel = mk_var("pc_rel",``:word32``)
  val has_pc_rel = can (find_term (fn x => aconv x pc_rel))
  fun foo y th =
    if not (has_pc_rel (concl th)) then th else let
      val (_,_,c,_) = dest_spec (concl th)
      val ys = find_terms (can (match_term ``(x1:word32,x2:word32)``)) c
      val const = ys |> filter has_pc_rel |> hd |> dest_pair |> fst
                     |> cdr |> cdr |> numSyntax.int_of_term |> find_instr code
      val const = if String.isPrefix "const:" const
                  then el 2 (String.tokens (fn c => c = #":") const) else const
      val n = numSyntax.mk_numeral (Arbnum.fromHexString const)
      val th = INST [pc_rel|->wordsSyntax.mk_n2w(n,``:32``)] th
      in th end
  in map (triple_apply foo) thms end

fun UNABBREV_CODE_RULE th = let
  val rw = (!code_abbreviations)
  val c = REWRITE_CONV rw THENC
          SIMP_CONV std_ss [word_arith_lemma1] THENC
          REWRITE_CONV [INSERT_UNION_EQ,UNION_EMPTY]
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) c) th
  in th end;

fun tidy_up_name name = let
  val name = if String.isPrefix "_" name then "fun" ^ name else name
  in String.translate (fn c => if c = #"-" then "_" else implode [c]) name end

fun abbreviate_code name thms = let
  fun extract_code (_,(th,_,_),_) = let val (_,_,c,_) = dest_spec (concl th) in c end
  val cs = map extract_code thms
  val ty = (hd o snd o dest_type o type_of o hd) cs
  val tm = foldr pred_setSyntax.mk_union (pred_setSyntax.mk_empty ty) cs
  val cth = QCONV (PURE_REWRITE_CONV [INSERT_UNION_EQ,UNION_EMPTY]) tm
  val c = (cdr o concl) cth
  val (_,(th,_,_),_) = hd thms
  val (m,_,_,_) = dest_spec (concl th)
  val model_name = (to_lower o implode o take_until (fn x => x = #"_") o explode o fst o dest_const) m
  val x = list_mk_pair (free_vars c)
  val def_name = name ^ "_" ^ model_name
  val def_name = tidy_up_name def_name
  val v = if aconv x ``():unit`` then mk_var(def_name,type_of c)
          else mk_var(def_name,type_of(mk_pabs(x,c)))
  val code_def = new_definition(def_name ^ "_def",
        if aconv x ``():unit`` then mk_eq(v,c)
        else mk_eq(mk_comb(v,x),c))
  val _ = add_code_abbrev [code_def]
  fun triple_apply f (y,(th1,x1:int,x2:int option),NONE) = (y,(f th1,x1,x2),NONE)
    | triple_apply f (y,(th1,x1,x2),SOME (th2,y1:int,y2:int option)) =
        (y,(f th1,x1,x2),SOME (f th2,y1,y2))
  val code_thm = CONV_RULE (RAND_CONV (fn _ => GSYM cth)) (SPEC_ALL code_def)
  fun foo th = let
    val thi = MATCH_MP ABBBREV_CODE_LEMMA (DISCH_ALL_AS_SINGLE_IMP th)
    val thi = SPEC ((fst o dest_eq o concl o SPEC_ALL) code_def) thi
    val goal = (fst o dest_imp o concl) thi
    val lemma = auto_prove "abbreviate_code" (goal,
        REPEAT (REWRITE_TAC [code_thm,SUBSET_DEF,IN_UNION] THEN REPEAT STRIP_TAC
                THEN ASM_REWRITE_TAC [] THEN (fn _ => fail()))
        THEN REWRITE_TAC [EMPTY_SUBSET]
        THEN REWRITE_TAC [SUBSET_DEF,IN_INSERT,IN_UNION,NOT_IN_EMPTY,code_def]
        THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss [])
    val thi = UNDISCH_ALL (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] (MP thi lemma))
    in thi end
  val thms = map (triple_apply foo) thms
  val _ = (aconv x ``():unit``) orelse failwith "code contains variables"
  in (code_def,thms) end

fun apply_thms f (i:int,(th,l:int,j:int option),NONE) = (i,(f th,l,j),NONE)
  | apply_thms f (i,(th,l,j),SOME (th1,l1,j1)) = (i,(f th,l,j),SOME (f th1,l1,j1))

fun try_map g f [] = []
  | try_map g f (x::xs) = let
      val y = f x
      in y :: try_map g f xs end
      handle HOL_ERR _ =>
        (g x; try_map g f xs)

val stack_intro_fails = ref ([] : (int * string) list);

fun print_stack_intro_fail (pos,sec_name) = let
  val b = !writer_prints
  val _ = (writer_prints := true)
  val _ = write_line ("Stack intro failed in " ^ sec_name ^ " for pos " ^
                      (int_to_hex pos) ^ ".")
  val _ = (writer_prints := b)
  in () end

fun add_stack_intro_fail pos sec_name =
  (print_stack_intro_fail (pos,sec_name);
   stack_intro_fails := (pos, sec_name) :: (!stack_intro_fails));

fun clear_stack_intro_fails () = (stack_intro_fails := []);

fun print_stack_intro_report () =
  (if length (!stack_intro_fails) = 0 then
    (write_line "No stack intro failures."; [])
   else (has_failures := true;
         map print_stack_intro_fail (!stack_intro_fails)))

fun derive_specs_for sec_name = let
  val code = section_body sec_name
  val _ = write_subsection "Deriving specifications"
  val cl = int_to_string (length code)
  val str = "Section `"^sec_name^"` consists of "^cl^" instructions."
  val _ = write_line str
  val thms = snd (derive_individual_specs code)
  val stack_accesses =
    if length thms = 0 then [] else
      find_stack_accesses sec_name thms
      handle HOL_ERR _ => (add_stack_intro_fail 0 sec_name; [])
  val _ = (writer_prints := false)
  val thms = try_map (fn (n,_,_) => add_stack_intro_fail n sec_name)
                     (apply_thms (STACK_INTRO_RULE stack_accesses)) thms
  val _ = (writer_prints := true)
  val (code_abbrev_def, thms) =
    if length thms = 0 then (TRUTH, thms) else
      abbreviate_code sec_name thms
  in thms end;

(*

  val base_name = "kernel-riscv/kernel-riscv"
  val base_name = "loop-riscv/example"
  val base_name = "example-arm8/SysModel"
  val _ = read_files base_name []
  val _ = open_current "test"
  val sec_name = "lookupSlot"
  val sec_name = "memzero"
  val sec_name = "memcpy"
  val sec_name = "isIRQPending"
  val sec_name = "createNewObjects"
  val sec_name = "get_num_avail_p_regs"
  val sec_name = "ensureEmptySlot"
  val sec_name = "after"

  val _ = file_readerLib.show_code sec_name

  val base_name = "loop/example"
  val _ = read_files base_name []
  val _ = open_current "test"
  val sec_name = "g"

  val l3_arm_tools = arm_decompLib.l3_arm_tools
  val (arm_spec,_,_,_) = l3_arm_tools
  val instruction = "e200300f"
  val th = arm_spec instruction

  val l3_arm8_tools = arm8_decompLib.arm8_tools
  val (arm8_spec,_,_,_) = l3_arm8_tools
  val instruction = "0b000020"
  val instruction = "540000ca"
  val instruction = "6b01001f"
  val instruction = "b9401fe0"
  val instruction = "d65f03c0"
  val instruction = "910083ff"
  val instruction = "94000000"
  val th = arm8_spec instruction

*)

end
