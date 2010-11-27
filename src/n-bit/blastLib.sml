structure blastLib :> blastLib =
struct

open HolKernel boolLib bossLib;
open bitTheory wordsTheory blastTheory;
open wordsLib bitSyntax;

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars blastTheory.blast_grammars
end

open Parse

(* ------------------------------------------------------------------------ *)

val ERR = Feedback.mk_HOL_ERR "blastLib";

val blast_trace = ref 0;
val blast_counter = ref true;

val _ = Feedback.register_trace ("bit blast", blast_trace, 3);
val _ = Feedback.register_btrace ("print blast counterexamples", blast_counter);

val rhsc = boolSyntax.rhs o Thm.concl;

fun dest_strip t = let
  val (l,r) = boolSyntax.strip_comb t
in
  (fst (Term.dest_const l), r)
end;

val dim_of_word = fcpLib.index_to_num o wordsSyntax.dim_of;

(* ------------------------------------------------------------------------
   FCP_INDEX_CONV : Conversion for evaluating ``($FCP f) ' i``.
   ------------------------------------------------------------------------ *)

fun mk_size_thm (i,ty) =
   numSyntax.mk_less (i, wordsSyntax.mk_dimindex ty)
     |> (Conv.RAND_CONV wordsLib.SIZES_CONV THENC numLib.REDUCE_CONV)
     |> Drule.EQT_ELIM;

local
  val fcp_beta_thm = fcpTheory.FCP_BETA
                     |> Drule.SPEC_ALL
                     |> Thm.INST_TYPE [Type.alpha |-> Type.bool]
in
  fun FCP_INDEX_CONV conv tm =
    case dest_strip tm
    of ("fcp_index", [w, i]) =>
        (case Lib.total dest_strip w
         of SOME ("FCP", [f]) =>
             let
               val ty = wordsSyntax.dim_of w
               val _ = Arbnum.< (numLib.dest_numeral i, fcpLib.index_to_num ty)
                       orelse raise ERR "FCP_INDEX_CONV" "index out of range"
               val indx_thm = fcp_beta_thm
                              |> Thm.INST_TYPE [beta |-> ty]
                              |> Thm.INST [``i:num`` |-> i,
                                           ``g:num->bool`` |-> f]
             in
               Conv.RIGHT_CONV_RULE conv (Thm.MP indx_thm (mk_size_thm (i,ty)))
             end
          | _ => raise Conv.UNCHANGED)
     | _ => raise ERR "FCP_INDEX_CONV" "not an application of fcp_index"
end

(* ------------------------------------------------------------------------ *)

val BCARRY_mp = Q.prove(
  `(i = SUC n) /\ (x n = b1) /\ (y n = b2) /\ (BCARRY n x y c = b3) ==>
   (BCARRY i x y c = bcarry b1 b2 b3)`,
   SRW_TAC [] [BCARRY_def]);

val BCARRY_mp = REWRITE_RULE [bcarry_def] BCARRY_mp;

val BCARRY_mp_carry =
  BCARRY_mp
  |> Q.INST [`b3` |-> `T`]
  |> PURE_REWRITE_RULE [DECIDE ``x /\ y \/ (x \/ y) /\ T = x \/ y``];

val BCARRY_mp_not_carry =
  BCARRY_mp
  |> Q.INST [`b3` |-> `F`]
  |> PURE_REWRITE_RULE [DECIDE ``x /\ y \/ (x \/ y) /\ F = x /\ y``];

val BSUM_mp = Q.prove(
  `(x i = b1) /\ (y i = b2) /\ (BCARRY i x y c = b3) ==>
   (BSUM i x y c = bsum b1 b2 b3)`,
  SRW_TAC [] [BSUM_def]);

val BSUM_mp = REWRITE_RULE [bsum_def] BSUM_mp;

val BSUM_mp_carry =
  BSUM_mp
  |> Q.INST [`b3` |-> `T`]
  |> PURE_REWRITE_RULE [DECIDE ``((x = ~y) = ~T) = (x:bool = y)``];

val BSUM_mp_not_carry =
  BSUM_mp
  |> Q.INST [`b3` |-> `F`]
  |> PURE_REWRITE_RULE [DECIDE ``((x = ~y) = ~F) = (x:bool = ~y)``];

val rhs_rewrite =
  Conv.RIGHT_CONV_RULE
    (Rewrite.REWRITE_CONV
       [satTheory.AND_INV, EQF_INTRO boolTheory.NOT_AND,
        DECIDE ``!b:bool. (b = ~b) = F``,
        DECIDE ``!b:bool. (~b = b) = F``])

(* --------------------------------------------------------------------
   mk_summation : returns theorems of the form  ``BSUM i x y c = exp``
                  for all 0 < i < max, where "exp" is a propositional
                  expression.
   -------------------------------------------------------------------- *)

fun mk_summation conv (max, x, y, c) =
let
  val INST_SUM = Thm.INST [``x:num -> bool`` |-> x,
                           ``y:num -> bool`` |-> y,
                           ``c:bool`` |-> c]

  val iBSUM_mp_carry       = INST_SUM BSUM_mp_carry
  val iBSUM_mp_not_carry   = INST_SUM BSUM_mp_not_carry
  val iBSUM_mp             = INST_SUM BSUM_mp
  val iBCARRY_mp_carry     = INST_SUM BCARRY_mp_carry
  val iBCARRY_mp_not_carry = INST_SUM BCARRY_mp_not_carry
  val iBCARRY_mp           = INST_SUM BCARRY_mp

  fun mk_sums p (s, c_thm) =
    if p = max then
      s
    else let val pp = Arbnum.plus1 p in
      mk_sums pp
       (let
          val n = numLib.mk_numeral p
          val i = numLib.mk_numeral pp
          val _ = if !blast_trace > 2 then
                    TextIO.print
                      ("Expanding bit... " ^ Arbnum.toString pp ^ "\n")
                  else
                    ()
          val i_thm = boolSyntax.mk_eq (i, numSyntax.mk_suc n)
                      |> numLib.REDUCE_CONV |> Drule.EQT_ELIM
          val x_thm = Conv.QCONV conv (Term.mk_comb (x, n))
          val y_thm = Conv.QCONV conv (Term.mk_comb (y, n))
          val x_concl = rhsc x_thm
          val y_concl = rhsc y_thm
          val c_concl = rhsc c_thm
          val (thm1,thm2) =
                if c_concl = boolSyntax.T then
                  (iBSUM_mp_carry, iBCARRY_mp_carry)
                else if c_concl = boolSyntax.F then
                  (iBSUM_mp_not_carry, iBCARRY_mp_not_carry)
                else
                  (iBSUM_mp, iBCARRY_mp)
         val thm1 = Thm.INST [``i:num`` |-> n,
                              ``b1:bool`` |-> x_concl,
                              ``b2:bool`` |-> y_concl,
                              ``b3:bool`` |-> c_concl] thm1
         val thm2 = Thm.INST [``i:num`` |-> i,
                              ``n:num`` |-> n,
                              ``b1:bool`` |-> x_concl,
                              ``b2:bool`` |-> y_concl,
                              ``b3:bool`` |-> c_concl] thm2
        in
          (rhs_rewrite
             (Thm.MP thm1 (Drule.LIST_CONJ [x_thm, y_thm, c_thm])) :: s,
           rhs_rewrite
             (Thm.MP thm2 (Drule.LIST_CONJ [i_thm, x_thm, y_thm, c_thm])))
         end)
    end
in
  mk_sums Arbnum.zero
    ([], BCARRY_def |> Thm.CONJUNCT1 |> Drule.SPECL [x,y,c])
end;

(* --------------------------------------------------------------------
   mk_carry : returns theorem of the form  ``BCARRY max x y c = exp``,
              where "exp" is a propositional expression.
   -------------------------------------------------------------------- *)

fun mk_carry conv (max, x, y, c) =
let
  val INST_CARRY = Thm.INST [``x:num -> bool`` |-> x,
                           ``y:num -> bool`` |-> y,
                           ``c:bool`` |-> c]

  val iBCARRY_mp_carry     = INST_CARRY BCARRY_mp_carry
  val iBCARRY_mp_not_carry = INST_CARRY BCARRY_mp_not_carry
  val iBCARRY_mp           = INST_CARRY BCARRY_mp

  fun mk_c p c_thm =
    if p = max then
      c_thm
    else let val pp = Arbnum.plus1 p in
      mk_c pp
       (let
          val n = numLib.mk_numeral p
          val i = numLib.mk_numeral pp
          val _ = if !blast_trace > 2 then
                    TextIO.print
                      ("Expanding bit... " ^ Arbnum.toString pp ^ "\n")
                  else
                    ()
          val i_thm = boolSyntax.mk_eq (i, numSyntax.mk_suc n)
                        |> numLib.REDUCE_CONV |> Drule.EQT_ELIM
          val x_thm = Conv.QCONV conv (Term.mk_comb (x, n))
          val y_thm = Conv.QCONV conv (Term.mk_comb (y, n))
          val x_concl = rhsc x_thm
          val y_concl = rhsc y_thm
          val c_concl = rhsc c_thm
          val thm =
                if c_concl = boolSyntax.T then
                  iBCARRY_mp_carry
                else if c_concl = boolSyntax.F then
                  iBCARRY_mp_not_carry
                else
                  iBCARRY_mp
         val thm = Thm.INST [``i:num`` |-> i,
                             ``n:num`` |-> n,
                             ``b1:bool`` |-> x_concl,
                             ``b2:bool`` |-> y_concl,
                             ``b3:bool`` |-> c_concl] thm
        in
          rhs_rewrite
            (Thm.MP thm (Drule.LIST_CONJ [i_thm, x_thm, y_thm, c_thm]))
        end)
    end
in
  mk_c Arbnum.zero (BCARRY_def |> Thm.CONJUNCT1 |> Drule.SPECL [x,y,c])
end;

(* --------------------------------------------------------------------
   mk_sums : find terms of the form ``FCP i. BSUM i x y c`` and
             ``BCARRY n x y c``; it then uses mk_summation and mk_carry
             to generate rewrites and returns an appropriate conversion.
   -------------------------------------------------------------------- *)

local
  fun dest_sum tm = case dest_strip tm
                    of ("FCP", [f]) =>
                      (case f |> Term.dest_abs |> snd |> dest_strip
                       of ("BSUM", [i, x, y, c]) =>
                           (false, (dim_of_word tm, x, y, c))
                        | _ => raise ERR "dest_sum" "")
                     | ("BCARRY", [n, x, y, c]) =>
                          (true, (numLib.dest_numeral n, x, y, c))
                     | _ => raise ERR "dest_sum" ""
  val is_sum = Lib.can dest_sum
in
  fun mk_sums conv tm =
    let
      val tms = HolKernel.find_terms is_sum tm
      val tms = tms |> Lib.mk_set
                    |> Listsort.sort
                         (Int.compare o (Term.term_size ## Term.term_size))
                    |> List.map dest_sum
      val _ = if !blast_trace > 0 andalso not (List.null tms) then
                print ("Found " ^ Int.toString (List.length tms) ^
                       " summation term(s)\n")
              else
                ()
      val (_, rwts, c_outs) =
            List.foldl
              (fn ((b,nxyc), (i, rwts, c_outs)) =>
                 let
                   val cnv = PURE_REWRITE_CONV [combinTheory.o_THM]
                             THENC TOP_DEPTH_CONV (FCP_INDEX_CONV
                               (conv THENC PURE_REWRITE_CONV rwts))
                   val _ = if !blast_trace > 0 then
                             TextIO.print
                               ("Expanding term... " ^ Int.toString i ^ "\n")
                           else
                             ()
                 in
                   if b then
                     (i + 1, rwts, mk_carry cnv nxyc :: c_outs)
                   else
                     (i + 1, mk_summation cnv nxyc @ rwts, c_outs)
                 end) (1, [],[]) tms
    in
      conv THENC PURE_REWRITE_CONV (rwts @ c_outs)
    end
end

(* ------------------------------------------------------------------------
   WORD_LIT_CONV : Rewrites occurances of ``BIT i v`` using theorems
                   ``BIT i v = (i = p1) \/ ... \/ (i = pn)``, where
                   v is the numeric value of the literal and p1..pn
                   are the bit positions for T bits.
   ------------------------------------------------------------------------ *)

local
  val cmp = wordsLib.words_compset()

  val _ = computeLib.add_thms
            [pred_setTheory.NOT_IN_EMPTY, pred_setTheory.IN_INSERT,
             REWRITE_RULE [GSYM arithmeticTheory.DIV2_def] BIT_SET_def] cmp

  val BIT_SET_CONV = Conv.REWR_CONV wordsTheory.BIT_SET
                     THENC computeLib.CBV_CONV cmp

  val i = Term.mk_var ("i", numLib.num)

  fun is_bit_lit tm = case Lib.total bitSyntax.dest_bit tm
                      of SOME (_, n) => numSyntax.is_numeral n
                       | NONE => false
  fun mk_bit_sets tm =
    let
      val tms = Lib.mk_set (HolKernel.find_terms is_bit_lit tm)
    in
      List.map BIT_SET_CONV tms
    end
in
  fun WORD_LIT_CONV tm = PURE_REWRITE_CONV (mk_bit_sets tm) tm
end

(* ------------------------------------------------------------------------
   fcp_eq_thm : generates a bitwise equality theorem for a given word type.
                For example, fcp_eq_thm ``:word2`` gives the theorem
                |- !a b. (a = b) = (a ' 0 = b ' 0) /\ (a ' 1 = b ' 1).
   ------------------------------------------------------------------------ *)

val SUC_RULE = Conv.CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

local
  val FCP_EQ_EVERY = Q.prove(
    `!a b:'a word.
        (a = b) = EVERY (\i. a ' i = b ' i) (GENLIST I (dimindex (:'a)))`,
    SRW_TAC [fcpLib.FCP_ss] [listTheory.EVERY_GENLIST])

  val FCP_EQ_EVERY =
        REWRITE_RULE [GSYM rich_listTheory.COUNT_LIST_GENLIST,
                      rich_listTheory.COUNT_LIST_AUX] FCP_EQ_EVERY

  val cmp = reduceLib.num_compset ()

  val _ = computeLib.add_thms
            [listTheory.EVERY_DEF, SUC_RULE rich_listTheory.COUNT_LIST_AUX_def]
            cmp

  val _ = computeLib.add_conv
            (``fcp$dimindex:'a itself -> num``, 1, wordsLib.SIZES_CONV) cmp

  val FCP_EQ_CONV = Conv.REWR_CONV FCP_EQ_EVERY THENC computeLib.CBV_CONV cmp

  val fcp_map = ref (Redblackmap.mkDict Arbnum.compare)
                  : (Arbnum.num, Thm.thm) Redblackmap.dict ref
in
  fun fcp_eq_thm ty =
       case Lib.total (fcpLib.index_to_num o wordsSyntax.dest_word_type) ty
       of SOME n =>
            (case Redblackmap.peek (!fcp_map, n)
             of SOME thm => thm
              | _ => let
                       val a = Term.mk_var ("a", ty)
                       val b = Term.mk_var ("b", ty)
                       val thm = FCP_EQ_CONV (boolSyntax.mk_eq (a,b))
                       val thm = Thm.GEN a (Thm.GEN b thm)
                       val _ = fcp_map := Redblackmap.insert (!fcp_map, n, thm)
                     in
                       thm
                     end)
       | NONE => raise ERR "fcp_eq_thm" ""
end

(* ------------------------------------------------------------------------ *)

local
  val word_ss = std_ss++wordsLib.SIZES_ss++wordsLib.WORD_ARITH_ss++
                wordsLib.WORD_LOGIC_ss++wordsLib.WORD_SHIFT_ss

  val SYM_WORD_NOT_LOWER = GSYM WORD_NOT_LOWER;

  val bit_rwts =
    [word_lsb_def, word_msb_def, word_bit_def]

  val order_rwts =
    [WORD_HIGHER,
     REWRITE_RULE [SYM_WORD_NOT_LOWER] WORD_HIGHER_EQ,
     SYM_WORD_NOT_LOWER,
     WORD_GREATER,
     WORD_GREATER_EQ,
     REWRITE_RULE [SYM_WORD_NOT_LOWER, word_L_def] WORD_LT_LO,
     REWRITE_RULE [SYM_WORD_NOT_LOWER, word_L_def] WORD_LE_LS,
     WORD_LOWER_REFL, WORD_LOWER_EQ_REFL,
     WORD_LESS_REFL, WORD_LESS_EQ_REFL,
     WORD_0_LS, WORD_LESS_0_word_T,
     WORD_LS_word_0, WORD_LO_word_0]
in
  val WORD_SIMP_CONV = SIMP_CONV word_ss bit_rwts
                       THENC REWRITE_CONV order_rwts
                       THENC Conv.DEPTH_CONV wordsLib.SIZES_CONV
end

(* ------------------------------------------------------------------------
   SMART_MUL_LSL_CONV : converts ``n2w n * w`` into either
                        ``w << p1 + ... + w << pn`` or
                        ``-w << p1 + ... + -w << pn`` depending on
                        which gives the fewest additions.
                        NB. ``-w`` is ``~w + 1w``.
   ------------------------------------------------------------------------ *)

local
  val NEG_WORD = Drule.EQT_ELIM
                   (wordsLib.WORD_CONV ``a * b = -a * -b :'a word``)
  val SYM_WORD_NEG_MUL = GSYM wordsTheory.WORD_NEG_MUL
  fun boolify sz = (fn l => List.take(l, sz)) o
                   String.explode o
                   StringCvt.padLeft #"0" sz o
                   Arbnum.toBinString
in
  fun SMART_MUL_LSL_CONV tm =
    let
      val l = fst (wordsSyntax.dest_word_mul tm)
    in
      case Lib.total wordsSyntax.dest_word_2comp l
      of SOME v =>
           if Lib.total wordsSyntax.dest_word_literal v = SOME (Arbnum.one) then
             Conv.REWR_CONV SYM_WORD_NEG_MUL tm
           else
             raise ERR "SMART_MUL_LSL_CONV" "not -1w * x"
       | NONE =>
          let val (N,sz) = wordsSyntax.dest_mod_word_literal l in
            if Arbnum.<(N, Arbnum.fromInt 11) then
              wordsLib.WORD_MUL_LSL_CONV tm
            else
              let
                val sz = Arbnum.toInt sz
                val c_pos = N |> boolify sz
                              |> List.filter (Lib.equal #"1")
                              |> List.length
                val c_neg = N |> Arbnum.less1
                              |> boolify sz
                              |> List.filter (Lib.equal #"0")
                              |> List.length
              in
                if c_pos <= 2 * c_neg + 1 then
                  wordsLib.WORD_MUL_LSL_CONV tm
                else
                  (Conv.REWR_CONV NEG_WORD
                   THENC Conv.RATOR_CONV wordsLib.WORD_EVAL_CONV
                   THENC wordsLib.WORD_MUL_LSL_CONV) tm
              end
          end
    end
end

(* ------------------------------------------------------------------------
   BLAST_CONV : expands a bit vector term using the definitions for
                the standard operations.  First does a normalization to
                re-introduce subtraction
   ------------------------------------------------------------------------ *)

local
  val word_join = SIMP_RULE (std_ss++boolSimps.LET_ss) [] word_join_def
  val index_cond =
      ``(if b then x:'a word else y) ' i = if b then x ' i else y ' i``
        |> simpLib.SIMP_PROVE std_ss [COND_RAND, COND_RATOR] |> GEN_ALL
  val xor_thm = tautLib.TAUT_PROVE ``~(a = b) = (a = ~b:bool)``
  val word_xor = REWRITE_RULE [xor_thm] word_xor_def
  val reduce_xor = REWRITE_RULE [xor_thm] reduce_xor_def

  val word_L_thm = Q.prove(
    `INT_MINw :'a word = FCP i. i = dimindex (:'a) - 1`,
    SRW_TAC [fcpLib.FCP_ss] [word_L]);

  val minus1_thm = Q.prove(
    `-1w = $FCP (K T)`,
    SRW_TAC [fcpLib.FCP_ss] [REWRITE_RULE [SYM WORD_NEG_1] word_T]);

  val w2w_thm = Q.prove(
    `!w: 'a word. w2w w = FCP i. i < dimindex (:'a) /\ w ' i`,
    SRW_TAC [fcpLib.FCP_ss] [w2w]);

  val sw2sw_thm = Q.prove(
    `!w: 'a word.
        sw2sw w :'b word =
        FCP i. if i < dimindex (:'a) \/ dimindex (:'b) < dimindex (:'a) then
                 w ' i
               else
                 w ' (dimindex (:'a) - 1)`,
    SRW_TAC [fcpLib.FCP_ss] [sw2sw, word_msb_def]);

  fun WORD_NEG_CONV tm =
      let
        val t = wordsSyntax.dest_word_2comp tm
      in
        case Lib.total wordsSyntax.dest_word_literal t
        of SOME v => if v = Arbnum.one then
                       raise Conv.UNCHANGED
                     else
                       wordsLib.WORD_EVAL_CONV tm
         | NONE => ONCE_REWRITE_CONV [WORD_NEG] tm
      end

  val cmp = reduceLib.num_compset()

  val _ = computeLib.add_thms
     [n2w_def, word_xor, word_or_def, word_and_def, word_1comp_def,
      word_nor_def, word_xnor_def, word_nand_def, word_reduce_def,
      reduce_or_def, reduce_and_def, reduce_xor, reduce_xnor_def,
      reduce_nand_def, word_replicate_def, word_join, word_concat_def,
      word_reverse_def, word_modify_def, word_lsl_def, word_lsr_def,
      word_asr_def, word_ror_def, word_rol_def, word_rrx_def, word_msb_def,
      word_lsb_def, word_extract_def, word_bits_def, word_slice_def,
      word_bit_def, word_signed_bits_def, bit_field_insert_def, index_cond,
      SYM WORD_NEG_1, word_L_thm, minus1_thm, w2w_thm, sw2sw_thm,
      BITWISE_ADD, BITWISE_SUB, BITWISE_LO, fcpTheory.FCP_UPDATE_def,
      listTheory.HD, listTheory.TL, listTheory.SNOC, listTheory.FOLDL,
      listTheory.GENLIST_GENLIST_AUX, SUC_RULE listTheory.GENLIST_AUX,
      combinTheory.o_THM, pairTheory.SND, pairTheory.FST] cmp

  val _ = computeLib.add_conv
            (``fcp$dimindex:'a itself -> num``, 1, wordsLib.SIZES_CONV) cmp

  val _ = computeLib.add_conv
            (``words$dimword:'a itself -> num``, 1, wordsLib.SIZES_CONV) cmp

  val _ = computeLib.add_conv
            (``words$INT_MIN:'a itself -> num``, 1, wordsLib.SIZES_CONV) cmp

  val _ = computeLib.add_conv
            (``words$word_2comp:bool['a] -> bool['a]``, 1, WORD_NEG_CONV) cmp
in
  val BLAST_CONV =
        Conv.DEPTH_CONV SMART_MUL_LSL_CONV
        THENC PURE_REWRITE_CONV [GSYM word_sub_def, WORD_SUB]
        THENC computeLib.CBV_CONV cmp
        THENC WORD_LIT_CONV
end;

(* ------------------------------------------------------------------------
   BIT_TAUT_CONV : wrapper around HolSatLib.SAT_PROVE
   ------------------------------------------------------------------------ *)

fun non_prop_terms tm =
let
  fun non_prop_args acc tmlist =
      case tmlist of
        [] => acc
      | tm::ts =>
          let
            val (opp,args) = dest_strip tm handle HOL_ERR _ => ("", [])
          in
            if Lib.mem opp ["T","F","~","/\\","\\/","==>"] then
              non_prop_args acc (args @ ts)
            else if Lib.mem opp ["=","COND"] andalso
                    Lib.all (fn t => Term.type_of t = Type.bool) args
            then
              non_prop_args acc (args @ ts)
            else if Term.type_of tm = Type.bool then
              non_prop_args (HOLset.add(acc, tm)) ts
            else raise ERR "non_prop_terms" "Not a boolean term"
          end
in
  non_prop_args Term.empty_tmset [tm]
end

local
  val lem = numLib.DECIDE ``!b. if b then T else T``;
in
  fun PROP_PROVE conv tm =
  let
    val thm = Conv.QCONV (REWRITE_CONV [lem]) tm
    val c = rhsc thm
  in
    if c = boolSyntax.T orelse c = boolSyntax.F then
      thm
    else
      Conv.RIGHT_CONV_RULE (Conv.REWR_CONV (Drule.EQT_INTRO (conv c))) thm
      handle HOL_ERR _ =>
        Drule.EQF_INTRO (conv (boolSyntax.mk_neg tm))
        handle HOL_ERR _ =>
          raise ERR "PROP_PROVE" "contingent proposition"
  end
end

fun SAT_CONV tm = HolSatLib.SAT_PROVE tm (* HolSatLib.SAT_ORACLE *)
                  handle HolSatLib.SAT_cex _ => raise ERR "SAT_CONV" ""

fun DPLL_CONV tm = Thm.CCONTR tm (Lib.trye dpll.DPLL_TAUT tm)

fun BIT_TAUT_CONV tm =
let
  val insts = HOLset.listItems (non_prop_terms tm)
  val vars = Term.genvars Type.bool (List.length insts)
  val theta = Lib.map2 (Lib.curry (op |->)) insts vars
  val tm' = Term.subst theta tm
  val sz = Term.term_size tm'
  val f = if !blast_trace > 2 then
            (print ("Checking proposition of size: " ^ Int.toString sz ^ "\n");
             real_time)
          else
            I
  val thm = f (PROP_PROVE (if sz < 100 then DPLL_CONV else SAT_CONV)) tm'
  val theta' = Lib.map2 (Lib.curry (op |->)) vars insts
in
  Thm.INST theta' thm
end

local
  fun eq_fst_partition [] = []
    | eq_fst_partition ((x,y)::l) =
        let val (eqx,neqx) = List.partition (term_eq x o fst) l in
          ((x,y::List.map snd eqx)) :: eq_fst_partition neqx
        end

  fun word_counter (x,l) =
  let
    val i = Term.mk_var ("i", numLib.num)
    val ty' = wordsSyntax.dest_word_type (type_of x)
  in
    l |> List.filter fst
      |> List.map (fn (_,n) => boolSyntax.mk_eq (i, n))
      |> (fn l => if List.null l then
                    boolSyntax.F
                  else
                    boolSyntax.list_mk_disj l)
      |> (fn f => fcpSyntax.mk_fcp (Term.mk_abs (i, f), ty'))
      |> wordsLib.WORD_EVAL_CONV
      |> concl
      |> rhs
      |> (fn t => {redex = x, residue = t})
  end

  fun bool_counter tm =
        case Lib.total boolSyntax.dest_neg tm
        of SOME t => {redex = t, residue = boolSyntax.F}
         | NONE => {redex = tm, residue = boolSyntax.T}

  fun dest_bit tm =
    case Lib.total boolSyntax.dest_neg tm
    of SOME t => let val (x,y) = fcpSyntax.dest_fcp_index t in (x,(false,y)) end
     | NONE => let val (x,y) = fcpSyntax.dest_fcp_index tm in (x,(true,y)) end
in
  fun counterexample tm =
    let val tm = snd (boolSyntax.strip_forall tm) in
      if tm = boolSyntax.F orelse tm = boolSyntax.T then
        []
      else
        let
          val insts = HOLset.listItems (non_prop_terms tm)
          val vars = Term.genvars Type.bool (List.length insts)
          val theta = Lib.map2 (Lib.curry (op |->)) insts vars
          val tm' = Term.subst theta tm
          val thm = (HolSatLib.SAT_PROVE tm'; NONE)
                    handle HolSatLib.SAT_cex thm => SOME thm
        in
          case thm
          of NONE => []
           | SOME t =>
               let
                 val theta' = Lib.map2 (Lib.curry (op |->)) vars insts
                 val c = fst (boolSyntax.dest_imp (concl t))
                 val c = boolSyntax.strip_conj (Term.subst theta' c)
                 val (bits,rest) = List.partition (Lib.can dest_bit) c
                 val bits = eq_fst_partition (List.map dest_bit bits)
               in
                 List.map word_counter bits @ List.map bool_counter rest
               end
        end
    end
end

fun print_counterexample l =
   if List.null l then
     print "No counterexample found!\n"
   else let
     fun f {redex,residue} = Hol_pp.term_to_string redex ^ " -> " ^
                             Hol_pp.term_to_string residue ^ "\n\n"
   in
     print "Found counterexample:\n\n";
     List.app (fn c => print (f c ^ "and\n\n")) (Lib.butlast l);
     print (f (List.last l))
    end

(* ------------------------------------------------------------------------
   BIT_BLAST_CONV : convert a bit vector assertion ``a = b``, ``a ' n`` or
                    ``a <+ b`` into bitwise propositions. Uses SAT to try
                    to reduce sub-expressions to T or F.
   BBLAST_CONV : wrapper around BIT_BLAST_CONV.
   ------------------------------------------------------------------------ *)

local
  fun is_word_index tm =
         case Lib.total wordsSyntax.dest_index tm
         of SOME (w,i) => numLib.is_numeral i andalso Lib.can dim_of_word w
          | NONE => false
in
  fun is_blastable tm =
         is_word_index tm orelse
         (case Lib.total boolSyntax.dest_eq tm
          of SOME (w,v) =>
                Lib.can dim_of_word w orelse
                is_word_index w andalso is_word_index v
           | NONE =>
               (case Lib.total wordsSyntax.dest_word_lo tm
                of SOME (w,_) => Lib.can dim_of_word w
                 | NONE => false))
end

local
  val FCP_NEQ = trace ("metis",0) Q.prove(
    `!i a b:'a word.
       i < dimindex (:'a) /\ ((a ' i = b ' i) = F) ==> ((a = b) = F)`,
    SRW_TAC [fcpLib.FCP_ss] []
    THEN METIS_TAC []);

  val dummy_thm = SPEC_ALL combinTheory.I_THM

  fun INDEX_CONV conv = TOP_DEPTH_CONV (FCP_INDEX_CONV conv)
                        THENC Conv.TRY_CONV BIT_TAUT_CONV

  fun TRY_INDEX_CONV conv tm =
        INDEX_CONV conv tm
        handle HOL_ERR _ => dummy_thm
             | Conv.UNCHANGED => dummy_thm

  fun bit_theorems conv (n, l, r) =
      let
        val _ = if !blast_trace > 1 then
                  TextIO.print ("Checking " ^ Arbnum.toString n ^ " bit word\n")
                else
                  ()
        fun bit_theorem i a =
              if i = n then
                Lib.PASS a
              else let
                val _ = if !blast_trace > 1 then
                          TextIO.print
                             ("Checking bit... " ^ Arbnum.toString i ^ "\n")
                        else
                          ()
                val ii = numLib.mk_numeral i
                val li = wordsSyntax.mk_index (l, ii)
                val ri = wordsSyntax.mk_index (r, ii)
                val eq_tm = boolSyntax.mk_eq (li, ri)
                val idx_thm = INDEX_CONV conv eq_tm
                              handle Conv.UNCHANGED => dummy_thm
              in
                if rhsc idx_thm = boolSyntax.F then
                  Lib.FAIL (ii, idx_thm)
                else
                  bit_theorem (Arbnum.plus1 i) (idx_thm :: a)
              end
      in
        bit_theorem Arbnum.zero []
      end
  val cmp = reduceLib.num_compset ()
  val _ = computeLib.add_thms [combinTheory.o_THM, combinTheory.K_THM] cmp
  val NUM_CONV = computeLib.CBV_CONV cmp
  fun FORALL_EQ_RULE vars t =
        List.foldr (fn (v,t) => Drule.FORALL_EQ v t) t vars
        |> Conv.RIGHT_CONV_RULE (Rewrite.REWRITE_CONV [])
in
  fun BIT_BLAST_CONV tm =
  let
    val _ = is_blastable tm orelse
            raise ERR "BIT_BLAST_CONV" "term not suited to bit blasting"
    val thm = Conv.QCONV BLAST_CONV tm
    val c = rhsc thm
  in
    if Term.term_eq c boolSyntax.T orelse Term.term_eq c boolSyntax.F then
      thm
    else let val conv = mk_sums NUM_CONV c in
      if wordsSyntax.is_index tm then
        let
          val thm2 = INDEX_CONV conv c
        in
          Conv.RIGHT_CONV_RULE (Conv.REWR_CONV thm2) thm
        end
      else if wordsSyntax.is_word_lo tm then
        Conv.RIGHT_CONV_RULE (Conv.REWR_CONV (conv c)) thm
      else let val (l,r) = boolSyntax.dest_eq c in
        if wordsSyntax.is_index l andalso wordsSyntax.is_index r then
          let
            val thm2 = TRY_INDEX_CONV conv l
            val thm3 = TRY_INDEX_CONV conv r
          in
            Conv.RIGHT_CONV_RULE
              (PURE_REWRITE_CONV [thm2, thm3]
               THENC Conv.TRY_CONV BIT_TAUT_CONV) thm
          end
        else
          case bit_theorems conv (dim_of_word l, l, r)
          of Lib.PASS thms =>
                 Conv.RIGHT_CONV_RULE
                   (Conv.REWR_CONV (fcp_eq_thm (Term.type_of l))
                    THENC REWRITE_CONV thms) thm
           | Lib.FAIL (i, fail_thm) =>
               let
                 val ty = wordsSyntax.dim_of l
                 val sz_thm = mk_size_thm (i, ty)
                 val thm2 = Drule.MATCH_MP FCP_NEQ (Thm.CONJ sz_thm fail_thm)
               in
                 Conv.RIGHT_CONV_RULE (Conv.REWR_CONV thm2) thm
               end
      end
    end
  end

  fun BBLAST_CONV tm =
      let
        val _ = Term.type_of tm = Type.bool orelse
                raise ERR "BBLAST_CONV" "not a bool term"
        val (vars,tm') = boolSyntax.strip_forall tm
        val thm = Conv.QCONV WORD_SIMP_CONV tm'
        val tms = HolKernel.find_terms is_blastable (rhsc thm)
        val thms = Lib.mapfilter BIT_BLAST_CONV tms
      in
        FORALL_EQ_RULE vars
          (Conv.RIGHT_CONV_RULE
             (Rewrite.ONCE_REWRITE_CONV thms THENC
              Conv.TRY_CONV BIT_TAUT_CONV) thm)
      end
end

local
  fun is_quant tm = boolSyntax.is_forall tm orelse boolSyntax.is_exists tm;

  fun counter_terms _ [] = raise ERR "counter_terms" "empty"
    | counter_terms [] tms = tl tms
    | counter_terms ({redex,residue}::l) (t::tms) =
        counter_terms l
          (Term.subst [redex |-> residue]
             (snd (boolSyntax.dest_exists t)) :: t :: tms)

  fun build_exists [] _ cthm = cthm
    | build_exists _ [] cthm = cthm
    | build_exists ({redex,residue}::l1) (t::l2) cthm =
        build_exists l1 l2 (Thm.EXISTS (t, residue) cthm);

  fun order_counter [] [] a = List.rev a
    | order_counter [] _ _ = raise ERR "BBLAST_PROVE" "Couldn't prove goal."
    | order_counter (v::vars) counter a =
        let
          val (c,rest) = Lib.pluck (fn {redex,residue} => (redex = v)) counter
        in
          order_counter vars rest (c :: a)
        end handle HOL_ERR _ => raise ERR "BBLAST_PROVE" "Couldn't prove goal."
in
  fun BBLAST_PROVE tm =
  let
    val (vars,tm') = boolSyntax.strip_exists tm
    val thm = BBLAST_CONV tm'
  in
    if List.null vars then
      Drule.EQT_ELIM thm
      handle HOL_ERR _ =>
         let
           val body = snd (boolSyntax.strip_forall tm)
           val counter = counterexample (rhsc thm)
         in
           if not (List.null counter) andalso
              Lib.can (order_counter (Term.free_vars body) counter) []
           then
             let val _ = if !blast_counter then
                           print_counterexample counter
                         else
                           ()
                 val ctm = Term.subst counter body
             in
               raise HolSatLib.SAT_cex (wordsLib.WORD_EVAL_CONV ctm)
             end
           else
             raise ERR "BBLAST_PROVE" "Couldn't prove goal."
         end
    else let val ctm = rhsc thm in
      if ctm = boolSyntax.T then
        Drule.EQT_ELIM
          ((PURE_ONCE_REWRITE_CONV [thm] THENC
            REPEATC Conv.EXISTS_SIMP_CONV) tm)
      else let
        val counter = counterexample (boolSyntax.mk_neg ctm)
        val counter = order_counter vars counter []
        val ctms = counter_terms counter [boolSyntax.list_mk_exists(vars,ctm)]
        val cthm = Drule.EQT_ELIM
                     (wordsLib.WORD_EVAL_CONV (Term.subst counter ctm))
        val cthm' = build_exists (List.rev counter) ctms cthm
      in
        PURE_ONCE_REWRITE_RULE [GSYM thm] cthm'
      end
    end
  end
end

val BBLAST_RULE = Conv.CONV_RULE BBLAST_CONV;
val BBLAST_TAC  = Tactic.CONV_TAC BBLAST_CONV;

val FULL_BBLAST_TAC =
  REPEAT
    (Tactical.PRED_ASSUM (Lib.can (HolKernel.find_term is_blastable)) MP_TAC)
  THEN BBLAST_TAC;

(* ------------------------------------------------------------------------ *)

end
