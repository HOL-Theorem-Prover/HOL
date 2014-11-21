structure blastLib :> blastLib =
struct

open HolKernel boolLib bossLib;
open bitTheory wordsTheory bitstringTheory blastTheory;
open listLib wordsLib bitSyntax bitstringSyntax;

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars blastTheory.blast_grammars
end

open Parse

(* ------------------------------------------------------------------------ *)

val ERR = Feedback.mk_HOL_ERR "blastLib"

val blast_trace = ref 0
val blast_counter = ref true
val blast_multiply_limit = ref 8

val _ = Feedback.register_trace ("bit blast", blast_trace, 3)
val _ = Feedback.register_btrace ("print blast counterexamples", blast_counter)
val _ = Feedback.register_trace
          ("blast multiply limit", blast_multiply_limit, 32)

val rhsc = boolSyntax.rhs o Thm.concl

val dim_of_word = fcpLib.index_to_num o wordsSyntax.dim_of

(* ------------------------------------------------------------------------
   mk_index_thms : Generate rewrites of the form  ``($FCP f) ' i = f i``.
   INDEX_CONV    : Evaluation for terms of the form  ``($FCP f) ' i``.
   ------------------------------------------------------------------------ *)

fun mk_leq_thm (i,j) =
   numSyntax.mk_leq (i, j)
   |> (DEPTH_CONV wordsLib.SIZES_CONV THENC numLib.REDUCE_CONV)
   |> Drule.EQT_ELIM

fun mk_less_thm (i,j) =
   numSyntax.mk_less (i, j)
   |> (Conv.RAND_CONV (TRY_CONV wordsLib.SIZES_CONV) THENC numLib.REDUCE_CONV)
   |> Drule.EQT_ELIM

fun mk_size_thm (i,ty) = mk_less_thm (i, wordsSyntax.mk_dimindex ty)

local
   val e_tys = ref (Redblackset.empty Type.compare)
   val cmp = reduceLib.num_compset ()
   val () = computeLib.add_thms [combinTheory.o_THM, combinTheory.K_THM] cmp
   val cnv = computeLib.CBV_CONV cmp

   val fcp_beta_thm = fcpTheory.FCP_BETA
                      |> Drule.SPEC_ALL
                      |> Thm.INST_TYPE [Type.alpha |-> Type.bool]
                      |> Q.GEN `i`

   fun mk_index_thms ty =
      case Lib.total fcpSyntax.dest_int_numeric_type ty of
         SOME n =>
           let
              val indx_thm = Thm.INST_TYPE [Type.beta |-> ty] fcp_beta_thm
           in
              List.tabulate
                (n, fn i =>
                       let
                          val j = numSyntax.term_of_int i
                       in
                          Thm.MP (Thm.SPEC j indx_thm) (mk_size_thm (j, ty))
                       end)
           end
       | NONE => []

   fun is_new tm =
      case Lib.total wordsSyntax.dim_of tm of
         SOME ty => not (Redblackset.member (!e_tys, ty)) andalso
                    (e_tys := Redblackset.add (!e_tys, ty); true)
       | NONE => false

   val new_index_thms =
      List.concat o List.map (mk_index_thms o wordsSyntax.dim_of) o
      HolKernel.find_terms is_new

   fun add_index_thms tm = computeLib.add_thms (new_index_thms tm) cmp
in
   fun ADD_INDEX_CONV tm = (add_index_thms tm; cnv tm)

   fun INDEX_CONV tm = Conv.CHANGED_CONV cnv tm
                       handle HOL_ERR _ => raise Conv.UNCHANGED
end

(* --------------------------------------------------------------------
   mk_testbit_thms : find terms of the form ``FCP i. testbit i [..]`` and
                     ``testbit n [..]``, then generate rewrites for extracting
                     bits from the bitstring
   -------------------------------------------------------------------- *)

local
   val nd = Drule.CONJUNCTS numeralTheory.numeral_distrib
   val cmp = computeLib.new_compset
              [Thm.CONJUNCT1 listTheory.EL, listTheory.EL_simp_restricted,
               listTheory.HD, numeralTheory.numeral_pre,
               arithmeticTheory.NORM_0, List.nth (nd, 15), List.nth (nd, 16)]
   val EL_CONV = computeLib.CBV_CONV cmp

   fun gen_testbit_thms (n, m) =
      let
         val vs = List.tabulate
                     (n, fn i => Term.mk_var ("v" ^ Int.toString i, Type.bool))
         val vs = listSyntax.mk_list (vs, Type.bool)
         val lvs = listSyntax.mk_length vs
         val l = listLib.LENGTH_CONV lvs
         val el_thms =
            List.tabulate (n,
               fn i => EL_CONV (listSyntax.mk_el (numSyntax.term_of_int i, vs)))
      in
         List.tabulate (m,
            fn i =>
              let
                 val ti = numSyntax.term_of_int i
              in
                 if i < n then
                    let
                       val thm = numSyntax.mk_less (ti, lvs)
                                   |> (Conv.RAND_CONV (Conv.REWR_CONV l)
                                       THENC numLib.REDUCE_CONV)
                                   |> Drule.EQT_ELIM
                       val thm = Drule.MATCH_MP bitstringTheory.testbit_el thm
                    in
                       Conv.RIGHT_CONV_RULE
                         (PURE_REWRITE_CONV [l]
                          THENC Conv.RATOR_CONV
                                  (Conv.RAND_CONV numLib.REDUCE_CONV)
                          THENC PURE_REWRITE_CONV el_thms) thm
                    end
                 else
                    let
                       val thm = numSyntax.mk_leq (lvs, ti)
                                   |> (Conv.LAND_CONV (Conv.REWR_CONV l)
                                       THENC numLib.REDUCE_CONV)
                                   |> Drule.EQT_ELIM
                    in
                       Drule.MATCH_MP bitstringTheory.testbit_geq_len thm
                    end
              end)
      end

   fun testbit_dest tm =
      let
         val (i, v) = bitstringSyntax.dest_testbit tm
      in
         (List.length (fst (listSyntax.dest_list v)),
          numSyntax.int_of_term i + 1)
      end
      handle HOL_ERR _ =>
         let
            val (j, t) =
               HolKernel.dest_binder fcpSyntax.fcp_tm (ERR "dest_FCP" "") tm
            val (i, v) = bitstringSyntax.dest_testbit t
         in
            (List.length (fst (listSyntax.dest_list v)),
             Arbnum.toInt (wordsSyntax.size_of tm))
         end
in
   fun mk_testbit_thms tm =
      tm |> HolKernel.find_terms (Lib.can testbit_dest)
         |> List.map testbit_dest
         |> Listsort.sort (Lib.pair_compare (Int.compare, Int.compare))
         |> Lib.op_mk_set (fn a => fn b => fst a = fst b)
         |> List.map gen_testbit_thms
         |> List.concat
end

(* ------------------------------------------------------------------------
   EVAL_CONV    : General purpose evaluation
   ------------------------------------------------------------------------ *)

local
  val cmp = reduceLib.num_compset ()

  val () =
     (computeLib.add_thms
        [pred_setTheory.NOT_IN_EMPTY, pred_setTheory.IN_INSERT,
         REWRITE_RULE [GSYM arithmeticTheory.DIV2_def] BIT_SET_def,
         listTheory.EVERY_DEF, listTheory.FOLDL,
         numLib.SUC_RULE rich_listTheory.COUNT_LIST_AUX_def,
         GSYM rich_listTheory.COUNT_LIST_GENLIST,
         rich_listTheory.COUNT_LIST_compute,
         numeral_bitTheory.numeral_log2, numeral_bitTheory.numeral_ilog2,
         numeral_bitTheory.LOG_compute, GSYM DISJ_ASSOC] cmp
      ; computeLib.add_conv
            (``fcp$dimindex:'a itself -> num``, 1, wordsLib.SIZES_CONV) cmp
      ; computeLib.add_conv
            (``words$word_mod:'a word -> 'a word -> 'a word``, 2,
             wordsLib.WORD_MOD_BITS_CONV) cmp)
in
   val EVAL_CONV = computeLib.CBV_CONV cmp
end

(* ------------------------------------------------------------------------ *)

fun INST_b3 t thm =
   Thm.GENL [``x:num->bool``, ``y:num->bool``, ``c:bool``, ``i:num``,
             ``n:num``, ``b1:bool``, ``b2:bool``] o
   PURE_REWRITE_RULE [thm] o Thm.INST [``b3:bool`` |-> t] o Drule.SPEC_ALL

val BCARRY_mp = Q.prove(
   `!x y c i n b1 b2 b3.
      (i = SUC n) /\ (x n = b1) /\ (y n = b2) /\ (BCARRY n x y c = b3) ==>
      (BCARRY i x y c = bcarry b1 b2 b3)`,
   SRW_TAC [] [BCARRY_def])

val BCARRY_mp = REWRITE_RULE [bcarry_def] BCARRY_mp

val BCARRY_mp_carry =
   INST_b3 boolSyntax.T (DECIDE ``x /\ y \/ (x \/ y) /\ T = x \/ y``) BCARRY_mp

val BCARRY_mp_not_carry =
   INST_b3 boolSyntax.F (DECIDE ``x /\ y \/ (x \/ y) /\ F = x /\ y``) BCARRY_mp

fun INST_b3 t thm =
   Thm.GENL [``x:num->bool``,``y:num->bool``, ``c:bool``, ``i:num``,
             ``b1:bool``, ``b2:bool``] o
   PURE_REWRITE_RULE [thm] o Thm.INST [``b3:bool`` |-> t] o Drule.SPEC_ALL

val BSUM_mp = Q.prove(
   `!x y c i b1 b2 b3.
      (x i = b1) /\ (y i = b2) /\ (BCARRY i x y c = b3) ==>
      (BSUM i x y c = bsum b1 b2 b3)`,
   SRW_TAC [] [BSUM_def])

val BSUM_mp = REWRITE_RULE [bsum_def] BSUM_mp

val BSUM_mp_carry =
   INST_b3 boolSyntax.T (DECIDE ``((x = ~y) = ~T) = (x:bool = y)``) BSUM_mp

val BSUM_mp_not_carry =
   INST_b3 boolSyntax.F (DECIDE ``((x = ~y) = ~F) = (x:bool = ~y)``) BSUM_mp

val rhs_rewrite =
   Conv.RIGHT_CONV_RULE
     (Rewrite.REWRITE_CONV
       [satTheory.AND_INV, Drule.EQF_INTRO boolTheory.NOT_AND,
        DECIDE ``!b:bool. (b = ~b) = F``,
        DECIDE ``!b:bool. (~b = b) = F``])

(* --------------------------------------------------------------------
   mk_summation : returns theorems of the form  ``BSUM i x y c = exp``
                  for all 0 < i < max, where "exp" is a propositional
                  expression.
   -------------------------------------------------------------------- *)

fun SP l (thm1, thm2) = (Drule.SPECL (tl l) thm1, Drule.SPECL l thm2)

fun mk_summation rwts (max, x, y, c) =
   let
      val conv = INDEX_CONV THENC PURE_REWRITE_CONV rwts
      val SPEC_SUM = Drule.SPECL [x, y, c]
      val iBSUM_mp_carry       = SPEC_SUM BSUM_mp_carry
      val iBSUM_mp_not_carry   = SPEC_SUM BSUM_mp_not_carry
      val iBSUM_mp             = SPEC_SUM BSUM_mp
      val iBCARRY_mp_carry     = SPEC_SUM BCARRY_mp_carry
      val iBCARRY_mp_not_carry = SPEC_SUM BCARRY_mp_not_carry
      val iBCARRY_mp           = SPEC_SUM BCARRY_mp
      fun mk_sums p (s, c_thm) =
         if p = max
            then s
         else let
                 val pp = Arbnum.plus1 p
              in
                 mk_sums pp
                  (let
                      val n = numLib.mk_numeral p
                      val i = numLib.mk_numeral pp
                      val () =
                         if !blast_trace > 2
                            then print ("Expanding bit... " ^
                                        Arbnum.toString pp ^ "\n")
                         else ()
                      val i_thm = boolSyntax.mk_eq (i, numSyntax.mk_suc n)
                                  |> numLib.REDUCE_CONV |> Drule.EQT_ELIM
                      val x_thm = Conv.QCONV conv (Term.mk_comb (x, n))
                      val y_thm = Conv.QCONV conv (Term.mk_comb (y, n))
                      val x_concl = rhsc x_thm
                      val y_concl = rhsc y_thm
                      val c_concl = rhsc c_thm
                      val (thm1,thm2) =
                         if c_concl = boolSyntax.T
                            then SP [i, n, x_concl, y_concl]
                                    (iBSUM_mp_carry, iBCARRY_mp_carry)
                         else if c_concl = boolSyntax.F
                            then SP [i, n, x_concl, y_concl]
                                    (iBSUM_mp_not_carry, iBCARRY_mp_not_carry)
                         else SP [i, n, x_concl, y_concl, c_concl]
                                 (iBSUM_mp, iBCARRY_mp)
                   in
                      (rhs_rewrite
                         (Thm.MP thm1
                            (Drule.LIST_CONJ [x_thm, y_thm, c_thm])) :: s,
                       rhs_rewrite
                         (Thm.MP thm2
                            (Drule.LIST_CONJ [i_thm, x_thm, y_thm, c_thm])))
                   end)
              end
   in
      mk_sums Arbnum.zero
         ([], BCARRY_def |> Thm.CONJUNCT1 |> Drule.SPECL [x,y,c])
   end

(* --------------------------------------------------------------------
   mk_carry : returns theorem of the form  ``BCARRY max x y c = exp``,
              where "exp" is a propositional expression.
   -------------------------------------------------------------------- *)

fun mk_carry rwts (max, x, y, c) =
   let
      val conv = INDEX_CONV THENC PURE_REWRITE_CONV rwts

      val SPEC_CARRY = Drule.SPECL [x, y, c]

      val iBCARRY_mp_carry     = SPEC_CARRY BCARRY_mp_carry
      val iBCARRY_mp_not_carry = SPEC_CARRY BCARRY_mp_not_carry
      val iBCARRY_mp           = SPEC_CARRY BCARRY_mp

      fun mk_c p c_thm =
         if p = max
            then c_thm
         else let
                 val pp = Arbnum.plus1 p
              in
                 mk_c pp
                  (let
                      val n = numLib.mk_numeral p
                      val i = numLib.mk_numeral pp
                      val () =
                         if !blast_trace > 2
                            then print ("Expanding bit... " ^
                                        Arbnum.toString pp ^ "\n")
                         else ()
                      val i_thm = boolSyntax.mk_eq (i, numSyntax.mk_suc n)
                                    |> numLib.REDUCE_CONV |> Drule.EQT_ELIM
                      val x_thm = Conv.QCONV conv (Term.mk_comb (x, n))
                      val y_thm = Conv.QCONV conv (Term.mk_comb (y, n))
                      val x_concl = rhsc x_thm
                      val y_concl = rhsc y_thm
                      val c_concl = rhsc c_thm
                      val thm =
                         if c_concl = boolSyntax.T
                            then Drule.SPECL [i, n, x_concl, y_concl]
                                   iBCARRY_mp_carry
                         else if c_concl = boolSyntax.F
                            then Drule.SPECL [i, n, x_concl, y_concl]
                                   iBCARRY_mp_not_carry
                         else Drule.SPECL [i, n, x_concl, y_concl, c_concl]
                                iBCARRY_mp
                   in
                      rhs_rewrite
                         (Thm.MP thm
                            (Drule.LIST_CONJ [i_thm, x_thm, y_thm, c_thm]))
                   end)
              end
   in
      mk_c Arbnum.zero (BCARRY_def |> Thm.CONJUNCT1 |> Drule.SPECL [x,y,c])
   end

(* --------------------------------------------------------------------
   mk_sums : find terms of the form ``FCP i. BSUM i x y c`` and
             ``BCARRY n x y c``; it then uses mk_summation and mk_carry
             to generate appropriate rewrites
   -------------------------------------------------------------------- *)

local
   fun dest_sum tm =
      case boolSyntax.dest_strip_comb tm of
         ("fcp$FCP", [f]) =>
           (case f |> Term.dest_abs |> snd |> boolSyntax.dest_strip_comb of
               ("blast$BSUM", [i, x, y, c]) =>
                   (false, (dim_of_word tm, x, y, c))
             | _ => raise ERR "dest_sum" "")
       | ("blast$BSUM", [n, x, y, c]) =>
           (false, (Arbnum.plus1 (numLib.dest_numeral n), x, y, c))
       | ("blast$BCARRY", [n, x, y, c]) =>
           (true, (numLib.dest_numeral n, x, y, c))
       | _ => raise ERR "dest_sum" ""

   val is_sum = Lib.can dest_sum

   fun pick_max [] m = m
     | pick_max ((h as (_,(n,_,_,_)))::t) (m as (_,(n2,_,_,_))) =
         pick_max t (if Arbnum.>(n, n2) then h else m)

   fun remove_redundant [] = []
     | remove_redundant ((h as (_,(n,x,y,c)))::t) =
        let
           val (l,r) = List.partition
                          (fn (_, (n2, x2, y2, c2)) =>
                             x = x2 andalso y = y2 andalso c = c2) t
        in
           pick_max l h :: remove_redundant r
        end
in
   fun mk_sums tm =
      let
         val rws = mk_testbit_thms tm
         val tms = HolKernel.find_terms is_sum tm
         val tms = tms |> Lib.mk_set
                       |> Listsort.sort
                            (Int.compare o (Term.term_size ## Term.term_size))
                       |> List.map dest_sum
                       |> remove_redundant
         val () = if !blast_trace > 0 andalso not (List.null tms)
                     then print ("Found " ^ Int.toString (List.length tms) ^
                                " summation term(s)\n")
                  else ()
         val (_, rwts, c_outs) =
            List.foldl
               (fn ((b,nxyc), (i, rwts, c_outs)) =>
                   (if !blast_trace > 0
                       then print ("Expanding term... " ^ Int.toString i ^ "\n")
                    else ()
                    ; if b then (i + 1, rwts, mk_carry rwts nxyc :: c_outs)
                      else (i + 1, mk_summation rwts nxyc @ rwts, c_outs)))
                 (1, rws, []) tms
      in
         rwts @ c_outs
      end
end

(* ------------------------------------------------------------------------
   WORD_LIT_CONV : Rewrites occurances of ``BIT i v`` using theorems
                   ``BIT i v = (i = p1) \/ ... \/ (i = pn)``, where
                   v is the numeric value of the literal and p1..pn
                   are the bit positions for T bits.
   ------------------------------------------------------------------------ *)

local
   val BIT_SET_CONV = Conv.REWR_CONV wordsTheory.BIT_SET THENC EVAL_CONV

   fun is_bit_lit tm =
      case Lib.total bitSyntax.dest_bit tm of
         SOME (_, n) => numSyntax.is_numeral n
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

local
   val FCP_EQ_EVERY = Q.prove(
      `!a b:'a word.
         (a = b) = EVERY (\i. a ' i = b ' i) (GENLIST I (dimindex (:'a)))`,
      SRW_TAC [fcpLib.FCP_ss] [listTheory.EVERY_GENLIST])

   val FCP_EQ_EVERY =
      REWRITE_RULE [GSYM rich_listTheory.COUNT_LIST_GENLIST,
                    rich_listTheory.COUNT_LIST_compute] FCP_EQ_EVERY

   val FCP_EQ_CONV = Conv.REWR_CONV FCP_EQ_EVERY THENC EVAL_CONV

   val fcp_map = ref (Redblackmap.mkDict Arbnum.compare)
                   : (Arbnum.num, Thm.thm) Redblackmap.dict ref
in
   fun fcp_eq_thm ty =
      case Lib.total (fcpLib.index_to_num o wordsSyntax.dest_word_type) ty of
         SOME n =>
             (case Redblackmap.peek (!fcp_map, n) of
                 SOME thm => thm
               | _ =>
                  let
                     val a = Term.mk_var ("a", ty)
                     val b = Term.mk_var ("b", ty)
                     val thm = FCP_EQ_CONV (boolSyntax.mk_eq (a,b))
                     val thm = Thm.GEN a (Thm.GEN b thm)
                     val () = fcp_map := Redblackmap.insert (!fcp_map, n, thm)
                  in
                     thm
                  end)
       | NONE => raise ERR "fcp_eq_thm" ""
end

(* ------------------------------------------------------------------------
   SMART_MUL_LSL_CONV : converts ``n2w n * w`` into either
                        ``w << p1 + ... + w << pn`` or
                        ``-w << p1 + ... + -w << pn`` depending on
                        which gives the fewest additions.
                        NB. ``-w`` is ``~w + 1w``.
   ------------------------------------------------------------------------ *)

local
   val NEG_WORD =
      Drule.EQT_ELIM (wordsLib.WORD_CONV ``a * b = -a * -b :'a word``)
   val SYM_WORD_NEG_MUL = GSYM wordsTheory.WORD_NEG_MUL
   fun boolify sz =
      (fn l => List.take (l, sz)) o String.explode o StringCvt.padLeft #"0" sz o
      Arbnum.toBinString
in
   fun SMART_MUL_LSL_CONV tm =
      let
         val l = fst (wordsSyntax.dest_word_mul tm)
      in
         case Lib.total wordsSyntax.dest_word_2comp l of
            SOME v =>
              if Lib.total wordsSyntax.dest_word_literal v = SOME Arbnum.one
                 then Conv.REWR_CONV SYM_WORD_NEG_MUL tm
              else raise ERR "SMART_MUL_LSL_CONV" "not -1w * x"
          | NONE =>
             let
                val (N,sz) = wordsSyntax.dest_mod_word_literal l
                             handle HOL_ERR _ =>
                                (wordsSyntax.dest_word_literal l, Arbnum.zero)
             in
                if sz = Arbnum.zero orelse Arbnum.< (N, Arbnum.fromInt 11)
                   then wordsLib.WORD_MUL_LSL_CONV tm
                else let
                        val sz = Arbnum.toInt sz
                        val c_pos = N |> boolify sz
                                      |> List.filter (Lib.equal #"1")
                                      |> List.length
                        val c_neg = N |> Arbnum.less1
                                      |> boolify sz
                                      |> List.filter (Lib.equal #"0")
                                      |> List.length
                     in
                        if c_pos <= 2 * c_neg + 1
                           then wordsLib.WORD_MUL_LSL_CONV tm
                        else (Conv.REWR_CONV NEG_WORD
                              THENC Conv.RATOR_CONV wordsLib.WORD_EVAL_CONV
                              THENC wordsLib.WORD_MUL_LSL_CONV) tm
                     end
             end
      end
end

(* ------------------------------------------------------------------------ *)

local
    val thm = Q.SPECL [`a`, `n2w (NUMERAL n)`] wordsTheory.WORD_SUM_ZERO
    val WORD_SUM_ZERO_CONV =
       Conv.REWR_CONV thm THENC Conv.RHS_CONV wordsLib.WORD_EVAL_CONV

   val word_ss = std_ss++wordsLib.SIZES_ss++wordsLib.WORD_ARITH_ss++
                 wordsLib.WORD_LOGIC_ss++wordsLib.WORD_SHIFT_ss++
                 wordsLib.WORD_CANCEL_ss

   val SYM_WORD_NOT_LOWER = GSYM WORD_NOT_LOWER

   val bit_rwts = [word_lsb_def, word_msb_def, word_bit_def]

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
   val WORD_SIMP_CONV =
      SIMP_CONV word_ss bit_rwts
      THENC Conv.TRY_CONV WORD_SUM_ZERO_CONV
      THENC REWRITE_CONV order_rwts
      THENC Conv.DEPTH_CONV wordsLib.SIZES_CONV
      THENC Conv.DEPTH_CONV SMART_MUL_LSL_CONV
      THENC Conv.DEPTH_CONV WORD_DIV_LSR_CONV
end

(* ------------------------------------------------------------------------
   LSL_BV_CONV, LSR_BV_CONV, ASR_BV_CONV, ROR_BV_CONV, ROL_BV_CONV :
      Expand shifts by bit-vector
   ------------------------------------------------------------------------ *)

local
  val word_bits_thm1 = Q.prove(
     `!l h n w:'a word.
         l + n < dimindex(:'a) /\ l + n <= h ==>
         ((h -- l) w ' n = w ' (n + l))`,
     SRW_TAC [fcpLib.FCP_ss, ARITH_ss] [word_bits_def])

  val word_bits_thm2 = Q.prove(
     `!l h n w:'a word.
        n < dimindex(:'a) /\ h < l + n ==> ((h -- l) w ' n = F)`,
     SRW_TAC [fcpLib.FCP_ss, ARITH_ss] [word_bits_def])

  val word_bits_thm3 = word_bits_thm1 |> Q.SPEC `0n` |> SIMP_RULE std_ss []
  val word_bits_thm4 = word_bits_thm1 |> Q.SPECL [`l`,`dimindex(:'a) - 1`]
                       |> SIMP_RULE (arith_ss++boolSimps.CONJ_ss) []
                       |> GEN_ALL
  val word_bits_thm5 = word_bits_thm2 |> Q.SPEC `0n` |> SIMP_RULE std_ss []
  val word_bits_thm6 = word_bits_thm2 |> Q.SPECL [`l`,`dimindex(:'a) - 1`]
                       |> SIMP_RULE (arith_ss++boolSimps.CONJ_ss)
                            [DECIDE ``a < b + (c + 1) = a <= b + c : num``]
                       |> GEN_ALL

  fun mk_word_eq_lit_thms ty =
     let
        val d = fcpSyntax.dest_int_numeric_type ty
        val wty = wordsSyntax.mk_word_type ty
        val v = Term.mk_var ("m", wty)
        val eq_thm = fcp_eq_thm wty
     in
        List.tabulate (d, fn i =>
           let
              val n = wordsSyntax.mk_n2w (numLib.term_of_int i, ty)
              val tm = boolSyntax.mk_eq (v, n)
           in
             (Conv.RHS_CONV (Conv.REWR_CONV n2w_def THENC WORD_LIT_CONV)
              THENC Conv.REWR_CONV eq_thm
              THENC ADD_INDEX_CONV) tm
           end)
     end

  fun mk_word_bits_indx_thms ty =
     let
        val d = fcpSyntax.dest_int_numeric_type ty
        val h = Arbnum.toInt (Arbnum.log2 (Arbnum.fromInt (d - 1)))
        val h_plus1 = h + 1
        val h_tm = numLib.term_of_int h
        val h_plus1_tm = numLib.term_of_int h_plus1
        val wty = wordsSyntax.mk_word_type ty
        val v = Term.mk_var ("m", wty)
        val dim = fcpSyntax.mk_dimindex ty
     in
        List.tabulate (d, fn i =>
          let
             val n = numLib.term_of_int i
             val lt_thm = mk_less_thm (n, dim)
             val sm = numSyntax.mk_plus (h_plus1_tm,n)
             val rwt1 =
                if i <= h
                   then let
                           val le_thm = mk_leq_thm (n, h_tm)
                        in
                           Thm.MP (Drule.ISPECL [h_tm, n, v] word_bits_thm3)
                                  (Thm.CONJ lt_thm le_thm)
                        end
                else let
                        val lt_thm2 = mk_less_thm (h_tm, n)
                     in
                        Thm.MP (Drule.ISPECL [h_tm, n, v] word_bits_thm5)
                               (Thm.CONJ lt_thm lt_thm2)
                     end
             val rwt2 =
                if i + h_plus1 < d
                   then let
                           val lt_thm2 = mk_less_thm (sm, dim)
                         in
                            wordsLib.WORD_EVAL_RULE
                              (Thm.MP (Drule.ISPECL [h_plus1_tm, n, v]
                                         word_bits_thm4) lt_thm2)
                         end
                   else let
                           val le_thm = mk_leq_thm (dim, sm)
                        in
                           wordsLib.WORD_EVAL_RULE
                             (Thm.MP (Drule.ISPECL [h_plus1_tm, n, v]
                                        word_bits_thm6)
                                     (Thm.CONJ lt_thm le_thm))
                        end
          in
             [rwt1,rwt2]
          end)
     end

  val mk_word_bits_indx_thms = List.concat o mk_word_bits_indx_thms

  fun mk_bv_thm thm ty =
     let
        val rwts = mk_word_eq_lit_thms ty @ mk_word_bits_indx_thms ty
     in
        thm
        |> Thm.INST_TYPE [Type.alpha |-> ty]
        |> Conv.CONV_RULE
             (Conv.STRIP_QUANT_CONV (Conv.RHS_CONV
                (EVAL_CONV THENC REWRITE_CONV rwts)))
     end

  fun BV_CONV last mk_bv tm =
     Conv.REWR_CONV (!last) tm
     handle HOL_ERR _ =>
        let
           val thm = mk_bv (wordsSyntax.dim_of tm)
        in
           (last := thm; Conv.REWR_CONV thm tm)
        end

  val last_lsl_thm = ref combinTheory.I_THM
  val last_lsr_thm = ref combinTheory.I_THM
  val last_asr_thm = ref combinTheory.I_THM
  val last_ror_thm = ref combinTheory.I_THM
  val last_rol_thm = ref combinTheory.I_THM
in
  fun LSL_BV_CONV tm = BV_CONV last_lsl_thm
                           (mk_bv_thm blastTheory.word_lsl_bv_expand) tm
  fun LSR_BV_CONV tm = BV_CONV last_lsr_thm
                           (mk_bv_thm blastTheory.word_lsr_bv_expand) tm
  fun ASR_BV_CONV tm = BV_CONV last_asr_thm
                           (mk_bv_thm blastTheory.word_asr_bv_expand) tm
  fun ROR_BV_CONV tm = BV_CONV last_rol_thm
                           (mk_bv_thm blastTheory.word_ror_bv_expand) tm
  fun ROL_BV_CONV tm = BV_CONV last_rol_thm
                           (mk_bv_thm blastTheory.word_rol_bv_expand) tm
end

(* ------------------------------------------------------------------------
   BLAST_MUL_CONV : expands bit vector multiplication
   ------------------------------------------------------------------------ *)

local
   fun mk_bitwise_mul i =
      blastTheory.BITWISE_MUL
      |> Thm.INST_TYPE [Type.alpha |-> fcpSyntax.mk_int_numeric_type i]
      |> Conv.CONV_RULE
            (Conv.STRIP_QUANT_CONV (Conv.RHS_CONV
                (EVAL_CONV THENC PURE_REWRITE_CONV [wordsTheory.WORD_ADD_0])))

   val mul_rwts = ref ([]: thm list)
in
   fun BLAST_MUL_CONV tm =
      let
         val l = fst (wordsSyntax.dest_word_mul tm)
         val sz = fcpSyntax.dest_int_numeric_type (wordsSyntax.dim_of l)
         val _ = sz <= !blast_multiply_limit orelse
                 raise ERR "BLAST_MUL_CONV" "bigger than multiply limit"
      in
         PURE_REWRITE_CONV (!mul_rwts) tm
         handle Conv.UNCHANGED =>
            (mul_rwts := mk_bitwise_mul sz :: !mul_rwts
             ; PURE_REWRITE_CONV (!mul_rwts) tm)
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
      SRW_TAC [fcpLib.FCP_ss] [word_L])

   val minus1_thm = Q.prove(
      `-1w = $FCP (K T)`,
      SRW_TAC [fcpLib.FCP_ss] [REWRITE_RULE [SYM WORD_NEG_1] word_T])

   val w2w_thm = Q.prove(
      `!w: 'a word. w2w w = FCP i. i < dimindex (:'a) /\ w ' i`,
      SRW_TAC [fcpLib.FCP_ss] [w2w])

   val sw2sw_thm = Q.prove(
      `!w: 'a word.
         sw2sw w :'b word =
         FCP i. if i < dimindex (:'a) \/ dimindex (:'b) < dimindex (:'a) then
                  w ' i
                else
                  w ' (dimindex (:'a) - 1)`,
      SRW_TAC [fcpLib.FCP_ss] [sw2sw, word_msb_def])

   fun WORD_NEG_CONV tm =
      let
         val t = wordsSyntax.dest_word_2comp tm
      in
         case Lib.total wordsSyntax.dest_word_literal t of
            SOME v => if v = Arbnum.one
                         then raise Conv.UNCHANGED
                      else wordsLib.WORD_EVAL_CONV tm
          | NONE => ONCE_REWRITE_CONV [WORD_NEG] tm
      end

   val cmp = reduceLib.num_compset ()

   val () =
     (computeLib.add_thms
        [n2w_def, v2w_def, word_xor, word_or_def, word_and_def,
         word_1comp_def, word_nor_def, word_xnor_def, word_nand_def,
         word_reduce_def, reduce_or_def, reduce_and_def, reduce_xor,
         reduce_xnor_def, reduce_nand_def, word_compare_def,
         word_replicate_def, word_join, word_concat_def, word_reverse_def,
         word_modify_def, word_lsl_def, word_lsr_def, word_asr_def,
         word_ror_def, word_rol_def, word_rrx_def, word_msb_def, word_lsb_def,
         word_extract_def, word_bits_def, word_abs, word_slice_def,
         word_bit_def, word_signed_bits_def, bit_field_insert_def, index_cond,
         SYM WORD_NEG_1, word_L_thm, minus1_thm, w2w_thm, sw2sw_thm,
         BITWISE_ADD, BITWISE_SUB, BITWISE_LO, fcpTheory.FCP_UPDATE_def,
         listTheory.HD, listTheory.TL, listTheory.SNOC, listTheory.FOLDL,
         listTheory.GENLIST_GENLIST_AUX, numLib.SUC_RULE
         listTheory.GENLIST_AUX, combinTheory.o_THM, pairTheory.SND,
         pairTheory.FST] cmp
      ; List.app (fn x => computeLib.add_conv x cmp)
         [(``fcp$dimindex:'a itself -> num``, 1, wordsLib.SIZES_CONV),
          (``words$dimword:'a itself -> num``, 1, wordsLib.SIZES_CONV),
          (``words$INT_MIN:'a itself -> num``, 1, wordsLib.SIZES_CONV),
          (``words$word_2comp:'a word -> 'a word``, 1, WORD_NEG_CONV),
          (``words$word_mul:'a word -> 'a word -> 'a word``, 2, BLAST_MUL_CONV),
          (``words$word_lsl_bv:'a word -> 'a word -> 'a word``, 2, LSL_BV_CONV),
          (``words$word_lsr_bv:'a word -> 'a word -> 'a word``, 2, LSR_BV_CONV),
          (``words$word_asr_bv:'a word -> 'a word -> 'a word``, 2, ASR_BV_CONV),
          (``words$word_ror_bv:'a word -> 'a word -> 'a word``, 2, ROR_BV_CONV),
          (``words$word_rol_bv:'a word -> 'a word -> 'a word``, 2, ROL_BV_CONV)
         ])
in
   val BLAST_CONV =
      PURE_REWRITE_CONV [GSYM word_sub_def, WORD_SUB]
      THENC computeLib.CBV_CONV cmp
      THENC WORD_LIT_CONV
end

(* ------------------------------------------------------------------------
   BIT_TAUT_CONV : wrapper around HolSatLib.SAT_PROVE
   ------------------------------------------------------------------------ *)

fun non_prop_terms tm =
   let
      fun non_prop_args acc tmlist =
         case tmlist of
            [] => acc
          | tm :: ts =>
              let
                 val (opp, args) = boolSyntax.dest_strip_comb tm
                                   handle HOL_ERR _ => ("", [])
              in
                 if Lib.mem opp ["bool$T", "bool$F", "bool$~",
                                 "bool$/\\", "bool$\\/", "min$==>"]
                    then non_prop_args acc (args @ ts)
                 else if Lib.mem opp ["min$=", "bool$COND"] andalso
                         Lib.all (fn t => Term.type_of t = Type.bool) args
                    then non_prop_args acc (args @ ts)
                 else if Term.type_of tm = Type.bool
                    then non_prop_args (HOLset.add (acc, tm)) ts
                 else raise ERR "non_prop_terms" "Not a boolean term"
              end
   in
      non_prop_args Term.empty_tmset [tm]
   end

local
   val lem = numLib.DECIDE ``!b. if b then T else T``
in
   fun PROP_PROVE conv tm =
      let
         val thm = Conv.QCONV (REWRITE_CONV [lem]) tm
         val c = rhsc thm
      in
         if c = boolSyntax.T orelse c = boolSyntax.F
            then thm
         else Conv.RIGHT_CONV_RULE
                (Conv.REWR_CONV (Drule.EQT_INTRO (conv c))) thm
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
      val f = if !blast_trace > 2
                 then (print ("Checking proposition of size: " ^
                              Int.toString sz ^ "\n")
                       ; real_time)
              else I
      val thm = f (PROP_PROVE (if sz < 100 then DPLL_CONV else SAT_CONV)) tm'
      val theta' = Lib.map2 (Lib.curry (op |->)) vars insts
   in
      Thm.INST theta' thm
   end

local
  fun eq_fst_partition [] = []
    | eq_fst_partition ((x,y)::l) =
        let
           val (eqx,neqx) = List.partition (term_eq x o fst) l
        in
           ((x, y :: List.map snd eqx)) :: eq_fst_partition neqx
        end

  fun word_counter (x,l) =
     let
        val i = Term.mk_var ("i", numLib.num)
        val ty' = wordsSyntax.dest_word_type (type_of x)
     in
        l |> List.filter fst
          |> List.map (fn (_,n) => boolSyntax.mk_eq (i, n))
          |> (fn l => if List.null l
                         then boolSyntax.F
                      else boolSyntax.list_mk_disj l)
          |> (fn f => fcpSyntax.mk_fcp (Term.mk_abs (i, f), ty'))
          |> wordsLib.WORD_EVAL_CONV
          |> concl
          |> rhs
          |> (fn t => {redex = x, residue = t})
     end

  fun bool_counter tm =
     case Lib.total boolSyntax.dest_neg tm of
        SOME t => {redex = t, residue = boolSyntax.F}
      | NONE => {redex = tm, residue = boolSyntax.T}

  fun dest_fcp (b: bool) tm =
     let
        val (x, y) = fcpSyntax.dest_fcp_index tm
     in
        (x, (b, y))
     end

  fun dest_bit tm =
     case Lib.total boolSyntax.dest_neg tm of
        SOME t => dest_fcp false t
      | NONE => dest_fcp true tm
in
  fun counterexample tm =
     let
        val tm = snd (boolSyntax.strip_forall tm)
     in
        if tm = boolSyntax.F orelse tm = boolSyntax.T
           then []
        else let
                val insts = HOLset.listItems (non_prop_terms tm)
                val vars = Term.genvars Type.bool (List.length insts)
                val theta = Lib.map2 (Lib.curry (op |->)) insts vars
                val tm' = Term.subst theta tm
                val thm = (HolSatLib.SAT_PROVE tm'; NONE)
                          handle HolSatLib.SAT_cex thm => SOME thm
             in
                case thm of
                   NONE => []
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

val arb_num_tm = boolSyntax.mk_arb numSyntax.num

local
   fun print_subst {redex,residue} =
      let
         val s = case Lib.total wordsSyntax.dest_n2w residue of
                    SOME (tm, _) =>
                       if Term.term_eq tm arb_num_tm
                          then "ARB (0w)"
                       else Hol_pp.term_to_string residue
                  | NONE => Hol_pp.term_to_string residue
      in
         Hol_pp.term_to_string redex ^ " -> " ^ s ^ "\n\n"
      end
in
   fun print_counterexample l =
      if List.null l
         then print "No counterexample found!\n"
      else (print "Found counterexample:\n\n"
            ; List.app (fn c => print (print_subst c ^ "and\n\n"))
                       (Lib.butlast l)
            ; print (print_subst (List.last l)))
end

(* ------------------------------------------------------------------------
   BIT_BLAST_CONV : convert a bit vector assertion ``a = b``, ``a ' n`` or
                    ``a <+ b`` into bitwise propositions. Uses SAT to try
                    to reduce sub-expressions to T or F.
   BBLAST_CONV : wrapper around BIT_BLAST_CONV.
   ------------------------------------------------------------------------ *)

local
  fun is_word_index tm =
     case Lib.total wordsSyntax.dest_index tm of
        SOME (w, i) => numLib.is_numeral i andalso Lib.can dim_of_word w
      | NONE => false
in
  fun is_blastable tm =
     is_word_index tm orelse
     case Lib.total boolSyntax.dest_eq tm of
        SOME (w, v) => Lib.can dim_of_word w
      | NONE => (case Lib.total wordsSyntax.dest_word_lo tm of
                    SOME (w, _) => Lib.can dim_of_word w
                  | NONE => false)

  fun full_is_blastable tm =
     is_blastable tm orelse
     case Lib.total boolSyntax.dest_strip_comb tm of
        SOME ("words$word_bit", [_, w]) => Lib.can dim_of_word w
      | SOME (s, [w, _]) =>
          Lib.can dim_of_word w andalso
          Lib.mem s
            ["words$word_lt", "words$word_le", "words$word_gt",
             "words$word_ge", "words$word_hi", "words$word_hs", "words$word_ls"]
      | SOME (s, [w]) =>
          Lib.can dim_of_word w andalso
          Lib.mem s ["words$word_msb", "words$word_lsb"]
      | _ => false
end

local
  fun TAUT_INDEX_CONV top conv =
     conv THENC (if top then Conv.ALL_CONV else Conv.TRY_CONV BIT_TAUT_CONV)

  val FCP_NEQ = trace ("metis",0) Q.prove(
    `!i a b:'a word.
       i < dimindex (:'a) /\ ((a ' i = b ' i) = F) ==> ((a = b) = F)`,
    SRW_TAC [fcpLib.FCP_ss] []
    THEN METIS_TAC [])

  val dummy_thm = SPEC_ALL combinTheory.I_THM

  val toString = Arbnum.toString

  fun bit_theorems top conv (n, l, r) =
     let
        fun BIT_TAUT_CONV tm = (INDEX_CONV THENC TAUT_INDEX_CONV top conv) tm
                               handle Conv.UNCHANGED => dummy_thm
        val tr = !blast_trace > 1
        val () = if tr then print ("Checking " ^ toString n ^ " bit word\n")
                 else ()
        fun bit_theorem i a =
           if i = n
              then Lib.PASS a
           else let
                   val () =
                      if tr then print ("Checking bit... " ^ toString i ^ "\n")
                      else ()
                   val ii = numLib.mk_numeral i
                   val li = wordsSyntax.mk_index (l, ii)
                   val ri = wordsSyntax.mk_index (r, ii)
                   val idx_thm = BIT_TAUT_CONV (boolSyntax.mk_eq (li, ri))
                in
                   if rhsc idx_thm = boolSyntax.F
                      then Lib.FAIL (ii, idx_thm)
                   else bit_theorem (Arbnum.plus1 i) (idx_thm :: a)
                end
     in
        bit_theorem Arbnum.zero []
     end

  fun FORALL_EQ_RULE vars t =
     List.foldr (fn (v,t) => Drule.FORALL_EQ v t) t vars
     |> Conv.RIGHT_CONV_RULE (Rewrite.REWRITE_CONV [])
in
  fun BIT_BLAST_CONV top tm =
     let
        val _ = is_blastable tm orelse
                raise ERR "BIT_BLAST_CONV" "term not suited to bit blasting"
        val thm = Conv.QCONV (BLAST_CONV THENC ADD_INDEX_CONV) tm
        val c = rhsc thm
     in
        if Term.term_eq c boolSyntax.T orelse Term.term_eq c boolSyntax.F
           then thm
        else let
                val RW_CONV = PURE_REWRITE_CONV (mk_sums c)
             in
                if wordsSyntax.is_index tm
                   then Conv.RIGHT_CONV_RULE (TAUT_INDEX_CONV top RW_CONV) thm
                        handle Conv.UNCHANGED => thm
                else if wordsSyntax.is_word_lo tm
                   then Conv.RIGHT_CONV_RULE RW_CONV thm
                else let
                        val (l,r) = boolSyntax.dest_eq c
                     in
                        case bit_theorems top RW_CONV (dim_of_word l, l, r) of
                           Lib.PASS thms =>
                             Conv.RIGHT_CONV_RULE
                                (Conv.REWR_CONV (fcp_eq_thm (Term.type_of l))
                                 THENC REWRITE_CONV thms) thm
                         | Lib.FAIL (i, fail_thm) =>
                             let
                                val ty = wordsSyntax.dim_of l
                                val sz_thm = mk_size_thm (i, ty)
                                val thm2 = Drule.MATCH_MP FCP_NEQ
                                             (Thm.CONJ sz_thm fail_thm)
                             in
                                Conv.RIGHT_CONV_RULE (Conv.REWR_CONV thm2) thm
                             end
                     end
             end
     end

  fun BBLAST_CONV top tm =
     let
        val _ = Term.type_of tm = Type.bool orelse
                raise ERR "BBLAST_CONV" "not a bool term"
        val (vars,tm') = boolSyntax.strip_forall tm
        val thm = Conv.QCONV WORD_SIMP_CONV tm'
        val tms = HolKernel.find_terms is_blastable (rhsc thm)
        val thms = Lib.mapfilter (BIT_BLAST_CONV top) tms
        val res = FORALL_EQ_RULE vars
                    (Conv.RIGHT_CONV_RULE
                       (Rewrite.ONCE_REWRITE_CONV thms
                        THENC Conv.TRY_CONV BIT_TAUT_CONV) thm)
     in
        if term_eq (rhsc res) tm then raise Conv.UNCHANGED else res
     end
end

local
  fun is_quant tm = boolSyntax.is_forall tm orelse boolSyntax.is_exists tm

  fun counter_terms _ [] = raise ERR "counter_terms" "empty"
    | counter_terms [] tms = tl tms
    | counter_terms ({redex,residue}::l) (t::tms) =
        counter_terms l
          (Term.subst [redex |-> residue]
             (snd (boolSyntax.dest_exists t)) :: t :: tms)

  fun build_exists [] _ cthm = cthm
    | build_exists _ [] cthm = cthm
    | build_exists ({redex,residue}::l1) (t::l2) cthm =
        build_exists l1 l2 (Thm.EXISTS (t, residue) cthm)

  fun order_ctr [] [] a = List.rev a
    | order_ctr [] _ _ = raise ERR "BBLAST_PROVE" "Couldn't prove goal."
    | order_ctr (v::vars) counter a =
        let
           val (c,rest) = Lib.pluck (fn {redex,residue} => (redex = v)) counter
        in
           order_ctr vars rest (c :: a)
        end
        handle HOL_ERR _ => raise ERR "BBLAST_PROVE" "Couldn't prove goal."
  fun order_counter v c = order_ctr v c []

  val arb_tm = wordsSyntax.mk_n2w (arb_num_tm, Type.alpha)
  fun mk_zero_subst v =
     (v |-> Term.inst [Type.alpha |-> wordsSyntax.dim_of v] arb_tm)
  fun add_subst (s1: (term, term) Lib.subst, s2: (term, term) Lib.subst) =
     let
        val reds =
           List.map (#redex) s2 fun okay v = Lib.all (not o term_eq v) reds
     in
        s2 @ (List.filter (okay o #redex) s1)
     end
in
  fun BBLAST_PROVE top tm =
     let
        val (vars,tm') = boolSyntax.strip_exists tm
        val thm = Conv.QCONV (BBLAST_CONV top) tm'
     in
        if List.null vars
           then Drule.EQT_ELIM thm
                handle HOL_ERR _ =>
                  let
                     val body = snd (boolSyntax.strip_forall tm)
                     val fvars = Term.free_vars body
                     val w_subst = Lib.mapfilter mk_zero_subst fvars
                     val counter =
                        add_subst (w_subst, counterexample (rhsc thm))
                  in
                     if not (List.null counter) andalso
                        Lib.can (order_counter fvars) counter
                        then let
                                val () = if !blast_counter
                                            then print_counterexample counter
                                         else ()
                                val ctm =
                                   Term.subst [arb_num_tm |-> numSyntax.zero_tm]
                                              (Term.subst counter body)
                          in
                             raise HolSatLib.SAT_cex
                                     (wordsLib.WORD_EVAL_CONV ctm)
                          end
                     else raise ERR "BBLAST_PROVE" "Couldn't prove goal."
                  end
        else let
                val ctm = rhsc thm
             in
                if ctm = boolSyntax.T
                   then Drule.EQT_ELIM
                           ((PURE_ONCE_REWRITE_CONV [thm]
                             THENC REPEATC Conv.EXISTS_SIMP_CONV) tm)
                else let
                        val counter = counterexample (boolSyntax.mk_neg ctm)
                        val counter = order_counter vars counter
                        val ctms = counter_terms counter
                                     [boolSyntax.list_mk_exists (vars, ctm)]
                        val cthm =
                           Drule.EQT_ELIM
                              (wordsLib.WORD_EVAL_CONV (Term.subst counter ctm))
                        val cthm' = build_exists (List.rev counter) ctms cthm
                     in
                        PURE_ONCE_REWRITE_RULE [GSYM thm] cthm'
                     end
        end
     end
end

val BIT_BLAST_CONV = BIT_BLAST_CONV false

val EBLAST_CONV  = BBLAST_CONV false
val EBLAST_PROVE = BBLAST_PROVE false
val EBLAST_RULE = Conv.CONV_RULE EBLAST_CONV
val EBLAST_TAC  = Tactic.CONV_TAC EBLAST_CONV

val BBLAST_CONV  = BBLAST_CONV true
val BBLAST_PROVE = BBLAST_PROVE true
val BBLAST_RULE = Conv.CONV_RULE BBLAST_CONV
val BBLAST_TAC  = Tactic.CONV_TAC BBLAST_CONV

val FULL_BBLAST_TAC =
   REPEAT (Tactical.PRED_ASSUM
              (Lib.can (HolKernel.find_term full_is_blastable)) MP_TAC)
   THEN BBLAST_TAC

fun BBLAST_PROVE_TAC (asl, w) = ACCEPT_TAC (BBLAST_PROVE w) (asl, w)

(* ------------------------------------------------------------------------ *)

end
