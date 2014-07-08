structure bitstringLib :> bitstringLib =
struct

open HolKernel Parse boolLib bossLib;
open lcsymtacs listLib wordsLib bitstringSyntax;

structure Parse = struct
  open Parse
  val (Type, Term) = parse_from_grammars bitstringTheory.bitstring_grammars
end
open Parse

val _ = Lib.with_flag (Feedback.emit_MESG, false) bossLib.srw_ss ()

val ERR = Feedback.mk_HOL_ERR "bitstringLib"

(* ------------------------------------------------------------------------- *)

fun Cases_on_v2w t =
   Q.ISPEC_THEN t Tactic.FULL_STRUCT_CASES_TAC
      bitstringTheory.ranged_bitstring_nchotomy

(* ------------------------------------------------------------------------- *)

fun qm l = Feedback.trace ("metis", 0) (metisLib.METIS_TAC l)

fun new_def s x = Definition.new_definition (s ^ "_def", boolSyntax.mk_eq x)

val list_length = List.length o fst o listSyntax.dest_list

val get_const =
   fst o Term.dest_comb o boolSyntax.lhs o Thm.concl o Drule.SPEC_ALL

fun CHANGE_CBV_CONV cmp = Conv.CHANGED_CONV (computeLib.CBV_CONV cmp)

local
   fun bit n =
      if Arbnum.mod2 n = Arbnum.one then boolSyntax.T else boolSyntax.F
   fun btfy (a, n) =
      if n = Arbnum.zero then a else btfy (bit n :: a, Arbnum.div2 n)
in
   fun bitify_num w n =
      let
         val l = btfy ([], n)
         val s = w - List.length l
         val () = ignore (0 <= s orelse raise ERR "bitify_num" "too big")
      in
         List.tabulate (s, K boolSyntax.F) @ l
      end
end

fun check P err thm =
   (P (boolSyntax.rhs (Thm.concl thm)) orelse raise err; thm)

(* ------------------------------------------------------------------------- *)

(* Evaluate ``fixwidth n [...]`` *)

local
   open bitstringTheory
   val thm = REWRITE_RULE [zero_extend_def] fixwidth_def
   val cmp = listSimps.list_compset ()
   val () = computeLib.add_thms [combinTheory.K_THM] cmp
   val () = computeLib.add_conv
             (``fcp$dimindex:'a itself -> num``, 1, wordsLib.SIZES_CONV) cmp
   val cnv = Conv.REWR_CONV thm THENC CHANGE_CBV_CONV cmp
in
   fun FIX_CONV tm = Lib.with_exn cnv tm (ERR "FIX_CONV" "")
end

(* ------------------------------------------------------------------------- *)

(* Canonicalize ``v2w [...]``.

   For example:

   FIX_v2w_CONV ``v2w [T;T] : word4``
   val it = |- v2w [T; T] = v2w [F; F; T; T]: thm
*)

local
   val cnv = Conv.REWR_CONV (GSYM bitstringTheory.v2w_fixwidth)
             THENC Conv.RAND_CONV FIX_CONV
in
   fun FIX_v2w_CONV tm =
     let
        val (l, n) = bitstringSyntax.dest_v2w tm
        val sz = Arbnum.toInt (fcpSyntax.dest_numeric_type n)
     in
        if sz = list_length l
           then raise Conv.UNCHANGED
        else Lib.with_exn cnv tm (ERR "FIX_v2w_CONV" "")
     end
end

(* ------------------------------------------------------------------------- *)

(* Evaluate ``v2n [...]`` *)

local
   open lcsymtacs arithmeticTheory numeralTheory

   val l2n_2_compute = Q.prove(
      `(l2n 2 [] = 0) /\
       (!l. l2n 2 (0::l) = 2 * l2n 2 l) /\
       (!l. l2n 2 (1::l) = 2 * l2n 2 l + 1)`,
      simp [numposrepTheory.l2n_def])

   val l2n_2_numeric = Q.prove(
      `(l2n 2 [] = ZERO) /\
       (!l. l2n 2 (0::l) = numeral$iDUB (l2n 2 l)) /\
       (!l. l2n 2 (1::l) = BIT1 (l2n 2 l))`,
      qm
       [l2n_2_compute, ALT_ZERO, ONE, ADD_ASSOC, BIT1, TIMES2, MULT_COMM, iDUB])

   val num_from_bin_list_compute = Q.prove(
     `(num_from_bin_list [] = 0) /\
      (!l. num_from_bin_list (0::l) = NUMERAL (l2n 2 (0::l))) /\
      (!l. num_from_bin_list (1::l) = NUMERAL (l2n 2 (1::l)))`,
      simp [numposrepTheory.num_from_bin_list_def] >> qm [NUMERAL_DEF])

   val cnv =
      Conv.REWR_CONV bitstringTheory.v2n_def
      THENC Conv.RAND_CONV (PURE_REWRITE_CONV [bitstringTheory.bitify_def])
      THENC PURE_ONCE_REWRITE_CONV [num_from_bin_list_compute]
      THENC Conv.TRY_CONV
              (Conv.RAND_CONV (PURE_REWRITE_CONV [l2n_2_numeric, iDUB_removal])
               THENC Conv.TRY_CONV (Conv.REWR_CONV NORM_0))
in
   fun v2n_CONV tm =
      check numLib.is_numeral (ERR "v2n_CONV" "not ground")
      (Lib.with_exn cnv tm (ERR "v2n_CONV" ""))
end

(* ------------------------------------------------------------------------- *)

(* Convert ``v2w [...]`` to ``n2w n`` *)

local
   val v2w_n2w_thm = Q.prove(
      `!l n. (v2n l = n) ==> (v2w l = n2w n : 'a word)`,
      qm [bitstringTheory.ops_to_n2w])
in
   fun v2w_n2w_CONV tm =
      let
         val (l, ty) = bitstringSyntax.dest_v2w tm
         val thm = v2n_CONV (bitstringSyntax.mk_v2n l)
      in
         Drule.MATCH_MP (Thm.INST_TYPE [Type.alpha |-> ty] v2w_n2w_thm) thm
      end
      handle HOL_ERR {message = m, ...} => raise ERR "v2w_n2w_CONV" m
end

(* ------------------------------------------------------------------------- *)

(* Convert ``n2w n`` to ``v2w [...]`` *)

fun n2w_v2w_CONV tm =
   let
      val (n, ty) = wordsSyntax.dest_n2w tm
      val b =
         bitify_num (fcpSyntax.dest_int_numeric_type ty) (numLib.dest_numeral n)
      val l = listSyntax.mk_list (b, Type.bool)
   in
      Thm.SYM (v2w_n2w_CONV (bitstringSyntax.mk_v2w (l, ty)))
   end
   handle HOL_ERR {message = m, ...} => raise ERR "n2w_v2w_CONV" m

(* ------------------------------------------------------------------------- *)

(* Bitify expressions of the form:
      ``v2w [...] = n2w n``
      ``n2w n = v2w [...]``
      ``v2w [...] = v2w [...]``
   for ground n.

   For example:

   v2w_eq_CONV ``v2w [T;b] = 3w : word4``
   val it = |- (v2w [T; b] = 3w) <=> b: thm

   v2w_eq_CONV ``v2w [T;b] = v2w [c;d] : word4``
   val it = (v2w [T; b] = v2w [c; d]) <=> c /\ (b <=> d): thm
*)

fun v2w_eq_CONV tm =
   let
      val (l, r) = boolSyntax.dest_eq tm
      val c = Conv.RHS_CONV (Conv.REWR_CONV (n2w_v2w_CONV r))
              handle HOL_ERR _ =>
              Conv.LHS_CONV (Conv.REWR_CONV (n2w_v2w_CONV l))
              handle HOL_ERR _ =>
              Conv.ALL_CONV
   in
      (c THENC Conv.REWR_CONV bitstringTheory.v2w_11
         THENC Conv.BINOP_CONV
                  (Conv.RATOR_CONV (Conv.RAND_CONV wordsLib.SIZES_CONV)
                   THENC FIX_CONV)
         THENC listLib.LIST_EQ_SIMP_CONV) tm
   end
   handle HOL_ERR {message = m, ...} => raise ERR "v2w_eq_n2w_CONV" m

(* ------------------------------------------------------------------------- *)

(* Equality check for any ground term combinations of ``v2w [..]`` and
   ``n2w n``. Should be faster than using the above.
*)

local
   val cmp = listSimps.list_compset ()
   val () = computeLib.add_thms
              [bitstringTheory.v2w_fixwidth,
               bitstringTheory.fixwidth,
               numLib.SUC_RULE bitstringTheory.extend_def] cmp
   val () = computeLib.add_conv
              (``fcp$dimindex:'a itself -> num``, 1, wordsLib.SIZES_CONV) cmp
   fun is_bool tm = tm = boolSyntax.T orelse tm = boolSyntax.F
   val cnv = Conv.REWR_CONV bitstringTheory.v2w_11 THENC CHANGE_CBV_CONV cmp
in
   fun word_eq_CONV tm =
      let
         val (l, r) = boolSyntax.dest_eq tm
      in
         if bitstringSyntax.is_v2w l
            then if bitstringSyntax.is_v2w r
                    then check is_bool (ERR "word_eq_CONV" "not ground")
                           (cnv tm)
                 else (Conv.LHS_CONV v2w_n2w_CONV
                       THENC wordsLib.word_EQ_CONV) tm
         else if bitstringSyntax.is_v2w r
            then (Conv.RHS_CONV v2w_n2w_CONV THENC wordsLib.word_EQ_CONV) tm
         else wordsLib.word_EQ_CONV tm
      end
      handle HOL_ERR {message = m, ...} => raise ERR "word_eq_CONV" m
end

(* ------------------------------------------------------------------------- *)

(* Simplify expressions of the form ``(h >< l) (v2w [...])``.

   For example:

   extract_v2w_CONV ``(3 >< 1) (v2w [a;b;c;d;e] : word5) : word3``
   |- (3 >< 1) (v2w [a; b; c; d; e]) = v2w [b; c; d]: thm
*)

local
   val extract_v2w_cor = Q.prove(
     `!h l v.
        (LENGTH v <= dimindex(:'a)) /\ (dimindex(:'b) = SUC h - l) /\
        dimindex(:'b) < dimindex(:'a) ==>
        ((h >< l) (v2w v : 'a word) : 'b word =
         v2w (fixwidth (dimindex(:'b)) (shiftr v l)))`,
     qm [bitstringTheory.extract_v2w, bitstringTheory.field_def])
   val shiftr_CONV =
     Conv.REWR_CONV bitstringTheory.shiftr_def
     THENC CHANGE_CBV_CONV (listSimps.list_compset())
in
   fun extract_v2w_CONV tm =
      let
         val (h, l, w, ty1) = wordsSyntax.dest_word_extract tm
         val (v, ty2) = bitstringSyntax.dest_v2w w
         val dim_a = fcpSyntax.mk_dimindex ty2
         val dim_a_thm = wordsLib.SIZES_CONV dim_a
         val dim_b = fcpSyntax.mk_dimindex ty1
         val dim_b_thm = wordsLib.SIZES_CONV dim_b
         val len_thm =
            numSyntax.mk_leq (listSyntax.mk_length v, dim_a)
              |> (Conv.FORK_CONV (listLib.LENGTH_CONV, Conv.REWR_CONV dim_a_thm)
                  THENC numLib.REDUCE_CONV)
              |> Drule.EQT_ELIM
         val width_thm =
            boolSyntax.mk_eq (dim_b, numSyntax.mk_minus (numSyntax.mk_suc h, l))
              |> (Conv.LHS_CONV (Conv.REWR_CONV dim_b_thm)
                  THENC numLib.REDUCE_CONV)
              |> Drule.EQT_ELIM
         val lt_thm =
            numSyntax.mk_less (dim_b, dim_a)
              |> (Conv.FORK_CONV (Conv.REWR_CONV dim_b_thm,
                                  Conv.REWR_CONV dim_a_thm)
                  THENC numLib.REDUCE_CONV)
              |> Drule.EQT_ELIM
         val thm = Drule.MATCH_MP extract_v2w_cor
                     (Drule.LIST_CONJ [len_thm, width_thm, lt_thm])
      in
         (Conv.REWR_CONV thm
          THENC Conv.RAND_CONV (Conv.RAND_CONV shiftr_CONV)
          THENC Conv.RAND_CONV FIX_CONV) tm
      end
      handle HOL_ERR {message = m, ...} => raise ERR "extract_v2w_CONV" m
end

(* ------------------------------------------------------------------------- *)

(* Simplify expressions of the form

   ``word_bit i (v2w [...])`` and ``v2w [...] ' i``.

   For example:

   word_bit_CONV ``word_bit 1 (v2w [a;b;c;d;e] : word5)``
   |- word_bit 1 (v2w [a; b; c; d; e]) <=> d: thm
*)

local
   open numeralTheory listTheory
   val word_bit_last_shiftr =
      REWRITE_RULE [bitstringTheory.shiftr_def]
         bitstringTheory.word_bit_last_shiftr
   val cmp = computeLib.bool_compset ()
   val () = computeLib.add_thms
              [numeral_distrib, numeral_suc, numeral_iisuc, numeral_sub,
               numeral_lt, iSUB_THM, iDUB_removal,
               LENGTH, TAKE_compute, NULL_DEF, LAST_compute] cmp
   val cnv = CHANGE_CBV_CONV cmp
in
   fun word_bit_CONV tm =
      let
         val ((i, t), c) =
            case Lib.total wordsSyntax.dest_word_bit tm of
               SOME x => (x, ALL_CONV)
             | NONE => (Lib.swap (fcpSyntax.dest_fcp_index tm),
                        wordsLib.WORD_BIT_INDEX_CONV false)
         val ty = wordsSyntax.dim_of t
         val lt_thm =
               numSyntax.mk_less (i, fcpSyntax.mk_dimindex ty)
                 |> (Conv.RAND_CONV wordsLib.SIZES_CONV
                     THENC numLib.REDUCE_CONV)
                 |> Drule.EQT_ELIM
         val thm = Drule.MATCH_MP word_bit_last_shiftr lt_thm
      in
         (c THENC Conv.REWR_CONV thm THENC cnv) tm
      end
      handle HOL_ERR {message = m, ...} => raise ERR "word_bit_CONV" m
end

(* ------------------------------------------------------------------------- *)

local
   fun mk_boolify i =
      let
         fun mk_n j =
            Term.mk_var ("n" ^ (if j + 1 = i then "" else Int.toString (i-1-j)),
                         numSyntax.num)
         val ns = List.tabulate (i, mk_n)
         val t = pairSyntax.list_mk_pair (List.map numSyntax.mk_odd ns)
         fun mk_p j = (List.nth (ns, j), List.nth (ns, j + 1))
         val ps = List.tabulate (i - 1, mk_p)
      in
        (List.last ns,
         List.foldl (fn ((a, b), t) =>
            boolSyntax.mk_let (Term.mk_abs (a, t), numSyntax.mk_div2 b))
            t ps)
      end

   fun BOOLIFY_v2w_CONV thm = RAND_CONV FIX_v2w_CONV THENC REWR_CONV thm

   fun add_boolify_v2w thm =
      let
         val c = thm |> Drule.SPEC_ALL |> Thm.concl
                     |> boolSyntax.lhs |> Term.dest_comb |> fst
      in
         computeLib.add_conv (c, 1, BOOLIFY_v2w_CONV thm)
      end

   val rw = SRW_TAC [boolSimps.LET_ss]

   fun Cases_on_v2w q =
      Q.ISPEC_THEN q STRUCT_CASES_TAC bitstringTheory.ranged_bitstring_nchotomy

   fun boolify_n2w_tac thm =
      Tactic.STRIP_TAC
      THEN Rewrite.PURE_REWRITE_TAC
             (thm :: [wordsTheory.word_bit_n2w, bitTheory.BIT_def,
                      bitTheory.BITS_def])
      THEN Tactic.CONV_TAC (Conv.LHS_CONV (Conv.DEPTH_CONV wordsLib.SIZES_CONV))
      THEN Tactic.CONV_TAC (Conv.RHS_CONV (Conv.DEPTH_CONV pairLib.let_CONV))
      THEN Rewrite.PURE_REWRITE_TAC [pairTheory.CLOSED_PAIR_EQ]
      THEN Tactical.REPEAT Tactic.CONJ_TAC
      THEN Rewrite.PURE_REWRITE_TAC
             [bitTheory.MOD_2EXP_def, bitTheory.ODD_MOD2_LEM,
              numeral_bitTheory.DIV_2EXP]
      THEN computeLib.EVAL_TAC

   fun boolify_v2w_tac thm =
      Tactical.REPEAT Tactic.STRIP_TAC
      THEN Rewrite.PURE_REWRITE_TAC [thm, bitstringTheory.bit_v2w]
      THEN computeLib.EVAL_TAC

   fun boolify_bitify_tac x l =
      Tactic.STRIP_TAC THEN pairLib.PairCases_on [HOLPP.ANTIQUOTE x]
      THEN rw l

   fun bitify_boolify_tac l =
      SRW_TAC [fcpLib.FCP_ss, boolSimps.LET_ss] (l @
        [wordsTheory.word_bit, bitstringTheory.bit_v2w,
         bitstringTheory.testbit])
      THEN Tactical.POP_ASSUM (fn th => Tactic.STRIP_ASSUME_TAC
              (Conv.CONV_RULE wordsLib.LESS_CONV th))
      THEN Tactical.POP_ASSUM Tactic.SUBST1_TAC
      THEN computeLib.EVAL_TAC
in
   fun define_bit_bool_maps (bitify_lhs, boolify_lhs) i =
   let
      val ty = wordsSyntax.mk_int_word_type i
      val tyi = wordsSyntax.dest_word_type ty
      val w = Term.mk_var ("w", ty)
      fun mk_bit j = wordsSyntax.mk_word_bit (numSyntax.term_of_int (i-1-j), w)
      val boolify_rhs = pairSyntax.list_mk_pair (List.tabulate (i, mk_bit))
      val f = Term.mk_var (boolify_lhs, Type.--> (ty, Term.type_of boolify_rhs))
      val boolify_def = new_def boolify_lhs (Term.mk_comb (f, w), boolify_rhs)
      val boolify_c = get_const boolify_def
      fun mk_b j = Term.mk_var ("b" ^ Int.toString (i-1-j), Type.bool)
      val bs = List.tabulate (i, mk_b)
      val btuple = pairSyntax.list_mk_pair bs
      val blist = listSyntax.mk_list (bs, Type.bool)
      val bitify_rhs = bitstringSyntax.mk_v2w (blist, tyi)
      val f = Term.mk_var (bitify_lhs,
                Type.--> (Term.type_of btuple, Term.type_of bitify_rhs))
      val bitify_def = new_def bitify_lhs (Term.mk_comb (f, btuple), bitify_rhs)
      val bitify_c = get_const bitify_def
      val (n, boolify_n2w_rhs) = mk_boolify i
      val boolify_n2w_lhs =
         Term.mk_comb (boolify_c, wordsSyntax.mk_n2w (n, tyi))
      val boolify_n2w_goal =
         boolSyntax.mk_forall (n,
           boolSyntax.mk_eq (boolify_n2w_lhs, boolify_n2w_rhs))
      val boolify_n2w_thm =
         Tactical.store_thm(boolify_lhs ^ "_n2w", boolify_n2w_goal,
                            boolify_n2w_tac boolify_def)
      val boolify_v2w_goal =
         boolSyntax.list_mk_forall (bs,
           boolSyntax.mk_eq (Term.mk_comb (boolify_c, bitify_rhs), btuple))
      val boolify_v2w_thm =
         Tactical.store_thm(boolify_lhs ^ "_v2w", boolify_v2w_goal,
                            boolify_v2w_tac boolify_def)
      val x = Term.mk_var ("x", Term.type_of btuple)
      val boolify_bitify_goal =
         boolSyntax.mk_forall (x,
           boolSyntax.mk_eq
             (Term.mk_comb (boolify_c, Term.mk_comb (bitify_c, x)), x))
      val boolify_bitify_thm =
         Tactical.store_thm(boolify_lhs ^ bitify_lhs, boolify_bitify_goal,
                            boolify_bitify_tac x [bitify_def, boolify_v2w_thm])
      val bitify_boolify_goal =
         boolSyntax.mk_forall (w,
           boolSyntax.mk_eq
             (Term.mk_comb (bitify_c, Term.mk_comb (boolify_c, w)), w))
      val bitify_boolify_thm =
         Tactical.store_thm(bitify_lhs ^ boolify_lhs, bitify_boolify_goal,
                            bitify_boolify_tac [bitify_def, boolify_def])
      val () = computeLib.add_funs [boolify_n2w_thm, bitify_def]
      val () = computeLib.add_convs
                  [(boolify_c, 1, BOOLIFY_v2w_CONV boolify_v2w_thm)]
   in
      (bitify_def, boolify_def)
   end
end

type bitify_boolify =
  { bitify_def : thm,
    bitify_tm : term,
    mk_bitify : term -> term,
    dest_bitify : term -> term,
    is_bitify : term -> bool,
    boolify_def : thm,
    boolify_tm : term,
    mk_boolify : term -> term,
    dest_boolify : term -> term,
    is_boolify : term -> bool }

local
   fun findDef s =
      case s |> DB.find
             |> List.partition (fn ((_, s2), (_, DB.Def)) => s2 = s
                                 | _ => false)
             |> fst of
        [((thy, _), (thm, _))] => SOME (thy, thm)
      | _ => NONE
   fun syntax_monop thy =
      HolKernel.syntax_fns thy 1 HolKernel.dest_monop HolKernel.mk_monop
in
   fun bitify_boolify i =
      let
         val n = Int.toString i
         val bitify = "bitify" ^ n
         val boolify = "boolify" ^ n
         fun f s = findDef (s ^ "_def")
         val ((thy1, bitify_def), (thy2, boolify_def)) =
            case (f bitify, f boolify)  of
              (SOME x, SOME y) => (x, y)
            | _ =>
              let
                 val () = Feedback.HOL_MESG
                             ("Defining " ^ n ^ "-bit bitify/boolify maps")
                 val thy = Theory.current_theory ()
                 val (thm1, thm2) = define_bit_bool_maps (bitify, boolify) i
              in
                 ((thy, thm1), (thy, thm2))
              end
         val (bitify_tm, mk_bitify, dest_bitify, is_bitify) =
            syntax_monop thy1 bitify
         val (boolify_tm, mk_boolify, dest_boolify, is_boolify) =
            syntax_monop thy2 boolify
      in
         { bitify_def = bitify_def,
           bitify_tm = bitify_tm,
           mk_bitify = mk_bitify,
           dest_bitify = dest_bitify,
           is_bitify = is_bitify,
           boolify_def = boolify_def,
           boolify_tm = boolify_tm,
           mk_boolify = mk_boolify,
           dest_boolify = dest_boolify,
           is_boolify = is_boolify } : bitify_boolify
      end
end

(* ------------------------------------------------------------------------- *)

val add_bitstring_compset =
   let
      open bitstringTheory
   in
      computeLib.add_thms
       [
        numLib.SUC_RULE extend_def, boolify_def, bitify_def, n2v_def, v2n_def,
        s2v_def, v2s_def, shiftl_def, shiftr_def, field_def, rotate_def,
        w2v_def, rev_count_list_def, modify_def, field_insert_def, add_def,
        bitwise_def, bnot_def, bor_def, band_def, bxor_def, bnor_def,
        bxnor_def, bnand_def, replicate_def, testbit, ops_to_v2w, ops_to_n2w,
        fixwidth, extend, v2w_11, bit_v2w, w2n_v2w, w2v_v2w, w2w_v2w,
        sw2sw_v2w, word_index_v2w, word_lsl_v2w, word_lsr_v2w, word_asr_v2w,
        word_ror_v2w, word_1comp_v2w, word_and_v2w, word_or_v2w, word_xor_v2w,
        word_nand_v2w, word_nor_v2w, word_xnor_v2w, word_lsb_v2w, word_msb_v2w,
        word_reverse_v2w, word_modify_v2w, word_bits_v2w, word_extract_v2w,
        word_slice_v2w, word_join_v2w, word_concat_v2w_rwt, word_reduce_v2w,
        reduce_and_v2w, reduce_or_v2w
       ]
   end

(* ------------------------------------------------------------------------- *)

end
