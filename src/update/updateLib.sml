structure updateLib :> updateLib =
struct

open HolKernel Parse boolLib bossLib
open wordsLib updateSyntax;

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars updateTheory.update_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "updateLib"

(* -----------------------------------------------------------------------
   COND_CONV
   Simpler version of Conv.COND_CONV (doesn't do alpha-conversion)
   ----------------------------------------------------------------------- *)

local
   val thm = Drule.SPEC_ALL boolTheory.COND_CLAUSES
   val cond_cnv1 = Conv.REWR_CONV (Thm.CONJUNCT1 thm)
   val cond_cnv2 = Conv.REWR_CONV (Thm.CONJUNCT2 thm)
   val cond_cnv3 = Conv.REWR_CONV boolTheory.COND_ID
in
   val COND_CONV = cond_cnv1 ORELSEC cond_cnv2 ORELSEC cond_cnv3
end

(* -----------------------------------------------------------------------
   NOT_CONV
   Simpler version of Boolconv.NOT_CONV (doesn't do double negation)
   ----------------------------------------------------------------------- *)

local
   val (_, thm1, thm2) =
      Lib.triple_of_list (Drule.CONJUNCTS boolTheory.NOT_CLAUSES)
in
   fun NOT_CONV tm =
      let
         val b = Lib.with_exn boolSyntax.dest_neg tm (ERR "NOT_CONV" "")
      in
         if b = boolSyntax.T
            then thm1
         else if b = boolSyntax.F
            then thm2
         else raise ERR "NOT_CONV" ""
      end
end

(* ------------------------------------------------------------------------
   UPDATE_APPLY_CONV cnv

   Evaluate terms of the from ``((a =+ b) f) c`` using "cnv" to decide
   whether or not ``a = c``.

   Example:

     UPDATE_APPLY_CONV numLib.REDUCE_CONV ``(1 =+ "a") ((2 =+ "b") f) 2``
     |- (1 =+ "a") ((2 =+ "b") f) 2 = "b"
  ------------------------------------------------------------------------- *)

local
   val cnv1 = Conv.REWR_CONV (Thm.CONJUNCT1 combinTheory.UPDATE_APPLY)
   val cnv2 = Conv.REWR_CONV combinTheory.APPLY_UPDATE_THM
in
   fun UPDATE_APPLY_CONV eqconv =
      let
         fun eqconv' tm =
            eqconv tm
            handle Conv.UNCHANGED => (Conv.SYM_CONV THENC eqconv) tm
         val cnv3 =
            cnv2
            THENC Conv.RATOR_CONV (Conv.RATOR_CONV (Conv.RAND_CONV eqconv'))
            THENC COND_CONV
         fun APPLY_CONV tm =
            let
               val (u, v) = Term.dest_comb tm
               val ((a, _), _) =
                  Lib.with_exn combinSyntax.dest_update_comb u Conv.UNCHANGED
            in
               if a = v
                  then cnv1 tm
               else (cnv3 THENC Conv.TRY_CONV APPLY_CONV) tm
            end
      in
         APPLY_CONV
      end
end

(* ------------------------------------------------------------------------
   LIST_UPDATE_INTRO_CONV

   Convert repeated applications of =+ into an application of LIST_UPDATE.

   Examples:

     LIST_UPDATE_INTRO_CONV ``(1 =+ "a") ((2 =+ "b") f)``
     |- (1 =+ "a") ((2 =+ "b") f) = LIST_UPDATE [(1,"a"); (2,"b")] f

     LIST_UPDATE_INTRO_CONV ``(1 =+ "a") o (2 =+ "b")``
     |- |- (1 =+ "a") o (2 =+ "b") = LIST_UPDATE [(1,"a"); (2,"b")]
   ------------------------------------------------------------------------ *)

val LIST_UPDATE_INTRO_CONV =
   PURE_REWRITE_CONV
      [updateTheory.LIST_UPDATE_THMS, listTheory.APPEND, listTheory.SNOC]

(* ------------------------------------------------------------------------
   LIST_UPDATE_ELIM_CONV

   Convert applications of LIST_UPDATE into repeated applications of =+.

   Examples:

     LIST_UPDATE_ELIM_CONV ``LIST_UPDATE [(1,"a"); (2,"b")] f``
     |- LIST_UPDATE [(1,"a"); (2,"b")] f = (1 =+ "a") ((2 =+ "b") f)

     LIST_UPDATE_ELIM_CONV ``LIST_UPDATE [(1,"a"); (2,"b")]``
     |- LIST_UPDATE [(1,"a"); (2,"b")] = (1 =+ "a") o (2 =+ "b")
   ------------------------------------------------------------------------ *)

local
   val (thm1, thm2) = Drule.CONJ_PAIR updateTheory.LIST_UPDATE_def
   val thm3 =
      PURE_REWRITE_RULE [pairTheory.FST, pairTheory.SND] (Q.SPEC `(a, b)` thm2)
   val thm4 = Thm.CONJUNCT2 (Drule.SPEC_ALL combinTheory.I_o_ID)
   val cnv1 = Conv.REWR_CONV thm3
   val cnv2 = Conv.REWR_CONV thm1
   val cnv3 = Conv.REWR_CONV thm2
   val cnv4 = Conv.ONCE_DEPTH_CONV (Conv.REWR_CONV thm4)
   val cnv5 = Conv.TOP_DEPTH_CONV (Conv.REWR_CONV combinTheory.o_THM)
   fun expand_conv0 tm =
      ((cnv1 THENC (Conv.RAND_CONV expand_conv0))
       ORELSEC cnv2
       ORELSEC (cnv3 THENC (Conv.RAND_CONV expand_conv0))) tm
   val expand_conv = expand_conv0 THENC cnv4
in
   fun LIST_UPDATE_ELIM_CONV tm =
      let
         val (f, x) = Term.dest_comb tm
         val is_upd = Term.same_const updateSyntax.list_update_tm f
         val _ = is_upd orelse updateSyntax.is_list_update f orelse
                 raise ERR "LIST_UPDATE_ELIM_CONV" ""
      in
         if is_upd
            then expand_conv tm
         else (Conv.RATOR_CONV expand_conv THENC cnv5) tm
      end
end

(* -----------------------------------------------------------------------
   Some syntax functions
   ----------------------------------------------------------------------- *)

local
   val is_ground = List.null o Term.free_vars
in
   fun is_ground_update tm =
      case Lib.total combinSyntax.dest_update tm of
         SOME (l, _) => is_ground l
       | NONE => false
   fun is_ground_list_update tm =
     case Lib.total updateSyntax.strip_list_update tm of
        SOME l => Lib.all (is_ground o fst) l
      | NONE => false
end

local
   fun is_ground_upd tm = is_ground_update tm orelse is_ground_list_update tm
in
   fun is_o_expr tm =
      is_ground_upd tm orelse
      case Lib.total combinSyntax.dest_o tm of
         SOME (l, r) =>
           is_ground_upd l andalso is_o_expr r orelse
           is_o_expr l andalso is_ground_upd r
       | NONE => false
   fun is_base tm =
      case Lib.total Term.dest_comb tm of
         SOME (l, _) => not (is_ground_upd l)
       | NONE => true
end

fun is_c_expr tm =
   case Lib.total Term.dest_comb tm of
      SOME (l, r) => is_o_expr l andalso (is_base r orelse is_c_expr r)
    | NONE => false

fun is_update_expr tm = is_o_expr tm orelse is_c_expr tm

(* -----------------------------------------------------------------------
   UNCHANGED_CONV cnv

   Raise Conv.UNCHANGED if conversion "cnv" produces result |- t = t' where
   t and t' are alpha-equivalent, or if an exception is raised.
   ----------------------------------------------------------------------- *)

fun UNCHANGED_CONV (conv: conv) tm =
   let
      val th = Lib.with_exn conv tm Conv.UNCHANGED
      val (l, r) = boolSyntax.dest_eq (Thm.concl th)
   in
      if Term.aconv l r then raise Conv.UNCHANGED else th
   end

(* -----------------------------------------------------------------------
   FILTER_CONV cnv

   Evaluation for ``FILTER P l``. Faster than version in listLib.
   ----------------------------------------------------------------------- *)

local
   val cnv1 = Conv.REWR_CONV (Thm.CONJUNCT1 listTheory.FILTER)
   val cnv2 = Conv.REWR_CONV (Thm.CONJUNCT2 listTheory.FILTER)
in
   fun FILTER_CONV cnv =
      let
         fun filter_conv tm =
            ((cnv2
              THENC Conv.RATOR_CONV (Conv.RATOR_CONV (Conv.RAND_CONV cnv))
              THENC COND_CONV
              THENC (fn tm => if listSyntax.is_cons tm
                                 then Conv.RAND_CONV filter_conv tm
                              else filter_conv tm)) ORELSEC cnv1) tm
      in
         filter_conv
      end
end

(* -----------------------------------------------------------------------
   OVERRIDE_CONV cnv

   Evaluation for ``OVERRIDE l``.
   ----------------------------------------------------------------------- *)

local
   val cnv1 = Conv.REWR_CONV (Thm.CONJUNCT1 updateTheory.OVERRIDE_def)
   val cnv2 = Conv.REWR_CONV (Thm.CONJUNCT2 updateTheory.OVERRIDE_def)
   val cnv3 = Conv.REWR_CONV pairTheory.FST
in
   fun OVERRIDE_CONV cnv =
      let
         val cnv' = PairRules.PBETA_CONV
                    THENC Conv.RAND_CONV (Conv.RHS_CONV cnv3 THENC cnv)
                    THENC NOT_CONV
         val fcnv = FILTER_CONV cnv'
         fun override_conv tm =
            ((cnv2
              THENC Conv.RAND_CONV
                      (Conv.RAND_CONV
                         (Conv.RATOR_CONV
                            (Conv.RAND_CONV
                               (Conv.ABS_CONV
                                  (Conv.RAND_CONV (Conv.LHS_CONV cnv3))))
                          THENC fcnv)
                       THENC override_conv)) ORELSEC cnv1) tm
      in
         override_conv
      end
end

(* -----------------------------------------------------------------------
   OVERRIDE_UPDATES_CONV ty cnv

   Eliminate redundant (overwritten) updates for functions of type "ty" using
   conversion "cnv" to evaluate equality.

   Examples:

      OVERRIDE_UPDATES_CONV ``:word32 -> string`` wordsLib.word_EQ_CONV
        ``(1w:word32 =+ "a") ((3w =+ "b") ((2w =+ "c") ((3w =+ "c") f)))``
      |- (1w =+ "a") ((3w =+ "b") ((2w =+ "c") ((3w =+ "c") f))) =
         (1w =+ "a") ((3w =+ "b") ((2w =+ "c") f))

      OVERRIDE_UPDATES_CONV ``:word32 -> string`` wordsLib.word_EQ_CONV
        ``(1w:word32 =+ "a") o (3w =+ "b") o (2w =+ "c") o (3w =+ "c")``
      |- (1w =+ "a") o (3w =+ "b") o (2w =+ "c") o (3w =+ "c") =
         (1w =+ "a") o (3w =+ "b") o (2w =+ "c")
   ----------------------------------------------------------------------- *)

local
   val cnv1 = Conv.REWR_CONV updateTheory.LIST_UPDATE_OVERRIDE
in
   fun OVERRIDE_UPDATES_CONV ty cnv =
      let
         val ocnv = cnv1 THENC Conv.RAND_CONV (OVERRIDE_CONV cnv)
         val ok1 = Lib.can (Type.match_type ty)
         val ok2 = Lib.can (Type.match_type (ty --> ty))
      in
         fn tm =>
            let
               val tm_ty = Term.type_of tm
               val c_form = ok1 tm_ty andalso is_c_expr tm
               val _ = c_form orelse ok2 tm_ty andalso is_o_expr tm
                       orelse raise ERR "OVERRIDE_UPDATES_CONV"
                                        "Not expected type/form"
            in
               UNCHANGED_CONV
                 (LIST_UPDATE_INTRO_CONV
                  THENC (if c_form then Conv.RATOR_CONV else Lib.I) ocnv
                  THENC LIST_UPDATE_ELIM_CONV) tm
            end
      end
end

(* -----------------------------------------------------------------------
   SORT_UPDATES_CONV ord cmp cnv

   Sort repeated applications of =+ using an ordering function "ord".
   The ordering can be based on the function's range as well as its domain,
   i.e. (2 =+ 1) can be "less-than" (1 =+ 2). The ordering is evaluated
   using the compset "cmp" and conversion "cnv" is used to test equality.

   Examples:

      SORT_UPDATES_CONV ``\(a, x:'a) (b, y:'a). a <+ b``
        (wordsLib.words_compset()) wordsLib.word_EQ_CONV
        ``(1w:word32 =+ "a") ((3w =+ "b") ((2w =+ "c") ((3w =+ "c") f)))``
      |- (1w =+ "a") ((3w =+ "b") ((2w =+ "c") ((3w =+ "c") f))) =
         (1w =+ "a") ((2w =+ "c") ((3w =+ "b") f))

      SORT_UPDATES_CONV ``\(a, x:'a) (b, y:'a). a <+ b``
        (wordsLib.words_compset()) wordsLib.word_EQ_CONV
        ``(1w:word32 =+ "a") o (3w =+ "b") o (2w =+ "c") o (3w =+ "c")``
      |- (1w =+ "a") o (3w =+ "b") o (2w =+ "c") o (3w =+ "c") =
         (1w =+ "a") o (2w =+ "c") o (3w =+ "b")
   ----------------------------------------------------------------------- *)

fun SORT_UPDATES_CONV ord cmp cnv =
   let
      val () = computeLib.add_thms
                [pairTheory.CURRY_DEF, pairTheory.UNCURRY_DEF,
                 pairTheory.PAIR_EQ, pairTheory.FST, pairTheory.SND,
                 listTheory.APPEND, combinTheory.o_THM, sortingTheory.PART_DEF,
                 REWRITE_RULE [sortingTheory.PARTITION_DEF]
                   sortingTheory.QSORT_DEF] cmp
      val SORT_CONV = computeLib.CBV_CONV cmp
      val thm = Drule.ISPEC ord updateTheory.LIST_UPDATE_SORT_OVERRIDE
      val cnv1 = Conv.REWR_CONV thm
      val cnv2 = OVERRIDE_CONV cnv
      val cnv3 = cnv1 THENC Conv.RAND_CONV (Conv.RAND_CONV cnv2 THENC SORT_CONV)
      val (ty1, ty2) =
         ord |> Term.type_of |> Type.dom_rng |> fst |> pairSyntax.dest_prod
      val ty3 = ty1 --> ty2
   in
      fn tm =>
        let
           val ty = Term.type_of tm
           val c_form = Lib.can (Type.match_type ty3) ty andalso is_c_expr tm
           val _ =
              c_form orelse
              Lib.can (Type.match_type (ty3 --> ty3)) ty andalso is_o_expr tm
              orelse raise ERR "SORT_UPDATES_CONV" "Not expected type/form"
        in
           UNCHANGED_CONV
             (LIST_UPDATE_INTRO_CONV
              THENC (if c_form then Conv.RATOR_CONV else Lib.I) cnv3
              THENC LIST_UPDATE_ELIM_CONV) tm
        end
   end

(* -----------------------------------------------------------------------
   SORT_UPDATES_MAPTO_CONV f ord cnv

   An alternative interface to SORT_UPDATES_CONV. The ordering is
   ``\x y. ord (f x) (f y)``.

   Examples:

      SORT_UPDATES_MAPTO_CONV ``FST : 'a word # 'b -> 'a word``
         (wordsLib.words_compset()) wordsLib.WORD_EVAL_CONV
         ``(1w:word32 =+ "a") ((3w =+ "b") ((2w =+ "c") ((3w =+ "c") f)))``
      |- (1w =+ "a") ((3w =+ "b") ((2w =+ "c") ((3w =+ "c") f))) =
         (1w =+ "a") ((2w =+ "c") ((3w =+ "b") f))

      SORT_UPDATES_MAPTO_CONV ``FST : 'a word # 'b -> 'a word``
         wordsSyntax.word_lo_tm wordsLib.WORD_EVAL_CONV
         ``(1w:word32 =+ "a") o (3w =+ "b") o (2w =+ "c") o (3w =+ "c")``
      |- (1w =+ "a") o (3w =+ "b") o (2w =+ "c") o (3w =+ "c") =
         (1w =+ "a") o (2w =+ "c") o (3w =+ "b")
   ----------------------------------------------------------------------- *)

fun SORT_UPDATES_MAPTO_CONV f ord =
   let
      val (uty, oty) = Type.dom_rng (Term.type_of f)
      val _ = Type.match_type (Term.type_of ord) (oty --> oty --> Type.bool)
      val x = Term.mk_var ("x", uty)
      val y = Term.mk_var ("y", uty)
      val f_x = Term.mk_comb (f, x)
      val f_y = Term.mk_comb (f, y)
      val f_ord = Term.list_mk_abs
                     ([x,y], boolSyntax.list_mk_icomb (ord, [f_x, f_y]))
   in
      SORT_UPDATES_CONV f_ord
   end

(* -----------------------------------------------------------------------
   SORT_NUM_UPDATES_CONV

   Sort sequences of updates for maps of type ``:num -> 'a``.

   Example:

      SORT_NUM_UPDATES_CONV
         ``(1 =+ "a") ((3 =+ "b") ((2 =+ "c") ((3 =+ "c") f)))``
      |- (1 =+ "a") ((3 =+ "b") ((2 =+ "c") ((3 =+ "c") f))) =
         (1 =+ "a") ((2 =+ "c") ((3 =+ "b") f))
   ----------------------------------------------------------------------- *)

val SORT_NUM_UPDATES_CONV =
   let
      val fty = pairSyntax.mk_prod (numSyntax.num, Type.alpha) --> numSyntax.num
      val f = Term.mk_thy_const {Ty = fty, Thy = "pair", Name = "FST"}
   in
      SORT_UPDATES_MAPTO_CONV
         f numSyntax.less_tm (reduceLib.num_compset()) numLib.REDUCE_CONV
   end

(* -----------------------------------------------------------------------
   SORT_WORD_UPDATES_CONV ty

   Sort sequences of updates for maps of type ``:ty word -> 'a``.

   Example:

      SORT_WORD_UPDATES_CONV ``:32``
         ``(1w:word32 =+ "a") ((3w =+ "b") ((2w =+ "c") ((3w =+ "c") f)))``
      |- (1 =+ "a") ((3 =+ "b") ((2 =+ "c") ((3 =+ "c") f))) =
         (1 =+ "a") ((2 =+ "c") ((3 =+ "b") f))
   ----------------------------------------------------------------------- *)

fun SORT_WORD_UPDATES_CONV ty =
   let
      val dimword =
         Lib.with_exn wordsLib.SIZES_CONV (wordsSyntax.mk_dimword ty)
                      (ERR "SORT_WORD_UPDATES_CONV"
                           "Cannot compute size or word type")
      val word_lo =
         PURE_REWRITE_RULE [dimword]
            (Thm.INST_TYPE [Type.alpha |-> ty] wordsTheory.word_lo_n2w)
      val cmp = reduceLib.num_compset()
      val () = computeLib.add_thms
                 [numLib.SUC_RULE numeral_bitTheory.MOD_2EXP_EQ, word_lo,
                  numLib.SUC_RULE numeral_bitTheory.MOD_2EXP_MAX] cmp
      val wty = wordsSyntax.mk_word_type ty
      val fty = pairSyntax.mk_prod (wty, Type.alpha) --> wty
      val f = Term.mk_thy_const {Ty = fty, Thy = "pair", Name = "FST"}
   in
      SORT_UPDATES_MAPTO_CONV f wordsSyntax.word_lo_tm cmp wordsLib.word_EQ_CONV
   end

(* -----------------------------------------------------------------------
   SORT_ENUM_UPDATES_CONV ty

   Sort sequences of updates for maps of type ``:ty -> 'a`` where ``:ty``
   if an enumerated type.

   Example:

      val () = Hol_datatype `enum = One | Two | Three`
      SORT_ENUM_UPDATES_CONV ``:enum``
         ``(One =+ "a") ((Three =+ "b") ((Two =+ "c") ((Three =+ "c") f)))``
      |- (One =+ "a") ((Three =+ "b") ((Two =+ "c") ((Three =+ "c") f))) =
         (One =+ "a") ((Two =+ "c") ((Three =+ "b") f))
   ----------------------------------------------------------------------- *)

fun SORT_ENUM_UPDATES_CONV ty =
   let
      val {Thy, Args, Tyop} = Type.dest_thy_type ty
      val _ = List.null Args orelse
              raise ERR "SORT_ENUM_UPDATES_CONV" "Not an enumerated type"
      val ty2num = Tyop ^ "2num"
      val ty2num_tm = Term.prim_mk_const {Thy = Thy, Name = ty2num}
      val ty2num_11 = DB.fetch Thy (ty2num ^ "_11")
      val ty2num_thm = DB.fetch Thy (ty2num ^ "_thm")
      val cmp = reduceLib.num_compset()
      val () = computeLib.add_thms [GSYM ty2num_11, ty2num_thm] cmp
      val cnv = computeLib.CBV_CONV cmp
   in
      SORT_UPDATES_MAPTO_CONV
        ``(^ty2num_tm o FST) : ^(ty_antiq ty) # 'a -> num`` numSyntax.less_tm
        cmp cnv
   end

end
