structure listSimps :> listSimps =
struct

open simpLib listTheory;

(*-==============================================================-*)
(*- CONVERSIONS added by TT 03 Dec 2009                          -*)
(*-==============================================================-*)

open boolLib HolKernel listSyntax
structure Parse =
struct
 open Parse
 val (Type,Term) = parse_from_grammars listTheory.list_grammars
 fun -- q x = Term q
 fun == q x = Type q
end
open Parse


val APPEND_EVAL_CONV = PURE_REWRITE_CONV [listTheory.APPEND_NIL,
                                          listTheory.APPEND];

local
  val NORM_CONS_conv1 = REWR_CONV (CONJUNCT2 listTheory.APPEND)
  val NORM_CONS_conv2 = REWR_CONV (CONJUNCT1 listTheory.APPEND)
  fun NORM_CONS_conv t = ((NORM_CONS_conv1 THENC RAND_CONV NORM_CONS_conv)
                          ORELSEC NORM_CONS_conv2) t
in

(* takes a list of the form ``x1::x2::..::xn::l`` and converts it to
   ``[x1;x2;...;xn]++l`` *)
fun NORM_CONS_CONV tt =
  let
     val (eL, r) = strip_cons tt;
     val _ = if null eL orelse is_nil r then raise UNCHANGED else ()
     val t' = mk_append (listSyntax.mk_list (eL, type_of (hd eL)), r);
  in
     GSYM (NORM_CONS_conv t')
  end
end

(* takes a list of the form ``[x1;...;xn] ++ [y1;...;ym]`` and converts it to
   ``[x1;...;xn;y1;...;ym]`` *)
fun APPEND_SIMPLE_LISTS_CONV t =
  let
     val (l1, l2) = dest_append t;
     val _ = if is_list l1 andalso is_list l2 then () else raise UNCHANGED;
  in
      APPEND_EVAL_CONV t
  end handle HOL_ERR _ => raise UNCHANGED;


(* takes a list of the form ``(l ++ [x1;...;xn]) ++ [y1;...;ym]`` and converts it to
   ``l ++ [x1;...;xn;y1;...;ym]`` *)
fun APPEND_SIMPLE_LISTS_ASSOC_CONV t =
  let
     val (l1, l2) = dest_append t;
     val (l11, l12) = dest_append l1;
     val _ = if is_list l2 andalso is_list l12 then () else raise UNCHANGED;
  in
     ((REWR_CONV (GSYM listTheory.APPEND_ASSOC)) THENC
     RAND_CONV (APPEND_EVAL_CONV)) t
  end handle HOL_ERR _ => raise UNCHANGED;


(* --------------------------------------------------------------------- *)
(* NORM_CONS_APPEND_NO_EVAL_CONV : conv                                  *)
(* bring appends and conses into normal form. The resulting list is      *)
(* consists of appending serveral lists. Cons operations are put into    *)
(* lists just containing these elements. Empty lists are removed and     *)
(* associative of append used. Moreover, some rewrites for SNOC and      *)
(* REVERSE are applied                                                   *)
(* |- x1::x2::l1 ++ (SNOC x3 (x4::l2 ++                                  *)
(*       REVERSE (x5::x6::x7::(l3 ++ l4 ++ l5)) ++ [x8;x9]))) =          *)
(*    [x1; x2] ++ l1 ++ [x4] ++ l2 ++ REVERSE l5 ++ REVERSE l4 ++        *)
(*       REVERSE l3 ++ [x7; x6; x5; x8; x9; x3]                          *)
(* --------------------------------------------------------------------- *)

val NORM_CONS_APPEND_NO_EVAL_CONV =
   (TOP_DEPTH_CONV NORM_CONS_CONV) THENC
   (PURE_REWRITE_CONV [listTheory.APPEND_NIL, listTheory.APPEND_ASSOC,
                      listTheory.SNOC_APPEND, listTheory.REVERSE_APPEND,
                      listTheory.REVERSE_DEF]) THENC
   (DEPTH_CONV ((QCHANGED_CONV APPEND_SIMPLE_LISTS_ASSOC_CONV) ORELSEC
                (QCHANGED_CONV APPEND_SIMPLE_LISTS_CONV)));


(* --------------------------------------------------------------------- *)
(* NORM_CONS_APPEND_CONV : conv                                          *)
(* The normal form produced by NORM_CONS_APPEND_NO_EVAL_CONV is useful   *)
(* for the tools developed below. It's the one this lib is mainly        *)
(* interested in. However, the REWRITES for APPEND as for example        *)
(* included in list_ss destroy this normal form. Therefore,              *)
(* simplification easily loops when for example using list_ss with this  *)
(* conversion.                                                           *)
(*                                                                       *)
(* In order to avoid such problems, NORM_CONS_APPEND_CONV used           *)
(* NORM_CONS_APPEND_NO_EVAL_CONV followed by rewrites of APPEND          *)
(* The result is moving conses for the first list outwards:              *)
(*                                                                       *)
(* |- x1::x2::l1 ++ (SNOC x3 (x4::l2 ++                                  *)
(*       REVERSE (x5::x6::x7::(l3 ++ l4 ++ l5)) ++ [x8;x9]))) =          *)
(*    x1::x2::(l1 ++ [x4] ++ l2 ++ REVERSE l5 ++ REVERSE l4 ++           *)
(*       REVERSE l3 ++ [x7; x6; x5; x8; x9; x3]                          *)
(* --------------------------------------------------------------------- *)

val NORM_CONS_APPEND_CONV =
   NORM_CONS_APPEND_NO_EVAL_CONV THENC APPEND_EVAL_CONV;


val GSYM_CONS_APPEND_CONV = PURE_REWRITE_CONV [GSYM (CONJUNCT2 listTheory.APPEND)]

(* --------------------------------------------------------------------- *)
(* LIST_EQ_SIMP_CONV : conv                                              *)
(* --------------------------------------------------------------------- *)

(*examples
val t = ``[x1;x2] ++ l1 ++ l2 ++ [x3] ++ l3 = x1::x2'::l1' ++ l3``
 |- ([x1; x2] ++ l1 ++ l2 ++ [x3] ++ l3 = x1::x2'::l1' ++ l3) <=>
    (x2 = x2') /\ (l1 ++ l2 ++ [x3] = l1')

val t = ``[x1;x2] ++ l1 ++ l2 ++ [x3] ++ [x4;x5;x6] = x1'::l1' ++ [x5;x6]``

 |- ([x1; x2] ++ l1 ++ l2 ++ [x3] ++ [x4; x5; x6] = x1'::l1' ++ [x5; x6]) <=>
     (x1 = x1') /\ (x2::(l1 ++ l2 ++ [x3; x4]) = l1') : thm

val t = ``l1 ++ l2 ++ [x3] ++ l3 = l1 ++ l2' ++ x3'::l3``

 |- (l1 ++ l2 ++ [x3] ++ l3 = l1 ++ l2' ++ x3'::l3) <=>
    (l2 = l2') /\ (x3 = x3')

val t = ``[x1;x2;x3] ++ l2 ++ [x3] ++ l3 = [x1;x2] ++ l1 ++ l2' ++ l3``

 |- ([x1; x2; x3] ++ l2 ++ [x3] ++ l3 = [x1; x2] ++ l1 ++ l2' ++ l3) <=>
     (x3::(l2 ++ [x3]) = l1 ++ l2')

val t = ``(x::l) = (l ++ l)``


ListConv1.LIST_EQ_SIMP_CONV t

*)

local
   fun strip_cons_append tt =
   let
      val (eL, b) = strip_cons tt;
      val lL = strip_append b
   in
      (eL, lL)
   end;


   fun EQ_CONV c = LHS_CONV c THENC RHS_CONV c

   fun is_non_empty_list t = is_list t andalso not (is_nil t)
   fun is_right_cons lL1 lL2 = (is_non_empty_list (last lL1)) andalso (is_non_empty_list (last lL2))
   fun is_right_same lL1 lL2 = ((length lL1 + length lL2) > 2) andalso (aconv (last lL1) (last lL2))
   fun left_nil_intro_CONV l = if is_append l then raise UNCHANGED else
                              (ISPEC l (GSYM (CONJUNCT1 listTheory.APPEND)))

   fun LIST_EQ_SIMP_CONV___internal_right_elim conv l =
   let
      val (l1, l2) = dest_eq l
      val lL1 = strip_append l1
      val lL2 = strip_append l2
   in
      if (is_right_same lL1 lL2) then
         ((EQ_CONV left_nil_intro_CONV) THENC
          (REWR_CONV (CONJUNCT2 listTheory.APPEND_11)) THENC
          (LIST_EQ_SIMP_CONV___internal_right_elim conv)) l
      else if (is_right_cons lL1 lL2) then
         let
           val (L1,_) = dest_list (last lL1)
           val (L2,_) = dest_list (last lL2)
           val n1 = length L1;
           val n2 = length L2;
           val (turn, L1, L2, n1, n2) =
               if n1 <= n2 then (false, L1, L2, n1, n2) else
                                (true,  L2, L1, n2, n1)

           val thm0 = ((if turn then SYM_CONV else ALL_CONV) THENC
                           (EQ_CONV left_nil_intro_CONV)) l handle UNCHANGED => REFL l;
           val thm1 = if n1 = n2 then thm0 else
               let
                  val (L21, L22) = Lib.split_after (n2 - n1) L2
                  val ty = type_of (hd L21)
                  val L21_t = listSyntax.mk_list (L21, ty)
                  val L22_t = listSyntax.mk_list (L22, ty)
                  val split_thm = GSYM (APPEND_EVAL_CONV (mk_append (L21_t, L22_t)))
               in
                  CONV_RULE ((RHS_CONV o RHS_CONV)
                     (RAND_CONV (K split_thm) THENC
                      REWR_CONV listTheory.APPEND_ASSOC)) thm0
               end;

           val thm2a = PART_MATCH (lhs o rand) (CONJUNCT2 listTheory.APPEND_11_LENGTH) (rhs (concl thm1))
           val thm2b = CONV_RULE ((RATOR_CONV o RAND_CONV)
                       (REWRITE_CONV [listTheory.LENGTH, prim_recTheory.INV_SUC_EQ])) thm2a
           val thm2 = TRANS thm1 (MP thm2b TRUTH)

           val thm3 = if turn then
              CONV_RULE ((RHS_CONV o RATOR_CONV o RAND_CONV) SYM_CONV) thm2 else thm2

           val thm4 = CONV_RULE ((RHS_CONV o RATOR_CONV o RAND_CONV)
                         (LIST_EQ_SIMP_CONV___internal_right_elim conv)) thm3
         in
           thm4
         end
      else conv l
   end handle HOL_ERR _ => raise UNCHANGED;


   fun is_left_cons lL1 lL2 = (is_non_empty_list (hd lL1)) andalso (is_non_empty_list (hd lL2))
   fun is_left_same lL1 lL2 = (length lL1 + length lL2 > 2) andalso (aconv (hd lL1) (hd lL2))
   fun right_nil_intro_CONV l = if is_append l then raise UNCHANGED
                                else
                                  ISPEC l (GSYM listTheory.APPEND_NIL)

   fun LIST_EQ_SIMP_CONV___internal_left_elim conv l =
   let
      val (l1, l2) = dest_eq l
      val lL1 = strip_append l1
      val lL2 = strip_append l2
   in
      if (is_left_same lL1 lL2) then
         ((EQ_CONV right_nil_intro_CONV) THENC
          (REWR_CONV (CONJUNCT1 listTheory.APPEND_11))  THENC
          LIST_EQ_SIMP_CONV___internal_left_elim conv) l
      else if (is_left_cons lL1 lL2) then
         let
           val (L1,_) = dest_list (hd lL1)
           val (L2,_) = dest_list (hd lL2)
           val n1 = length L1;
           val n2 = length L2;
           val (turn, L1, L2, n1, n2) =
               if n1 <= n2 then (false, L1, L2, n1, n2) else
                                (true,  L2, L1, n2, n1)

           val thm0 = ((if turn then SYM_CONV else ALL_CONV) THENC
                           (EQ_CONV right_nil_intro_CONV)) l handle UNCHANGED => REFL l
           val thm1 = if n1 = n2 then thm0 else
               let
                  val (L21, L22) = Lib.split_after n1 L2
                  val ty = type_of (hd L21)
                  val L21_t = listSyntax.mk_list (L21, ty)
                  val L22_t = listSyntax.mk_list (L22, ty)
                  val split_thm = GSYM (APPEND_EVAL_CONV (mk_append (L21_t, L22_t)))
               in
                  CONV_RULE ((RHS_CONV o RHS_CONV)
                     (RATOR_CONV (RAND_CONV (K split_thm)) THENC
                      REWR_CONV (GSYM listTheory.APPEND_ASSOC))) thm0
               end;

           val thm2a = PART_MATCH (lhs o rand) (CONJUNCT1 listTheory.APPEND_11_LENGTH)
                         (rhs (concl thm1))
           val thm2b = CONV_RULE ((RATOR_CONV o RAND_CONV)
                       (REWRITE_CONV [listTheory.LENGTH, prim_recTheory.INV_SUC_EQ])) thm2a
           val thm2 = TRANS thm1 (MP thm2b TRUTH)

           val thm3 = if turn then
              CONV_RULE ((RHS_CONV o RAND_CONV) SYM_CONV) thm2 else thm2

           val thm4 = CONV_RULE ((RHS_CONV o RAND_CONV)
                         (LIST_EQ_SIMP_CONV___internal_left_elim conv)) thm3
         in
           thm4
         end
      else conv l
   end handle HOL_ERR _ => raise UNCHANGED;

   val APPEND_LEFT_ASSOC_CONV =
      PURE_REWRITE_CONV [GSYM listTheory.APPEND_ASSOC];

   fun LIST_EQ_SIMP_CONV___internal t =
       let
          val (l1, l2) = dest_eq t;
       in
          if (aconv l1 l2) then EQT_INTRO (REFL l1) else
          (LIST_EQ_SIMP_CONV___internal_right_elim
            (APPEND_LEFT_ASSOC_CONV THENC
              LIST_EQ_SIMP_CONV___internal_left_elim
              NORM_CONS_APPEND_CONV)) t
       end handle HOL_ERR _ => raise UNCHANGED
in

fun LIST_EQ_SIMP_CONV t =
let
   val (l1', _) = dest_eq t
   val _ = if is_list_type (type_of l1') then () else raise UNCHANGED;
in
   ((EQ_CONV NORM_CONS_APPEND_NO_EVAL_CONV) THENC
     LIST_EQ_SIMP_CONV___internal THENC
     REWRITE_CONV [listTheory.APPEND_eq_NIL, listTheory.NOT_CONS_NIL, GSYM listTheory.NOT_CONS_NIL,
       listTheory.CONS_11]) t
end;

val LIST_EQ_ss =
  simpLib.name_ss "list EQ"
   (simpLib.conv_ss
      {name  = "LIST_EQ_SIMP_CONV",
       trace = 2,
       key   = SOME ([],Term `l1:'a list = l2:'a list`),
       conv  = K (K (CHANGED_CONV LIST_EQ_SIMP_CONV))})

end;


(*---------------------------------------------------------------------------
        For the simplifier.
 ---------------------------------------------------------------------------*)

val LIST_ss = BasicProvers.thy_ssfrag "list"
val _ = BasicProvers.augment_srw_ss [LIST_EQ_ss]

(*---------------------------------------------------------------------------
        For computeLib
 ---------------------------------------------------------------------------*)

val list_rws = computeLib.add_thms
    [ APPEND,APPEND_NIL, FLAT, HD, TL, LENGTH, MAP, MAP2,
      NULL_DEF, CONS_11, NOT_CONS_NIL, NOT_NIL_CONS,
      MEM, EXISTS_DEF, EVERY_DEF,
      ZIP, UNZIP,
      REVERSE_DEF, (* might want to think about more efficient
                      version of this *)
      FILTER, FOLDL, FOLDR, FOLDL, EL_restricted, EL_simp_restricted,
      computeLib.lazyfy_thm list_case_compute,
      list_size_def];

fun list_compset () = let
  open computeLib reduceLib
  val base = num_compset()
  val _ = list_rws base;
  val _ = computeLib.add_thms [ALL_DISTINCT,FRONT_DEF,LAST_DEF] base;
in
  base
end

end (* struct *)

