structure patriciaLib :> patriciaLib =
struct

(* interactive use:
  app load ["ConseqConv", "wordsLib", "listLib"]
*)

open HolKernel Parse boolLib bossLib
open patriciaTheory patriciaSyntax;

val ERR = mk_HOL_ERR "patricia"

(* ------------------------------------------------------------------------- *)

datatype term_ptree =
    Empty
  | Leaf of Arbnum.num * term
  | Branch of Arbnum.num * int * term_ptree * term_ptree

fun dest_ptree t =
   if is_empty t
      then Empty
   else if is_leaf t
      then let
              val (k, d) = dest_leaf t
           in
              Leaf (numLib.dest_numeral k, d)
           end
   else if is_branch t
      then let
              val (p, m, l, r) = dest_branch t
           in
              Branch (numLib.dest_numeral p, numLib.int_of_term m,
                      dest_ptree l, dest_ptree r)
           end
   else raise ERR "dest_ptree" ""

fun mk_ptree Empty = mk_empty Type.alpha
  | mk_ptree (Leaf (k, d)) = mk_leaf (numLib.mk_numeral k, d)
  | mk_ptree (Branch (p, m, l, r)) =
       mk_branch (numLib.mk_numeral p, numLib.term_of_int m,
                  mk_ptree l, mk_ptree r)

fun odd n = Arbnum.mod2 n = Arbnum.one
fun even n = Arbnum.mod2 n = Arbnum.zero
fun div_2exp x n = funpow x Arbnum.div2 n
fun bit b n = odd (div_2exp b n)

fun mod_2exp x n =
   if x = 0 orelse n = Arbnum.zero
      then Arbnum.zero
   else let
           val v = Arbnum.times2 (mod_2exp (x - 1) (Arbnum.div2 n))
        in
           if even n then v else Arbnum.plus1 v
        end

fun mod_2exp_eq x a b =
   if x = 0
      then true
   else odd a = odd b andalso
        mod_2exp_eq (x - 1) (Arbnum.div2 a) (Arbnum.div2 b)

fun lt_2exp x n = x = Arbnum.zero orelse Arbnum.toInt (Arbnum.log2 x) < n

val empty = Empty

fun every_leaf P Empty = true
  | every_leaf P (Leaf (j, d)) = P j d
  | every_leaf P (Branch (p, m, l, r)) = every_leaf P l andalso every_leaf P r

fun is_ptree Empty = true
  | is_ptree (Leaf (k, d)) = true
  | is_ptree (Branch (p, m, l, r)) =
      lt_2exp p m andalso l <> Empty andalso r <> Empty andalso
      every_leaf (fn k => fn d => mod_2exp_eq m k p andalso bit m k) l andalso
      every_leaf (fn k => fn d => mod_2exp_eq m k p andalso not (bit m k)) r
      andalso is_ptree l andalso is_ptree r

fun branching_bit p0 p1 =
   if odd p0 = even p1 orelse p0 = p1
      then 0
   else branching_bit (Arbnum.div2 p0) (Arbnum.div2 p1) + 1

fun peek Empty k = NONE
  | peek (Leaf (j, d)) k = if k = j then SOME d else NONE
  | peek (Branch (p, m, l, r)) k = peek (if bit m k then l else r) k;

fun join (p0, t0, p1, t1) =
   let
      val m = branching_bit p0 p1
   in
      if bit m p0
         then Branch (mod_2exp m p0, m, t0, t1)
      else Branch (mod_2exp m p0, m, t1, t0)
   end

fun add Empty x = Leaf x
  | add (Leaf (j, d)) (x as (k, e)) =
      if j = k then Leaf x else join (k, Leaf x, j, Leaf (j, d))
  | add (Branch (p, m, l, r)) (x as (k, e)) =
      if mod_2exp_eq m k p
         then if bit m k
                 then Branch (p, m, add l x, r)
              else Branch (p, m, l, add r x)
      else join (k, Leaf x, p, Branch (p, m, l, r))

fun add_list t = foldl (uncurry (C add)) t

fun ptree_of_list l = add_list Empty l

fun branch (_, _, Empty, t) = t
  | branch (_, _, t, Empty) = t
  | branch (p, m, t0, t1) = Branch (p, m, t0, t1)

fun remove Empty k = Empty
  | remove (t as Leaf (j, d)) k = if j = k then Empty else t
  | remove (t as Branch (p, m, l, r)) k =
      if mod_2exp_eq m k p
         then if bit m k
                 then branch (p, m, remove l k, r)
              else branch (p, m, l, remove r k)
      else t

local
   fun traverse_aux Empty f = f
     | traverse_aux (Leaf (j, d)) f = j :: f
     | traverse_aux (Branch (p, m, l, r)) f = traverse_aux l (traverse_aux r f)
in
   fun traverse t = traverse_aux t []
end

fun keys t = Listsort.sort Arbnum.compare (traverse t)

fun transform f Empty = Empty
  | transform f (Leaf (j, d)) = Leaf (j, f d)
  | transform f (Branch (p, m, l, r)) =
      Branch (p, m, transform f l, transform f r)

local
   fun list_of_ptree_aux Empty f = f
     | list_of_ptree_aux (Leaf (j, d)) f = (j, d) :: f
     | list_of_ptree_aux (Branch (p, m, l, r)) f =
         list_of_ptree_aux l (list_of_ptree_aux r f)
in
   fun list_of_ptree t = list_of_ptree_aux t []
end

fun size Empty = 0
  | size (Leaf (j, d)) = 1
  | size (Branch (p, m, l, r)) = size l + size r

fun depth Empty = 0
  | depth (Leaf (j, d)) = 1
  | depth (Branch (p, m, l, r)) = 1 + (Int.max (depth l, depth r))

fun tabulate (n, f) =
   let
      fun h i = if i < n then add (h (i + 1)) (f i) else Empty
   in
      if n < 0 then raise Size else h 0
   end

infix in_ptree insert_ptree

fun op in_ptree (n, t) = isSome (peek t n)
fun op insert_ptree (n, t) = add t (n, oneSyntax.one_tm)

val ptree_of_nums = foldl (op insert_ptree) Empty

fun int_peek t i = peek t (Arbnum.fromInt i)
fun int_add t (i, d) = add t (Arbnum.fromInt i, d)
fun int_add_list t = foldl (uncurry (C int_add)) t
fun int_ptree_of_list l = int_add_list Empty l
fun int_remove t i = remove t (Arbnum.fromInt i)
fun op int_in_ptree (n, t) = isSome (int_peek t n)
fun op int_insert_ptree (n, t) = int_add t (n, oneSyntax.one_tm)
val ptree_of_ints = foldl (op int_insert_ptree) Empty

local
   val n256 = Arbnum.fromInt 256
   fun l2n [] = Arbnum.zero
     | l2n (h::t) = Arbnum.+ (Arbnum.mod (h, n256), Arbnum.* (n256, l2n t))
in
   fun string_to_num s =
     l2n (List.rev
       (Arbnum.one :: List.map (Arbnum.fromInt o Char.ord) (String.explode s)))
end

fun string_peek t i = peek t (string_to_num i)
fun string_add t (i, d) = add t (string_to_num i, d)
fun string_add_list t = foldl (uncurry (C string_add)) t
fun string_ptree_of_list l = string_add_list Empty l
fun string_remove t i = remove t (string_to_num i)
fun op string_in_ptree (n, t) = isSome (string_peek t n)
fun op string_insert_ptree (n, t) = string_add t (n, oneSyntax.one_tm)
val ptree_of_strings = foldl (op string_insert_ptree) Empty

fun custom_pp_term_ptree pp_empty pp_entry i ppstrm t =
   let
      open Portable
      val {add_break, add_newline,
           add_string, begin_block, end_block, ...} = with_ppstream ppstrm
      val pp_empty = pp_empty ppstrm
      val pp_entry = pp_entry ppstrm
      val l = Listsort.sort (Arbnum.compare o (fst ## fst)) (list_of_ptree t)
      val ll = List.take (l, i) handle Subscript => l
      val ll_len = length ll
      val elided = length l - ll_len
      fun add_elided () =
         add_string ("|+ ... " ^ "(" ^ Int.toString elided ^
                     (if elided = 1 then " entry" else " entries") ^ " elided)")
   in
      if null l
         then pp_empty true
      else ( begin_block CONSISTENT 0
           ; pp_empty false
           ; begin_block CONSISTENT 0
           ; if null ll
                then add_elided ()
             else ( app (fn x => (pp_entry x; add_break(1,0)))
                       (List.take(ll, ll_len - 1))
                  ; pp_entry (last ll) : unit
                  ; if 0 < elided then (add_newline (); add_elided ()) else ()
                  )
           ; end_block ()
           ; end_block ()
           )
   end

fun standard_pp_empty ppstrm (b: bool) =
  ( Portable.add_string ppstrm "Empty"
  ; if b then () else Portable.add_break ppstrm (1, 1)
  )

fun standard_pp_entry ppstrm (n, tm) =
  ( Portable.add_string ppstrm "|+ ("
  ; Arbnum.pp_num ppstrm n
  ; Portable.add_string ppstrm ", "
  ; Hol_pp.pp_term ppstrm tm
  ; Portable.add_string ppstrm ")"
  )

fun pp_term_ptree ppstrm t =
  ( Portable.add_string ppstrm "``"
  ; custom_pp_term_ptree standard_pp_empty standard_pp_entry 150 ppstrm t
  ; Portable.add_string ppstrm "``"
  )

(* ------------------------------------------------------------------------- *)

local
   val ct_conv = Conv.REWR_CONV ConseqConvTheory.AND_CLAUSES_TX
   val cf_conv = Conv.REWR_CONV ConseqConvTheory.AND_CLAUSES_FX
   val dt_conv = Conv.REWR_CONV ConseqConvTheory.OR_CLAUSES_TX
   val df_conv = Conv.REWR_CONV ConseqConvTheory.OR_CLAUSES_FX
   val it_conv = Conv.REWR_CONV ConseqConvTheory.COND_CLAUSES_CT
   val if_conv = Conv.REWR_CONV ConseqConvTheory.COND_CLAUSES_CF
in
   fun CONJ_CONV cnv1 cnv2 =
      Conv.LAND_CONV cnv1 THENC ((ct_conv THENC cnv2) ORELSEC cf_conv)
   fun DISJ_CONV cnv1 cnv2 =
      Conv.LAND_CONV cnv1 THENC ((df_conv THENC cnv2) ORELSEC dt_conv)
   fun COND3_CONV cnv1 cnv2 cnv3 =
      RATOR_CONV (RATOR_CONV (RAND_CONV cnv1))
      THENC ((it_conv THENC cnv2) ORELSEC (if_conv THENC cnv3))
end

fun dest_strip t = let val (l, r) = strip_comb t in (fst (dest_const l), r) end

(* ------------------------------------------------------------------------- *)

local
   val (peek_empty, peek_leaf, peek_branch) =
      Lib.triple_of_list (List.map Drule.SPEC_ALL (CONJUNCTS PEEK_def))
   val p = Term.mk_var ("p", numLib.num)
   val m = Term.mk_var ("m", numLib.num)
   val k = Term.mk_var ("k", numLib.num)
   val j = Term.mk_var ("j", numLib.num)
   val leaf_rule =
      Conv.CONV_RULE
        (Conv.RHS_CONV (COND3_CONV Arithconv.NEQ_CONV ALL_CONV ALL_CONV))
   val bit_set_rule =
      CONV_RULE (STRIP_QUANT_CONV (RHS_CONV (RATOR_CONV (RAND_CONV
         (RATOR_CONV (RATOR_CONV (RAND_CONV wordsLib.BIT_SET_CONV)))))))
   val branch_rule =
      RIGHT_CONV_RULE
         (LAND_CONV (COND3_CONV (pred_setLib.IN_CONV Arithconv.NEQ_CONV)
                                ALL_CONV ALL_CONV))
in
   fun PTREE_PEEK_CONV tm =
      let
         val (t, i) = patriciaSyntax.dest_peek tm
         val ty = Term.type_of t
         val tty = patriciaSyntax.dest_ptree_type ty
         val tsbst = [Type.alpha |-> tty]
         val d = Term.mk_var ("d", tty)
         val l = Term.mk_var ("l", ty)
         val r = Term.mk_var ("r", ty)
         val inst_ty = Thm.INST_TYPE tsbst
         val bthm = bit_set_rule (Thm.INST [k |-> i] (inst_ty peek_branch))
         fun cnv tm =
            case dest_strip (fst (patriciaSyntax.dest_peek tm)) of
               ("Empty", []) => inst_ty peek_empty
             | ("Leaf", [jj, dd]) =>
                  leaf_rule
                    (Drule.INST_TY_TERM
                       ([k |-> i, j |-> jj, d |-> dd], tsbst) peek_leaf)
             | ("Branch", [pp, mm, ll, rr]) =>
                  let
                     val thm = branch_rule (Thm.INST [p |-> pp, m |-> mm] bthm)
                  in
                     RIGHT_CONV_RULE cnv (Thm.INST [l |-> ll, r |-> rr] thm)
                  end
             | _ => raise ERR "PTREE_PEEK_CONV" "unexpected term"
      in
         cnv tm
      end
end

val PTREE_IN_PTREE_CONV =
   Conv.REWR_CONV IN_PTREE_def
   THENC Conv.RAND_CONV PTREE_PEEK_CONV
   THENC PURE_ONCE_REWRITE_CONV [optionTheory.IS_SOME_DEF]

(* ------------------------------------------------------------------------- *)

val BRANCHING_BIT_numeral = Q.prove(
   `(BRANCHING_BIT 0 0 = 0) /\
    (!x. BRANCHING_BIT 0 (NUMERAL (BIT1 x)) = 0) /\
    (!x. BRANCHING_BIT (NUMERAL (BIT1 x)) 0 = 0) /\
    (!x. BRANCHING_BIT 0 (NUMERAL (BIT2 x)) =
         SUC (BRANCHING_BIT 0 (NUMERAL (SUC x)))) /\
    (!x. BRANCHING_BIT (NUMERAL (BIT2 x)) 0 =
         SUC (BRANCHING_BIT (NUMERAL (SUC x)) 0)) /\
    (!x y. BRANCHING_BIT (NUMERAL (BIT1 x)) (NUMERAL (BIT1 y)) =
           if x = y then 0 else SUC (BRANCHING_BIT (NUMERAL x) (NUMERAL y))) /\
    (!x y. BRANCHING_BIT (NUMERAL (BIT2 x)) (NUMERAL (BIT2 y)) =
           if x = y then 0
           else SUC (BRANCHING_BIT (NUMERAL (SUC x)) (NUMERAL (SUC y)))) /\
    (!x y. BRANCHING_BIT (NUMERAL (BIT1 x)) (NUMERAL (BIT2 y)) = 0) /\
    (!x y. BRANCHING_BIT (NUMERAL (BIT2 x)) (NUMERAL (BIT1 y)) = 0)`,
   REPEAT STRIP_TAC
   THEN CONV_TAC
          (LHS_CONV (ONCE_REWRITE_CONV [patriciaTheory.BRANCHING_BIT_def]))
   THEN SIMP_TAC std_ss
        [numeralTheory.numeral_distrib, numeralTheory.numeral_eq,
         numeralTheory.numeral_evenodd, numeralTheory.numeral_div2]
   )

val BRANCHING_BIT_CONV =
   REWRITE_CONV [BRANCHING_BIT_numeral, numeralTheory.numeral_eq,
                 numeralTheory.numeral_distrib, numeralTheory.numeral_suc,
                 arithmeticTheory.NORM_0]

val MOD_2EXP_CONV =
   PURE_REWRITE_CONV
      [numeral_bitTheory.MOD_2EXP, numeral_bitTheory.numeral_imod_2exp,
       numeralTheory.numeral_suc, numeralTheory.numeral_sub,
       numeralTheory.iSUB_THM, numeralTheory.numeral_lt,
       numeralTheory.iDUB_removal, numeralTheory.numeral_distrib,
       arithmeticTheory.NORM_0, boolTheory.COND_CLAUSES]

local
   val (add_empty, add_leaf, add_branch) =
      Lib.triple_of_list (List.map SPEC_ALL (CONJUNCTS ADD_def))
   val join_rwt =
      RIGHT_CONV_RULE (RATOR_CONV BETA_CONV THENC BETA_CONV)
         (REWRITE_RULE [boolTheory.LET_DEF] (Drule.SPEC_ALL JOIN_def))
   val add_list_cnv =
      Conv.REWR_CONV
        (CONV_RULE (REDEPTH_CONV Conv.FUN_EQ_CONV) patriciaTheory.ADD_LIST_def)
   val wcnv = RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV MOD_2EXP_CONV)))
   val join_conv =
      Conv.REWR_CONV join_rwt
      THENC RAND_CONV BRANCHING_BIT_CONV
      THENC BETA_CONV
      THENC COND3_CONV wordsLib.WORD_EVAL_CONV wcnv wcnv
   val join_rule =
      RIGHT_CONV_RULE
        (COND3_CONV wordsLib.WORD_EVAL_CONV
           (COND3_CONV wordsLib.WORD_EVAL_CONV ALL_CONV ALL_CONV)
           join_conv)
   val add_leaf_rule =
      RIGHT_CONV_RULE (COND3_CONV Arithconv.NEQ_CONV ALL_CONV join_conv)
   val p = Term.mk_var ("p", numLib.num)
   val m = Term.mk_var ("m", numLib.num)
   val j = Term.mk_var ("j", numLib.num)
   val k = Term.mk_var ("k", numLib.num)
in
   fun PTREE_ADD_CONV tm =
      let
         val ((t, _), is_list) =
            (patriciaSyntax.dest_add_list tm, true)
            handle HOL_ERR {origin_function = "dest_add_list", ...} =>
               (patriciaSyntax.dest_add tm, false)
         val ty = Term.type_of t
         val tty = patriciaSyntax.dest_ptree_type ty
         val d = Term.mk_var ("d", tty)
         val e = Term.mk_var ("e", tty)
         val l = Term.mk_var ("l", ty)
         val r = Term.mk_var ("r", ty)
         val inst_ty = Thm.INST_TYPE [Type.alpha |-> tty]
         val leaf = inst_ty add_leaf
         val branch = inst_ty add_branch
         fun add_conv t =
            case (dest_strip ## pairSyntax.dest_pair) (dest_add t) of
               (("Empty", []), (k0, e0)) =>
                 Drule.INST_TY_TERM
                    ([k |-> k0, e |-> e0], [Type.alpha |-> tty]) add_empty
             | (("Leaf", [j0, d0]), (k0, e0)) =>
                 add_leaf_rule
                    (Thm.INST ([k |-> k0, e |-> e0, j |-> j0, d |-> d0]) leaf)
             | (("Branch", [p0, m0, l0, r0]), (k0, e0)) =>
                 let
                    val thm =
                       join_rule
                          (Thm.INST [l |-> l0, r |-> r0, k |-> k0, e |-> e0,
                                     p |-> p0, m |-> m0] branch)
                    val (_, _, l1, r1) =
                       patriciaSyntax.dest_branch (rhs (concl thm))
                 in
                    if patriciaSyntax.is_add r1
                       then RIGHT_CONV_RULE (RAND_CONV add_conv) thm
                    else if patriciaSyntax.is_add l1
                       then RIGHT_CONV_RULE
                               (RATOR_CONV (RAND_CONV add_conv)) thm
                    else thm
                 end
             | _ => raise ERR "PTREE_ADD_LIST_CONV"
                              "Not Empty, Leaf or Branch";
      in
         if is_list
            then (add_list_cnv THENC listLib.FOLDL_CONV add_conv) tm
         else add_conv tm
      end
end

val PTREE_INSERT_PTREE_CONV =
   Conv.REWR_CONV patriciaTheory.INSERT_PTREE_def THENC PTREE_ADD_CONV

(* ------------------------------------------------------------------------- *)

local
   val (remove_empty, remove_leaf, remove_branch) =
      Lib.triple_of_list (List.map SPEC_ALL (CONJUNCTS REMOVE_def))
   val remove_leaf_rule =
      RIGHT_CONV_RULE (COND3_CONV Arithconv.NEQ_CONV ALL_CONV ALL_CONV)
   val branch_rule =
      RIGHT_CONV_RULE
        (COND3_CONV wordsLib.WORD_EVAL_CONV
           (COND3_CONV wordsLib.WORD_EVAL_CONV ALL_CONV ALL_CONV)
           ALL_CONV)
   val p = Term.mk_var ("p", numLib.num)
   val m = Term.mk_var ("m", numLib.num)
   val j = Term.mk_var ("j", numLib.num)
   val k = Term.mk_var ("k", numLib.num)
   val wcnv = RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV MOD_2EXP_CONV)))
   val branch_tm = Term.prim_mk_const {Name = "BRANCH", Thy = "patricia"}
   val remove_left =
      patriciaSyntax.is_remove o (fn l => hd (List.drop (l, 2))) o
      pairSyntax.strip_pair o HolKernel.dest_monop branch_tm (ERR "" "")
in
   fun PTREE_REMOVE_CONV tm =
      let
         val (t, k0) = patriciaSyntax.dest_remove tm
         val ty = Term.type_of t
         val tty = patriciaSyntax.dest_ptree_type ty
         val d = Term.mk_var ("d", tty)
         val e = Term.mk_var ("e", tty)
         val l = Term.mk_var ("l", ty)
         val r = Term.mk_var ("r", ty)
         val inst_ty = Thm.INST_TYPE [Type.alpha |-> tty]
         val leaf = inst_ty remove_leaf
         val branch = inst_ty remove_branch
         val branch_cnv = PURE_ONCE_REWRITE_CONV [inst_ty BRANCH_def]
         fun remove_conv t =
            case dest_strip (fst (dest_remove t)) of
               ("Empty", []) =>
                 Drule.INST_TY_TERM
                    ([k |-> k0], [Type.alpha |-> tty]) remove_empty
             | ("Leaf", [j0, d0]) =>
                 remove_leaf_rule
                    (Thm.INST ([k |-> k0, j |-> j0, d |-> d0]) leaf)
             | ("Branch", [p0, m0, l0, r0]) =>
                 let
                    val thm =
                       branch_rule
                          (Thm.INST [l |-> l0, r |-> r0, k |-> k0,
                                     p |-> p0, m |-> m0] branch)
                    val t' = rhs (concl thm)
                 in
                    if patriciaSyntax.is_branch t'
                       then thm
                    else RIGHT_CONV_RULE
                            (Conv.RAND_CONV
                               (Conv.RAND_CONV
                                  (Conv.RAND_CONV
                                     ((if remove_left t'
                                          then Conv.LAND_CONV
                                       else Conv.RAND_CONV) remove_conv)))
                             THENC branch_cnv) thm
                 end
             | _ => raise ERR "PTREE_REMOVE_LIST_CONV"
                              "Not Empty, Leaf or Branch";
      in
         remove_conv tm
      end
end

(* ------------------------------------------------------------------------- *)

local
   val (transform_empty, transform_leaf, transform_branch) =
      Lib.triple_of_list (List.map SPEC_ALL (CONJUNCTS TRANSFORM_def))
   val j = Term.mk_var ("j", numLib.num)
in
   fun PTREE_TRANSFORM_CONV tcnv tm =
      let
         val (ff, t) = dest_transform tm
         val (tty, rty) = Type.dom_rng (Term.type_of ff)
         val f = Term.mk_var ("f", tty --> rty)
         val d = Term.mk_var ("d", tty)
         val inst_ty =
            Drule.INST_TY_TERM
               ([f |-> ff], [Type.beta |-> rty, Type.alpha |-> tty])
         val leaf = inst_ty transform_leaf
         val branch_cnv = Conv.REWR_CONV (inst_ty transform_branch)
         fun cnv t =
            case dest_strip (snd (dest_transform t)) of
               ("Empty", []) => inst_ty transform_empty
             | ("Leaf", [jj, dd]) =>
                 Conv.RIGHT_CONV_RULE (Conv.RAND_CONV tcnv)
                    (Thm.INST [j |-> jj, d |-> dd] leaf)
             | ("Branch", [_, _, _, _]) =>
                   (branch_cnv
                    THENC Conv.RAND_CONV cnv
                    THENC Conv.RATOR_CONV (Conv.RAND_CONV cnv)) t
             | _ => raise ERR "PTREE_TRANSFORM_CONV" "Not Empty, Leaf or Branch"
      in
         cnv tm
      end
end

(* ------------------------------------------------------------------------- *)

local
   val (size_empty, size_leaf, size_branch) =
      Lib.triple_of_list (List.map SPEC_ALL (CONJUNCTS SIZE))
   val k = Term.mk_var ("k", numLib.num)
in
   fun PTREE_SIZE_CONV tm =
      let
         val t = dest_size tm
         val tty = patriciaSyntax.dest_ptree_type (Term.type_of t)
         val d = Term.mk_var ("d", tty)
         val inst_ty = Thm.INST_TYPE [Type.alpha |-> tty]
         val leaf = inst_ty size_leaf
         val branch_cnv = Conv.REWR_CONV (inst_ty size_branch)
         fun cnv t =
            case dest_strip (dest_size t) of
               ("Empty", []) => inst_ty size_empty
             | ("Leaf", [kk, dd]) => Thm.INST [k |-> kk, d |-> dd] leaf
             | ("Branch", [_, _, _, _]) =>
                   (branch_cnv THENC Conv.BINOP_CONV cnv) t
             | _ => raise ERR "PTREE_SIZE_CONV" "Not Empty, Leaf or Branch";
      in
         (cnv THENC numLib.REDUCE_CONV) tm
      end
end

(* ------------------------------------------------------------------------- *)

local
   val (depth_empty, depth_leaf, depth_branch) =
      Lib.triple_of_list (List.map SPEC_ALL (CONJUNCTS DEPTH_def))
   val j = Term.mk_var ("j", numLib.num)
in
   fun PTREE_DEPTH_CONV tm =
      let
         val t = dest_depth tm
         val tty = patriciaSyntax.dest_ptree_type (Term.type_of t)
         val d = Term.mk_var ("d", tty)
         val inst_ty = Thm.INST_TYPE [Type.alpha |-> tty]
         val leaf = inst_ty depth_leaf
         val branch_cnv = Conv.REWR_CONV (inst_ty depth_branch)
         fun cnv t =
            case dest_strip (dest_depth t) of
               ("Empty", []) => inst_ty depth_empty
             | ("Leaf", [jj, dd]) => Thm.INST [j |-> jj, d |-> dd] leaf
             | ("Branch", [_, _, _, _]) =>
                   (branch_cnv THENC Conv.RAND_CONV (Conv.BINOP_CONV cnv)) t
             | _ => raise ERR "PTREE_DEPTH_CONV" "Not Empty, Leaf or Branch"
      in
         (cnv THENC numLib.REDUCE_CONV) tm
      end
end

(* ------------------------------------------------------------------------- *)

local
   val (every_leaf_empty, every_leaf_leaf, every_leaf_branch) =
      Lib.triple_of_list (List.map SPEC_ALL (CONJUNCTS EVERY_LEAF_def))
   val j = Term.mk_var ("j", numLib.num)
in
   fun PTREE_EVERY_LEAF_CONV ecnv tm =
      let
         val (pp, t) = dest_every_leaf tm
         val tty = patriciaSyntax.dest_ptree_type (Term.type_of t)
         val d = Term.mk_var ("d", tty)
         val p = Term.mk_var ("P", numLib.num --> tty --> Type.bool)
         val inst_ty = Drule.INST_TY_TERM ([p |-> pp], [Type.alpha |-> tty])
         val leaf = inst_ty every_leaf_leaf
         val branch_cnv = Conv.REWR_CONV (inst_ty every_leaf_branch)
         fun cnv t =
            case dest_strip (snd (dest_every_leaf t)) of
               ("Empty", []) => inst_ty every_leaf_empty
             | ("Leaf", [jj, dd]) =>
                 Conv.RIGHT_CONV_RULE ecnv (Thm.INST [j |-> jj, d |-> dd] leaf)
             | ("Branch", [_, _, _, _]) =>
                 (branch_cnv THENC CONJ_CONV cnv cnv) t
             | _ =>
                raise ERR "PTREE_EVERY_LEAF_CONV" "Not Empty, Leaf or Branch"
      in
         cnv tm
      end
end

(* ------------------------------------------------------------------------- *)

local
   val (exists_leaf_empty, exists_leaf_leaf, exists_leaf_branch) =
      Lib.triple_of_list (List.map SPEC_ALL (CONJUNCTS EXISTS_LEAF_def))
   val j = Term.mk_var ("j", numLib.num)
in
   fun PTREE_EXISTS_LEAF_CONV ecnv tm =
      let
         val (pp, t) = dest_exists_leaf tm
         val tty = patriciaSyntax.dest_ptree_type (Term.type_of t)
         val d = Term.mk_var ("d", tty)
         val p = Term.mk_var ("P", numLib.num --> tty --> Type.bool)
         val inst_ty = Drule.INST_TY_TERM ([p |-> pp], [Type.alpha |-> tty])
         val leaf = inst_ty exists_leaf_leaf
         val branch_cnv = Conv.REWR_CONV (inst_ty exists_leaf_branch)
         fun cnv t =
            case dest_strip (snd (dest_exists_leaf t)) of
               ("Empty", []) => inst_ty exists_leaf_empty
             | ("Leaf", [jj, dd]) =>
                 Conv.RIGHT_CONV_RULE ecnv (Thm.INST [j |-> jj, d |-> dd] leaf)
             | ("Branch", [_, _, _, _]) =>
                 (branch_cnv THENC DISJ_CONV cnv cnv) t
             | _ =>
                raise ERR "PTREE_EXISTS_LEAF_CONV" "Not Empty, Leaf or Branch"
      in
         cnv tm
      end
end

(* ------------------------------------------------------------------------- *)

val is_ptree_compset = wordsLib.words_compset ()
val () = computeLib.add_thms
           [REWRITE_RULE [bitTheory.LT_TWOEXP] IS_PTREE_def,
            (GSYM o CONJUNCT1) ptree_distinct,
            (GSYM o CONJUNCT1 o CONJUNCT2) ptree_distinct] is_ptree_compset
val () = computeLib.add_conv
           (every_leaf_tm,  2, PTREE_EVERY_LEAF_CONV wordsLib.WORD_EVAL_CONV)
           is_ptree_compset

local
   val IS_PTREE_EVAL_CONV = CHANGED_CONV (computeLib.CBV_CONV is_ptree_compset)
   val IS_PTREE_X_CONV =
      Conv.FIRST_CONV
        (List.map (PART_MATCH (snd o dest_imp))
          [ADD_IS_PTREE, ADD_LIST_IS_PTREE, INSERT_PTREE_IS_PTREE,
           REMOVE_IS_PTREE, PTREE_OF_NUMSET_IS_PTREE, TRANSFORM_IS_PTREE])
in
   fun PTREE_IS_PTREE_CONV t =
      let
         val thm = ConseqConv.DEPTH_STRENGTHEN_CONSEQ_CONV IS_PTREE_X_CONV t
         val is_ptree_thm = IS_PTREE_EVAL_CONV (fst (dest_imp (concl thm)))
      in
         Lib.with_exn (EQT_INTRO o MATCH_MP thm o EQT_ELIM) is_ptree_thm
           (ERR "PTREE_IS_PTREE_CONV" "")
      end
      handle UNCHANGED => IS_PTREE_EVAL_CONV t
end

(* ------------------------------------------------------------------------- *)

(* add conversion(s) for PTREE_OF_NUMSET *)

val rhsc = rhs o concl
val lhsc = lhs o concl

val PTREE_OF_NUMSET_RWT = Q.prove(
   `(!x t s y.
      IS_PTREE t /\ FINITE s /\ (PTREE_OF_NUMSET t s = y) ==>
      (PTREE_OF_NUMSET t (x INSERT s) = x INSERT_PTREE y)) /\
    (!s1 s2 t y.
      IS_PTREE t /\ FINITE s1 /\ FINITE s2 /\
      (PTREE_OF_NUMSET t s1 = y) /\
      (PTREE_OF_NUMSET y s2 = z) ==>
      (PTREE_OF_NUMSET t (s1 UNION s2) = z))`,
   SRW_TAC [] [PTREE_OF_NUMSET_UNION, PTREE_OF_NUMSET_INSERT])

val ptee_of_numset_insert = CONJUNCT1 PTREE_OF_NUMSET_RWT
val ptee_of_numset_union = CONJUNCT2 PTREE_OF_NUMSET_RWT

fun PTREE_OF_NUMSET_CONV tm =
  case total dest_ptree_of_numset tm of
    SOME (t, s) =>
      if pred_setSyntax.is_insert s then
        let val (x, y) = pred_setSyntax.dest_insert s
            val is_ptree_thm = EQT_ELIM (PTREE_IS_PTREE_CONV (mk_is_ptree t))
            val finite_thm = EQT_ELIM (EVAL (pred_setSyntax.mk_finite y))
            val thm = PTREE_OF_NUMSET_CONV (mk_ptree_of_numset (t, y))
        in
          MATCH_MP (Drule.ISPEC x ptee_of_numset_insert)
                   (LIST_CONJ [is_ptree_thm, finite_thm, thm])
        end
      else if pred_setSyntax.is_empty s then
        REWR_CONV PTREE_OF_NUMSET_EMPTY tm
      else if pred_setSyntax.is_union s then
        let val (s1, s2) = pred_setSyntax.dest_union s
            val is_ptree_thm = EQT_ELIM (PTREE_IS_PTREE_CONV (mk_is_ptree t))
            val finite_thm1 = EQT_ELIM (EVAL (pred_setSyntax.mk_finite s1))
            val finite_thm2 = EQT_ELIM (EVAL (pred_setSyntax.mk_finite s2))
            val thm1 = PTREE_OF_NUMSET_CONV (mk_ptree_of_numset (t, s1))
            val thm2 = PTREE_OF_NUMSET_CONV (mk_ptree_of_numset (rhsc thm1, s2))
        in
          MATCH_MP ptee_of_numset_union
                  (LIST_CONJ [is_ptree_thm, finite_thm1, finite_thm2,thm1,thm2])
        end
      else raise ERR "PTREE_OF_NUMSET_CONV" ""
  | _ => raise ERR "PTREE_OF_NUMSET_CONV" ""

(* ------------------------------------------------------------------------- *)
(* Conversion for applications of ADD, REMOVE and INSERT_PTREE (ARI)         *)
(* ------------------------------------------------------------------------- *)

val DEPTH_ADD_THM = Q.prove(
   `(c1 = t) /\ (patricia$ADD t (k,d) = c2) ==> (patricia$ADD c1 (k,d) = c2)`,
   SRW_TAC [] [])

val DEPTH_REMOVE_THM = Q.prove(
   `(c1 = t) /\ (patricia$REMOVE t k = c2) ==> (patricia$REMOVE c1 k = c2)`,
   SRW_TAC [] [])

val DEPTH_INSERT_PTREE_THM = Q.prove(
   `(c1 = t) /\ (patricia$INSERT_PTREE k t = c2) ==>
                (patricia$INSERT_PTREE k c1 = c2)`,
   SRW_TAC [] [])

fun DEPTH_ARI_CONV rwt tm =
   REWR_CONV rwt tm
   handle HOL_ERR e =>
     if is_add tm
        then let
                val (t, x) = dest_add tm
                val thm = DEPTH_ARI_CONV rwt t
                val t' = rhsc thm
             in
                MATCH_MP DEPTH_ADD_THM
                   (CONJ thm (PTREE_ADD_CONV (mk_add (t', x))))
             end
     else if is_remove tm
        then let
                val (t, k) = dest_remove tm
                val thm = DEPTH_ARI_CONV rwt t
                val t' = rhsc thm
             in
                MATCH_MP DEPTH_REMOVE_THM
                   (CONJ thm (PTREE_REMOVE_CONV (mk_remove (t', k))))
             end
     else if is_insert_ptree tm
        then let
                val (k, t) = dest_insert_ptree tm
                val thm = DEPTH_ARI_CONV rwt t
                val t' = rhsc thm
             in
                MATCH_MP DEPTH_INSERT_PTREE_THM
                   (CONJ thm (PTREE_INSERT_PTREE_CONV
                                 (mk_insert_ptree (k, t'))))
             end
     else raise HOL_ERR e

(* ------------------------------------------------------------------------- *)

val ptree_consts_ref = ref ([]:term list)
val ptree_cache_ref = ref ([]:(term * thm) list)

val ptree_strict_defn_check = ref false
val ptree_max_cache_size = ref 10
val ptree_new_defn_depth = ref ~1

local
   fun contains_term t1 t2 = can (find_term (can (match_term t2))) t1
in
   fun best_match_ptree tm =
      let
         fun get_best_match c [] = c
           | get_best_match NONE (h::t) =
               get_best_match
                 (if contains_term tm (fst h) then SOME h else NONE) t
           | get_best_match (SOME x) (h::t) =
               get_best_match
                 (if contains_term tm (fst h) andalso
                     term_size (fst x) < term_size (fst h)
                  then SOME h else SOME x) t
     in
        get_best_match NONE (!ptree_cache_ref)
     end
end

fun remove_oldest_ptree_theorem () =
   let
      val n = length (!ptree_cache_ref)
   in
      if !ptree_max_cache_size < n
         then ptree_cache_ref := List.take (!ptree_cache_ref, n - 1)
      else ()
   end

fun const_definition c =
   let
      val {Name, Thy, ...} = dest_thy_const c
   in
      DB.fetch Thy (Name ^ "_def") handle HOL_ERR _ => DB.fetch Thy Name
   end

fun root_const tm =
   case Lib.total patriciaSyntax.dest_add tm of
      SOME (t, _) => root_const t
    | NONE =>
     (case Lib.total patriciaSyntax.dest_remove tm of
         SOME (t, _) => root_const t
       | NONE =>
        (case Lib.total patriciaSyntax.dest_insert_ptree tm of
            SOME (_, t) => root_const t
          | NONE => tm))

fun is_add_remove_insert tm =
   is_add tm orelse is_remove tm orelse is_insert_ptree tm

fun root_name tm =
   if is_const tm
      then let
              val defn = rhsc (const_definition tm)
           in
              if is_add_remove_insert defn
                 then root_name (root_const defn)
               else dest_const tm
           end
  else if is_add_remove_insert tm
     then root_name (root_const tm)
  else raise ERR "root_name" ""

fun const_variant c =
   let
      val (name, typ) = root_name c handle HOL_ERR _ => ("ptree", type_of c)
      val v = mk_var (name, typ)
   in
      with_flag (priming, SOME "") (uncurry variant) ([], v)
   end

fun is_ptree_const tm = isSome (List.find (term_eq tm) (!ptree_consts_ref))

fun root_const_depth tm =
   let
      fun const_depth d tm =
         case Lib.total patriciaSyntax.dest_add tm of
            SOME (t, _) => const_depth (d + 1) t
          | NONE =>
           (case Lib.total patriciaSyntax.dest_remove tm of
               SOME (t, _) => const_depth (d + 1) t
             | NONE =>
              (case Lib.total patriciaSyntax.dest_insert_ptree tm of
                  SOME (_, t) => const_depth (d + 1) t
                | NONE =>
                   if is_ptree_const tm
                      then d
                   else if not (!ptree_strict_defn_check) orelse
                           is_ptree (dest_ptree tm)
                      then ~d - 1
                   else raise ERR "root_const_depth" ""))
   in
      const_depth 0 tm
   end

fun insert_ptree_defn thm =
   let
      val (l, r) = dest_eq (concl thm)
      val d = root_const_depth r
   in
      is_const l andalso (0 < d orelse d = ~1) orelse
      raise ERR "insert_ptree_defn" "Not a patricia tree constant"
    ; ptree_consts_ref := l::(!ptree_consts_ref)
   end

fun insert_ptree_theorem thm =
   let
      val (l, r) = dest_eq (concl thm)
   in
      is_ptree_type (type_of l) andalso root_const_depth r = ~1 orelse
      raise ERR "insert_ptree_theorem" "Not a patricia tree constant"
    ; ptree_cache_ref := (l, thm)::(!ptree_cache_ref)
   end

fun save_ptree_thm save thm =
   if save
      then (insert_ptree_theorem thm; remove_oldest_ptree_theorem (); thm)
   else thm

fun ptree_thm save tm =
   case best_match_ptree tm of
      SOME (_, thm) =>
         if term_eq (lhsc thm) tm
            then let
                   val (h, t) = Lib.pluck (term_eq tm o fst) (!ptree_cache_ref)
                 in
                    ptree_cache_ref := h :: t; thm
                 end
         else save_ptree_thm save (DEPTH_ARI_CONV thm tm)
    | NONE =>
         let
            val thm = const_definition (root_const tm)
            val defn = rhsc thm
         in
            if is_add_remove_insert defn
               then let
                       val rwt = DEPTH_ARI_CONV
                                    (ptree_thm false (root_const defn)) defn
                    in
                       save_ptree_thm save
                         ((DEPTH_CONV (REWR_CONV thm)
                           THENC DEPTH_ARI_CONV rwt) tm)
                    end
           else save_ptree_thm save (DEPTH_ARI_CONV thm tm)
         end

val PTREE_DEFN_CONV = ptree_thm false

(* ------------------------------------------------------------------------- *)

fun create_ptree_definition v tm =
   let
      val name = fst (dest_var v)
      val thm = Definition.new_definition (name, mk_eq (v, tm))
   in
      insert_ptree_defn thm
    ; HOL_MESG ("Defined new ptree: " ^ name)
    ; REWR_CONV (SYM thm) tm
   end

fun find_const_ptree tm =
   case List.find (fn c => term_eq tm (rhsc (const_definition c)))
                  (!ptree_consts_ref) of
      SOME c => SOME (SYM (const_definition c))
    | NONE => NONE

fun PTREE_ARI_CONV tm =
   let
      val d = root_const_depth tm
   in
      if 0 < d andalso ((!ptree_new_defn_depth = ~1) orelse
                        d < !ptree_new_defn_depth)
         then raise ERR "PTREE_ARI_CONV" ""
      else if d < 0
         then CHANGED_CONV (DEPTH_ARI_CONV (Thm.REFL (root_const tm))) tm
      else case find_const_ptree tm of
              SOME thm => REWR_CONV thm tm
            | NONE => create_ptree_definition (const_variant tm) tm
   end

val DEPTH_PEEK_THM = Q.prove(
   `(c1 = t) /\ (patricia$PEEK t k = c2) ==> (patricia$PEEK c1 k = c2)`,
   SRW_TAC [] [])

fun PTREE_PEEK_ARI_CONV tm =
   let
      val (t, k) = dest_peek tm
   in
      if is_const t andalso not (is_empty t) orelse is_add_remove_insert t
         then let
                 val thm = ptree_thm true t
              in
                 MATCH_MP DEPTH_PEEK_THM
                    (CONJ thm (PTREE_PEEK_CONV (mk_peek (rhsc thm, k))))
              end
      else PTREE_PEEK_CONV tm
   end

fun mk_ptree_conv2 dest mk conv d_thm tm =
   let
      val (x, t) = dest tm
   in
      if is_const t andalso not (is_empty t) orelse is_add_remove_insert t
         then let
                 val thm = ptree_thm true t
              in
                 MATCH_MP d_thm (CONJ thm (conv (mk (x, rhsc thm))))
              end
      else conv tm
   end

val thm = Q.prove(
   `!f. (c1 = t) /\ (f k t = c2) ==> (f k c1 = c2)`,
   SRW_TAC [] [])

val PTREE_IN_PTREE_ARI_CONV =
   mk_ptree_conv2 dest_in_ptree mk_in_ptree PTREE_IN_PTREE_CONV
     (Drule.ISPEC patriciaSyntax.in_ptree_tm thm)

val PTREE_EVERY_LEAF_ARI_CONV =
   mk_ptree_conv2 dest_every_leaf mk_every_leaf (PTREE_EVERY_LEAF_CONV EVAL)
     (Drule.ISPEC patriciaSyntax.every_leaf_tm thm)

val PTREE_EXISTS_LEAF_ARI_CONV =
   mk_ptree_conv2 dest_exists_leaf mk_exists_leaf (PTREE_EXISTS_LEAF_CONV EVAL)
     (Drule.ISPEC patriciaSyntax.exists_leaf_tm thm)

val thm = Q.prove(
   `!f. (c1 = t) /\ (f t = c2) ==> (f c1 = c2)`,
   SRW_TAC [] [])

fun mk_ptree_conv dest mk conv d_thm tm =
   let
      val t = dest tm
   in
      if is_const t andalso not (is_empty t) orelse is_add_remove_insert t
         then let
                 val thm = ptree_thm true t
              in
                 MATCH_MP d_thm (CONJ thm (conv (mk (rhsc thm))))
              end
      else conv tm
   end

val PTREE_SIZE_ARI_CONV =
   mk_ptree_conv dest_size mk_size PTREE_SIZE_CONV
     (Drule.ISPEC patriciaSyntax.size_tm thm)

val PTREE_DEPTH_ARI_CONV =
   mk_ptree_conv dest_depth mk_depth PTREE_DEPTH_CONV
     (Drule.ISPEC patriciaSyntax.depth_tm thm)

(* ------------------------------------------------------------------------- *)

local
   open computeLib
in
   fun add_ptree_core compset =
    ( add_conv (peek_tm,         2, PTREE_PEEK_ARI_CONV)        compset
    ; add_conv (add_tm,          2, PTREE_ARI_CONV)             compset
    ; add_conv (remove_tm,       2, PTREE_ARI_CONV)             compset
    ; add_conv (insert_ptree_tm, 2, PTREE_ARI_CONV)             compset
    ; add_conv (size_tm,         1, PTREE_SIZE_ARI_CONV)        compset
    ; add_conv (depth_tm,        1, PTREE_DEPTH_ARI_CONV)       compset
    ; add_conv (every_leaf_tm,   2, PTREE_EVERY_LEAF_ARI_CONV)  compset
    ; add_conv (exists_leaf_tm,  2, PTREE_EXISTS_LEAF_ARI_CONV) compset
    ; add_conv (in_ptree_tm,     2, PTREE_IN_PTREE_ARI_CONV)    compset
    ; add_conv (is_ptree_tm,     1, PTREE_IS_PTREE_CONV)        compset
    ; add_conv (ptree_of_numset_tm, 2, PTREE_OF_NUMSET_CONV)    compset
    ; add_thms [PEEK_TRANSFORM] compset
    )
end

val () = add_ptree_core computeLib.the_compset

fun add_ptree_compset compset =
   let
      open listTheory pred_setTheory
   in
      computeLib.add_thms
        [pairTheory.UNCURRY_DEF,
         optionTheory.THE_DEF, optionTheory.option_case_def,
         IS_EMPTY_def, FIND_def, ADD_INSERT, PEEK_TRANSFORM,
         FOLDL, NUMSET_OF_PTREE_def, ADD_LIST_def, LIST_TO_SET_THM,
         PTREE_OF_NUMSET_EMPTY, UNION_PTREE_def, COND_CLAUSES,
         EMPTY_DELETE, DELETE_INSERT, DELETE_UNION] compset
    ; add_ptree_core compset
   end

fun ptree_compset () =
   let
      val compset = computeLib.new_compset []
   in
      add_ptree_compset compset; compset
   end

val PTREE_CONV = computeLib.CBV_CONV (ptree_compset ())

(* ------------------------------------------------------------------------- *)

fun Define_mk_ptree s t =
   let
      val tm = mk_ptree t
      val def = boolSyntax.mk_eq (Term.mk_var (s, Term.type_of tm), tm)
      val thm = Definition.new_definition (s ^ "_def", def)
   in
      insert_ptree_defn thm
    ; insert_ptree_theorem thm
    ; remove_oldest_ptree_theorem ()
    ; thm
   end

local
   val is_ptree_cnv =
      REWR_CONV (EQT_INTRO (SPEC_ALL patriciaTheory.ADD_LIST_TO_EMPTY_IS_PTREE))
   val empty_is_ptree_conv =
      Conv.REWR_CONV (EQT_INTRO patriciaTheory.EMPTY_IS_PTREE)
   fun to_add_list_cnv l =
      if List.null l
         then empty_is_ptree_conv
      else let
              val ty = Term.type_of (snd (hd l))
              val tm =
                 listSyntax.mk_list
                    (List.map (pairSyntax.mk_pair o (numLib.mk_numeral ## I)) l,
                     pairSyntax.mk_prod (numLib.num, ty))
              val tm =
                 patriciaSyntax.mk_add_list (patriciaSyntax.mk_empty ty, tm)
           in
              RAND_CONV (fn _ => SYM (PTREE_ADD_CONV tm)) THENC is_ptree_cnv
           end
in
   fun Define_mk_ptree_with_is_ptree s t =
      let
         val thm = Define_mk_ptree s t
         val l = list_of_ptree t
         val e = patriciaSyntax.mk_is_ptree (lhs (concl thm))
         val is_ptree_thm =
            EQT_ELIM ((RAND_CONV (fn _ => thm) THENC (to_add_list_cnv l)) e)
      in
          computeLib.add_thms [is_ptree_thm] is_ptree_compset
        ; (thm, is_ptree_thm)
      end
end

val dest_ptree_no_test = dest_ptree

fun dest_ptree tm =
   let
      val t = dest_ptree_no_test tm
   in
      if is_ptree t
         then t
     else raise ERR "dest_ptree" "not a valid Patricia tree"
   end

val is_ptree = Lib.can dest_ptree

(* ------------------------------------------------------------------------- *)

end
