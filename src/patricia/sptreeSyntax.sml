structure sptreeSyntax :> sptreeSyntax =
struct

open HolKernel boolLib
open sptreeTheory

val ERR = Feedback.mk_HOL_ERR "sptreeSyntax"

fun syntax_fns n d m = HolKernel.syntax_fns "sptree" n d m

(* ------------------------------------------------------------------------- *)

fun mk_sptree_ty a = Type.mk_thy_type {Tyop = "spt", Thy = "sptree", Args = [a]}

fun dest_sptree_ty ty =
   case Lib.total Type.dest_thy_type ty of
      SOME {Tyop = "spt", Thy = "sptree", Args = [a]} => a
    | _ => raise ERR "dest_sptree_ty" ""

val sptree_ty_of = dest_sptree_ty o Term.type_of

(* ------------------------------------------------------------------------- *)

val s0 =
   syntax_fns 0
      (fn tm1 => fn e => fn tm2 =>
          if Term.same_const tm1 tm2 then sptree_ty_of tm2 else raise e)
      (fn tm => fn ty => Term.inst [Type.alpha |-> ty] tm)

val (ln_tm, mk_ln, dest_ln, is_ln) = s0 "LN"

(* ------------------------------------------------------------------------- *)

val s1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop
val s1' = syntax_fns 2 HolKernel.dest_monop HolKernel.mk_monop

val (domain_tm, mk_domain, dest_domain, is_domain) = s1' "domain"
val (fromAList_tm, mk_fromAList, dest_fromAList, is_fromAList) = s1 "fromAList"
val (fromList_tm, mk_fromList, dest_fromList, is_fromList) = s1 "fromList"
val (lrnext_tm, mk_lrnext, dest_lrnext, is_lrnext) = s1 "lrnext"
val (ls_tm, mk_ls, dest_ls, is_ls) = s1 "LS"
val (mk_wf_tm, mk_mk_wf, dest_mk_wf, is_mk_wf) = s1 "mk_wf"
val (size_tm, mk_size, dest_size, is_size) = s1 "size"
val (toAList_tm, mk_toAList, dest_toAList, is_toAList) = s1 "toAList"
val (toList_tm, mk_toList, dest_toList, is_toList) = s1 "toList"
val (wf_tm, mk_wf, dest_wf, is_wf) = s1 "wf"

(* ------------------------------------------------------------------------- *)

val s2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop

val (bn_tm, mk_bn, dest_bn, is_bn) = s2 "BN"
val (delete_tm, mk_delete, dest_delete, is_delete) = s2 "delete"
val (difference_tm, mk_difference, dest_difference, is_difference) =
   s2 "difference"
val (inter_eq_tm, mk_inter_eq, dest_inter_eq, is_inter_eq) = s2 "inter_eq"
val (inter_tm, mk_inter, dest_inter, is_inter) = s2 "inter"
val (lookup_tm, mk_lookup, dest_lookup, is_lookup) = s2 "lookup"
val (mk_bn_tm, mk_mk_bn, dest_mk_bn, is_mk_bn) = s2 "mk_BN"
val (union_tm, mk_union, dest_union, is_union) = s2 "union"

(* ------------------------------------------------------------------------- *)

val s3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop

val (bs_tm, mk_bs, dest_bs, is_bs) = s3 "BS"
val (mk_bs_tm, mk_mk_bs, dest_mk_bs, is_mk_bs) = s3 "mk_BS"
val (insert_tm, mk_insert, dest_insert, is_insert) = s3 "insert"

(* ------------------------------------------------------------------------- *)

val s4 = syntax_fns 4 HolKernel.dest_quadop HolKernel.mk_quadop

val (foldi_tm, mk_foldi, dest_foldi, is_foldi) = s4 "foldi"

(* ------------------------------------------------------------------------- *)

(* Pretty-printing support *)

datatype spt = LN | LS of term | BN of spt * spt | BS of spt * term * spt

fun dest_sptree tm =
   case Lib.total boolSyntax.dest_strip_comb tm of
      SOME ("sptree$LN", []) => LN
    | SOME ("sptree$LS", [t]) => LS t
    | SOME ("sptree$BN", [t1, t2]) => BN (dest_sptree t1, dest_sptree t2)
    | SOME ("sptree$BS", [t1, v, t2]) => BS (dest_sptree t1, v, dest_sptree t2)
    | _ => raise ERR "dest_sptree" ""

fun mk_sptree t =
   case t of
      LN => mk_ln Type.alpha
    | LS a => mk_ls a
    | BN (LN, t2) =>
         let
            val tm = mk_sptree t2
         in
            mk_bn (mk_ln (sptree_ty_of tm), tm)
         end
    | BN (t1, LN) =>
         let
            val tm = mk_sptree t1
         in
            mk_bn (tm, mk_ln (sptree_ty_of tm))
         end
    | BN (t1, t2) => mk_bn (mk_sptree t1, mk_sptree t2)
    | BS (t1, a, t2) =>
         let
            val ln = mk_ln (Term.type_of a)
            val tm1 = if t1 = LN then ln else mk_sptree t1
            val tm2 = if t2 = LN then ln else mk_sptree t2
         in
            mk_bs (tm1, a, tm2)
         end

local
   open Arbnum
   fun even n = n mod two = zero
   fun lrnext n =
      if n = zero
         then one
      else times2 (lrnext ((n - (if even n then two else one)) div two))
   fun foldi f i acc =
      fn LN => acc
       | LS a => f i a acc
       | BN (t1, t2) =>
           let
              val inc = lrnext i
           in
              foldi f (i + inc) (foldi f (i + two * inc) acc t1) t2
           end
       | BS (t1, a, t2) =>
           let
              val inc = lrnext i
           in
              foldi f (i + inc) (f i a (foldi f (i + two * inc) acc t1)) t2
           end
   fun insert k a =
      fn LN => if k = zero
                  then LS a
               else if even k
                  then BN (insert ((k - one) div two) a LN, LN)
               else BN (LN, insert ((k - one) div two) a LN)
       | LS a' =>
               if k = zero
                  then LS a
               else if even k
                  then BS (insert ((k - one) div two) a LN, a', LN)
               else BS (LN, a', insert ((k - one) div two) a LN)
       | BN (t1, t2) =>
               if k = zero
                  then BS (t1, a, t2)
               else if even k
                  then BN (insert ((k - one) div two) a t1, t2)
               else BN (t1, insert ((k - one) div two) a t2)
       | BS (t1, a', t2) =>
               if k = zero
                  then BS (t1, a, t2)
               else if even k
                  then BS (insert ((k - one) div two) a t1, a', t2)
               else BS (t1, a', insert ((k - one) div two) a t2)
in
   val toAList =
      Lib.sort (fn (a, _) => fn (b, _) => Arbnum.< (a, b)) o
      foldi (fn k => fn v => fn a => (k, v) :: a) zero [] o dest_sptree
   fun fromList l =
      mk_sptree (snd (List.foldl (fn (a, (i, t)) => (i + one, insert i a t))
                        (zero, LN) l))
   fun fromAList l =
      mk_sptree (List.foldl (fn ((i, a), t) => insert i a t) LN l)
end

local
   fun f (k, v) = pairSyntax.mk_pair (numSyntax.mk_numeral k, v)
in
   fun sptree_pretty_term tm =
      let
         val ty = sptree_ty_of tm
         val l = toAList tm
      in
         if List.null l
            then raise ERR "sptree_pretty_term" ""
         else if fst (List.last l) = Arbnum.fromInt (List.length l - 1)
            then mk_fromList (listSyntax.mk_list (List.map snd l, ty))
         else let
                 val nl = List.map f l
                 val pty = pairSyntax.mk_prod (numSyntax.num, ty)
              in
                 mk_fromAList (listSyntax.mk_list (nl, pty))
              end
      end
end

fun sptree_print Gs B sys ppfns (pg, _, _) d t =
   let
      open Portable term_pp_types smpp
      val {add_string = str, add_break = brk, ublock, ...} =
         ppfns: term_pp_types.ppstream_funs
      val t2 = sptree_pretty_term t
               handle HOL_ERR _ => raise term_pp_types.UserPP_Failed
      fun delim s =
         case pg of
            Prec (j, _) => if 200 <= j then str s else nothing
          | _ => nothing

   in
      case Lib.total dest_fromAList t2 of
         SOME l => ublock INCONSISTENT 0
                      (delim "("
                       >> str "sptree$fromAList"
                       >> brk (1, 2)
                       >> sys (Top, Top, Top) (d - 1) l
                       >> delim ")")
       | NONE =>
           (case Lib.total dest_fromList t2 of
               SOME l => ublock INCONSISTENT 0
                            (delim "("
                             >> str "sptree$fromList"
                             >> brk (1, 2)
                             >> sys (Top, Top, Top) (d - 1) l
                             >> delim ")")
             | NONE => raise term_pp_types.UserPP_Failed)
   end

fun temp_add_sptree_printer () =
   Parse.temp_add_user_printer ("sptree", ``x: 'a sptree$spt``, sptree_print)

fun remove_sptree_printer () =
   General.ignore (Parse.remove_user_printer "sptree")

(* ------------------------------------------------------------------------- *)

(* Testing

open sptreeSyntax

val () = temp_add_sptree_printer ()
val () = remove_sptree_printer ()

val th = EVAL ``fromAList [(23746, a:num); (73246, b); (912, c); (0, d)]``
val th = EVAL ``fromList [a;b;c;d:num]``

val tm = fromList (List.tabulate (100, fn i => numSyntax.term_of_int (2 * i)))
val tm = fromAList (List.tabulate (100, fn i => (Arbnum.fromInt (2 * i), numSyntax.term_of_int i)))

val th = EVAL ``wf ^tm``

*)

end
