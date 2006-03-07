signature RelNorm_Input =
sig

  eqtype t
  include Abbrev
  val dest    : term -> term * term
  val mk      : term * term -> term
  val listmk  : term list -> term
  val destf   : term ->  t * term
  val mkf     : t * term -> term
  val destrel : term -> term * term
  val canon   : term -> thm
  val addid   : term -> thm
  val opr     : term
  val rwt     : thm
  val +       : t * t -> t
  val -       : t * t -> t
  val ~       : t -> t
  val <       : t * t -> bool
  val one     : t
  val zero    : t
end

signature RelNorm_Output =
sig
  val gen_relnorm : Term.term -> Thm.thm
end


functor GenRelNorm(RelNorm_Input : RelNorm_Input) : RelNorm_Output =
struct

open HolKernel boolLib RelNorm_Input

fun gen_relnorm t = let
  val (l,r) = destrel t
  fun coeff_count bmap left t = let
    fun base bmap t = let
      val (c,t0) = destf t
    in
      case Binarymap.peek(bmap,t0) of
        NONE => Binarymap.insert(bmap,t0, if left then (c,c,zero)
                                          else (~c,zero,c))
      | SOME(tot,l,r) => if left then
                           Binarymap.insert(bmap,t0,(tot + c, l + c, r))
                         else
                           Binarymap.insert(bmap,t0,(tot - c, l, r + c))
    end
    fun recurse bmap t = let
      val (l,r) = dest t
    in
      recurse (recurse bmap l) r
    end handle HOL_ERR _ => base bmap t
  in
    recurse bmap t
  end
  val bmap = coeff_count (coeff_count (Binarymap.mkDict Term.compare) true l)
                         false r
  fun cons_mkf' (i,r) acc = if i = one then r::acc
                            else if i = zero then acc
                            else  mkf(i,r)::acc
  fun foldthis (k,(tot,l,r),(common,ls,rs)) =
      if l = zero then (common, ls, cons_mkf'(r,k) rs)
      else if r = zero then (common, cons_mkf'(l,k) ls, rs)
      else if tot < zero then (cons_mkf'(l,k) common, ls, cons_mkf'(r-l,k) rs)
      else (cons_mkf'(r,k) common, cons_mkf'(l-r,k) ls, rs)
  val (common, ls, rs) = Binarymap.foldr foldthis ([],[],[]) bmap
  val _ = not (null common) orelse raise Conv.UNCHANGED
  val common_t = listmk common
  val left_thm = if null ls then addid common_t
                 else SYM (QCONV canon (mk(common_t, listmk ls)))
  val right_thm = if null rs then addid common_t
                  else SYM (QCONV canon (mk(common_t, listmk rs)))
  val lr_thm = MK_COMB (AP_TERM opr left_thm, right_thm)
in
  CONV_RULE (RAND_CONV (REWR_CONV rwt)) lr_thm
end

end

(*
val add_leq_rei = let
  open numSyntax
  fun destf t = let
    val (l,r) = dest_mult t
  in
    (Arbint.fromNat (dest_numeral l), r)
  end handle HOL_ERR _ => (Arbint.one, t)
in
  {dest = dest_plus,
   mk = mk_plus,
   listmk = list_mk_plus,
   destf = destf,
   mkf = (fn (i,t) => mk_mult(mk_numeral (Arbint.toNat i), t)),
   destrel = dest_leq,
   canon = gencanon natadd_gci,
   addid = REWR_CONV (GSYM arithmeticTheory.ADD_0),
   opr = leq_tm,
   rwt = arithmeticTheory.LE_ADD_LCANCEL,
   + = Arbint.+, - = Arbint.-, ~ = Arbint.~,
   < = Arbint.<, zero = Arbint.zero, one = Arbint.one}
end

val canon = gencanon natadd_gci

(BINOP_CONV canon THENC gen_relnorm add_leq_rei) ``2 * (x:num) + y <= 1 * x``;
(BINOP_CONV canon THENC gen_relnorm add_leq_rei) ``(x:num) + y <= 1 * x``;

val int_add_leq_rei = let
  open intSyntax
  fun destf t = let
    val (l,r) = dest_mult t
  in
    if is_int_literal l then (int_of_term l, r)
    else (Arbint.one, t)
  end handle HOL_ERR _ => if is_negated t then (Arbint.~ Arbint.one, rand t)
                          else (Arbint.one, t)
in
  {dest = dest_plus,
   mk = mk_plus,
   listmk = list_mk_plus,
   destf = destf,
   mkf = (fn (i,t) => mk_mult(term_of_int i, t)),
   destrel = dest_leq,
   canon = gencanon intadd_gci,
   addid = REWR_CONV (GSYM integerTheory.INT_ADD_RID),
   opr = leq_tm,
   rwt = integerTheory.INT_LE_LADD,
   + = Arbint.+, - = Arbint.-, ~ = Arbint.~,
   < = Arbint.<, zero = Arbint.zero, one = Arbint.one}
end

val intcanon = gencanon intadd_gci;
val inttest = BINOP_CONV intcanon THENC gen_relnorm int_add_leq_rei

inttest  ``2 * (x:int) + y <= 1 * x``;
inttest ``(x:int) + y <= 1 * x``;
inttest ``(x:int) + y <= ~1 * x + ~y + z``;

*)