structure DecimalFractionPP :> DecimalFractionPP =
struct

open HolKernel Parse term_pp_types

fun isconst thy name t = let
  val {Thy,Name,...} = dest_thy_const t
in
  Thy = thy andalso name = Name
end handle HOL_ERR _ => false

val ten = Arbnum.fromInt 10

fun power_of10 n = let
  open Arbnum
  fun recurse (m,acc) =
      if m = one then SOME acc
      else let
        val (q, r) = divmod (m, ten)
      in
        if r = zero then recurse (q,acc+one)
        else NONE
      end
in
  if n > one then recurse(n,zero) else NONE
end

fun fraction {Thy,Division,fromNum} Gs backend sysp ppfns gravs depth t = let
  val {add_string,...}  = ppfns : ppstream_funs
  val (f, args) = strip_comb t
  val _ = length args = 2 orelse raise UserPP_Failed
  val _ = isconst Thy Division f orelse raise UserPP_Failed
  fun getNum t =
      case dest_term t of
        COMB(t1, t2) => let
          val _ = isconst Thy fromNum t1 orelse raise UserPP_Failed
        in
          numSyntax.dest_numeral t2 handle HOL_ERR _ => raise UserPP_Failed
        end
      | _ => raise UserPP_Failed
  val nums = map getNum args
  val numerator = hd nums
  val denominator = hd (tl nums)
  val places = case power_of10 denominator of NONE => raise UserPP_Failed
                                            | SOME n => Arbnum.toInt n
  val (q,r) = Arbnum.divmod(numerator, denominator)
  val qstr = Arbnum.toString q
  val rstr = StringCvt.padLeft #"0" places (Arbnum.toString r)
in
  add_string (qstr ^ "." ^ rstr)
end

end

