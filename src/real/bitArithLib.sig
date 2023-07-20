(**
  Library implementing Karatsuba multiplication for the HOL4 evaluator
  based on the theorems in bitArithScript.sml
**)
signature bitArithLib =
sig
  include Abbrev
  type num = Arbnum.num

  (* Make definitions *)
  val karatsuba_lim : num ref

  (* new functions *)
  val karatsuba_conv : term -> thm
  val real_mul_conv : term -> thm
end
