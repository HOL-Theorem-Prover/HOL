signature bitArithLib =
sig
  include Abbrev Arbnum
  (* Make definitions *)
  val karatsuba_lim : num ref

  (* new functions *)
  val karatsuba_conv : term -> thm
  val real_mul_conv : term -> thm
end
