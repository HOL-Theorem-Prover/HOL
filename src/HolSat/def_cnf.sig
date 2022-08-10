signature def_cnf =
sig

  include Abbrev
  val presimp_conv : conv
  val to_cnf : bool -> term ->
               (string option * int *
                (term,term)satCommonTools.RBM.dict *
                (term * thm) Array.array)

end
