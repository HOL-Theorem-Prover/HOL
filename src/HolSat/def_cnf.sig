signature def_cnf =
sig

  include Abbrev
  val presimp_conv : conv
  exception to_cnf_unsat of thm
  val to_cnf : bool -> term ->
               (string option * int *
                (term,term)satCommonTools.RBM.dict *
                (term * thm) Array.array)

end
