structure GrammarAncestry :> GrammarAncestry =
struct

open HolKernel HOLsexp

val ERR = mk_HOL_ERR "GrammarAncestry"
val tag = "GrammarAncestry"

infix >~ >>
fun f >~ g = Option.mapPartial g o f
fun f >> g = Option.map g o f

val (write, read) =
    Theory.LoadableThyData.new {
      thydataty = tag, merge = op @,
      read = fn {strings,...} => list_decode (int_decode >> strings),
      terms = Lib.K [], strings = (fn l => l),
      pp = fn sl => "[" ^ String.concatWith ", " sl ^ "]",
      write = fn {strings,...} => list_encode (Integer o strings)
    }

fun ancestry {thy} =
  case Theory.LoadableThyData.segment_data{thy=thy, thydataty=tag} of
      NONE => []
    | SOME t => case read t of
                    NONE => raise ERR "ancestry" "Badly encoded data"
                  | SOME sl => sl

fun set_ancestry sl =
  Theory.LoadableThyData.set_theory_data{thydataty = tag, data = write sl}


end
