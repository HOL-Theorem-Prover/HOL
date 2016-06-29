structure listLib :> listLib =
struct

open HolKernel boolLib

open listSimps rich_listSimps indexedListsSimps ListConv1

(* from theorems of the form |- P x1, |- P x2, ..., produce |- EVERY P [x1,x2,...] *)
fun join_EVERY P =
  let
    val nilth = listTheory.EVERY_DEF |> CONJUNCT1 |> ISPEC P |> EQT_ELIM
    val consth = listTheory.EVERY_DEF |> CONJUNCT2 |> ISPEC P |> SPEC_ALL |> EQ_IMP_RULE |> snd
                 |> CONV_RULE(REWR_CONV(GSYM AND_IMP_INTRO))
    fun f [] = nilth
      | f (t::ts) = MATCH_MP (MATCH_MP consth t) (f ts)
  in
    f
  end



end
