open HolKernel boolLib bossLib oneTheory

val _ = new_theory "ttt_regression"

local
  fun classify 0 =
        (ignore (List.exists (fn x => x = 1) [1, 2]);
         case [] of [] => "z" | _ => "?")
    | classify _ = "nonzero"
in
  val _ = ignore (classify 0)
end

Theorem Q_TAC_QUOTE_REGRESSION:
  !uf : one -> 'a. P uf ==> P (\y. uf ())
Proof
  SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `(\y. uf ()) = uf` THEN1 SRW_TAC [][] THEN
  SRW_TAC [][FUN_EQ_THM, one]
QED

val _ = export_theory ()
