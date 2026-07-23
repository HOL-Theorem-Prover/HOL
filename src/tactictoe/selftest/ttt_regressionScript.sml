Theory ttt_regression
Ancestors
  one

local
  fun classify 0 =
        (ignore (List.exists (fn x => x = 1) [1, 2]);
         case [] of [] => "z" | _ => "?")
    | classify _ = "nonzero"

  fun classify_nested xs =
    let
      fun keep x = x handle _ => 0
    in
      case xs of
        [x] =>
          let
            fun keep_again y = y handle _ => x
            val y = keep_again (keep x)
          in
            y
          end
      | _ => 0
    end
in
  val _ = (ignore (classify 0); ignore (classify_nested []))
end

Theorem Q_TAC_QUOTE_REGRESSION:
  !uf : one -> 'a. P uf ==> P (\y. uf ())
Proof
  SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `(\y. uf ()) = uf` THEN1 SRW_TAC [][] THEN
  SRW_TAC [][FUN_EQ_THM, one]
QED

Theorem ATTR_REGRESSION[simp]:
  T
Proof
  SIMP_TAC bool_ss []
QED
