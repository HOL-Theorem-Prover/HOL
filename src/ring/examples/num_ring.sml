(*
load "bossLib";
load "ringLib";
open bossLib arithLib arithmeticTheory semi_ringTheory;
*)
local
open Parse basicHol90Lib bossLib  arithLib arithmeticTheory semi_ringTheory;
in
infix THEN THENL o;


val ARITH_PROVE = EQT_ELIM o ARITH_CONV;
val ARW_TAC = RW_TAC arith_ss;

(* num is a semi-ring: *)
val num_semi_ring = store_thm
    ("num_semi_ring",
     --` is_semi_ring (semi_ring 0 1 $+ $* : num semi_ring) `--,
ARW_TAC [ is_semi_ring_def, semi_ring_accessors,
	  RIGHT_ADD_DISTRIB, MULT_ASSOC ] THEN
MATCH_ACCEPT_TAC MULT_SYM);


local open numeralTheory
in
val numeral_rewrites =
  [ numeral_distrib, numeral_eq, numeral_suc, numeral_iisuc,
    numeral_add, numeral_mult, iDUB_removal,
    ARITH_PROVE(--` ((ALT_ZERO = ALT_ZERO)=T) /\ ((0 = 0) = T) `--) ];
end;

val {EqConv=NUM_RING_CONV, NormConv=NUM_NORM_CONV, ...} =
  ringLib.declare_ring { Name = "num",
                         Theory = num_semi_ring,
			 Const = Term.is_numeral,
			 Rewrites = numeral_rewrites }
;

end;

(*
val ring_conv = NUM_RING_CONV;
val norm_conv = NUM_NORM_CONV;

norm_conv(--` 3*(9+7):num `--);
norm_conv(--`x+y+x:num`--);
norm_conv(--`(a+b)*(a+b):num`--);
norm_conv(--`(b+a)*(b+a):num`--);
norm_conv(--`(a+b)*(a+b)*(a+b):num`--);
ring_conv(--`(a+b)*(a+b) = (b+a)*(b+a):num`--);
*)
