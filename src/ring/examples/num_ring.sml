(*
load "bossLib";
load "ringLib";
*)
local
open basicHol90Lib Parse bossLib arithLib arithmeticTheory semi_ringTheory;
in
infix THEN THENL o;

(* num is a semi-ring: *)
val num_semi_ring = store_thm
    ("num_semi_ring",
     --` is_semi_ring (semi_ring 0 1 $+ $*) `--,
RW_TAC arith_ss [is_semi_ring_def, semi_ringTheory.semi_ring_accessors,
		 RIGHT_ADD_DISTRIB, MULT_ASSOC] THEN
MATCH_ACCEPT_TAC MULT_SYM);


local open numeralTheory
in
val REFL_EQ_0 = prove(--` ((ALT_ZERO = ALT_ZERO)=T) /\ ((0 = 0) = T) `--,
RW_TAC arith_ss []);

val numeral_rewrites =
  [ REFL_EQ_0, numeral_distrib, numeral_eq, numeral_suc, numeral_iisuc,
    numeral_add, numeral_mult, iDUB_removal ];

end;


val ARITH_PROVE = EQT_ELIM o ARITH_CONV;

local open arithmeticTheory in
val nat_rewrites =
  [ ADD_CLAUSES, MULT_CLAUSES, NUMERAL_DEF, ALT_ZERO, NUMERAL_BIT1,
    NUMERAL_BIT2,
    ARITH_PROVE (--`(SUC n = SUC m) = (n = m)`--),
    ARITH_PROVE (--`(0 = 0) = T`--),
    ARITH_PROVE (--`(SUC n = 0) = F`--),
    ARITH_PROVE (--`(0 = SUC n) = F`--) ]
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

norm_conv(--` 3*(9+7) `--);
norm_conv(--`x+y+x`--);
norm_conv(--`(a+b)*(a+b)`--);
norm_conv(--`(b+a)*(b+a)`--);
norm_conv(--`(a+b)*(a+b)*(a+b)`--);
ring_conv(--`(a+b)*(a+b) = (b+a)*(b+a)`--);
*)
