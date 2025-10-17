Theory simplifier
Ancestors
  finite_map

(*---------------------------------------------------------------------------------*)
(*      Simplifier on finite maps                                                  *)
(*---------------------------------------------------------------------------------*)

val FUPDATE_LT_COMMUTES = Q.store_thm (
  "FUPDATE_LT_COMMUTES",
  ` !f a b c d. c < a ==> (f |+ (a:num, b) |+ (c,d) = f |+ (c,d) |+ (a,b))`,
    RW_TAC arith_ss [FUPDATE_COMMUTES]
    );

