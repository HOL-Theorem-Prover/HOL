(*---------------------------------------------------------------------------
      Another example: sum of squares
 ---------------------------------------------------------------------------*)

open arithmeticTheory;

val sum_def =
 Define `(sum f 0 = 0n) /\ (sum f (SUC n) = sum f n + f (SUC n))`;

val lemma = Q.prove
(`!n:num. sum (\m. m * m) n * 6 = n * (n+1) * (2 * n + 1)`,
 Induct THEN RW_TAC arith_ss [sum_def,RIGHT_ADD_DISTRIB] THEN NUM_RING_TAC);

val sum_squares = Q.prove
(`!n:num. sum (\m. m * m) n  = (n*(n+1) * (2*n + 1)) DIV 6`,
 GEN_TAC THEN MATCH_MP_TAC (GSYM DIV_UNIQUE) THEN Q.EXISTS_TAC `0`
 THEN RW_TAC arith_ss [lemma]);
