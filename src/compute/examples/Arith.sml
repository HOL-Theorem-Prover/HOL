
(*
load "computeLib";
load "arithLib";
*)
open arithLib computeLib;

val rws = from_list false [COND_CLAUSES];
val _ = add_clauses true [strictify_thm LET_DEF] rws;

val norm = CBV_CONV rws;
val wk_norm = WEAK_CBV_CONV rws;

norm (--` (\x.x) ((\x.x) if T then 0 else 10) `--);
(* |- (\x. x) ((\x. x) if T then 0 else 10) = 0 : Thm.thm *)
norm (--` (\x.x) (\x.x) if T then 0 else 10 `--);
(* |- (\x. x) (\x. x) (if T then 0 else 10) = 0 : Thm.thm *)

norm (--` (\x y.x) ((\x.x) if T then 0 else 10) `--);
(* |- (\x y. x) ((\x. x) if T then 0 else 10) = (\y. 0) : Thm.thm *)

(* strong and weak reduction *)
norm    (--` (\x.x) ((\x y. (\z.z) x) 0) `--);
(* |- (\x. x) ((\x y. (\z. z) x) 0) = (\y. 0) : Thm.thm *)
wk_norm (--` (\x.x) ((\x y. (\z.z) x) 0) `--);
(* |- (\x. x) ((\x y. (\z. z) x) 0) = (\y. (\z. z) 0) : Thm.thm *)

(* strict evaluation with LET and eta-reduction *)
norm    (--` (LET \x y z. f x z) if T then 0 else 10 `--);
(* |- LET (\x y z. f x z) (if T then 0 else 10) = (\y. f 0) : Thm.thm *)
wk_norm (--` (LET \x y z. f x z) if T then 0 else 10 `--);
(* |- LET (\x y z. f x z) (if T then 0 else 10) = (\y z. f 0 z) : Thm.thm *)
wk_norm (--`     (\x y z. f x z) if T then 0 else 10 `--);
(* |- (\x y z. f x z) (if T then 0 else 10) =
       (\y z. f (if T then 0 else 10) z) : Thm.thm *)



(* addition, church representation *)
val ARITH_PROVE = EQT_ELIM o ARITH_CONV;

fun church 0 = --`0`--
  | church n = --`SUC ^(church (n-1))`--
;

val rws2 = from_list false
    [ ARITH_PROVE (--` !n. 0+n = n `--),
      ARITH_PROVE (--` !n m. (SUC m)+n = SUC (m+n) `--) ];

val norm2 = CBV_CONV rws2;

val f = --` ^(church 2)+^(church 3) `--;
val g = --` ^(church 2)+n `--;
val h = --` n+0 `--;
val j = --` n+^(church 3) `--;

norm2 (--` $+ 0 `--);
norm2 f;
norm2 g;
norm2 h;

val _ = add_clauses true
    [ ARITH_PROVE (--` !n. n+0 = n `--),
      ARITH_PROVE (--` !n m. m+SUC n = SUC (m+n) `--) ]
    rws2;

norm2 h;
norm2 j;


(* using the numeral representation *)

open numeralTheory reduceLib;

val REFL_EQ_0 = prove(--` ((ALT_ZERO = ALT_ZERO)=T) /\ ((0 = 0) = T) `--,
REWRITE_TAC [REFL_CLAUSE]);

val bool_rewrites = [ COND_CLAUSES, NOT_CLAUSES ];

val numeral_rewrites =
  [  REFL_EQ_0, numeral_distrib, numeral_eq, numeral_suc, numeral_iisuc,
    numeral_add, numeral_mult, iDUB_removal,
    numeral_sub, numeral_lt, numeral_lte, iSUB_THM,
    numeral_exp, iSQR ];

val rws3 = from_list false bool_rewrites;
val _ = add_clauses true numeral_rewrites rws3;

fun norm3 q = time (CBV_CONV rws3) (Term q);
fun reduce q = time REDUCE_CONV (Term q);

norm3 `100=100`;
norm3 `65536+65536`;
norm3 `131072+131072`;
norm3 `100-99`;
norm3 `100*100`;
norm3 `2 EXP 64`;   (* 1.3s *) 
norm3 `2 EXP 128`;  (* 5.7s *)
reduce `2 EXP 128`; (* 10.5 *)
