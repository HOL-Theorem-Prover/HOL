
(*
load "computeLib";
load "arithLib";
*)
open arithLib computeLib;

val rws = from_list false [boolTheory.COND_CLAUSES];
val norm = CBV_CONV rws;


norm (--` (\x.x) ((\x.x) if T then 0 else 10)) `--);
norm (--` (\x.x) (\x.x) if T then 0 else 10 `--);

norm (--` (\x y.x) ((\x.x) if T then 0 else 10) `--);
norm (--` (\x.x) ((\x y. (\z.z) x) 0) `--);

norm_wk rws (--` (\x.x) ((\x y. (\z.z) x) 0) `--);



(* addition *)
val ARITH_PROVE = EQT_ELIM o ARITH_CONV;

fun church 0 = --`0`--
  | church n = --`SUC ^(church (n-1))`--
;

val rws2 = from_list true
    [ ARITH_PROVE (--` !n. 0+n = n `--),
      ARITH_PROVE (--` !n m. (SUC m)+n = SUC (m+n) `--) ];

val norm2 = CBV_CONV rws2;

val f = --` ^(church 2)+^(church 3) `--;
val g = --` ^(church 2)+n `--;
val h = --` n+0 `--;
val j = --` n+^(church 3) `--;

norm2 f;
norm2 g;
norm2 h;

val _ = add_clauses true
    [ ARITH_PROVE (--` !n. n+0 = n `--),
      ARITH_PROVE (--` !n m. m+SUC n = SUC (m+n) `--) ]
    rws2;

norm2 h;
norm2 j;

