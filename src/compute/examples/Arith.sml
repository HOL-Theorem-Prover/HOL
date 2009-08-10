
(*
load "computeLib";
load "arithLib";
*)
open arithLib computeLib;

val rws = reduceLib.basic_rws();

val norm = REDUCE_CONV;
(* val norm = timing.with_stats (CBV_CONV rws); *)
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


(* Tricky case. The \y is first reduced weakly. Then \z must be reduced
 * strongly (arg of a free var), but we will have to reduce the
 * function strongly.
 *)
CBV_CONV (new_rws()) (--` LET (\y. (\z. z) y) (x \z.z)`--);
(* |- (let y = x (\z. z) in (\z. z) y) = (let y = x (\z. z) in y) : Thm.thm *)
WEAK_CBV_CONV (new_rws()) (--` LET (\y. (\z. z) y) (x \z.z)`--);

CBV_CONV (new_rws()) (--` x (LET \z.z) (\y. (\z. z) y)`--);



(* addition, church representation *)
val ARITH_PROVE = EQT_ELIM o ARITH_CONV;

val suc = --`SUC`--;
val zer = --`0`--;

fun church 0 = zer
  | church n = mk_comb{Rator=suc,Rand=church(n-1)}
;

(* Would fail (after printing OK) with non tail recursive implementation. *)
val _ =
  let val n = church 200000 in
  print "OK.\n";
  CBV_CONV (new_rws()) n
  end;


val rws2 = from_list (List.map lazyfy_thm
      [ ARITH_PROVE (--` !n. 0+n = n `--),
	ARITH_PROVE (--` !n m. (SUC m)+n = SUC (m+n) `--) ]);

val norm2 = CBV_CONV rws2;

val f = --` ^(church 2)+^(church 3) `--;
val g = --` ^(church 2)+n `--;
val h = --` n+0 `--;
val j = --` n+^(church 3) `--;

norm2 (--` $+ 0 `--);
norm2 f;
norm2 g;
norm2 h;

val _ = add_thms
    [ ARITH_PROVE (--` !n. n+0 = n `--),
      ARITH_PROVE (--` !n m. m+SUC n = SUC (m+n) `--) ]
    rws2;

norm2 h;
norm2 j;


(* using the numeral representation *)
(*
load "bossLib";
*)

open reduceLib;

fun norm3 q = time REDUCE_CONV (Term q);

norm3 `100=100`;
norm3 `PRE 100`;
norm3 `PRE 1`;
dest_term (rhs (concl it)); (* `0` and NOT `NUMERAL ALT_ZERO` *)
norm3 `65536+65536`;
norm3 `131072+131072`;
norm3 `100-99`;
norm3 `100*100`;
norm3 `2 EXP 64`;   (* 1.3s / 1.1s (ES) *)
norm3 `2 EXP 128`;  (* 5.7s / 4.6s (ES) *)
reduce `2 EXP 128`; (* 10.5 *)

(* calling external conv. *)
norm3 ` 17 DIV (6-1) * 3`;
norm3 ` 17 MOD (6-1) * 3`;

norm3 `123456789123456789 DIV 9876`;  (* 0.6s *)
norm3 `123456789123456789 MOD 9876`;  (* 0.6s *)


(* "Bug" *)
val th = ASSUME(--`0=x`--);
val tm = --`\(x:num).x=0`--;

val rws = from_list [th];
CBV_CONV rws tm;
