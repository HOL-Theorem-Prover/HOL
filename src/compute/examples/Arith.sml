
(*
load "computeLib";
load "arithLib";
*)
open arithLib computeLib;

val rws = from_list (false,[COND_CLAUSES]);
val _ = add_thms (true,[strictify_thm LET_DEF]) rws;

val norm = CBV_CONV rws;
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


val rws2 = from_list
    (false,
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
    (true,
     [ ARITH_PROVE (--` !n. n+0 = n `--),
       ARITH_PROVE (--` !n m. m+SUC n = SUC (m+n) `--) ])
    rws2;

norm2 h;
norm2 j;


(* using the numeral representation *)
(*
load "bossLib";
*)

open arithmeticTheory numeralTheory;

(* bool *)
val bool_rewrites =
  [ INST_TYPE [{redex= ==`:'a`==, residue=bool}] REFL_CLAUSE,
    COND_CLAUSES, COND_ID, NOT_CLAUSES, AND_CLAUSES, OR_CLAUSES,
    IMP_CLAUSES, EQ_CLAUSES ];

(* arith *)

val REFL_EQ_0 =
  INST_TYPE [{redex= ==`:'a`==, residue= ==`:num`==}] REFL_CLAUSE;

val NORM_0 = prove(--`NUMERAL ALT_ZERO = 0`--,
  REWRITE_TAC [arithmeticTheory.NUMERAL_DEF, arithmeticTheory.ALT_ZERO]);

val numeral_rewrites =
  [ numeral_distrib, REFL_EQ_0, numeral_eq, numeral_suc, numeral_pre, NORM_0,
    numeral_iisuc, numeral_add, numeral_mult, iDUB_removal,
    numeral_sub, numeral_lt, numeral_lte, iSUB_THM,
    numeral_exp, iSQR ];

local open bossLib;

  val div_thm =
    prove
      (--` !x y q r. x DIV y =
           if (x = r + q * y) /\ (r < y) then q else x DIV y `--,
       ZAP_TAC base_ss [DIV_UNIQUE] THEN
       MATCH_MP_TAC (DIV_UNIQUE) THEN
       EXISTS_TAC (--`r:num`--) THEN ZAP_TAC arith_ss []);

  val mod_thm =
    prove
      (--` !x y q r. x MOD y = 
           if (x = r + q * y) /\ (r < y) then r else x MOD y `--,
       ZAP_TAC base_ss [] THEN
       MATCH_MP_TAC (arithmeticTheory.MOD_UNIQUE) THEN
       EXISTS_TAC (--`q:num`--) THEN ZAP_TAC arith_ss []);


  fun dest_op opr tm =
    let val (opr',arg) = Dsyntax.strip_comb tm in
    if (opr=opr') then arg else raise Fail "dest_op"
    end;

  val divop = (--`$DIV`--)
  val modop = (--`$MOD`--)

in 
fun DIV_CONV tm =
  case (dest_op divop tm) of
    [x,y] => (let
      open Arbnum
      val (q,r) = divmod (dest_numeral x, dest_numeral y) in
      SPECL [x, y, mk_numeral q, mk_numeral r] div_thm
    end handle HOL_ERR _ => raise Fail "DIV_CONV")
  | _ => raise Fail "DIV_CONV"

fun MOD_CONV tm =
  case (dest_op modop tm) of
    [x,y] => (let
      open Arbnum
      val (q,r) = divmod (dest_numeral x, dest_numeral y) in
      SPECL [x, y, mk_numeral q, mk_numeral r] mod_thm
    end handle HOL_ERR _ => raise Fail "MOD_CONV")
  | _ => raise Fail "MOD_CONV"
end;

(* tests *)

val rws3 = from_list (false,bool_rewrites);
val _ = add_thms (true,numeral_rewrites) rws3;
val _ = add_conv (--`$DIV`--, 2, DIV_CONV) rws3;
val _ = add_conv (--`$MOD`--, 2, MOD_CONV) rws3;

fun norm3 q = time (CBV_CONV rws3) (Term q);

(* Comparison with reduceLib *)
fun reduce q = time reduceLib.REDUCE_CONV (Term q);

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
reduce `123456789123456789 DIV 9876`; (* 0.89s *)
norm3 `123456789123456789 MOD 9876`;  (* 0.6s *)
reduce `123456789123456789 MOD 9876`; (* 0.88s *)


(* "Bug" *)
val th = ASSUME(--`0=x`--);
val tm = --`\(x:num).x=0`--;

val rws = from_list(true,[th]);
CBV_CONV rws tm;
