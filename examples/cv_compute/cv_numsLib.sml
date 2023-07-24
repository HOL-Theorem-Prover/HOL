structure cv_numsLib :> cv_numsLib =
struct

open HolKernel boolLib cv_numsTheory cvSyntax cv_computeLib;

val ERR = mk_HOL_ERR "cv_numsLib";

(* A basic translator for terms containing arithmetic on numerals into :cv.
 * Proves theorems of this kind:
 *
 *   |- n2c (t: num) = (v: cv)
 *)

fun into_cv tm =
  if numSyntax.is_plus tm then
    into numSyntax.dest_plus n2c_add tm
  else if numSyntax.is_minus tm then
    into numSyntax.dest_minus n2c_sub tm
  else if numSyntax.is_mult tm then
    into numSyntax.dest_mult n2c_mul tm
  else if numSyntax.is_div tm then
    into numSyntax.dest_div n2c_div tm
  else if numSyntax.is_mod tm then
    into numSyntax.dest_mod n2c_mod tm
  else if numSyntax.is_exp tm then
    into numSyntax.dest_exp n2c_exp tm
  else if numSyntax.is_numeral tm then
    SPEC tm n2c_def
  else
    raise ERR "into_cv" "not arithmetic on numerals"
and into dest cth tm =
  let
    val (x,y) = dest tm
    val v = into_cv x (* |- n2c x = cv *)
    val w = into_cv y (* |- n2c y = cw *)
  in
    MATCH_MP (MATCH_MP cth v) w
  end;

val c2n_tm = prim_mk_const {Name="c2n", Thy="cv_nums"};

val cnv = cv_compute [cv_exp_def];

(* A basic conversion for arithmetic on numerals. The conversion turns the term
 * into a :cv problem using into_cv, and then reduces it using cv_compute.
 *
 * cv_num_conv ``t`` returns a theorem:
 *
 *   |- t = t'
 *
 * where t' is a numeral.
 *)

fun cv_num_conv tm =
  let
    val th1 = (into_cv THENC cnv) tm
    val th2 = AP_TERM c2n_tm th1
    val th3 = PURE_ONCE_REWRITE_RULE [GSYM n2c_def] th2
  in
    PURE_ONCE_REWRITE_RULE [c2n_n2c] th3
  end
  handle HOL_ERR {message, ...} => raise ERR "cv_num_conv" message;

end (* struct *)
