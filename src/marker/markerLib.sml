structure markerLib :> markerLib =
struct

open HolKernel boolLib

open markerTheory

infix THENC ORELSEC

val stmarker_t = prim_mk_const{Thy = "marker", Name = "stmarker"};
val stmark_term = REWR_CONV (GSYM stmarker_def)

fun stmark_conjunct P tm = let
in
  if is_conj tm then
    LAND_CONV (stmark_conjunct P) ORELSEC RAND_CONV (stmark_conjunct P)
  else if P tm then stmark_term
  else NO_CONV
end tm

fun stmark_disjunct P tm = let
in
  if is_disj tm then
    LAND_CONV (stmark_disjunct P) ORELSEC RAND_CONV (stmark_disjunct P)
  else if P tm then stmark_term
  else NO_CONV
end tm

fun is_stmarked t = same_const stmarker_t (rator t) handle HOL_ERR _ => false

val [comm, assoc, commassoc] = CONJUNCTS (SPEC_ALL markerTheory.move_left_conj)
open QConv
val THENQC = fn (c1, c2) => THENQC c1 c2
val ORELSEQC = fn (c1, c2) => ORELSEQC c1 c2
infix THENQC ORELSEQC

fun move_stmarked_conj_left tm = let
in
  if is_stmarked tm then ALL_QCONV
  else if is_conj tm then
    (LAND_CONV move_stmarked_conj_left THENQC TRY_QCONV (REWR_CONV assoc))
      ORELSEQC
    (RAND_CONV move_stmarked_conj_left THENQC
     (REWR_CONV commassoc ORELSEQC REWR_CONV comm))
  else NO_CONV
end tm
val move_stmarked_conj_left =
    move_stmarked_conj_left THENQC
    (LAND_CONV (REWR_CONV stmarker_def) ORELSEQC REWR_CONV stmarker_def)


val move_stmarked_conj_right =
    PURE_REWRITE_CONV [move_right_conj] THENC
    (RAND_CONV (REWR_CONV stmarker_def) ORELSEC REWR_CONV stmarker_def)
val move_stmarked_disj_left =
    PURE_REWRITE_CONV [move_left_disj] THENC
    (LAND_CONV (REWR_CONV stmarker_def) ORELSEC REWR_CONV stmarker_def)
val move_stmarked_disj_right =
    PURE_REWRITE_CONV [move_right_conj] THENC
    (RAND_CONV (REWR_CONV stmarker_def) ORELSEC REWR_CONV stmarker_def)

fun move_conj_left P = stmark_conjunct P THENC move_stmarked_conj_left
fun move_conj_right P = stmark_conjunct P THENC move_stmarked_conj_right
fun move_disj_left P = stmark_disjunct P THENC move_stmarked_disj_left
fun move_disj_right P = stmark_disjunct P THENC move_stmarked_disj_right

end (* struct *)
