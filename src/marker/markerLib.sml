structure markerLib :> markerLib =
struct

open HolKernel boolLib markerTheory

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

fun move_stmarked_conj_left tm = let
in
  if is_stmarked tm then ALL_CONV
  else if is_conj tm then
    (LAND_CONV move_stmarked_conj_left THENC TRY_CONV (REWR_CONV assoc))
      ORELSEC
    (RAND_CONV move_stmarked_conj_left THENC
     (REWR_CONV commassoc ORELSEC REWR_CONV comm))
  else NO_CONV
end tm
val move_stmarked_conj_left =
    move_stmarked_conj_left THENC
    (LAND_CONV (REWR_CONV stmarker_def) ORELSEC REWR_CONV stmarker_def)


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

(*---------------------------------------------------------------------------*)
(* Dealing with simplifier directives encoded as tags on theorems.           *)
(*---------------------------------------------------------------------------*)

fun AC th1 th2 =
  EQ_MP (SYM (SPECL [concl th1, concl th2] markerTheory.AC_DEF))
        (CONJ th1 th2);

fun unAC th = let val th1 = PURE_REWRITE_RULE [AC_DEF] th
              in (CONJUNCT1 th1, CONJUNCT2 th1)
              end;

fun Cong th = EQ_MP (SYM(SPEC (concl th) markerTheory.Cong_def)) th;

fun unCong th = PURE_REWRITE_RULE [Cong_def] th;

val AC_tm = prim_mk_const{Name="AC",Thy="marker"}
val Cong_tm = prim_mk_const{Name="Cong",Thy="marker"};


end
