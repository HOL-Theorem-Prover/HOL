structure markerLib :> markerLib =
struct

open HolKernel boolLib markerTheory

val ERR = mk_HOL_ERR "markerLib" ;

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

val AC_tm = prim_mk_const{Name="AC",Thy="marker"}
val Cong_tm = prim_mk_const{Name="Cong",Thy="marker"};
val Abbrev_tm = prim_mk_const {Name = "Abbrev", Thy = "marker"}

fun AC th1 th2 =
  EQ_MP (SYM (SPECL [concl th1, concl th2] markerTheory.AC_DEF))
        (CONJ th1 th2);

fun unAC th = let val th1 = PURE_REWRITE_RULE [AC_DEF] th
              in (CONJUNCT1 th1, CONJUNCT2 th1)
              end;

fun Cong th = EQ_MP (SYM(SPEC (concl th) markerTheory.Cong_def)) th;

fun unCong th = PURE_REWRITE_RULE [Cong_def] th;

(*---------------------------------------------------------------------------*)
(* Abbr`n` is used as an element of a simplification list in order to have   *)
(* the abbreviation (Abbrev (n = M)) in the hypotheses of the goal to be     *)
(* expanded before simplification.                                           *)
(*---------------------------------------------------------------------------*)

fun Abbr q =
    case q of
      [QUOTE s] => REFL (mk_var(s, mk_vartype "'abbrev"))
    | _ => raise ERR "Abbr" "Ill-formed quotation"

fun is_Abbr th = let
  val (l,r,ty) = dest_eq_ty (concl th)
  val vname = dest_vartype ty
in
  vname = "'abbrev" andalso #1 (dest_var l) = #1 (dest_var r)
end handle HOL_ERR _ => false

fun dest_Abbr th = let
  val _ = assert is_Abbr th
in
  [QUOTE (#1 (dest_var(lhs (concl th))))]
end

(*---------------------------------------------------------------------------*)
(* Abbrev (n = M) can appear as a hypothesis in a goal.                      *)
(*---------------------------------------------------------------------------*)

fun mk_Abbrev (s,tm) = 
 let val l = mk_var(s,type_of tm)
     val eq = mk_eq (l,tm)
 in mk_comb (Abbrev_tm,eq)
 end;

fun dest_Abbrev tm = 
  ((fst o dest_var)##I)
   (dest_eq(dest_monop Abbrev_tm (ERR "" "") tm))
  handle HOL_ERR _ => raise ERR "dest_Abbrev" "";

val is_Abbrev = Lib.can dest_Abbrev;

end
