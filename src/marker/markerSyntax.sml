structure markerSyntax :> markerSyntax =
struct

open HolKernel boolLib markerTheory

val ERR = mk_HOL_ERR "markerSyntax";

val stmarker_tm = prim_mk_const{Name="stmarker", Thy="marker"};
val AC_tm       = prim_mk_const{Name="AC",       Thy="marker"};
val Cong_tm     = prim_mk_const{Name="Cong",     Thy="marker"};
val abbrev_tm   = prim_mk_const{Name="Abbrev",   Thy="marker"};
val label_tm    = prim_mk_const{Name=":-",       Thy="marker"};

(*---------------------------------------------------------------------------*)
(* Abbrev (n = M) can appear as a hypothesis in a goal.                      *)
(*---------------------------------------------------------------------------*)

fun mk_abbrev (s,tm) =
 let val l = mk_var(s,type_of tm)
     val eq = mk_eq (l,tm)
 in mk_comb (abbrev_tm,eq)
 end;

fun dest_abbrev tm =
  ((fst o dest_var)##I)
   (dest_eq(dest_monop abbrev_tm (ERR "" "") tm))
  handle HOL_ERR _ => raise ERR "dest_abbrev" "";

val is_abbrev = Lib.can dest_abbrev;

fun compare_abbrev a1 a2 =
 let val (s1,rhs1) = dest_abbrev a1
     val (s2,rhs2) = dest_abbrev a2
     val v1 = mk_var(s1,type_of rhs1)
 in
   free_in v1 rhs2
 end;

(*---------------------------------------------------------------------------*)
(* Abbr `n` is used as an element of a simplification list in order to have  *)
(* the abbreviation (Abbrev (n = M)) in the hypotheses of the goal be        *)
(* expanded before simplification.                                           *)
(*---------------------------------------------------------------------------*)

fun Abbr q =
 let val parse = Lib.with_flag(Feedback.emit_MESG,false) Parse.Term
 in case total parse q
   of NONE => raise ERR "Abbr" "Ill-formed quotation"
    | SOME tm =>
       if is_var tm then
          REFL(mk_var(fst(dest_var tm),mk_vartype "'abbrev"))
        else raise ERR "Abbr" "Ill-formed quotation"
 end;

fun is_abbr th = let
  val (l,r,ty) = dest_eq_ty (concl th)
  val vname = dest_vartype ty
in
  vname = "'abbrev" andalso #1 (dest_var l) = #1 (dest_var r)
end handle HOL_ERR _ => false

fun dest_abbr th = let
  val _ = assert is_abbr th
in
  fst(dest_var(lhs (concl th)))
end

(*---------------------------------------------------------------------------*)
(* Support for user-controlled labelled assumptions.                         *)
(*---------------------------------------------------------------------------*)

val label_ty = fst(dom_rng(type_of label_tm))

fun mk_label (s, t) =
    if type_of t <> bool then
      raise ERR "mk_label" "First argument not boolean"
    else
      list_mk_comb(label_tm, [mk_var(s, label_ty), t]);

fun dest_label tm =
 ((fst o dest_var)##I)
 (dest_binop label_tm (ERR "" "") tm)
 handle HOL_ERR _ => raise ERR "dest_label" "" ;

val is_label = can dest_label;

fun dest_label_ref th = let
  val p as (l,r) = dest_eq (concl th)
  val _ =
      is_var l andalso is_var r andalso Term.compare p = EQUAL andalso
      Type.compare(type_of l, label_ty) = EQUAL orelse
      raise ERR "dest_label_ref" "Theorem not a label reference"
in
  #1 (dest_var l)
end

val is_label_ref = can dest_label_ref

end
