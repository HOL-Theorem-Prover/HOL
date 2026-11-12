fun check_sequent name hyps expected th =
  if length (Thm.hyp th) = length hyps andalso
     List.all (fn h => List.exists (Term.aconv h) (Thm.hyp th)) hyps andalso
     Term.aconv (Thm.concl th) expected then
    print ("PFT_EXACT " ^ name ^ "\n")
  else raise Fail ("wrong sequent: " ^ name);
fun check_saved db name hs tm =
  check_sequent name hs tm (valOf (PFTReplay.lookup db name));
fun check_eq x y = let
  val ty = Term.type_of x
  val eq = Term.mk_thy_const
    {Thy="min",Name="=",Ty=Type.--> (ty,Type.--> (ty,Type.bool))}
in Term.mk_comb(Term.mk_comb(eq,x),y) end;

local
  val b = Type.bool
  fun arr a c = Type.--> (a,c)
  fun constant thy name ty = Term.mk_thy_const {Thy=thy,Name=name,Ty=ty}
  fun apply2 f x y = Term.mk_comb(Term.mk_comb(f,x),y)
  fun truth () = constant "bool" "T" b
  fun conj p q = apply2 (constant "bool" "/\\" (arr b (arr b b))) p q
  fun imp p q = apply2 (constant "min" "==>" (arr b (arr b b))) p q
  fun forall v body = Term.mk_comb
    (constant "bool" "!" (arr (arr (Term.type_of v) b) b),
     Term.mk_abs(v,body))
  val x = Term.mk_var("x",b)
  val y = Term.mk_var("y",b)
  val eq = check_eq
in
fun check_export_results db = let
  val truth = truth ()
  val check = check_saved db
  val a = constant "pftExport_shadow" "first" b
  val c = constant "pftExport_shadow" "second" b
  val () = check "pftExport_shadow$SHADOW" []
    (conj (eq a a) (conj (forall x (eq x x)) (eq c c)))
  val () = check "pftExport_vacuous$VACUOUS" [] truth
  val unused = constant "pftExport_vacuous" "unused" b
  val () = check "pftExport_vacuous$UNUSED_REFL" [] (eq unused unused)
  val v = Term.mk_var("pftExport_overlap$first",b)
  val first = constant "pftExport_overlap" "first" b
  val () = check "pftExport_overlap$OVERLAP" [] (forall v (eq first first))
  val p = eq x x
  fun collision name = check ("pftExport_hypotheses$" ^ name)
  val () = collision "CONJ_LEFT" [p] (conj p p)
  val () = collision "CONJ_RIGHT" [p] (conj p p)
  val () = collision "MP" [truth] p
  val () = collision "DISJ_CASES" [p,imp p p] p
  val guard = forall y (imp (Term.mk_comb(Term.mk_abs(y,truth),y)) p)
  val () = collision "CHOOSE" [guard] p
  val let_tm = constant "bool" "LET" (arr (arr b b) (arr b b))
  val result = Term.mk_comb(let_tm,Term.mk_abs(x,truth))
in check "pftExport_binder$LET" [] (eq result result) end;

fun check_oracle_results db = let
  val truth = truth ()
  fun v name = Term.mk_var(name,b)
  val check = check_saved db
  val () = check "oracle_hyps$hyps" [v "q",v "r"] (v "p")
  val lam = Term.mk_abs(y,eq x (v "x pft%0"))
  val () = check "oracle_hyps$capture" [eq lam lam] (v "p")
  fun poly (name,ty) = let
    val c = constant "oracle_hyps" "c" (arr ty ty)
  in check ("oracle_hyps$" ^ name) [] (eq c c) end
  val () = List.app poly [("POLY_BOOL",b),("POLY_FUN",arr b b)]
in check "oracle_retired_instance$RESULT" [] (eq truth truth) end;

fun term_kind_check db = let
  val truth = truth ()
  val f = Term.mk_var("f",arr b b)
  fun check (name,tm) =
    check_saved db ("pft_term_kinds$" ^ name) [] (eq tm tm)
  val () = List.app check
    [("RENAME",Term.mk_abs(f,Term.mk_abs(f,x))),
     ("SPEC",Term.mk_abs(f,truth)),
     ("EMPTY_BINDER",Term.mk_abs(x,Term.mk_abs(y,x)))]
in ignore (constant "pft_term_kinds" "unused" b) end;
end;
