fun check_export_results db = let
  val b = Type.bool
  fun arr a c = Type.--> (a,c)
  fun constant thy name ty = Term.mk_thy_const {Thy=thy,Name=name,Ty=ty}
  fun apply2 f x y = Term.mk_comb(Term.mk_comb(f,x),y)
  fun eq x y = apply2 (constant "min" "="
    (arr (Term.type_of x) (arr (Term.type_of x) b))) x y
  val and_tm = constant "bool" "/\\" (arr b (arr b b))
  val imp_tm = constant "min" "==>" (arr b (arr b b))
  fun conj p q = apply2 and_tm p q
  fun imp p q = apply2 imp_tm p q
  fun forall v body = Term.mk_comb
    (constant "bool" "!" (arr (arr (Term.type_of v) b) b),
     Term.mk_abs(v,body))
  val x = Term.mk_var("x",b)
  val y = Term.mk_var("y",b)
  val truth = constant "bool" "T" b
  fun check name hyps expected = let
    val th = valOf (PFTReplay.lookup db name)
    val actual = Thm.hyp th
  in if length actual = length hyps andalso
        List.all (fn h => List.exists (Term.aconv h) actual) hyps andalso
        Term.aconv (Thm.concl th) expected then
       print ("EXPORT_HOL_EXACT " ^ name ^ "\n")
     else raise Fail ("wrong replay sequent: " ^ name)
  end
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
  fun collision name hs tm = check ("pftExport_hypotheses$" ^ name) hs tm
  val () = collision "CONJ_LEFT" [p] (conj p p)
  val () = collision "CONJ_RIGHT" [p] (conj p p)
  val () = collision "MP" [truth] p
  val () = collision "DISJ_CASES" [p,imp p p] p
  val guard = forall y (imp (Term.mk_comb(Term.mk_abs(y,truth),y)) p)
  val () = collision "CHOOSE" [guard] p
  val let_tm = constant "bool" "LET" (arr (arr b b) (arr b b))
  val result = Term.mk_comb(let_tm,Term.mk_abs(x,truth))
  val () = check "pftExport_binder$LET" [] (eq result result)
in print "EXPORTS_HOL_REPLAYED_EXACT\n" end;
