val () = load "cv_computeLib";
open HolKernel boolSyntax;

val () = Theory.new_theory "pft_compute_binders";
val x = mk_var("x",cvSyntax.cv);
val y = mk_var("y",cvSyntax.cv);
fun cv_num n = cvSyntax.mk_cv_num (numSyntax.term_of_int n);
val cv_let = Term.inst [alpha |-> cvSyntax.cv,beta |-> cvSyntax.cv] let_tm;
val inner_body = cvSyntax.mk_cv_add (x,y);
(* Cosmetic names coincide, but the inner body still uses both binders.
   Emission must choose a fresh inner name to preserve the outer reference. *)
val inner_abs = Term.rename_bvar "x" (mk_abs(y,inner_body));
val inner = mk_comb(mk_comb(cv_let,inner_abs),cv_num 4);
val capture = mk_comb(mk_comb(cv_let,mk_abs(x,inner)),cv_num 2);
val z = mk_var("z",cvSyntax.cv);
fun delayed body value = rhs (concl
  (Thm.Beta (REFL (mk_comb(mk_abs(z,body),value)))));
val nested_body = mk_comb(mk_comb(cv_let,
  mk_abs(x,cvSyntax.mk_cv_add(z,x))),cv_num 2);
val closure_nested = delayed nested_body (cv_num 4);
fun cv_decimal s = cvSyntax.mk_cv_num
  (numSyntax.mk_numeral (Arbnum.fromString s));
val large = cv_decimal "18446744073709551616";
val compute_cases =
  [("CAPTURE",capture,cv_num 6),
   ("CLOSURE_NESTED",closure_nested,cv_num 6),
   ("LARGE_NUMERAL",delayed large (cv_num 0),large)];
fun save_compute (name,input,expected) =
  let val result = cv_computeLib.cv_compute [] input
      val () = if null (hyp result) andalso
        aconv (concl result) (mk_eq(input,expected)) then ()
        else raise Fail (name ^ ": wrong producer sequent")
  in ignore (Theory.save_thm(name,result)) end;
val () = List.app save_compute compute_cases;

(* COMB(f,x) and ABS(f,x) are distinct nodes with an identical child pair.
   Keep the COMB proof while a closure substitutes the ABS. *)
val kind_f = mk_var("f",bool --> bool);
val kind_x = mk_var("kind_x",bool);
val kind_comb = mk_comb(kind_f,kind_x);
val kind_abs = mk_abs(kind_f,kind_x);
val kind_source = CONJUNCT2 (CONJ (REFL kind_comb) (REFL kind_abs));
(* The substitution target has no free f: its identical child pair must not
   make capture analysis treat the inner ABS as a COMB. *)
val kind_a = mk_var("a",type_of kind_abs);
val kind_capture = rhs (concl (Thm.Beta (REFL
  (mk_comb(mk_abs(kind_a,mk_abs(kind_f,kind_a)),kind_abs)))));
val kind_capture_result = CONJUNCT2
  (CONJ kind_source (REFL kind_capture));
val () = ignore (Theory.save_thm("KIND_CAPTURE",kind_capture_result));
val () = Theory.export_theory ();
val () = print "COMPUTE_BINDER_ACTUAL_EXPORT_PASS\n";

val () = load_pft [];
val () = PFTEmit.emit_theory
  {trace=".hol/objs/pft_compute_bindersTheory.tr.gz",
   output="compute-binders.pft.bin",ruleset=PFTEmit.Candle};
val () = print "COMPUTE_BINDER_FOCUSED_TESTS_PASS\n";
