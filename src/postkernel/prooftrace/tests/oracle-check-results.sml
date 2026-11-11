fun check_oracle_results db = let
  val p = Term.mk_var ("p", Type.bool)
  val q = Term.mk_var ("q", Type.bool)
  val r = Term.mk_var ("r", Type.bool)
  val th = valOf (PFTReplay.lookup db "oracle_hyps$hyps")
  val () = if length (Thm.hyp th) = 2 andalso
     List.exists (Term.aconv q) (Thm.hyp th) andalso
     List.exists (Term.aconv r) (Thm.hyp th) andalso
     Term.aconv (Thm.concl th) p
  then ()
  else raise Fail "oracle replay lost hypotheses or changed its conclusion"
  fun eq x y = let
    val ty = Term.type_of x
    val equality = Term.mk_thy_const
      {Thy="min",Name="=",Ty=Type.--> (ty,Type.--> (ty,Type.bool))}
  in Term.mk_comb(Term.mk_comb(equality,x),y) end
  val x = Term.mk_var("x",Type.bool)
  val y = Term.mk_var("y",Type.bool)
  val synthetic = Term.mk_var("x pft%0",Type.bool)
  val lam = Term.mk_abs(y,eq x synthetic)
  val capture = valOf (PFTReplay.lookup db "oracle_hyps$capture")
  val () = if null (Thm.hyp capture) andalso
    Term.aconv (Thm.concl capture) (eq lam lam) then
      print "PFT_ORACLE_CAPTURE_EXACT_PASS\n"
    else raise Fail "oracle abstraction captured a free variable"
  fun check_poly (name,ty) = let
    val c = Term.mk_thy_const {Thy="oracle_hyps",Name="c",
      Ty=Type.--> (ty,ty)}
    val th = valOf (PFTReplay.lookup db ("oracle_hyps$" ^ name))
  in if null (Thm.hyp th) andalso Term.aconv (Thm.concl th) (eq c c)
     then () else raise Fail ("wrong polymorphic constant sequent: " ^ name)
  end
  val () = List.app check_poly
    [("POLY_BOOL",Type.bool),("POLY_FUN",Type.--> (Type.bool,Type.bool))]
  val () = print "PFT_POLYMORPHIC_DECL_EXACT_PASS\n"
in print "PFT_ORACLE_ALL_CHECKS_PASSED\n" end;
