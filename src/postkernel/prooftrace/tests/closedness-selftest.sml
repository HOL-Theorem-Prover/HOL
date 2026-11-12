val () = Theory.new_theory "pft_closedness";
val x = Term.mk_var ("x",Type.bool);
val y = Term.mk_var ("y",Type.bool);
val inner = Term.mk_abs (y,y);
val outer = Term.mk_abs (x,inner);
val f = Term.mk_var ("f",Type.--> (Term.type_of outer,Type.bool));
val () = ignore (Theory.save_thm ("RESULT",
  Thm.REFL (Term.mk_comb (f,outer))));
val () = Theory.export_theory ();
open ProofTraceParser;
val (root,heap) = parse ".hol/objs/pft_closednessTheory.tr.gz";
val {all_thms,anon_thms,theory,...} = shRoot heap root;
val {const_name,type_name} = names heap root;
val (_, (thp,_)) = hd (list heap (tuple3 heap (str heap,Lib.I,Lib.I)) all_thms);
val (_,conclusion,proof) = shThm heap thp;
fun refl_term p = case shProof heap p of
    REFL_prf tm => tm
  | save_dep_prf th => refl_term (#3 (shThm heap th))
  | Mark_prf (_,th) => refl_term (#3 (shThm heap th))
  | _ => raise Fail "closedness fixture is not REFL";
val composite = refl_term proof;
val outer = case shTerm heap composite of Comb (_,tm) => tm
  | _ => raise Fail "closedness fixture is not COMB";
val inner = case shTerm heap outer of Abs (_,tm) => tm
  | _ => raise Fail "closedness fixture is not ABS";
val {is_closed,...} = ProofTraceWalk.walk
  {heap=heap,thyname=theory,const_name=const_name,type_name=type_name,
   named_thms=all_thms,anon_thms=anon_thms,incr=fn _ => (),
   on_def_thm=fn _ => (),on_fv=fn _ => ()};
val () = print ("CLOSEDNESS inner=" ^ Bool.toString (is_closed inner) ^
  " outer=" ^ Bool.toString (is_closed outer) ^
  " unvisited=" ^ Bool.toString (is_closed conclusion) ^ "\n");
val () = if is_closed inner andalso is_closed outer andalso
            not (is_closed conclusion) then ()
         else raise Fail "closedness sentinel collision";
val () = print "CLOSEDNESS_REGRESSION_PASS\n";
