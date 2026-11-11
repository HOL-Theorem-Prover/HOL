open HolKernel boolSyntax;
val () = Theory.new_theory "pft_term_kinds";
val f = mk_var("f",bool --> bool);
val x = mk_var("x",bool);
val abstraction = mk_abs(f,x);
val nested = mk_abs(f,abstraction);
val retained = CONJUNCT2 (CONJ (REFL (mk_comb(f,x))) (REFL nested));
val renamed = Thm.SUBST [x |-> REFL x] (concl retained) retained;
fun save_exact name expected th =
  if null (hyp th) andalso aconv (concl th) expected then
    ignore (Theory.save_thm(name,th))
  else raise Fail ("wrong source sequent: " ^ name);
val () = save_exact "RENAME" (mk_eq(nested,nested)) renamed;

(* The discarded COMB shares its children with this closed ABS. Its proof
   remains reachable, while the existential's body has no free variables. *)
val closed_abs = mk_abs(f,T);
val closed = CONJUNCT2
  (CONJ (REFL (mk_comb(f,T))) (REFL closed_abs));
val v = mk_var("v",bool);
val witness = EXISTS (mk_exists(v,concl closed),T) closed;
val specified = Thm.prim_specification ["unused"] witness;
val () = save_exact "SPEC" (mk_eq(closed_abs,closed_abs)) specified;
val () = Theory.export_theory ();
val () = print "TERM_KIND_ACTUAL_EXPORT_PASS\n";

val () = load_pft [];
val term_kind_trace = ".hol/objs/pft_term_kindsTheory.tr.gz";
val () = List.app (fn (name,ruleset) => PFTEmit.emit_theory
  {trace=term_kind_trace,output="term-kinds." ^ name ^ ".pft.bin",
   ruleset=ruleset})
  [("candle",PFTEmit.Candle),("hol4",PFTEmit.HOL4)];
val () = print "TERM_KIND_FOCUSED_TESTS_PASS\n";
