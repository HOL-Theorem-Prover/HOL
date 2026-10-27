val () = load "cv_computeLib";
open HolKernel boolSyntax;

val compute_source = case OS.Process.getEnv "HOL_PFT_SOURCE_ROOT" of
    SOME root => root ^ "/src/postkernel/prooftrace/"
  | NONE => raise Fail "run compute-binder-tests.sh";
fun compute_require message condition =
  if condition then () else raise Fail message;

val () = Theory.new_theory "pft_compute_binders";
val simple = Parse.Term [QUOTE "let x = cv$Num 0 in x"];
val nested = Parse.Term
  [QUOTE "let x = cv$Num 2 in let y = cv$Num 4 in cv$cv_add x y"];
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
fun save_compute (name,input,expected) =
  let val result = cv_computeLib.cv_compute [] input
      val () = compute_require (name ^ ": wrong producer sequent")
        (null (hyp result) andalso
         aconv (concl result) (mk_eq(input,cv_num expected)))
  in ignore (Theory.save_thm(name,result)) end;
val () = List.app save_compute
  [("SIMPLE",simple,0),("NESTED",nested,6),("CAPTURE",capture,6)];
val () = Theory.export_theory ();
val () = print "COMPUTE_BINDER_ACTUAL_EXPORT_PASS\n";

val () = List.app load ["DArray","PIntMap","RawTheory_dtype"];
fun compute_module name =
  (use (compute_source ^ name ^ ".sig");
   use (compute_source ^ name ^ ".sml"));
val () = List.app compute_module
  ["ProofTraceParser","ProofTraceWalk","PFTOpcodes","PFTWriter",
   "IntPairTable","PFTCandleComputePreamble","PFTEmit","PFTReader"];
val () = PFTEmit.emit_theory
  {trace=".hol/objs/pft_compute_bindersTheory.tr.gz",
   output="compute-binders.pft.bin",binary=true,ruleset=PFTEmit.Candle};

val compute_calls = ref 0;
val compute_capture = ref false;
val compute_saves = ref ([] : string list);
val compute_fh : PFTReader.format_handler =
  {tyvar=fn _ => (),tyop=fn _ => (),const=fn _ => (),
   var=fn (_,name,_) =>
     if String.isSubstring " pft%" name then compute_capture := true else (),
   comb=fn _ => (),abs=fn _ => (),new_const=fn _ => (),new_type=fn _ => (),
   axiom=fn _ => (),save=fn (name,_) => compute_saves := name :: !compute_saves,
   load=fn _ => (),del=fn _ => (),del_range=fn _ => ()};
val compute_rh : PFTReader.ruleset_handler = fn opc => fn sr =>
  let val desc = PFTOpcodes.lookup_desc PFTOpcodes.candle_descs opc
      val () = ignore (#readVarint sr ())
      val () = ignore (PFTReader.read_raw_args desc sr)
  in if opc = 0x41 then compute_calls := !compute_calls + 1 else () end;
val _ = PFTReader.read
  {file="compute-binders.pft.bin",binary=true,
   format_handler=compute_fh,ruleset_handler=compute_rh};
val () = compute_require "missing compute commands or capture-safe binder"
  (!compute_calls = 3 andalso !compute_capture);
val () = compute_require "missing compute exports"
  (List.all (fn name => List.exists (fn saved =>
     saved = "pft_compute_binders$" ^ name) (!compute_saves))
    ["SIMPLE","NESTED","CAPTURE"]);
val () = print "COMPUTE_BINDER_FOCUSED_TESTS_PASS\n";
