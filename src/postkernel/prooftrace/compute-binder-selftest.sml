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
val compute_cases =
  [("SIMPLE",simple,cv_num 0),("NESTED",nested,cv_num 6),
   ("CAPTURE",capture,cv_num 6)];
fun save_compute (name,input,expected) =
  let val result = cv_computeLib.cv_compute [] input
      val () = compute_require (name ^ ": wrong producer sequent")
        (null (hyp result) andalso
         aconv (concl result) (mk_eq(input,expected)))
  in ignore (Theory.save_thm(name,result)) end;
val () = List.app save_compute compute_cases;

(* COMB(f,x) and ABS(f,x) are distinct nodes with an identical child pair.
   Keep the COMB proof before SUBST traverses the ABS template. *)
val kind_f = mk_var("f",bool --> bool);
val kind_x = mk_var("kind_x",bool);
val kind_comb = mk_comb(kind_f,kind_x);
val kind_abs = mk_abs(kind_f,kind_x);
val kind_source = CONJUNCT2 (CONJ (REFL kind_comb) (REFL kind_abs));
val kind_result = Thm.SUBST [kind_x |-> REFL kind_x]
  (concl kind_source) kind_source;
val () = compute_require "wrong COMB/ABS discriminator producer sequent"
  (null (hyp kind_result) andalso
   aconv (concl kind_result) (mk_eq(kind_abs,kind_abs)));
val () = ignore (Theory.save_thm("KIND_COLLISION",kind_result));
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

val () = List.app load ["DArray","PIntMap","RawTheory_dtype"];
fun compute_module name =
  (use (compute_source ^ name ^ ".sig");
   use (compute_source ^ name ^ ".sml"));
val () = List.app compute_module
  ["ProofTraceParser","ProofTraceWalk","PFTOpcodes","PFTWriter",
   "IntPairTable","PFTCandleComputePreamble","PFTEmit","PFTReader"];
val () = let
  open ProofTraceParser
  val (root,heap) = parse ".hol/objs/pft_compute_bindersTheory.tr.gz"
  val {all_thms,...} = shRoot heap root
  val closures = ref 0
  val kind_closure = ref false
  fun input th = case shProof heap (#3 (shThm heap th)) of
      save_dep_prf p => input p
    | Mark_prf (_,p) => input p
    | compute_prf (_,tm) => tm
    | _ => raise Fail "expected a genuine compute proof"
  val () = appList heap (fn p => let
    val (name,(th,_)) = tuple3 heap (str heap,Lib.I,Lib.I) p
  in if name = "KIND_CAPTURE" then
       let val (_,conclusion,_) = shThm heap th
           val lhs = case shTerm heap conclusion of
               Comb (f,_) => (case shTerm heap f of
                   Comb (_,l) => l
                 | _ => raise Fail "expected equality")
             | _ => raise Fail "expected equality"
       in case shTerm heap lhs of
            Clos _ => kind_closure := true
          | _ => raise Fail "KIND_CAPTURE: expected a raw closure"
       end
     else if String.isPrefix "CLOSURE" name orelse
        String.isPrefix "NUM_" name then
       (case shTerm heap (input th) of
          Clos _ => closures := !closures + 1
        | _ => raise Fail (name ^ ": expected a raw closure"))
     else () end) all_thms
in compute_require "missing raw compute closures"
     (!closures = 0 andalso !kind_closure) end;
val () = PFTEmit.emit_theory
  {trace=".hol/objs/pft_compute_bindersTheory.tr.gz",
   output="compute-binders.pft.bin",binary=true,ruleset=PFTEmit.Candle};

val compute_calls = ref 0;
val compute_capture = ref false;
val compute_combs = ref ([] : (int * int) list);
val compute_kind_collision = ref false;
val compute_collision_abs = ref ([] : int list);
val compute_plain_f = ref ~1;
val compute_no_false_capture = ref false;
val compute_saves = ref ([] : string list);
val compute_fh : PFTReader.format_handler =
  {tyvar=fn _ => (),tyop=fn _ => (),const=fn _ => (),
   var=fn (id,name,_) =>
     (if String.isSubstring " pft%" name then compute_capture := true else ();
      if name = "f" then compute_plain_f := id else ()),
   comb=fn (_,f,x) => compute_combs := (f,x) :: !compute_combs,
   abs=fn (id,v,b) =>
     (if List.exists (fn pair => pair = (v,b)) (!compute_combs)
      then (compute_kind_collision := true;
            compute_collision_abs := id :: !compute_collision_abs) else ();
      if v = !compute_plain_f andalso
         List.exists (fn inner => inner = b) (!compute_collision_abs)
      then compute_no_false_capture := true else ()),
   new_const=fn _ => (),new_type=fn _ => (),
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
  (!compute_calls = length compute_cases andalso !compute_capture);
val () = compute_require "COMB/ABS child-pair collision was not exercised"
  (!compute_kind_collision);
val () = compute_require "bound f was incorrectly counted free"
  (!compute_no_false_capture);
val () = compute_require "missing compute exports"
  (List.all (fn name => List.exists (fn saved =>
     saved = "pft_compute_binders$" ^ name) (!compute_saves))
    ("KIND_COLLISION" :: "KIND_CAPTURE" :: map #1 compute_cases));
val () = print "COMPUTE_BINDER_FOCUSED_TESTS_PASS\n";
