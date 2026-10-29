(* Run each case in a fresh min-only tracing heap. *)
local
  open Lib Type Term Thm
  val custom = OS.Process.getEnv "HOL_PFT_IDENTITY_PHASE" = SOME "custom-role"
  val thy = if custom then "identity_custom_role" else "bool"
  fun name s = if custom then "custom_" ^ s else s
  fun eq left right = list_mk_comb
    (mk_thy_const {Thy="min",Name="=",
      Ty=type_of left --> type_of left --> bool},[left,right])
  fun imp left right = list_mk_comb
    (mk_thy_const {Thy="min",Name="==>",Ty=bool --> bool --> bool},
     [left,right])
  fun define nm rhs = #2 (gen_prim_specification
    (ASSUME (eq (mk_var(name nm,type_of rhs)) rhs)))
  fun constant nm = prim_mk_const {Thy=thy,Name=name nm}
  val () = Thm.setCT thy
  val x = mk_var("x",bool)
  val identity = mk_abs(x,x)
  val truth_def = define "T" (eq identity identity)
  val () = register_T truth_def
  val predicate = mk_var("P",alpha --> bool)
  val variable = mk_var("x",alpha)
  val forall_def = define "!"
    (mk_abs(predicate,eq predicate (mk_abs(variable,constant "T"))))
  val () = register_forall forall_def
  val t1 = mk_var("t1",bool)
  val t2 = mk_var("t2",bool)
  val t = mk_var("t",bool)
  val body = imp (imp t1 (imp t2 t)) t
  val forall_bool = inst [alpha |-> bool] (constant "!")
  val conj_def = define "/\\"
    (mk_abs(t1,mk_abs(t2,mk_comb(forall_bool,mk_abs(t,body)))))
  val () = register_conj conj_def

  (* Only the intermediate sequent mentions the registered conjunction. *)
  val result = CONJUNCT2 (CONJ (REFL x) (REFL x))
  val () = if custom then () else
    (prim_delete_const {Thy=thy,Name="/\\"};
     ignore (prim_new_const {Thy=thy,Name="/\\"}
       (bool --> bool --> bool)))
  val () = if null (hyp result) andalso aconv (concl result) (concl (REFL x))
           then () else raise Fail "logical-role final sequent changed"
  val () = Tracing.trace_theory (thy ^ "Theory")
    {theory=thy,parents=[],types=Type.thy_types thy,
     constants=map Term.dest_const (Term.thy_consts thy),
     all_thms=[("RESULT",result,
       {private=false,loc=RawTheory_dtype.Unknown,class=RawTheory_dtype.Thm})],
     anon_thms=[],mldeps=[]}
  val expected = if custom then "ProofTraceWalk: noncanonical logical role "
                 else "ProofTraceParser: retired registered bool constant "
  val trace = ".hol/objs/" ^ thy ^ "Theory.tr.gz"
  fun rejects action =
    if ((action (); false) handle Fail message => String.isPrefix expected message)
    then () else raise Fail "unsupported registered role was accepted"
in
  val () = rejects (fn () => ProofTraceReplay.replay trace)
  val () = List.app (fn ruleset => rejects (fn () => PFTEmit.emit_theory
    {trace=trace,output="role.pft",ruleset=ruleset}))
    [PFTEmit.HOL4,PFTEmit.Candle]
  val () = print "IDENTITY_LOGICAL_ROLE_REJECTION_PASS\n"
end;
