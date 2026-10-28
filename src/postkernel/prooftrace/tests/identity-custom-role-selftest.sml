(* Supplemental minimal-kernel guard: the final sequent is reflexive, while
   its intermediate conjunction uses a noncanonical registered name. *)
local
  open Lib Type Term Thm
  fun eq left right = list_mk_comb
    (mk_thy_const {Thy="min",Name="=",
      Ty=type_of left --> type_of left --> bool},[left,right])
  fun imp left right = list_mk_comb
    (mk_thy_const {Thy="min",Name="==>",Ty=bool --> bool --> bool},
     [left,right])
  fun define name rhs = #2 (gen_prim_specification
    (ASSUME (eq (mk_var(name,type_of rhs)) rhs)))
  val () = Theory.new_theory "identity_custom_role"
  val x = mk_var("x",bool)
  val identity = mk_abs(x,x)
  val truth_def = define "custom_truth" (eq identity identity)
  val () = register_T truth_def
  val truth = prim_mk_const {Thy="identity_custom_role", Name="custom_truth"}
  val predicate = mk_var("P",alpha --> bool)
  val variable = mk_var("x",alpha)
  val forall_def = define "custom_forall"
    (mk_abs(predicate,eq predicate (mk_abs(variable,truth))))
  val () = register_forall forall_def
  val forall_const = prim_mk_const {Thy="identity_custom_role", Name="custom_forall"}
  val t1 = mk_var("t1",bool)
  val t2 = mk_var("t2",bool)
  val t = mk_var("t",bool)
  val body = imp (imp t1 (imp t2 t)) t
  val forall_bool = inst [alpha |-> bool] forall_const
  val conj_def = define "custom_conj"
    (mk_abs(t1,mk_abs(t2,mk_comb(forall_bool,mk_abs(t,body)))))
  val () = register_conj conj_def


  val result = CONJUNCT2 (CONJ (REFL x) (REFL x))
  val () = if null (hyp result) andalso aconv (concl result) (concl (REFL x))
           then () else raise Fail "custom-role final sequent changed"
  val () = Tracing.trace_theory "identity_custom_roleTheory"
    {theory="identity_custom_role",parents=[],
     types=Type.thy_types "identity_custom_role",
     constants=map Term.dest_const (Term.thy_consts "identity_custom_role"),
     all_thms=[("RESULT",result,
       {private=false,loc=RawTheory_dtype.Unknown,class=RawTheory_dtype.Thm})],
     anon_thms=[],mldeps=[]}
  val trace = ".hol/objs/identity_custom_roleTheory.tr.gz"
  fun rejects action =
    if ((action (); false) handle Fail message =>
        String.isPrefix "ProofTraceWalk: noncanonical logical role " message)
    then () else raise Fail "custom registered role was accepted"
in
  val () = rejects (fn () => PFTEmit.emit_theory
    {trace=trace,output="custom-role-hol.pft.bin",ruleset=PFTEmit.HOL4})
  val () = rejects (fn () => PFTEmit.emit_theory
    {trace=trace,output="custom-role-candle.pft.bin",ruleset=PFTEmit.Candle})
  val () = rejects (fn () => ProofTraceReplay.replay trace)
  val () = print "IDENTITY_CUSTOM_ROLE_EXPLICIT_REJECTION_PASS\n"
end;
