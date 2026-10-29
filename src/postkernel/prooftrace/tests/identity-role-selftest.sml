(* Run in a min-only tracing heap, with the prooftrace modules loaded. *)
local
  open Lib Type Term Thm

  fun require message condition =
    if condition then () else raise Fail message

  fun eq left right = list_mk_comb
    (mk_thy_const {Thy="min", Name="=",
                  Ty=type_of left --> type_of left --> bool}, [left,right])
  fun imp left right = list_mk_comb
    (mk_thy_const {Thy="min", Name="==>", Ty=bool --> bool --> bool},
     [left,right])
  fun define name rhs = #2 (gen_prim_specification
    (ASSUME (eq (mk_var(name,type_of rhs)) rhs)))

  val () = Thm.setCT "bool"
  val x = mk_var("x",bool)
  val identity = mk_abs(x,x)
  val truth_def = define "T" (eq identity identity)
  val () = register_T truth_def
  val truth = prim_mk_const {Thy="bool", Name="T"}
  val predicate = mk_var("P",alpha --> bool)
  val variable = mk_var("x",alpha)
  val forall_def = define "!"
    (mk_abs(predicate,eq predicate (mk_abs(variable,truth))))
  val () = register_forall forall_def
  val forall_const = prim_mk_const {Thy="bool", Name="!"}
  val t1 = mk_var("t1",bool)
  val t2 = mk_var("t2",bool)
  val t = mk_var("t",bool)
  val body = imp (imp t1 (imp t2 t)) t
  val forall_bool = inst [alpha |-> bool] forall_const
  val conj_def = define "/\\"
    (mk_abs(t1,mk_abs(t2,mk_comb(forall_bool,mk_abs(t,body)))))
  val () = register_conj conj_def

  fun keep first second = CONJUNCT2 (CONJ first second)
  val retained = keep truth_def (keep forall_def (keep conj_def (REFL x)))
  (* No explicit proof argument or definition mentions the conjunction. *)
  val implicit = CONJUNCT2 (CONJ (REFL x) (REFL x))
  val () = prim_delete_const {Thy="bool", Name="/\\"}
  val _ = prim_new_const {Thy="bool", Name="/\\"}
    (bool --> bool --> bool)

  val trace = ".hol/objs/boolTheory.tr.gz"
  val expected = "retired registered bool constant bool$/\\"
  fun rejects label action =
    case (action (); NONE) handle Fail message => SOME message of
        SOME message => require (label ^ ": unexpected failure: " ^ message)
          (String.isSubstring expected message)
      | NONE => raise Fail (label ^ ": accepted a retired bool connective")

  fun check (name,result) =
    let
      val () = require (name ^ ": stale final sequent")
        (uptodate_term (concl result) andalso null (hyp result))
      val () = Tracing.trace_theory "boolTheory"
        {theory="bool", parents=[], types=[],
         constants=map dest_const (thy_consts "bool"),
         all_thms=[("RESULT",result,
           {private=false, loc=RawTheory_dtype.Unknown,
            class=RawTheory_dtype.Thm})],
         anon_thms=[], mldeps=[]}
      fun convert ruleset = PFTEmit.emit_theory
        {trace=trace, output=name ^ ".pft", ruleset=ruleset}
      val () = rejects (name ^ " HOL4")
        (fn () => convert PFTEmit.HOL4)
      val () = rejects (name ^ " Candle")
        (fn () => convert PFTEmit.Candle)
      val () = rejects (name ^ " raw")
        (fn () => ProofTraceReplay.replay trace)
    in print ("PASS " ^ name ^ ": HOL4, Candle, raw rejection\n") end
in
  val () = List.app check
    [("epoch_bool_retired_definition",retained),
     ("epoch_bool_retired_implicit",implicit)]
end;
