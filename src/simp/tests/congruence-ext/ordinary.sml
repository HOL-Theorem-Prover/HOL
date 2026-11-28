(* Fresh ordinary-only process: do not import the extension selftest. *)
open HolKernel boolSyntax testutils
val checks = ref 0
fun check name ok =
  (checks := !checks + 1; tprint name;
   if ok then OK () else die name)
fun eqrefl {Rinst,arg} = REFL arg
val a = mk_var ("a",bool)
val b = mk_var ("b",bool)
val f = mk_var ("f",bool --> bool)
val cong = DISCH (mk_eq (a,b)) (AP_TERM f (ASSUME (mk_eq (a,b))))
val tm = mk_comb (f,a)
val cv = Opening.CONGPROC eqrefl cong equality
  {solver=ASSUME,freevars=[],depther=fn _ => REFL}
val th = cv tm
val _ = check "ordinary CONGPROC preserves conclusion and hypotheses"
  (aconv (concl th) (mk_eq (tm,tm)) andalso null (hyp th))
val th2 = cv tm
val _ = check "saved ordinary CONGPROC proof on reuse"
  (aconv (concl th2) (concl th) andalso null (hyp th2))
val Travrules.TRAVRULES {congprocs,weakenprocs,relations} =
  Travrules.mk_travrules [Travrules.EQ_preorder] [cong]
val _ = check "ordinary builder constructs only requested rules"
  (length congprocs = 1 andalso null weakenprocs andalso
   length relations = 1)
fun forbidden s = List.exists (fn n => s = n)
  ["TraverseExt","Cond_rewrExt",
   "simpExtLib","congExtLib","simpLib","congLib"]
val modules = Meta.loaded ()
val _ = print ("ORDINARY_LOADED " ^ String.concatWith "," modules ^ "\n")
val _ = check "ordinary primitives load no extension machinery"
  (not (List.exists forbidden modules))
val _ = print ("Ordinary congruence focused checks: " ^
               Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success
