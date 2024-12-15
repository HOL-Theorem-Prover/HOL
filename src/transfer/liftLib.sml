structure liftLib :> liftLib =
struct

open HolKernel boolLib

open liftingTheory
val funQ' = CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) funQ
val HK_thm2' = HK_thm2 |> Q.GEN ‘f’ |> CONV_RULE Unwind.UNWIND_FORALL_CONV

fun grt th1 th2 = resolve_then.gen_resolve_then Any th1 th2 I

fun tidy_tyvars th =
  let val tyvs = type_vars_in_term (concl th)
      val newvs =
        List.tabulate(length tyvs,
                      fn i => mk_vartype("'" ^ str (Char.chr(i + 97))))
  in
      INST_TYPE (ListPair.map(fn (ty1,ty2) => ty1 |-> ty2) (tyvs, newvs)) th
  end

val thmset_rec = ThmSetData.export_list {initial = [], settype = "liftQt"}
val QtDB = #getDB thmset_rec

fun dofirst f [] = raise mk_HOL_ERR "" "" ""
  | dofirst f (x::xs) = f x handle HOL_ERR _ => dofirst f xs

fun opxfer res_th = let
  val qts = QtDB ()
  val hk = grt res_th HK_thm2' |> repeat (grt funQ')
  val qts_applied = repeat (fn th => dofirst (C grt th) qts) hk
in
  qts_applied
    |> repeat (grt idQ) |> tidy_tyvars
    |> CONV_RULE (REPEATC Unwind.UNWIND_FORALL_CONV)
end

fun liftdef respth nm =
  let
    val xfer = opxfer respth
    val defrhs = rand (concl xfer)
    val cvar = mk_var(nm, type_of defrhs)
    val def = new_definition (nm ^ "_def", mk_eq(cvar, defrhs))
    val relates = save_thm(nm ^ "_relates[transfer_rule]",
                           REWRITE_RULE [SYM def] xfer)
  in
    (def, relates)
  end

end
