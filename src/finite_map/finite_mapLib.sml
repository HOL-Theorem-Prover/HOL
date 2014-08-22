structure finite_mapLib :> finite_mapLib =
struct

  open HolKernel boolLib

  val ERR = mk_HOL_ERR "finite_mapLib"

local open finite_mapTheory finite_mapSyntax pred_setTheory simpLib in

val add_finite_map_compset = computeLib.add_thms
  [o_f_FEMPTY
  ,FLOOKUP_EMPTY
  ,FLOOKUP_UPDATE
  ,FLOOKUP_FUNION
  ,DOMSUB_FLOOKUP_THM
  ,FUNION_FEMPTY_1
  ,FUNION_FEMPTY_2
  ,FUNION_FUPDATE_1
  ,FUPDATE_LIST_THM
  ,FDOM_FUPDATE
  ,FDOM_FEMPTY
  ]

val FEVERY_cs = computeLib.bool_compset ()
val _         = computeLib.add_thms
                           [FEVERY_FEMPTY, DRESTRICT_FEMPTY,
			    FEVERY_FUPDATE, IN_INSERT,
			    NOT_IN_EMPTY,
			    FEVERY_DRESTRICT_COMPL] FEVERY_cs;

fun fevery_EXPAND_CONV t =
let
   val _ = if (is_fevery t) then () else raise UNCHANGED;
   val thm = computeLib.CBV_CONV FEVERY_cs t
in
   thm
end;

local
   fun add_fup ([], []) kL2 thm = thm
     | add_fup (k::kL, v::vL) kL2 thm =
       let
          val c = concl thm
          val ks = rand c
          val f2 = (rand o rator) c
          val f1 = (rand o rator o rator) c

          val (kL2, inkL2) = (snd (Lib.pluck (fn x => x = k) kL2), true) handle HOL_ERR _ =>
                             (kL2, false)
          val inkL = mem k kL
          val kL2 = if inkL then k::kL2 else kL2;
          val imp_thm = if inkL then fmap_EQ_UPTO___FUPDATE_SING else
               if inkL2 then
                  fmap_EQ_UPTO___FUPDATE_BOTH
               else
                  fmap_EQ_UPTO___FUPDATE_BOTH___NO_DELETE

          val imp_thm_inst = ISPECL [f1,f2, ks, k, v] imp_thm
          val thm1 = MP imp_thm_inst thm

       in
          add_fup (kL, vL) kL2 thm1
       end
     | add_fup _ kL2 thm = Feedback.fail ();

   val emp_conv =
        simpLib.SIMP_CONV (boolSimps.bool_ss++boolSimps.CONJ_ss) [EXTENSION, NOT_IN_EMPTY, IN_DELETE, IN_INSERT]
in


fun fupdate_NORMALISE_CONV t =
let
   val (base, kvL) = strip_fupdate t
   val (kL,vL) = unzip (map pairSyntax.dest_pair kvL)

   val typed_empty_tm =
        Term.inst [alpha |-> fst (finite_mapSyntax.dest_fmap_ty (type_of base))] pred_setSyntax.empty_tm

   val thm0 = ISPECL [typed_empty_tm, base] fmap_EQ_UPTO___EQ
   val thm1 = add_fup (kL, vL) [] thm0
   val emp_thm = EQT_ELIM (emp_conv (mk_eq ((rand o concl) thm1, typed_empty_tm)));

   val thm2 = CONV_RULE (RAND_CONV (K emp_thm) THENC
                         REWR_CONV fmap_EQ_UPTO___EMPTY) thm1
in
   thm2
end;

end;

end;

end;
