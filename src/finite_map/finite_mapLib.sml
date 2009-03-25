structure finite_mapLib :> finite_mapLib =
struct

  open HolKernel boolLib

  val ERR = mk_HOL_ERR "finite_mapLib"

  local open finite_mapTheory finite_mapSyntax pred_setTheory in 


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



end;
end;



