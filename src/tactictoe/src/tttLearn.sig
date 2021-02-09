signature tttLearn =
sig

  include Abbrev

  type thmdata = mlThmData.thmdata
  type loc = mlTacticData.loc
  type call = mlTacticData.call
  type tacdata = mlTacticData.tacdata
  type symweight = mlFeature.symweight

  val pred_svar : int -> goal -> string list

  val ortho_predstac_time : real ref
  val ortho_predthm_time : real ref
  val ortho_teststac_time : real ref
  val orthogonalize : (thmdata * tacdata *
    (symweight * (string * mlFeature.fea) list)) ->
    ((goal * goal list) * (loc * call)) -> (loc * call)

end
