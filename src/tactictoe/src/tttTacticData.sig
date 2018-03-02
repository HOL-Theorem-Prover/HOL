signature tttTacticData =
sig

  include Abbrev

  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)

  val feature_time : real ref (* statistics *)

  val import_tacdata : string list -> unit
  val export_tacdata : string -> unit
  val update_tacdata : lbl_t -> unit (* includes orthogonalization *)

end
