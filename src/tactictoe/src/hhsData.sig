signature hhsData =
sig

  include Abbrev

  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)

  val feature_time : real ref
  val save_lbl : lbl_t -> unit

  val export_feavl : string -> feav_t list -> unit
  val import_feavl : string list -> feav_t list

  val import_mc : string list -> unit
  val export_mc : string -> unit
  
end
