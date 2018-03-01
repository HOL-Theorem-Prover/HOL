signature hhsTacticData =
sig

  include Abbrev

  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)

  (* statistics for hhsRecord *)
  val feature_time : real ref

  (* update *)
  val save_lbl : lbl_t -> unit

  (* I/O *)
  val export_tacfea : string -> unit
  val import_feavl : string list -> feav_t list


  
end
