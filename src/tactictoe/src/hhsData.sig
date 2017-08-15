signature hhsData =
sig

include Abbrev

type lbl_t = (string * real * goal * goal list)
type fea_t = string list
type feav_t = (lbl_t * fea_t)

val feature_time : real ref
val save_lbl : lbl_t -> unit

val export_feav : feav_t list -> unit
val import_feav : string list -> feav_t list


end
