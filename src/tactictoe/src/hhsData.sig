signature hhsData =
sig

include Abbrev

type lbl_t = (string * real * goal * goal list)
type fea_t = string list
type feav_t = (lbl_t * fea_t)

val feav_reader : feav_t list ref

val save_lbl : lbl_t -> unit
val import_feav : string list -> feav_t list


end
