signature hhsData =
sig

include Abbrev

type lbl_t = (string * real * goal * goal list)
type fea_t = string list
type feav_t = (lbl_t * fea_t)

val data_glob : feav_t list ref
val data2_glob : (string * (int * int)) list ref

val save_lbl : lbl_t -> unit
val read_fea : string list -> feav_t list
val read_succ : string list -> (string * (int * int)) list

val hhs_ortho_flag : bool ref

end
