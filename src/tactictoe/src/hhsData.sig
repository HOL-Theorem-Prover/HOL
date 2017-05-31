signature hhsData =
sig

val hhs_read_list : (string * string list) list ref
val hht_read_list : (string * string list * string list) list ref

val read_data : string list -> 
  (string * string list) list * (string * string list * string list) list

end
