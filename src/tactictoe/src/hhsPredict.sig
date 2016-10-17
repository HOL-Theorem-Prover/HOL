signature hhsPredict =
sig

  include Abbrev
  val hhs_nolengthpen_flag : bool ref
  val learn_tfidf : 
    (string * string list) list -> (string, real) Redblackmap.dict
  val fast_learn_tfidf:
    int ->
    (string, int) Redblackmap.dict -> 
    string list -> 
    (string, real) Redblackmap.dict
  val knn_self_distance  : 
    int -> 
    (string, real) Redblackmap.dict ->
    string list -> 
    real
  val knn_sort    : 
    (string, real) Redblackmap.dict ->
    (string * string list) list -> 
    string list -> 
    (string * string list) list
  val knn_shark :
    string -> 
    int -> 
    (string, real) Redblackmap.dict ->
    (string * string list) list -> 
    string list -> 
    string list
  val knn_score  :
    (string, real) Redblackmap.dict ->
    int -> 
    (string * string list) list -> 
    string list -> 
    (string * real) list
  val knn      : 
    (string, real) Redblackmap.dict ->
    int -> 
    (string * string list) list -> 
    string list -> 
    string list
  val knn_ext :
    int -> (string * string list * string list) list -> string list -> 
    string list
  val tknn_ext :
    int -> (string * string list * string list) list -> string list -> 
    string list


end
