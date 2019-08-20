signature FlagDB =
sig

  type t
  type 'a tag
  val empty : t
  val peek : t -> 'a tag -> string -> ('a * string) option
  val update : string -> ('a tag * 'a) -> t -> t
  val update_new : {desc: string, name : string} -> 'a tag * 'a -> t -> t
  val keys : t -> {key : string, desc : string} list

  val string : string tag
  val int : int tag
  val bool : bool tag
  val stringopt : string option tag
  val mkTag : string -> 'a tag
end
