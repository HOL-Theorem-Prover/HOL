signature tttSynt =
sig

  include Abbrev

  (* debugging *)
  val ttt_synt_dir  : string ref
  val log_synt      : string -> unit 
  val log_synt_file : string -> string -> unit
  val msg_synt      : 'a list -> string -> unit
  val time_synt     : string -> ('a -> 'b) -> 'a -> 'b
  val writel_synt   : string -> string list -> unit
  
  (* conjecturing *)
  val cjenum     : 
    int -> thm ->
    int -> int ->
    (int -> term list -> term list) -> 
    term list ->
    term list * term list

end
