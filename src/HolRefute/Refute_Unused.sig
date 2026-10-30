signature Refute_Unused = sig
  type config = Refute_Core.config
  type thm = Thm.thm

  val check_unused_assms :
    config -> string * thm -> string * int list list option
  val find_unused_assms :
    config -> string -> (string * int list list option) list
  val print_unused_assms : config -> string option -> unit
end
