signature tttGoallistData =
sig

include Abbrev

  val export_glfea : string -> unit
  val import_glfea : string list -> unit
  val update_glfea : int list -> (bool * int) -> unit

end
