signature Globals =
sig

  val HOLDIR                  : string
  val release                 : string
  val version                 : int

  val goal_line               : string ref
  val oldify                  : int -> string -> string
  val linewidth               : int ref
  val max_print_depth         : int ref
  val max_print_length        : int ref

  val checking_type_names     : bool ref
  val checking_const_names    : bool ref

  val interactive             : bool ref
  val print_thy_loads         : bool ref
  val dumpheap_on_failure     : bool ref

  val hol_clock               : Timer.cpu_timer
  val emitMLDir               : string ref
  val emitCAMLDir             : string ref
end
