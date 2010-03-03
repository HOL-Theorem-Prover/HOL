signature holfoot_pp_print =
sig
  include Abbrev

  (* trace "use holfoot_pp" for turning pretty printing on and off *);

  val holfoot_pretty_printer_block_indent : int ref

  val temp_add_holfoot_pp     : unit -> unit  
  val temp_remove_holfoot_pp  : unit -> unit  

  val add_holfoot_pp          : unit -> unit  
  val remove_holfoot_pp       : unit -> unit  
  val add_holfoot_pp_quiet    : unit -> unit  
  val remove_holfoot_pp_quiet : unit -> unit  

end
