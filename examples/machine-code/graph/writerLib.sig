signature writerLib =
sig

  val close_current : unit -> unit
  val open_current : string -> unit
  val reset_graph_file : unit -> unit
  val set_base : string -> unit
  val write_blank_line : unit -> unit
  val write_graph : string -> unit
  val write_indented_block : string -> unit
  val write_line : string -> unit
  val write_section : string -> unit
  val write_subsection : string -> unit
  val write_term : Term.term -> unit
  val write_thm : Thm.thm -> unit
  val write_txt_and_print : string -> unit
  val writer_prints : bool ref

end
