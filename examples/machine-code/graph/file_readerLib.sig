signature file_readerLib =
sig

  datatype arch = ARM | ARM8 | M0 | RISCV

  val arch_name : arch ref
  val int_to_hex : int -> string
  val get_tools : unit -> helperLib.decompiler_tools
  val arm_spec : string -> helperLib.instruction
  val arm8_spec : string -> helperLib.instruction
  val m0_spec : string -> helperLib.instruction
  val riscv_spec : string -> helperLib.instruction
  val read_files : string -> string list -> unit
  val section_body : string -> (int * string * string) list
  val section_io : string -> int list * int * bool
  val section_location : string -> string
  val section_names : unit -> string list
  val show_annotated_code : (int -> string) -> string -> unit
  val show_code : string -> unit

  val tysize : unit -> Type.hol_type
  val wsize  : unit -> Type.hol_type

end
