signature emit_eval =
sig

  type run_trace =
    { cycle : bool, pc : bool, ireg : bool, regs : bool, mem : bool,
      rule : (int * char) }

  type arm_mem = armML.word8 patriciaML.ptree

  val traceOut : TextIO.outstream ref

  val instruction_printer : (string *
                            (armML.Encoding *
                            (armML.word4 *
                             armML.ARMinstruction)) -> unit) ref

  val print_arm_mem      : arm_mem -> unit
  val print_diff_arm_mem : arm_mem -> arm_mem -> unit

  val arm_run : run_trace -> armML.word8 patriciaML.ptree -> string -> int ->
                string * (arm_mem * armML.arm_state) option

  val main    : unit -> unit

  (*
    usage:

    arm_run
      trace    (*  select updates to print                 *)
      prog     (*  main memory ptree                       *)
      options  (*  e.g. arch = armv4, pc = A00, cpsr = 10  *)
      count    (*  max number of cycles, -ve for unbounded *)

      ->

      (message, final state)
  *)

end
