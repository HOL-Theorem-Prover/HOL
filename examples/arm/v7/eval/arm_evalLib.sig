signature arm_evalLib =
sig
  type arm_load = patriciaLib.term_ptree * (string, Arbnum.num) Redblackmap.dict

  val arm_load_empty       : arm_load

  val arm_load_from_elf    : string -> string -> arm_load -> arm_load
  val arm_load_from_file   : string -> string -> arm_load -> arm_load
  val arm_load_from_string : string -> string -> arm_load -> arm_load
  val arm_load_from_quote  : string -> string frag list -> arm_load -> arm_load

  val output_program  : string option -> patriciaLib.term_ptree -> unit

  val encode_psr      : string -> string
  val arm_eval        : string -> Term.term -> int -> Thm.thm
  val print_arm_state : Thm.thm -> unit

  (* Usage:

     * arm_load_from_elf <start address> <elf filename> <ld>
         e.g. val ld = arm_load_from_elf "0" "a.out" arm_load_empty

         Note: the elf file must be generated with "arm-elf-as -EB ..." and
               arm-elf-objdump needs to be available at your command line

     * arm_load_from_file <start address> <assembler filename> <ld>
         e.g. val ld = arm_load_from_file "A00" "code.s" arm_load_empty

     * arm_load_from_string <start address> <code string> <ptree>
         e.g. val ld = arm_load_from_string "B00" "add r1,r2" arm_load_empty

     * arm_load_from_quote <start address> <code quotation> <ptree>
         e.g. val ld = arm_load_from_quote "C00" `ascii "hello"` arm_load_empty

     * encode_psr <options>
         e.g. val s = encode_psr "n=T, q=T, it=0xBA, ge=0xE, t=T, m=fiq"
              result: val s = "8C0EBA31" : string

     * arm_eval <options> <ptree term> <max cycles>
         e.g. val prog_def =
                    arm_load_empty
                      |> arm_load_from_string "A00" "thumb\n str r1,[r0],#4"
                      |> fst
                      |> patriciaLib.Define_mk_ptree "prog";
              val t = arm_eval "r0=B00, r1=A, pc=A00, cpsr=8C0EBA31" ``prog`` 1;
              val _ = print_arm_state t

         Note: output is controlled with the trace variable "arm eval" (0--6).
  *)

end
