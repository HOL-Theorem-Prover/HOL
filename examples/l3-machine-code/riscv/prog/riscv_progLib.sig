signature riscv_progLib =
sig
   val riscv_config: bool -> unit
   val riscv_spec: Term.term -> Thm.thm list
   val riscv_spec_hex: string -> Thm.thm list
end
