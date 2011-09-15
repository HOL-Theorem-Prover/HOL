structure bossLib =
struct
  open bossLib Logging
  val new_theory = start_logging o HolKernel.new_theory
  val store_thm = export_thm o Tactical.store_thm
  val export_theory = HolKernel.export_theory o stop_logging
  val Define = fn q => Define q before log_definitions()
  val Hol_datatype = fn q => Hol_datatype q before log_definitions()
  val Hol_reln = fn q => Hol_reln q before log_definitions()
  val xHol_reln = fn s => fn q => xHol_reln s q before log_definitions()
end
