structure bossLib =
struct
  open bossLib Logging
  val new_theory = start_logging o HolKernel.new_theory
  fun export_theory() = let open Lib Theory
    val _ = map (export_thm o snd) (current_theorems())
    val _ = map (export_thm o snd) (current_definitions())
    val _ = map (export_thm o snd) (current_axioms())
    val _ = stop_logging()
  in HolKernel.export_theory() end
  val Define = fn q => Define q before log_definitions()
  val Hol_datatype = fn q => Hol_datatype q before log_definitions()
  val Hol_reln = fn q => Hol_reln q before log_definitions()
  val xHol_reln = fn s => fn q => xHol_reln s q before log_definitions()
end
