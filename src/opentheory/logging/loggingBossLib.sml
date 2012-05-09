structure bossLib =
struct
  open bossLib Logging
  fun new_theory s = let
    val _ = HolKernel.new_theory s
    val _ = start_logging()
    fun th {Thy,Tyop} = if Thy = s then ([Thy],Tyop) else raise Match
    fun ch {Thy,Name} = if Thy = s then ([Thy],Name) else raise Match
    val _ = set_tyop_name_handler th
    val _ = set_const_name_handler ch
  in () end
  fun export_theory() = let open Lib Theory
    val _ = map (export_thm o snd) (current_theorems())
    val _ = map (export_thm o snd) (current_definitions())
    val _ = map (export_thm o snd) (current_axioms())
    val _ = stop_logging()
  in HolKernel.export_theory() end
end
