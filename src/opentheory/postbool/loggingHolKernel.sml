structure HolKernel =
struct
  open HolKernel Logging
  fun new_theory s = let
    val _ = HolKernel.new_theory s
    val _ = start_logging s
    fun th {Thy,Tyop} =
      case (Thy,Tyop) of
          ("min", "fun") => ([], "->")
        | ("min", "bool") => ([], "bool")
        | _ => (["HOL4",Thy],Tyop)
    fun ch {Thy,Name} =
      case (Thy,Name) of
          ("min", "=") => ([], "=")
        | ("arithmetic", "NUMERAL") => (["Unwanted"],"id")
        | _ => (["HOL4",Thy],Name)
    val _ = set_tyop_name_handler th
    val _ = set_const_name_handler ch
  in () end

  fun export_theory() = let
    open Lib Theory
    val directives = Logging.read_otdfile (current_theory() ^ ".otd")
                                          handle IO.Io _ => []
    fun prepare (nm, th) =
      (if Lib.mem (DeleteProof, nm) directives
       then Thm.delete_proof th else ();
       if Lib.mem (SkipThm, nm) directives
       then NONE else SOME th)
    val defs' = List.mapPartial prepare (current_definitions())
    val ths' = List.mapPartial prepare (current_theorems())
    val axs' = List.mapPartial prepare (current_axioms())
    val _ = List.app (ignore o export_thm) defs'
    val _ = List.app (ignore o export_thm) ths'
    val _ = List.app (ignore o export_thm) axs'
    val _ = stop_logging()
  in () end
end
