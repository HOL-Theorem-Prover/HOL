structure HolKernel =
struct
  open HolKernel Logging
  fun new_theory s = let
    val _ = HolKernel.new_theory s
    val _ = start_logging()
    fun th {Thy,Tyop} = (["HOL4",Thy],Tyop)
    fun ch {Thy,Name} = (["HOL4",Thy],Name)
    val _ = set_tyop_name_handler th
    val _ = set_const_name_handler ch
  in () end
  val donotdefines = ["transitive","TC","WF","RSUBSET","RUNION","RINTER","RUNIV"]
  val dnd = List.map (fn d => d^"_def") donotdefines @
            List.map (fn d => d^"_DEF") donotdefines @
            donotdefines
  structure Q =
  struct
    open HolKernel Q
    fun new_definition (a as (name,q)) =
      if List.exists (equal name) dnd
      then
        let
          val (l,r) = boolSyntax.dest_eq(Parse.Term q)
          val (v,args) = strip_comb l
          val () = new_constant (dest_var v)
          val th = Drule.GEN_ALL(mk_thm([],Parse.Term q))
        in
          save_thm(name,th)
        end
      else Q.new_definition a
  end
  fun new_definition (a as (name,tm)) =
    if List.exists (equal name) dnd
    then
      let
        val (l,r) = boolSyntax.dest_eq tm
        val (v,args) = strip_comb l
        val c = dest_var v
        val () = new_constant c
        val l' = list_mk_comb(mk_const c,args)
        val th = Drule.GEN_ALL(mk_thm([],boolSyntax.mk_eq(l',r)))
      in
        save_thm(name,th)
      end
    else HolKernel.new_definition a
  fun export_theory() = let open Lib Theory
    val _ = map (export_thm o snd) (current_theorems())
    val _ = map (export_thm o snd) (current_definitions())
    val _ = map (export_thm o snd) (current_axioms())
    val _ = stop_logging()
  in () end
end
