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
  val donotdefines = ["K","I","S","W","C"]
  structure Q =
  struct
    open Q
    fun new_definition (a as (name,q)) =
      if List.exists (equal name)
          (List.map (fn d => d^"_DEF") donotdefines)
      then
        let
          val tm = rand(Parse.Term q)
          val c = (String.extract(name,0,SOME 1),type_of tm)
          val () = new_constant c
          val th = mk_thm([],boolSyntax.mk_eq(mk_const c,tm))
        in
          save_thm(name,th)
        end
      else Q.new_definition a
    (* for o_DEF *)
    fun new_infixr_definition (name,q,prec) =
      let
        val _ = Parse.add_infix("o",prec,Parse.RIGHT)
        val eq = Parse.Term q
        val ty = eq |> boolSyntax.lhs
                 |> boolSyntax.strip_comb |> #1 |> type_of
        val c = ("o",ty)
        val () = new_constant c
        val th = Q.GENL[`g`,`f`](mk_thm([],Parse.Term q))
      in
        save_thm(name,th)
      end
  end
  fun export_theory() = let open Lib Theory
    val _ = map (export_thm o snd) (current_theorems())
    val _ = map (export_thm o snd) (current_definitions())
    val _ = map (export_thm o snd) (current_axioms())
    val _ = stop_logging()
  in () end
end
