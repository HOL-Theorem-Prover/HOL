(*---------------------------------------------------------------------------*
 * Setting information for types.                                            *
 *                                                                           *
 * Here we fill in the "size" entries in theTypeBase for some types that     *
 * are non-recursive and built before numbers. Also add some lifters.        *
 *---------------------------------------------------------------------------*)

structure basicSize =
struct

local
  open HolKernel boolLib Parse basicSizeTheory basicSizeSyntax

  (*----------------------------------------------------------------------*)
  (* Booleans                                                             *)
  (*----------------------------------------------------------------------*)

  val bool_info = Option.valOf (TypeBase.read {Thy="min", Tyop = "bool"});
  val bool_size_info = (bool_size_tm,TypeBasePure.ORIG bool_size_def)
  val ty = mk_vartype "'type"
  val tm = mk_vartype "'term"
  val lift_bool_var = mk_var("boolSyntax.lift_bool",ty --> bool --> tm)
  val bool_info' =
      bool_info
          |> TypeBasePure.put_size bool_size_info
          |> TypeBasePure.put_lift lift_bool_var
          |> TypeBasePure.add_rewrs [bool_size_def]

  (*----------------------------------------------------------------------*)
  (* Products                                                             *)
  (*----------------------------------------------------------------------*)

  val prod_size_info = (pair_size_tm,TypeBasePure.ORIG pair_size_def)
  val prod_info' =
      TypeBase.read {Tyop="prod", Thy="pair"}
         |> Option.valOf
         |> TypeBasePure.put_size prod_size_info
         |> TypeBasePure.add_rewrs [pair_size_def,min_pair_size_def]

  (*----------------------------------------------------------------------*)
  (* Sums                                                                 *)
  (*----------------------------------------------------------------------*)

  val sum_size_info = (full_sum_size_tm,TypeBasePure.ORIG full_sum_size_thm)
  val sum_info' =
      TypeBase.read {Tyop="sum", Thy="sum"}
         |> Option.valOf
         |> TypeBasePure.put_size sum_size_info
         |> TypeBasePure.add_rewrs [sum_size_def,full_sum_size_thm]

  (*----------------------------------------------------------------------*)
  (* Unit type                                                            *)
  (*----------------------------------------------------------------------*)

  val one_info = Option.valOf (TypeBase.read {Tyop="one",Thy="one"})
  val one_size_info = (one_size_tm,TypeBasePure.ORIG one_size_def)
  val ty = mk_vartype "'type"
  val tm = mk_vartype "'term"
  val lift_one_var = mk_var("oneSyntax.lift_one", ty --> oneSyntax.one_ty --> tm)
  val one_info' =
      one_info
         |> TypeBasePure.put_size one_size_info
         |> TypeBasePure.put_lift lift_one_var
         |> TypeBasePure.add_rewrs [one_size_def]

  (*----------------------------------------------------------------------*)
  (* "Itself" type                                                        *)
  (*----------------------------------------------------------------------*)

  val itself_info = Option.valOf (TypeBase.read {Tyop="itself",Thy="bool"})
  val itself_size_info = (itself_size_tm,TypeBasePure.ORIG itself_size_def)
  val itself_info' =
      itself_info
         |> TypeBasePure.put_size itself_size_info
         |> TypeBasePure.add_rewrs [itself_size_def]

  (*----------------------------------------------------------------------*)
  (* Options                                                              *)
  (*----------------------------------------------------------------------*)

  val option_info = Option.valOf (TypeBase.read {Tyop="option", Thy="option"})
  val option_size_info = (option_size_tm,TypeBasePure.ORIG option_size_def)
  val option_info' =
      option_info
         |> TypeBasePure.put_size option_size_info
         |> TypeBasePure.add_rewrs [option_size_def]
in
   val _ = TypeBase.write [bool_info']
   val _ = TypeBase.write [prod_info']
   val _ = TypeBase.write [sum_info']
   val _ = TypeBase.write [one_info']
   val _ = TypeBase.write [itself_info']
   val _ = TypeBase.write [option_info']
end

end
