(*---------------------------------------------------------------------------*
 * Setting information for types.                                            *
 *                                                                           *
 * Here we fill in the "size" entries in theTypeBase for some types that     *
 * are non-recursive and built before numbers.                               *
 *---------------------------------------------------------------------------*)

structure NonRecSize =
struct

local
  open HolKernel boolLib Parse pairSyntax numSyntax
  infix |->; infixr -->;

  local open pairTheory sumTheory optionTheory arithmeticTheory in end;

  val bool_info = Option.valOf (TypeBase.read "bool");
  val bool_size_info = (rator(mk_bool_case(zero_tm,zero_tm,mk_arb bool)),
                        TypeBasePure.ORIG boolTheory.bool_case_ID)
  val bool_info' = TypeBasePure.put_size bool_size_info bool_info

  val prod_size_info =
    (let val f = mk_var("f", alpha --> num)
         val g = mk_var("g", beta --> num)
         val x = mk_var("x", alpha)
         val y = mk_var("y", beta)
     in list_mk_abs([f,g],
          mk_pabs(mk_pair(x,y),mk_plus(mk_comb(f,x),mk_comb(g,y))))
     end,
     TypeBasePure.ORIG pairTheory.UNCURRY_DEF)

  val prod_info' = TypeBasePure.put_size prod_size_info 
                     (Option.valOf (TypeBase.read"prod"))

  val sum_info = Option.valOf(TypeBase.read "sum");
  val sum_case = prim_mk_const{Name="sum_case", Thy="sum"}
  val num = numSyntax.num
  val sum_case_into_num = inst [alpha |-> num] sum_case
  val f = mk_var("f",beta --> num)
  val g = mk_var("g",gamma --> num)
  val s = mk_var("s",mk_thy_type{Tyop="sum",Thy="sum",Args=[beta, gamma]})
  val tm = list_mk_abs ([f,g,s], list_mk_comb(sum_case_into_num,[f,g,s]))
  val sum_size_info = (tm,TypeBasePure.ORIG sumTheory.sum_case_def)
  val sum_info' = TypeBasePure.put_size sum_size_info sum_info

  val option_info = Option.valOf (TypeBase.read "option")
  val option_case_tm = prim_mk_const{Name="option_case",Thy="option"}
  val option_size_info =
       (let val f = mk_var("f",alpha --> num)
            val x = mk_var("x",alpha)
        in mk_abs(f,list_mk_comb(inst [beta|->num] option_case_tm,
                    [zero_tm,mk_abs(x,mk_suc(mk_comb(f,x)))]))
        end,
        TypeBasePure.ORIG optionTheory.option_case_def)
  val option_info' = TypeBasePure.put_size option_size_info option_info

in
   val _ = TypeBase.write [bool_info']
   val _ = TypeBase.write [prod_info']
   val _ = TypeBase.write [option_info']
   val _ = TypeBase.write [sum_info']
end

end;
