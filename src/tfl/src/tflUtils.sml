structure tflUtils :> tflUtils =
struct

open HolKernel

fun ERR func mesg =
   Exception.HOL_ERR{origin_structure = "tflUtils",
           origin_function = func,message=mesg};


val list_mk_type = end_itlist (curry(op -->));

fun strip_type ty =
 case Type.dest_type ty
  of {Tyop="fun", Args=[ty1,ty2]} =>
        let val (D,r) = strip_type ty2
        in (ty1::D, r)
        end
   | _ =>  ([],ty);

fun strip_prod_type ty =
 if (Type.is_vartype ty) then [ty]
 else case Type.dest_type ty
       of {Tyop="prod", Args=[l,r]}
            => strip_prod_type l @ strip_prod_type r
        | _ => [ty];


fun strip_imp tm = 
   if is_neg tm then ([],tm) else 
   if is_imp tm then 
        let val {ant,conseq} = Dsyntax.dest_imp tm
            val (imps,rst) = strip_imp conseq
        in (ant::imps, rst)
        end
   else ([],tm);

fun gen_all tm =
  itlist (fn v => fn M => Dsyntax.mk_forall{Bvar=v,Body=M})
        (free_vars_lr tm) tm;


local fun break [] = raise ERR "mk_vstruct" "unable"
        | break (h::t) = (h,t)
in
fun mk_vstruct ty V =
  if is_vartype ty then break V
  else
   case (Type.dest_type ty)
    of {Tyop="prod", Args = [ty1,ty2]} =>
           let val (ltm,vs1) = mk_vstruct ty1 V
               val (rtm,vs2) = mk_vstruct ty2 vs1
           in
             (Dsyntax.mk_pair{fst=ltm, snd=rtm}, vs2)
           end
     | _ => break V
end;

fun func_of_cond_eqn tm =
    #1(strip_comb(#lhs(dest_eq(#2 (strip_forall(#2(strip_imp tm)))))));

fun dest_relation tm =
   if type_of tm = Type.bool
   then let val {Rator,Rand=r} = Term.dest_comb tm
            val {Rator,Rand=d} = Term.dest_comb Rator
        in (Rator,d,r)
        end
        handle HOL_ERR _ => raise ERR "dest_relation" "term structure"
   else raise ERR "dest_relation" "not a boolean term";


fun is_WFR tm = (#Name(Term.dest_const(rator tm))="WF")
                 handle Exception.HOL_ERR _ => false;

fun mk_arb ty = Term.mk_const{Name="ARB", Ty=ty};

(*---------------------------------------------------------------------------
 * "vary" makes variables that are guaranteed not to be in vlist and
 * furthermore, are guaranteed not to be equal to each other. The names of
 * the variables will start with "v" and end in a number.
 *---------------------------------------------------------------------------*)

local val counter = ref 0
in
fun vary vlist =
  let val slist = ref (map (#Name o dest_var) vlist)
      val _ = counter := 0
      fun pass str = 
         if Lib.mem str (!slist) 
         then ( counter := !counter + 1;
                pass (concat"v" (int_to_string(!counter))))
         else (slist := str :: !slist; str)
  in 
    fn ty => mk_var{Name=pass "v",  Ty=ty}
  end
end;

end;
