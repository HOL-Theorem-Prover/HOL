structure wfrecUtils :> wfrecUtils =
struct

open HolKernel

fun ERR func mesg =
   Exception.HOL_ERR{origin_structure = "wfrecUtils",
           origin_function = func,message=mesg};


fun zip3 [][][] = []
  | zip3 (x::l1) (y::l2) (z::l3) = (x,y,z)::zip3 l1 l2 l3
  | zip3 _ _ _ = raise ERR "zip3" "different lengths";


fun unzip3 [] = ([],[],[])
  | unzip3 ((x,y,z)::rst) = 
      let val (l1,l2,l3) = unzip3 rst
      in (x::l1, y::l2, z::l3)
      end;

fun gtake f =
  let fun grab(0,rst) = ([],rst)
        | grab(n, x::rst) = 
             let val (taken,left) = grab(n-1,rst)
             in (f x::taken, left) end
        | grab _ = raise ERR "gtake" "grab.empty list"
  in grab
  end;


fun list_to_string f delim =
  let fun stringulate [] = []
        | stringulate [x] = [f x]
        | stringulate (h::t) = f h::delim::stringulate t
  in 
    fn l => String.concat (stringulate l)
  end;


fun mk_sum_type ty1 ty2  = Type.mk_type{Tyop="sum", Args=[ty1,ty2]}
fun mk_prod_type ty1 ty2 = Type.mk_type{Tyop="prod",Args=[ty1,ty2]}

val list_mk_fun_type  = end_itlist (curry(op -->));
val list_mk_prod_type = end_itlist mk_prod_type;

fun strip_fun_type ty =
 case Type.dest_type ty
  of {Tyop="fun", Args=[ty1,ty2]} =>
        let val (D,r) = strip_fun_type ty2
        in (ty1::D, r)
        end
   | _ =>  ([],ty);

fun strip_prod_type ty =
 if Type.is_vartype ty then [ty]
 else case Type.dest_type ty
       of {Tyop="prod", Args=[l,r]}
            => strip_prod_type l @ strip_prod_type r
        | _ => [ty];


fun atom_name tm = #Name(dest_var tm handle HOL_ERR _ => dest_const tm);

fun strip_imp tm = 
   if is_neg tm then ([],tm) else 
   if is_imp tm then 
        let val {ant,conseq} = Dsyntax.dest_imp tm
            val (imps,rst) = strip_imp conseq
        in (ant::imps, rst)
        end
   else ([],tm);

fun gen_all tm = itlist (curry Psyntax.mk_forall) (free_vars_lr tm) tm;


local fun break [] = raise ERR "mk_vstruct" "unable"
        | break (h::t) = (h,t)
in
fun mk_vstruct ty V =
 if is_vartype ty then break V
 else case Type.dest_type ty
       of {Tyop="prod", Args = [ty1,ty2]} =>
            let val (ltm,vs1) = mk_vstruct ty1 V
                val (rtm,vs2) = mk_vstruct ty2 vs1
            in
               (Dsyntax.mk_pair{fst=ltm, snd=rtm}, vs2)
            end
        | _ => break V
end;

fun func_of_cond_eqn tm =
    #1(strip_comb(#lhs(dest_eq
       (#2 (strip_forall(#2(strip_imp (#2 (strip_forall tm)))))))))

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
         then (counter := !counter + 1; pass ("v"^int_to_string(!counter)))
         else (slist := str :: !slist; str)
  in 
    fn ty => mk_var{Name=pass "v",  Ty=ty}
  end
end;


fun match_term thry tm1 tm2 = Term.match_term tm1 tm2;
fun match_type thry ty1 ty2 = Type.match_type ty1 ty2;

(*---------------------------------------------------------------------------
      MoscowML returns lists of QUOTE'd strings when a quote is spread
      over more than one line. "norm_quotel" concatenates all adjacent
      QUOTE elements in this list. This should go in Portable.
 ---------------------------------------------------------------------------*)

fun norm_quote [] = []
  | norm_quote [x] = [x]
  | norm_quote (QUOTE s1::QUOTE s2::rst) = norm_quote (QUOTE(s1^s2)::rst)
  | norm_quote (h::rst) = h::norm_quote rst;

end;
