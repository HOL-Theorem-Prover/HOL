(*===========================================================================*)
(* Lifters: mapping datatype elements from ML to HOL                         *)
(*===========================================================================*)

structure Lift :> Lift =
struct

open HolKernel Parse boolLib combinSyntax;

val ERR = mk_HOL_ERR "Lift";

fun enum_list s 0 = []
  | enum_list s 1 = [s]
  | enum_list s n = for 1 n (Lib.strcat s o Int.toString);

fun Undef ty =
  raise Fail ("Undef: "^Lib.quote (Parse.type_to_string ty)^
              " is an unknown type operator");

fun apply_interp interp tm = mk_comb(interp (type_of tm), tm);

local val typety = mk_vartype "'type"
      val termty = mk_vartype "'term"
      val list_mk_comb_var = mk_var("list_mk_comb", Type`:'term -> 'term`)
      val cons_var  = mk_var ("cons",Type`:'term -> 'term -> 'term`)
      val nil_var   = mk_var ("nil",Type`:'term`)
      val comma_var = mk_var (",",Type`:'term -> 'term -> 'term`)
      fun Cons x y  = list_mk_comb(cons_var,[x,y])
      fun Pair x y  = list_mk_comb(comma_var,[x,y])
      fun to_list alist = itlist Cons alist nil_var
      fun genargs c =
        let val argtys = fst (strip_fun (type_of c))
            val argvs = map mk_var (zip (enum_list "v" (length argtys)) argtys)
        in argvs
        end
      fun RW tm = PURE_REWRITE_CONV [combinTheory.K_THM] tm
                  handle _ => REFL tm
      fun ELIM_K tm = boolSyntax.rhs (snd(dest_thm (RW tm)))
      fun unc c = let val (cname,ty) = dest_const c
                      val (dtys,rty) = boolSyntax.strip_fun ty
                      val ty' = if null dtys then rty else
                                pairSyntax.list_mk_prod dtys --> rty
                  in mk_var(cname,ty')
                  end
in
fun lift_def_syntax (Gamma,typ) =
 let val Clist = TypeBasePure.constructors_of
                  (Option.valOf(TypeBase.fetch typ))
     val ty = snd(strip_fun(type_of (hd Clist)))
     val args = snd(dest_type ty)
     val Clistnames = enum_list "C" (length Clist)
     val flistnames = enum_list "f" (length args)
     val flist_types = map (fn ty => (ty --> termty)) args
     val flist = map mk_var (zip flistnames flist_types)
     val Theta = Lib.C assoc (zip args flist)
     val lift_type = list_mk_fun(flist_types@[ty],termty)
     val lift_var = mk_var("lift",lift_type)
     val K_lift_ty = mk_K_1 (lift_var,typety)
     fun Gamma' c = if typ=c then SOME K_lift_ty else Gamma c
     val Interp = TypeBasePure.tyValue (total Theta, Gamma', Undef)
     fun mk_clause (C,Cname) =
       let val args = genargs C
           val paired_args = if null args then args
                             else [pairSyntax.list_mk_pair args]
           val Capp = list_mk_comb (unc C,paired_args)
           val lhs  = list_mk_comb(lift_var,flist@[Capp])
           val rhs  = mk_comb(list_mk_comb_var,
                              Pair (mk_var(Cname,termty))
                                (to_list
                                  (map (apply_interp Interp) args)))
       in ELIM_K (mk_eq(lhs,rhs))
       end
 in
   (flistnames,Clistnames, map mk_clause (zip Clist Clistnames))
 end
end;

(*---------------------------------------------------------------------------*)
(* Generate the ML definition of a lifter for datatype tyop and print the    *)
(* proposed definition to ppstrm.                                            *)
(*---------------------------------------------------------------------------*)

fun pp_lifter_def ppstrm typ =
 let open Portable
     val {add_break,add_newline,
          add_string,begin_block,end_block,...} = with_ppstream ppstrm
     val pp_term = Parse.pp_term ppstrm
     val db = TypeBase.theTypeBase()
     val Gamma = Option.composePartial (TypeBasePure.lift_of,
                                        TypeBasePure.fetch db)
     val (flistnames,Clistnames,clauses) = lift_def_syntax (Gamma,typ)
     val tyop = let val {Thy,Tyop,Args} = dest_thy_type typ in (Thy,Tyop) end
 in
  begin_block CONSISTENT 0;
  add_string "local val Clist = TypeBase.constructors_of ";
  add_string ("("^Lib.quote (#1 tyop)^","^Lib.quote (#2 tyop)^")");
  add_break (1,0);
  add_string "in";
  add_break (1,0);
  add_string ("fun lift_"^ #2 tyop^" ty = ");
  add_newline();
  add_string "  let val ";
  begin_block INCONSISTENT 1;
       add_string "[";
       pr_list add_string (fn () => add_string ",") (fn () => add_break(0,0))
               Clistnames;
       add_string "]"; end_block ();
  add_string " = map (TypeBasePure.cinst ty) Clist";
  add_newline();
  add_string "      ";
  begin_block CONSISTENT 4;
  add_string "fun ";
  pr_list pp_term
          (fn () => add_string " | ")
          (fn () => add_break (0,0))
          clauses;
  end_block();
  add_newline();
  add_string "  in";
  add_newline();
  add_string "  lift";
  add_newline();
  add_string "  end";
  add_newline();
  add_string "end;";   (* local *)
  add_newline();
  end_block()
 end;

end
