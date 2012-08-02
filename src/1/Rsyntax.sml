structure Rsyntax :> Rsyntax =
struct

 type thm      = Thm.thm;
 type term     = Term.term;
 type hol_type = Type.hol_type;


fun mk_type{Tyop,Args}      = Type.mk_type(Tyop,Args)
fun mk_var{Name,Ty}         = Term.mk_var(Name,Ty)
fun mk_primed_var{Name,Ty}  = Term.mk_primed_var(Name,Ty)
fun mk_const{Name,Ty}       = Term.mk_const(Name,Ty)
fun mk_comb{Rator,Rand}     = Term.mk_comb(Rator,Rand)
fun mk_abs{Bvar,Body}       = Term.mk_abs(Bvar,Body)
fun mk_eq{lhs,rhs}          = boolSyntax.mk_eq(lhs,rhs)
fun mk_imp{ant,conseq}      = boolSyntax.mk_imp(ant,conseq)
fun mk_forall{Bvar,Body}    = boolSyntax.mk_forall(Bvar,Body)
fun mk_exists{Bvar,Body}    = boolSyntax.mk_exists(Bvar,Body)
fun mk_exists1{Bvar,Body}   = boolSyntax.mk_exists1(Bvar,Body)
fun mk_select{Bvar,Body}    = boolSyntax.mk_select(Bvar,Body)
fun mk_conj{conj1,conj2}    = boolSyntax.mk_conj(conj1,conj2)
fun mk_disj{disj1,disj2}    = boolSyntax.mk_disj(disj1,disj2)
fun mk_let{func,arg}        = boolSyntax.mk_let(func,arg)
fun mk_cond{cond,larm,rarm} = boolSyntax.mk_cond(cond,larm,rarm);

fun dest_type ty = let val (s,l) = Type.dest_type ty in {Tyop=s,Args=l} end
fun dest_var M   = let val (s,ty) = Term.dest_var M in {Name=s,Ty=ty} end
fun dest_const M = let val (s,ty) = Term.dest_const M in {Name=s,Ty=ty} end
fun dest_comb M  = let val (f,x) = Term.dest_comb M in {Rator=f,Rand=x} end
fun dest_abs M   = let val (v,N) = Term.dest_abs M in {Bvar=v,Body=N} end;

fun dest_eq M  = let val (l,r) = boolSyntax.dest_eq M in {lhs=l,rhs=r} end;
fun dest_imp M = let val (l,r) = boolSyntax.dest_imp M in {ant=l,conseq=r} end;
fun dest_imp_only M =
   let val (l,r) = boolSyntax.dest_imp_only M in {ant=l,conseq=r} end;
fun dest_select M =
   let val (v,N) = boolSyntax.dest_select M in {Bvar=v,Body=N} end;
fun dest_forall M =
   let val (v,N) = boolSyntax.dest_forall M in {Bvar=v,Body=N} end;
fun dest_exists M =
   let val (v,N) = boolSyntax.dest_exists M in {Bvar=v,Body=N} end;
fun dest_exists1 M =
   let val (v,N) = boolSyntax.dest_exists1 M in {Bvar=v,Body=N} end;
fun dest_conj M =
   let val (l,r) = boolSyntax.dest_conj M in {conj1=l,conj2=r} end;
fun dest_disj M =
   let val (l,r) = boolSyntax.dest_disj M in {disj1=l,disj2=r} end;
fun dest_cond M =
   let val (b,l,r) = boolSyntax.dest_cond M in {cond=b,larm=l,rarm=r} end
fun dest_let M = let val (f,a) = boolSyntax.dest_let M in {func=f,arg=a} end;

fun new_type{Name,Arity}    = boolSyntax.new_type(Name,Arity);
fun new_constant{Name,Ty}   = boolSyntax.new_constant(Name,Ty);
fun new_infix{Name,Prec,Ty} = boolSyntax.new_infix(Name,Ty,Prec);
fun new_binder{Name,Ty}     = boolSyntax.new_binder(Name,Ty);

fun new_specification {name,sat_thm,consts} = let
  open Parse
  val cnames = map #const_name consts
  val res = Theory.Definition.new_specification(name, cnames, sat_thm)
  fun modify_grammar {const_name,fixity=SOME fxty} = set_fixity const_name fxty
    | modify_grammar _ = ()
in
  app modify_grammar consts;
  res
end;

datatype lambda
   = VAR   of {Name:string, Ty:hol_type}
   | CONST of {Name:string, Thy:string, Ty:hol_type}
   | COMB  of {Rator:term, Rand:term}
   | LAMB  of {Bvar:term, Body:term};

local open Feedback
in
fun dest_term M =
  COMB(dest_comb M) handle HOL_ERR _ =>
  LAMB(dest_abs M)  handle HOL_ERR _ =>
  VAR (dest_var M)  handle HOL_ERR _ =>
  CONST(Term.dest_thy_const M)
end;

end (* Rsyntax *)
