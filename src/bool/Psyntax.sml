structure Psyntax :> Psyntax =
struct

open Feedback HolKernel;
infix ##;
infix |->;

    type term = Term.term;
    type thm = Thm.thm;
    type hol_type = Type.hol_type;
    type fixity = Parse.fixity;

fun PSYNTAX_ERR{func,mesg} =
        HOL_ERR{origin_structure = "Psyntax",
                origin_function = func,
                message = mesg};

fun mk_var(s,ty) = Term.mk_var{Name = s, Ty = ty};
fun mk_const(s,ty) = Term.mk_const{Name = s, Ty = ty};
fun mk_thy_const(s,thy,ty) = Term.mk_thy_const{Name = s, Thy=thy,Ty = ty};
fun mk_comb(t1,t2) = Term.mk_comb {Rator = t1, Rand = t2};
fun mk_abs(v,body) = Term.mk_abs{Bvar = v, Body = body};
fun mk_primed_var(s,ty) = Term.mk_primed_var{Name = s, Ty = ty};
fun mk_eq(t1,t2) = boolSyntax.mk_eq{lhs = t1, rhs = t2};
fun mk_imp(t1,t2) = boolSyntax.mk_imp{ant = t1, conseq = t2};
fun mk_select(v,body) = boolSyntax.mk_select{Bvar = v, Body = body};
fun mk_forall(v,body) = boolSyntax.mk_forall{Bvar = v, Body = body};
fun mk_exists(v,body) = boolSyntax.mk_exists{Bvar = v, Body = body};
fun mk_exists1(v,body) = boolSyntax.mk_exists1{Bvar = v, Body = body};
fun mk_conj(t1,t2) = boolSyntax.mk_conj{conj1 = t1, conj2 = t2};
fun mk_disj(t1,t2) = boolSyntax.mk_disj{disj1 = t1, disj2 = t2};
fun mk_cond(p,t1,t2) = boolSyntax.mk_cond{cond = p, larm = t1, rarm = t2};
fun mk_let(f,a)= boolSyntax.mk_let{func = f, arg  = a};

(* Destruction routines *)
fun pair_atom{Name,Ty} = (Name,Ty);
fun pair_comb{Rator,Rand} = (Rator,Rand);
fun pair_binder{Bvar,Body} = (Bvar,Body);

val dest_var = pair_atom o Term.dest_var;
val dest_const = pair_atom o Term.dest_const;
fun dest_thy_const c =
 let val {Name,Thy,Ty} = Term.dest_thy_const c
 in (Name,Thy,Ty) end
val dest_comb = pair_comb o Term.dest_comb;
val dest_abs = pair_binder o Term.dest_abs;
fun dest_eq tm = let val {lhs,rhs} = boolSyntax.dest_eq tm in (lhs,rhs) end;
fun dest_imp tm = 
 let val {ant,conseq} = boolSyntax.dest_imp tm in (ant,conseq) end;
fun dest_imp_only tm = 
 let val {ant,conseq} = boolSyntax.dest_imp_only tm in (ant,conseq) end;
val dest_select = pair_binder o boolSyntax.dest_select;
val dest_forall = pair_binder o boolSyntax.dest_forall;
val dest_exists = pair_binder o boolSyntax.dest_exists;
val dest_exists1 = pair_binder o boolSyntax.dest_exists1;
fun dest_conj tm = let val {conj1,conj2} = boolSyntax.dest_conj tm
                   in (conj1,conj2) end;
fun dest_disj tm = let val {disj1,disj2} = boolSyntax.dest_disj tm
                   in (disj1,disj2) end;
fun dest_cond tm = let val {cond,larm,rarm} = boolSyntax.dest_cond tm
                   in (cond,larm,rarm)  end;
fun dest_let M = let val {func,arg} = boolSyntax.dest_let M in (func,arg) end;

fun mk_type(s,ty) = Type.mk_type{Tyop = s, Args = ty};
fun dest_type ty = let val {Tyop,Args} = Type.dest_type ty
                   in (Tyop,Args)
                   end;

fun mk_subst L = map (fn (residue,redex) => {redex=redex,residue=residue}) L;
fun mk_old_subst L = map (fn {residue,redex} =>(residue,redex)) L;

fun type_subst x = Type.type_subst (mk_subst x);
fun subst s = Term.subst (mk_subst s);
fun subst_occs occs_list = (HolKernel.subst_occs occs_list) o mk_subst;

val inst = Term.inst o mk_subst
val INST = Thm.INST o mk_subst

fun match_type ty = mk_old_subst o Type.match_type ty
fun match_term tm = (mk_old_subst##mk_old_subst) o Term.match_term tm;

local fun mk_s x = map (fn (th,v) => (v |-> th)) x
in
fun SUBST s template th = Thm.SUBST (mk_s s) template th
fun SUBST_CONV s template tm = Drule.SUBST_CONV (mk_s s) template tm
end;

val INST_TYPE = Thm.INST_TYPE o mk_subst;
val INST_TY_TERM = Drule.INST_TY_TERM o (mk_subst##mk_subst);

fun new_type i s = boolSyntax.new_type{Name = s, Arity = i};
fun new_constant(s,ty) = boolSyntax.new_constant{Name = s, Ty = ty};
fun new_infix(s,ty,i) = boolSyntax.new_infix{Name = s, Ty = ty,Prec=i};
fun new_binder(s,ty) = boolSyntax.new_binder{Name = s, Ty = ty};

local
  fun mk_fixity "binder" _ = Parse.Binder
    | mk_fixity "constant" _ = Parse.Prefix
    | mk_fixity "infixl" i = Parse.Infixl i
    | mk_fixity "infixr" i = Parse.Infixr i
    | mk_fixity s _ = raise PSYNTAX_ERR
       {func = "new_specification",
        mesg=s^" must be \"constant\", \"infixl\", \"infixr\" or \"binder\""}
  fun tran (f,n,i) = {fixity=mk_fixity f i, const_name=n}
in
fun new_specification s alist th =
  boolSyntax.new_specification{name=s, consts=map tran alist, sat_thm=th}
end;

val new_type_definition = boolSyntax.new_type_definition;

end; (* Psyntax *)
