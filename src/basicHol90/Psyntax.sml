structure Psyntax :> Psyntax =
struct

open HolKernel;
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
fun mk_comb(t1,t2) = Term.mk_comb {Rator = t1, Rand = t2};
fun mk_abs(v,body) = Term.mk_abs{Bvar = v, Body = body};
fun mk_primed_var(s,ty) = Term.mk_primed_var{Name = s, Ty = ty};
fun mk_eq(t1,t2) = Dsyntax.mk_eq{lhs = t1, rhs = t2};
fun mk_imp(t1,t2) = Dsyntax.mk_imp{ant = t1, conseq = t2};
fun mk_select(v,body) = Dsyntax.mk_select{Bvar = v, Body = body};
fun mk_forall(v,body) = Dsyntax.mk_forall{Bvar = v, Body = body};
fun mk_exists(v,body) = Dsyntax.mk_exists{Bvar = v, Body = body};
fun mk_conj(t1,t2) = Dsyntax.mk_conj{conj1 = t1, conj2 = t2};
fun mk_disj(t1,t2) = Dsyntax.mk_disj{disj1 = t1, disj2 = t2};
fun mk_cond(p,t1,t2) = Dsyntax.mk_cond{cond = p, larm = t1, rarm = t2};
fun mk_pair(t1,t2) = Dsyntax.mk_pair{fst = t1, snd = t2};
fun mk_let(f,a)= Dsyntax.mk_let{func = f, arg  = a};
fun mk_cons(h,t) = Dsyntax.mk_cons {hd = h, tl = t};
fun mk_list(L,ty) = Dsyntax.mk_list{els = L, ty = ty};
fun mk_pabs(t1,t2) = Dsyntax.mk_pabs{varstruct = t1, body = t2};

(* Destruction routines *)
fun pair_atom{Name,Ty} = (Name,Ty);
fun pair_comb{Rator,Rand} = (Rator,Rand);
fun pair_binder{Bvar,Body} = (Bvar,Body);

val dest_var = pair_atom o Term.dest_var;
val dest_const = pair_atom o Term.dest_const;
val dest_comb = pair_comb o Term.dest_comb;
val dest_abs = pair_binder o Term.dest_abs;
fun dest_eq tm = let val {lhs,rhs} = Dsyntax.dest_eq tm in (lhs,rhs) end;
fun dest_imp tm = let val {ant,conseq} = Dsyntax.dest_imp tm
                  in (ant,conseq) end;
val dest_select = pair_binder o Dsyntax.dest_select;
val dest_forall = pair_binder o Dsyntax.dest_forall;
val dest_exists = pair_binder o Dsyntax.dest_exists;
fun dest_conj tm = let val {conj1,conj2} = Dsyntax.dest_conj tm
                   in (conj1,conj2) end;
fun dest_disj tm = let val {disj1,disj2} = Dsyntax.dest_disj tm
                   in (disj1,disj2) end;
fun dest_cond tm = let val {cond,larm,rarm} = Dsyntax.dest_cond tm
                   in (cond,larm,rarm)  end;
fun dest_pair tm = let val{fst,snd} = Dsyntax.dest_pair tm in (fst,snd) end;
fun dest_let tm = let val {func, arg} = Dsyntax.dest_let tm in (func,arg) end;
fun dest_cons tm = let val {hd, tl} = Dsyntax.dest_cons tm in (hd,tl) end;
fun dest_list tm = let val {els, ty} = Dsyntax.dest_list tm in (els,ty) end;
fun dest_pabs tm = let val {varstruct, body} = Dsyntax.dest_pabs tm
                   in (varstruct,body)
                   end;

fun mk_type(s,ty) = Type.mk_type{Tyop = s, Args = ty};
fun dest_type ty = let val {Tyop,Args} = Type.dest_type ty
                   in (Tyop,Args)
                   end;

fun mk_subst L = map (fn (residue,redex) => {redex=redex,residue=residue}) L;
fun mk_old_subst L = map (fn {residue,redex} =>(residue,redex)) L;

fun type_subst x = Type.type_subst (mk_subst x);
fun subst s = Term.subst (mk_subst s);
fun subst_occs occs_list = (Dsyntax.subst_occs occs_list) o mk_subst;

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
val INST_TY_TERM = Conv.INST_TY_TERM o (mk_subst##mk_subst);

fun new_type i s = Parse.new_type{Name = s, Arity = i};
fun new_constant(s,ty) = Parse.new_constant{Name = s, Ty = ty};
fun new_infix(s,ty,i) = Parse.new_infix{Name = s, Ty = ty,Prec=i};
fun new_binder(s,ty) = Parse.new_binder{Name = s, Ty = ty};

local
  fun mk_fixity "binder" _ = Parse.Binder
    | mk_fixity "constant" _ = Parse.Prefix
    | mk_fixity "infixl" i = Parse.Infixl i
    | mk_fixity "infixr" i = Parse.Infixr i
    | mk_fixity s _ =
    raise PSYNTAX_ERR
      {func = "new_specification",
       mesg=s^" must be \"constant\", \"infixl\", \"infixr\" or \"binder\""}
fun tran (f,n,i) = {fixity=mk_fixity f i, const_name=n}
in
fun new_specification s alist th =
  Parse.new_specification{name=s,consts = map tran alist,sat_thm = th}
end;

fun new_type_definition (n,p,th) =
   Parse.new_type_definition{name = n, pred = p, inhab_thm = th};


fun new_recursive_definition ax name tm =
     Prim_rec.new_recursive_definition {name = name, rec_axiom = ax, def = tm};

fun define_new_type_bijections name ABS REP tyax =
     Type_def_support.define_new_type_bijections
             {name = name, ABS = ABS, REP = REP, tyax = tyax};

end; (* Psyntax *)
