(*
load "rules";
*)
local open HolKernel basicHol90Lib compute_rules
in

(* The functions in this module (except [from_term] and [inst_dterm]) are
 * called only to build the database of rewrite rules. Therefore,
 * optimisation is not so important.
 *
 * [from_term] is the first step of normalisation, and it is not called
 * later on (except with external conv).
 *)

fun CL_ERR function message =
    HOL_ERR{origin_structure = "clauses",
		      origin_function = function,
		      message = message};


(* Checking that a given thm is a reduction rule we can handle:
 *         (c p1...pn) = rhs
 * with p1...pn  either a const applied to patterns or a free variable.
 *)
datatype pattern =
    Pvar of int
  | Papp of { Head : term, Args : pattern list}
;

fun check_arg_form trm =
  let fun chk t stk free =
    if is_comb t then
      let val {Rator,Rand} = dest_comb t
          val (free',pat1) = chk Rand [] free in
      chk Rator (pat1::stk) free'
      end
    else if (is_var t) andalso (stk=[]) then
      let val newi = length free in
      (free, Pvar (newi - index t free - 1))
      handle HOL_ERR _ => (t::free, Pvar newi)
      end
    else if is_const t then (free, Papp{Head=t, Args=rev stk})
    else raise CL_ERR "check_arg_form" "ill-formed pattern"
  in case chk trm [] [] of
       (fv,Papp{Head,Args}) => (rev fv,Head,Args)
     | _ => raise CL_ERR "check_arg_form" "ill-formed pattern"
  end
;



(* CLOS denotes a delayed substitution (closure).
 * CST denotes an applied constant. Its first argument is the head constant;
 *   the second is the list of its arguments (we keep both the term and its
 *   abstract representation); the last one is the set of rewrites that
 *   still have a chance to be used, ie. those with a lhs wider than the
 *   number of applied args.
 * NEUTR is a slight improvement of CST with an empty list of rewrites, so
 *   that arguments of a variable are immediatly strongly reduced.
 *)
datatype 'a fterm =
  (* order of Args: outermost ahead *)
  CST of { Head : term, Args : (term * 'a fterm) list, Rws : 'a,
           Skip : int option }
| NEUTR
| CLOS of { Env : 'a fterm list, Term : 'a dterm }

(* An alternative representation of terms, with all information needed:
 * - they are real de Bruijn terms, so that abstraction destruction is in
 *   constant time.
 * - application is n-ary (slight optimization)
 * - we forget the names of variables
 * - constants are tagged with the set of rewrites that apply to it.
 *   It's a reference since dterm is used to represent rhs of rewrites,
 *   and fixpoints equations add rewrites for a constant that appear in the
 *   rhs.
 *)
and 'a dterm =
    Bv of int
  | Fv
  | Cst of term * ('a * int option) ref
  | App of 'a dterm * 'a dterm list  (* order: outermost ahead *)
  | Abs of 'a dterm
;

(* Invariant: the first arg of App never is an App. *)
fun appl(App(a,l1),arg) = App(a,arg::l1)
  | appl(t,arg) = App(t,[arg])
;

(* Type variable instantiation in dterm. Make it tail-recursive ? *)
fun inst_type_dterm ([],v) = v
  | inst_type_dterm (tysub,v) =
      let fun tyi_dt (Cst(c,dbsk)) = Cst(Term.inst tysub c, dbsk)
            | tyi_dt (App(h,l))  = App(tyi_dt h, map tyi_dt l)
  	    | tyi_dt (Abs v)     = Abs(tyi_dt v)
  	    | tyi_dt v           = v
      in tyi_dt v end
;



datatype action =
    Rewrite of rewrite list
  | Conv of (term -> Thm.thm * db fterm)

and db =
    EndDb
  | Try of { Hcst : term, Rws : action, Tail : db }
  | NeedArg of db

and rewrite =
    RW of { cst: term,          (* constant which the rule applies to *)
            lhs: pattern list,  (* patterns = constant args in lhs of thm *)
	    npv: int,           (* number of distinct pat vars in lhs *)
	    rhs: db dterm,
            thm: Thm.thm }      (* thm we use for rewriting *)
;

fun add_in_db (n,cst,act,EndDb) =
      funpow n NeedArg (Try{Hcst=cst, Rws=act, Tail=EndDb})
  | add_in_db (0,cst,act as Rewrite nrws,Try{Hcst,Rws as Rewrite rws,Tail}) =
      if cst=Hcst then Try{ Hcst=Hcst, Rws=Rewrite(nrws@rws), Tail=Tail }
      else Try { Hcst=Hcst, Rws=Rws, Tail=add_in_db(0,cst,act,Tail) }
  | add_in_db (n,cst,act,Try{Hcst,Rws,Tail}) =
      Try { Hcst=Hcst, Rws=Rws, Tail=add_in_db(n,cst,act,Tail) }
  | add_in_db (0,cst,act,db) = Try{ Hcst=cst, Rws=act, Tail=db }
  | add_in_db (n,cst,act,NeedArg tail) =
      NeedArg(add_in_db(n-1,cst,act,tail))
;

fun key_of (RW{cst, lhs, ...}) =
  let val {Name,...} = dest_const cst in
  (Name, length lhs, cst)
  end
;



(* *)
fun is_skip (_, CST {Skip=SOME n,Args,...}) = (n <= List.length Args)
  | is_skip _ = false
;

(* equation database
 * We should try to factorize the rules (cf discrimination nets)
 * Rules are packed according to their head constant, and then sorted
 * according to the width of their lhs.
 *)
datatype comp_rws = RWS of (string, (db * int option) ref) Polyhash.hash_table;

fun empty_rws () = RWS (Polyhash.mkPolyTable(29,CL_ERR "empty_rws" ""));

fun assoc_clause (RWS rws) cst =
  case Polyhash.peek rws cst of
    SOME rl => rl
  | NONE =>
      let val mt = ref (EndDb, NONE) in
      Polyhash.insert rws (cst,mt);
      mt
      end
;

fun add_in_db_upd rws (name,arity,hcst) act =
  let val (rl as ref(db,sk)) = assoc_clause rws name in
  rl := (add_in_db (arity,hcst,act,db), sk)
  end
;

fun set_skip (rws as RWS htbl) name sk =
  let val (rl as ref(db,_)) = assoc_clause rws name in
  rl := (db,sk)
  end;


fun from_term (rws,env,t) =
  let fun down (env,t,c) =
        case dest_term t of
	  VAR _ => up((Bv (index t env) handle HOL_ERR _ => Fv), c)
  	| CONST{Name,...} => up(Cst (t,assoc_clause rws Name),c)
  	| COMB{Rator,Rand} => down(env,Rator,Zrator{Rand=(env,Rand),Ctx=c})
  	| LAMB{Bvar,Body} => down(Bvar :: env, Body, Zabs{Bvar=(), Ctx=c})

      and up (dt, Ztop) = dt
	| up (dt, Zrator{Rand=(env,arg), Ctx=c}) =
	    down (env,arg,Zrand{Rator=dt, Ctx=c})
	| up (dt, Zrand{Rator=dr, Ctx=c}) = up (appl(dr,dt), c)
	| up (dt, Zabs{Ctx=c,...}) = up(Abs dt, c)
  in down (env,t,Ztop)
  end
;



(* Note: if the list of free variables of the lhs was empty, we could
 * evaluate (weak reduction) the rhs now. This implies that the
 * theorems must be added in dependencies order.
 *)
fun mk_rewrite rws eq_thm =
  let val {lhs,rhs} = dest_eq (concl eq_thm)
      val (fv,cst,pats) = check_arg_form lhs
      val gen_thm = foldr (uncurry GEN) eq_thm fv
      val rhsc = from_term (rws, rev fv, rhs)
  in RW{ cst=cst,
	 lhs=pats,
	 rhs=rhsc,
	 npv=length fv,
	 thm=gen_thm }
  end
;

fun enter_thm rws thm0 =
  let val thm = eq_intro thm0
      val rw =
 	mk_rewrite rws thm
  	handle HOL_ERR _ =>
	  raise CL_ERR "enter_thm"
	    ("computeLib cannot use thm\n"^Parse.thm_to_string thm0)
  in add_in_db_upd rws (key_of rw) (Rewrite [rw])
  end;

fun add_thms lthm rws =
  List.app (List.app (enter_thm rws) o Drule.BODY_CONJUNCTS) lthm;

fun add_extern (cst,arity,fconv) rws =
  let val {Name,...} = dest_const cst in
  add_in_db_upd rws (Name,arity,cst) (Conv fconv)
  end;


fun new_rws () =
  let val rws = empty_rws() in
  add_thms [REFL_CLAUSE] rws;
  rws
  end;

fun from_list lthm =
  let val rws = new_rws() in
  add_thms lthm rws;
  rws
  end;

end;

