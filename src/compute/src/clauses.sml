(*
load "rules";
*)
local open HolKernel rules
in

(* The functions in this module (except [from_term]) are called only to
 * build the database of rewrite rules. Therefore, optimisation is not
 * so important.
 * 
 * [from_term] is the first step of normalisation, and it is not called
 * later on.
 *)

fun CL_ERR function message =
    HOL_ERR{origin_structure = "clauses",
		      origin_function = function,
		      message = message};


(* Checking that a given thm is a reduction rule we can handle:
 *         (c p1...pn) = rhs
 * with p1...pn  either a const applied to patterns or a free variable.
 * patterns must be linear.
 *)
datatype pattern =
    Pvar of int
  | Papp of {Name:string, Ty:Type.hol_type, Args:pattern list}
;

fun check_arg_form trm =
  let fun chk t stk free =
    if is_comb t then
      let val {Rator,Rand} = dest_comb t
          val (free',pat1) = chk Rand [] free in
      chk Rator (pat1::stk) free'
      end
    else if (is_var t) andalso (stk=[]) then
      if mem t free then raise CL_ERR "check_arg_form" "non linear pattern"
      else (t::free, Pvar (length free))
    else if is_const t then
      let val {Name,Ty} = dest_const t in
      (free, Papp{Name=Name, Ty=Ty, Args=rev stk}) end
    else raise CL_ERR "check_arg_form" "ill-formed pattern"
  in case chk trm [] [] of
       (fv,Papp{Name,Ty,Args}) => (rev fv,Name,Ty,Args)
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
  CST of { Head : term, Args : (term * 'a fterm) list, Rws : 'a }
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
  | Cst of term * 'a ref 
  | App of 'a dterm * 'a dterm list  (* order: outermost ahead *)
  | Abs of 'a dterm
;

(* Invariant: the first arg of App never is an App. *)
fun appl(App(a,l1),arg) = App(a,arg::l1)
  | appl(t,arg) = App(t,[arg])
;

(* Type variable instantiation in dterm *)
fun tyi_dt tysub (Cst(c,db)) = Cst(Term.inst tysub c, db)
  | tyi_dt tysub (App(h,l)) = App(tyi_dt tysub h, map (tyi_dt tysub) l)
  | tyi_dt tysub (Abs v) = Abs(tyi_dt tysub v)
  | tyi_dt _ v = v
;

fun inst_dt tysub v = if null tysub then v else tyi_dt tysub v;



datatype db =
    EndDb
  | Try of { Ty : hol_type, Rws : rewrite list, Tail : db }
  | NeedArg of db

and rewrite =
    RW of { cst: string,        (* constant which the rule applies to *)
	    cty: Type.hol_type, (* type of the constant *)
            lhs: pattern list,  (* patterns = constant args in lhs of thm *)
	    rhs: db dterm,
	    env: (term * db fterm) array,
                                (* space for values of free vars. of lhs *)
            thm: thm }          (* thm we use for rewriting *)
;

fun add_in_db (n,ty,rw,EndDb) =
      funpow n NeedArg (Try{Ty=ty, Rws=[rw], Tail=EndDb})
  | add_in_db (n,ty,rw,Try{Ty,Rws,Tail}) =
      if n=0 andalso ty=Ty then Try{ Ty=Ty, Rws=rw::Rws, Tail=Tail }
      else Try { Ty=Ty, Rws=Rws, Tail=add_in_db(n,ty,rw,Tail) }
  | add_in_db (0,ty,rw,db as (NeedArg _)) =
      Try{ Ty=ty, Rws=[rw], Tail=db }
  | add_in_db (n,ty,rw,NeedArg tail) =
      NeedArg(add_in_db(n-1,ty,rw,tail))
;

fun key_of (RW{cst, lhs, cty,...}) = (cst, length lhs, cty)
;


(* equation database
 * We should try to factorize the rules (cf discrimination nets)
 * Rules are packed according to their head constant, and then sorted
 * according to the width of their lhs.
 *)
datatype comp_rws = RWS of (string, db ref) Polyhash.hash_table;

fun new_rws () = RWS (Polyhash.mkPolyTable(29,CL_ERR "new_rws" ""));

fun assoc_clause (RWS rws) cst =
  case Polyhash.peek rws cst of
    SOME rl => rl
  | NONE =>
      let val mt = ref EndDb in
      Polyhash.insert rws (cst,mt);
      mt
      end
;

fun from_term rws env t =
  case dest_term t of
    VAR _ => (Bv (index t env) handle HOL_ERR _ => Fv)
  | CONST{Name,...} => Cst (t,assoc_clause rws Name)
  | COMB{Rator,Rand} => appl(from_term rws env Rator, from_term rws env Rand)
  | LAMB{Bvar,Body} => Abs(from_term rws (Bvar :: env) Body)
;



(* Note: if the list of free variables of the lhs was empty, we could
 * evaluate (weak reduction) the rhs now. This implies that the
 * theorems must be added in dependencies order.
 *)
fun mk_rewrite rws eq_thm =
  let val {lhs,rhs} = dest_eq (concl eq_thm)
      val (fv,cst,ty,pats) = check_arg_form lhs 
      val gen_thm = foldr (uncurry GEN) eq_thm fv
      val rhsc = from_term rws (rev fv) rhs
  in RW{ cst=cst,
	 cty=ty,
	 lhs=pats,
	 rhs=rhsc,
	 env=Array.array(length fv,(lhs,NEUTR)),
	 thm=gen_thm }
  end
  handle HOL_ERR _ => raise CL_ERR "mk_rewrite" "cannot use this thm"
;


fun add_in_db_upd rws (name,arity,ty) rw =
  let val rl = assoc_clause rws name in
  rl := add_in_db (arity,ty,rw,!rl)
  end
;


fun enter_thm rws str thm =
  let val thm0 = Drule.SPEC_ALL thm
      val thm1 = if str then thm0 else lazyfy_thm thm0
      val rw = mk_rewrite rws thm1 in
  add_in_db_upd rws (key_of rw) rw
  end;

fun enter_one_thm rws str thm =
  List.app (enter_thm rws str) (Drule.CONJUNCTS (Drule.SPEC_ALL thm))
;

fun add_clauses str lthm rws =
  List.app (enter_one_thm rws str) lthm
;

fun from_list str lthm =
  let val rws = new_rws() in
  add_clauses str lthm rws;
  rws
  end;

end;
