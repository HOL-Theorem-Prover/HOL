
local open HolKernel basicHol90Lib rules clauses
in

(* The First order matching function.
 *
 * We don't consider non-linear patterns. We could try (requires a conversion
 * algorithm).
 *)
exception No_match;

fun match_const (bds,tbds) cst cty c =
  let val {Name,Ty} = dest_const c in
  if cst=Name then (bds, Type.type_reduce cty Ty tbds)
  else raise No_match
  end
  handle HOL_ERR _ => raise No_match
;

(* We modify the env of the rule itself. This means that matching cannot
   be mutually recursive with reduction. It's a problem if constants are
   called by name. Otherwise, a new array must be allocated (in try_rwn)
 *)
fun match_var (bds,tbds) var arg =
  let val _ = Array.update(bds,var,arg) in
  (bds, tbds)
  end;


(* Tries to match a list of pattern to a list of arguments.
 * We assume that we already checked the lengths (probably a good short-cut)
 *
 * Returns a list of bindings (that extend the ones given as
 * argument (bds), or a No_match exception.
 *)

fun match_list bds (pat::pats) (arg::args) =
      match_list (match_solve bds pat arg) pats args
  | match_list bds []          []          = bds
  | match_list _   _           _           = raise DEAD_CODE "match_list"

and match_solve bds (Pvar var)           arg = match_var bds var arg
  | match_solve bds (Papp{Name,Ty,Args=pargs}) (_,CST{Head,Args,...}) =
      if (length pargs) = (length Args)
      then match_list (match_const bds Name Ty Head) pargs Args
      else raise No_match
  | match_solve _ _ _ = raise No_match
;


fun try_rwn ibds lt =
  let fun try_rec []                         = raise No_match 
        | try_rec ((rw as RW{lhs,env,...})::rwn) =
	    ({Rule=rw, Inst=match_list (env,ibds) lhs lt}
             handle No_match => try_rec rwn)
  in try_rec end
;




(* Instanciating the rule according to the ouptut of the matching
 *)

fun comb_ct {Rws=(0,_,_)::l,...} arg =
      raise DEAD_CODE "comb_ct: yet rules to match"
  | comb_ct {Head,Args,Rws=(n,ty,rws)::l} arg =
      CST{Head=Head, Args=arg::Args, Rws=(n-1,ty,rws)::l }
  | comb_ct {Head,Args,Rws=[]} arg = CST{Head=Head,Args=arg::Args,Rws=[]}
;

fun mk_clos(env,t) =
  case t of
    Cst (hc,c) => CST{Head=hc, Args=[], Rws= !c}
  | Bv i => List.nth(env,i)
  | Fv => NEUTR
  | _ => CLOS{Env=env, Term=t}
;


(* copied from Type *)
local
fun del [] A = A
  | del ((rr as {redex,residue})::rst) A =
      if (redex=residue) then del rst A else del rst (rr::A)
in fun del_ty_sub theta = del theta []
end;


(* TODO: reverse order of quantified vars to avoid rev *)
fun inst_rw {Rule=RW{thm,rhs,...}, Inst=(bds,tbds)} =
  let fun inst_one_var ((tm,v),(th,lv)) = (tm::th, v::lv)
      val tysub = del_ty_sub tbds
      val tirhs = inst_dt tysub rhs
      val (tenv,venv) = Array.foldl inst_one_var ([],[]) bds
      val ith = SPECL (rev tenv) (INST_TYPE tysub thm) in
  {Thm=ith, Residue=mk_clos(venv,tirhs)}
  end
;


(* TODO: match type in from_term. *)
fun reduce_cst {Head, Args, Rws=(0,ty,rws)::arw} =
      (let val inst =
 	     Type.match_type ty (type_of Head)
 	     handle HOL_ERR _ => raise No_match
 	   val rule_inst = (try_rwn inst Args) rws in
       LEFT (inst_rw rule_inst)
       end
       handle No_match => reduce_cst {Head=Head, Args=Args, Rws=arw})
  | reduce_cst cst = RIGHT cst
;

end;
