
local open HolKernel basicHol90Lib rules clauses
in

(* The First order matching function.
 *
 * We don't consider non-linear patterns. We could try (requires a conversion
 * algorithm).
 *)
exception No_match;

(* p and pc are both constants *)
fun match_const (bds,tbds) pc c =
  (bds, snd (term_reduce pc c ([],tbds)))
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
 * Returns a list of bindings that extend the ones given as
 * argument (bds), or a No_match exception.
 *)

fun match_list bds (pat :: pats) (arg :: args) =
      match_list (match_solve bds pat arg) pats args
  | match_list bds []          []          = bds
  | match_list _   _           _           = raise DEAD_CODE "match_list"

and match_solve bds (Pvar var)           arg = match_var bds var arg
  | match_solve bds (Papp{Head=phead,Args=pargs}) (_,CST{Head,Args,...}) =
      if (length pargs) = (length Args)
      then match_list (match_const bds phead Head) pargs Args
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

fun comb_ct {Head,Args,Rws=NeedArg tail} arg =
      CST{Head=Head, Args=arg::Args, Rws=tail }
  | comb_ct {Head,Args,Rws=EndDb} arg =
      CST{Head=Head, Args=arg::Args, Rws=EndDb}
  | comb_ct {Rws=Try _,...} arg =
      raise DEAD_CODE "comb_ct: yet rules to try"
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
in
fun del_ty_sub theta = del theta []
end;


fun inst_rw {Rule=RW{thm,rhs,...}, Inst=(bds,tbds)} =
  let fun inst_one_var ((tm,v),(thm,lv)) = (Spec tm thm, v :: lv)
      val tysub = del_ty_sub tbds
      val tirhs = inst_dterm tysub rhs
      val tithm = INST_TYPE tysub thm
      val (spec_thm,venv) = Array.foldl inst_one_var (tithm,[]) bds in
  {Thm=spec_thm, Residue=mk_clos(venv,tirhs)}
  end
;


(* TODO: match type in from_term? *)
fun reduce_cst {Head, Args, Rws=Try{Hcst,Rws,Tail}} =
      (let val (_,inst) = match_term Hcst Head
                          handle HOL_ERR _ => raise No_match
 	   val rule_inst = (try_rwn inst Args) Rws in
       LEFT (inst_rw rule_inst)
       end
       handle No_match => reduce_cst {Head=Head, Args=Args, Rws=Tail})
  | reduce_cst cst = RIGHT cst
;

end;
