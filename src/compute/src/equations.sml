
local open HolKernel basicHol90Lib rules clauses
in

(* The First order matching functions.
 *
 * We do not consider general non-linear patterns. We could try (requires a
 * more elaborate conversion algorithm, and it makes matching and reduction
 * mutually dependent).
 *)
exception No_match;

(* p and pc are both constants *)
fun match_const (bds,tbds) pc c =
  (bds, snd (term_reduce pc c ([],tbds)))
  handle HOL_ERR _ => raise No_match
;

(* Match pattern variable number var with term arg.
 * We do not need to match types, because pattern variables appear as argument
 * of a constant which has already be matched succesfully.
 *)
fun match_var (bds,tbds) var arg =
  let val _ = case Array.sub(bds,var) of
      SOME(tm,_) => if aconv tm (fst arg) then () else raise No_match
    | NONE => Array.update(bds,var,SOME arg) in
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

(* Try a sequence of rewrite rules. No attempt to factorize patterns! *)
fun try_rwn ibds lt =
  let fun try_rec []                         = raise No_match 
        | try_rec ((rw as RW{lhs,npv,...})::rwn) =
	    (let val env = Array.array(npv,NONE) in
	     {Rule=rw, Inst=match_list (env,ibds) lhs lt}
	     end
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


(* It is probably this code that can be improved the most *)
local fun inst_one_var (SOME(tm,v),(thm,lv)) = (Spec tm thm, v :: lv)
        | inst_one_var (NONE,_) = raise DEAD_CODE "inst_rw"
in
fun inst_rw (th,{Rule=RW{thm,rhs,...}, Inst=(bds,tbds)}) =
  let val tysub = del_ty_sub tbds
      val tirhs = inst_type_dterm (tysub,rhs)
      val tithm = INST_TYPE tysub thm
      val (spec_thm,venv) = Array.foldl inst_one_var (tithm,[]) bds in
  (TRANS th spec_thm, mk_clos(venv,tirhs))
  end
end;

(* Reducing a constant *)
fun reduce_cst (rws,th,{Head, Args, Rws=Try{Hcst,Rws=Rewrite rls,Tail}}) =
      (let val (_,inst) = match_term Hcst Head
                          handle HOL_ERR _ => raise No_match
 	   val rule_inst = try_rwn inst Args rls in
       (true,(inst_rw (th,rule_inst)))
       end
       handle No_match => reduce_cst (rws,th,{Head=Head,Args=Args,Rws=Tail}))
  | reduce_cst (rws,th,{Head, Args, Rws=Try{Hcst,Rws=Conv conv,Tail}}) =
      (let val thm = TRANS th (conv (rhs (concl th))) in
       (true, (thm, mk_clos([],from_term (rws,[],rhs (concl thm)))))
       end
       handle HOL_ERR _ => reduce_cst (rws,th,{Head=Head,Args=Args,Rws=Tail}))
  | reduce_cst (rws,th,cst) = (false,(th,CST cst))
;

end;
