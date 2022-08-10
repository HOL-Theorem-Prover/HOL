structure equations =
struct

local open HolKernel boolSyntax Drule compute_rules clauses
in

(*---------------------------------------------------------------------------
 * The First order matching functions.
 *
 * We do not consider general non-linear patterns. We could try (requires a
 * more elaborate conversion algorithm, and it makes matching and reduction
 * mutually dependent).
 *---------------------------------------------------------------------------*)
exception No_match;

(* p and pc are both constants *)

val raw_match = raw_match [] empty_tmset

fun match_const (bds,tbds) pc c =
  (bds, fst(snd (raw_match pc c ([],tbds))))
  handle HOL_ERR _ => raise No_match
;

(*---------------------------------------------------------------------------
 * Match pattern variable number var with term arg.
 * We do not need to match types, because pattern variables appear as argument
 * of a constant which has already been matched succesfully.
 *---------------------------------------------------------------------------*)

fun match_var (bds,tbds) var arg =
 let val _ =
    case Array.sub(bds,var)
     of SOME(tm,_) => if aconv tm (fst arg) then () else raise No_match
      | NONE => Array.update(bds,var,SOME arg)
 in
    (bds, tbds)
 end;


(*---------------------------------------------------------------------------
 * Tries to match a list of pattern to a list of arguments.
 * We assume that we already checked the lengths (probably a good short-cut)
 *
 * Returns a list of bindings that extend the ones given as
 * argument (bds), or a No_match exception.
 *---------------------------------------------------------------------------*)

fun match_list bds (pat :: pats) (arg :: args) =
      match_list (match_solve bds pat arg) pats args
  | match_list bds []          []          = bds
  | match_list _   _           _           = raise DEAD_CODE "match_list"

and match_solve bds (Pvar var)           arg = match_var bds var arg
  | match_solve bds (Papp{Head=phead,Args=pargs}) (_,CST{Head,Args,...}) =
      if length pargs = length Args
      then match_list (match_const bds phead Head) pargs Args
      else raise No_match
  | match_solve _ _ _ = raise No_match
;

(*
   `try_rwn ty_inst args rewrites --> {Rule: rule, Inst: inst}`

   Try a sequence of rewrite rules. No attempt to factorize patterns!

   - `ty_inst`: Type instantiation.
   - `args`: Arguments to which the constant is applied.
   - `rewrites`: Information about rewrite equations of the applied constant.
   - `rule`: The chosen rewritting rule.
   - `inst`: Instantiation of the variables in the rewriting rule to make the
     arguments of the LHS match `args`.
*)
fun try_rwn ibds lt =
 let fun try_rec [] = raise No_match
       | try_rec ((rw as RW{lhs,npv,...})::rwn) =
          (let val env = Array.array(npv,NONE)
           in {Rule=rw, Inst=match_list(env,ibds) lhs lt}
           end handle No_match => try_rec rwn)
 in try_rec end
;


(*---------------------------------------------------------------------------
 * Instantiating the rule according to the output of the matching.
 *---------------------------------------------------------------------------*)

fun comb_ct {Head,Args,Rws=NeedArg tail, Skip} arg =
      CST{Head=Head, Args=arg::Args, Rws=tail, Skip=Skip }
  | comb_ct {Head,Args,Rws=EndDb, Skip} arg =
      CST{Head=Head, Args=arg::Args, Rws=EndDb, Skip=Skip }
  | comb_ct {Rws=Try _,...} arg =
      raise DEAD_CODE "comb_ct: yet rules to try"
;

fun mk_clos(env,t) =
  case t of
    Cst (hc,r) => let val (db,b) = !r in CST{Head=hc, Args=[], Rws= db, Skip = b} end
  | Bv i => List.nth(env,i)
  | Fv => NEUTR
  | _ => CLOS{Env=env, Term=t}
;


(*---------------------------------------------------------------------------
 * It is probably this code that can be improved the most
 *---------------------------------------------------------------------------*)

fun inst_one_var (SOME(tm,v),(thm,lv)) = (Specialize tm thm, v :: lv)
  | inst_one_var (NONE,_) = raise DEAD_CODE "inst_rw"

(* Instantiate an equational rewrite. *)
fun inst_rw ({Rule=RW{thm,rhs=rule_rhs,ants,...}, Inst=(bds,tysub)},
             monitoring_p) =
  let
    val ty_inst_rw_thm = INST_TYPE tysub thm
    val (spec_thm, env) = Array.foldl inst_one_var (ty_inst_rw_thm, []) bds
    val cl = mk_clos (env, inst_type_dterm (tysub, rule_rhs))
    val (ants_hol4, eq_t) = strip_imp_only (concl spec_thm)
    val new_rhs = rhs eq_t
    fun inst_ant ant = mk_clos (env, inst_type_dterm (tysub, ant))
    val ants_cl = List.map inst_ant ants
  in
    if monitoring_p then
      !Feedback.MESG_outstream (Parse.term_to_string (concl spec_thm) ^ "\n")
    else
      ();
    (spec_thm, new_rhs, cl, zip ants_hol4 ants_cl)
  end

val monitoring = ref NONE : (term -> bool) option ref;
val stoppers = ref NONE : (term -> bool) option ref;

(*---------------------------------------------------------------------------
 * Reducing a constant
 *---------------------------------------------------------------------------*)

(*
   `reduce_cst (thm, cl) --> (reduced_p, t', cl', ants, mk_thm)`

   Reduce an application of a constant in the compset. `thm` must be of the form
   `|- lhs = rhs`. `cl` is information about `rhs`. If `cl` is an application of
   a constant for which there is an usable rule in its compset then reduce it
   using that equation. `t'` is the HOL term after reducing the application in
   `rhs`. `cl'` is information about `t'`. `ants` is a list of the antecedents
   to be reduced to `T` where each element is of the form `(t'', cl'')`. If
   `reduced_p` is true then `mk_thm` takes a list of theorems of the form
   `ant <=> T’ where `ant` is the correponding term of `ants` and returns
   `lhs = t'`.
*)
fun reduce_cst (th,{Head, Args, Rws=Try{Hcst,Rws=Rewrite rls,Tail},Skip}) =
    (let
       val _ = (case !stoppers of
                  NONE => ()
                | SOME p => if p Head then raise No_match else ())
       val (_,tytheta) = match_term Hcst Head
                         handle HOL_ERR _ => raise No_match
       val rule_inst = try_rwn tytheta Args rls
       val monitoring_p =
         case !monitoring of
           NONE => false
         | SOME f => f Head
       val (spec_thm, new_rhs, cl, ants) = inst_rw (rule_inst, monitoring_p)
       fun mk_thm thml =
         TRANS th
               (List.foldl (fn (ant_eq_t, thm) =>
                              MP spec_thm (EQT_ELIM ant_eq_t))
                           spec_thm
                           thml)
     in
       (true, new_rhs, cl, ants, mk_thm)
     end
     handle No_match
     => reduce_cst (th,{Head=Head,Args=Args,Rws=Tail,Skip=Skip}))
  | reduce_cst (th,{Head, Args, Rws=Try{Hcst,Rws=Conv fconv,Tail},Skip}) =
    (let
       val (thm, cl) = fconv (rhs (concl th))
       val mk_thm = K (TRANS th thm)
     in
       (true, rhs (concl thm), cl, [], mk_thm)
     end
     handle HOL_ERR _
     => reduce_cst (th,{Head=Head,Args=Args,Rws=Tail,Skip=Skip}))
  | reduce_cst (th,cst) =
    (false, rhs (concl th), CST cst, [], K th)

end;

end
