(*
set_trace "Unicode" 0;
set_trace "pp_annotations" 0;
*)

use (HOLDIR^"/src/pfl/defchoose");

(* quietdec := true; *)
open numSyntax optionSyntax pairSyntax optionTheory;
(* quietdec := false; *)


val suc_zero = ``SUC 0``;

(*---------------------------------------------------------------------------*)
(* Examples                                                                  *)
(*---------------------------------------------------------------------------*)

val ack_tm =
 ``ack m n =
    if m=0 then n + 1 else
    if n=0 then ack (m-1) 1 else
    ack (m-1) (ack m (n-1))``;

val ack1_tm =
 ``(ack 0 n = n+1) /\
   (ack m 0 = ack (m-1) 1) /\
   (ack (SUC m) (SUC n) = ack m (ack (SUC m) n))``;

val ack2_tm =
 ``(!n. ack 0 n = n+1) /\
   (!m. ack m 0 = ack (m-1) 1) /\
   (!m n. ack (SUC m) (SUC n) = ack m (ack (SUC m) n))``;

val fact_tm = ``fact n = if n=0 then 1 else n * fact (n-1)``;

val fact1_tm = ``fact n = if n=0 then 1 else (n + n) * (13 * fact (n-1) + n)``;

val fact2_tm = ``fact n = if n=0 then 1 else
                 (n + fact (n-1)) * (13 * fact (n-1) + n)``;

val fact3_tm = ``fact n = if n=0 then 1 else
                  let x = n + n
                  in x * fact (n-1)``;

val fact4_tm = ``fact n = if n=0 then 1 else
                  let x = fact (n-1)
                  in x + n * x``;

val fact5_tm = ``fact n = if n=0 then 1 else
                  let x = fact (n-1)
                  and y = n + n
                  in y + n * x``;

val map_tm = ``(map f [] = []) /\ (map f (h::t) = f h :: map f t)``;
val f91_tm = ``f91 n = if n>100 then n-10 else f91(f91(n+11))``;
val f91a_tm = ``f91 n = if n>100 then n-10 else n + f91(f91(n+11))``;

val Z_tm = ``Z n = if n=0 then 0 else Z(Z(Z(n-1)))``;
val Z1_tm = ``Z1 n = if n=0 then 0 else SUC(SUC(Z(n-1))) + Z1 (n-1)``;
val Z2_tm = ``Z1 n = if n=0 then 0 else SUC(SUC(Z1(n-1))) + Z1 (n-1)``;

val partle_tm =
  ``(part x [] = ([],[])) /\
    (part x (h::t) =
      let (l1,l2) = part x t
      in if h <= x then (h::l1, l2) else (l1,h::l2))``;

val part_tm =
  ``(part P [] = ([],[])) /\
    (part P (h::t) =
      let (l1,l2) = part P t
      in if P h then (h::l1, l2) else (l1,h::l2))``;

val qsort0_tm =
  ``(qsort [] = []) /\
    (qsort (h::t) =
      let l1 = FILTER (\x. x <= h) t in
      let l2 = FILTER (\x. x > h) t
      in qsort l1 ++ [h] ++ qsort l2)``;

val qsort1_tm =
  ``(qsort [] = []) /\
    (qsort (h::t) =
      let l1 = FILTER (\x. x <= h) t in
      let l2 = FILTER (\x. x > h) t
      in qsort l1 ++ [h] ++ qsort l2)``;

val qsort2_tm =
  ``(qsort [] = []) /\
    (qsort (h::t) =
      let l1 = FILTER (\x. x <= h) t
      and l2 = FILTER (\x. x > h) t
      in qsort l1 ++ [h] ++ qsort l2)``;

val qsort3_tm =
  ``(qsort [] = []) /\
    (qsort (h::t) =
      let (l1,l2) = part (\x. x <= h) t
      in qsort l1 ++ [h] ++ qsort l2)``;

val qsort4_tm =
  ``(qsort R [] = []) /\
    (qsort R (h::t) =
      let (l1,l2) = part (\x. R x h) t
      in qsort R l1 ++ [h] ++ qsort R l2)``;

(*---------------------------------------------------------------------------*)
(* Code                                                                      *)
(*---------------------------------------------------------------------------*)
(*
val pair_case_tm = prim_mk_const{Name="pair_case",Thy="pair"};

fun mk_pair_case (f,a) =
  let val theta = match_type (type_of pair_case_tm) (type_of f)
  in list_mk_comb(inst theta pair_case_tm,[f,a])
  end;
*)

fun list_mk_option_cases u d ty =
 itlist (fn (a,v) => fn c =>
            mk_option_case (mk_none ty, mk_abs(v, c), a))
        u d;

(*---------------------------------------------------------------------------*)
(* Splits tmlist into a triple (u,d,vs) in which u is a list of pairs of     *)
(* form (term,var), d is a list of terms, and vs is a list of used variables *)
(* The intent is that tmlist represents a list of terms, some of which are   *)
(* statically known to be defined, i.e. are of the form "SOME t". The other  *)
(* terms are not statically known to be defined. It is possible that they    *)
(* might statically be known to be undefined, i.e. NONE, but that is not     *)
(* catered for at the moment. If a term is not of the form SOME t, then, we  *)
(* have to put the definedness test into the term structure. This is done    *)
(* by making case analysis on an option. So ... d is the transformed tmlist  *)
(* and u contains the elements of tmlist that can't be trivially shown to    *)
(* be defined.                                                               *)
(*---------------------------------------------------------------------------*)

fun split_args tmlist fvs =
  itlist (fn t => fn (u,d,vs) =>
     if is_some t then (u,dest_some t::d,vs)
      else let val ty = dest_option(type_of t)
               val v = variant vs (mk_var("v",ty))
           in ((t,v)::u, v::d, (v::vs))
           end) tmlist ([],[],fvs);

(*---------------------------------------------------------------------------*)
(* Partiality transformation. Note that it is, at present, really only       *)
(* applicable to first-order terms. Explicit lambdas are handled, but not    *)
(* other terms of functional type.                                           *)
(*---------------------------------------------------------------------------*)

fun partialize env tm =
 if is_var tm orelse is_const tm then mk_some tm else
 if is_abs tm then
    let val (v,M) = dest_abs tm
    in mk_abs(v,partialize env M)
    end else
 if is_cond tm then
    let val (b,t1,t2) = dest_cond tm
        val b' = partialize env b
        val t1' = partialize env t1
        val t2' = partialize env t2
    in
      if is_some b' andalso is_some t1' andalso is_some t2'
        then mk_some (mk_cond(dest_some b', dest_some t1', dest_some t2'))
        else
      if is_some b' then mk_cond (dest_some(b'), t1', t2')
        else
      let val rty = type_of tm
          val v = variant (free_vars tm) (mk_var("v",bool))
      in mk_option_case (mk_none rty, mk_abs(v, mk_cond(v,t1',t2')), b')
      end
    end else
 if TypeBase.is_case tm then
    let val (case_tm,ob,clauses) = TypeBase.dest_case tm
        val ob' = partialize env ob
        val clauses' = map (I ## partialize env) clauses
    in
      if is_some ob' andalso Lib.all (is_some o snd) clauses'
        then mk_some (TypeBase.mk_case
                        (dest_some ob',map (I##dest_some) clauses'))
        else
      if is_some ob' then TypeBase.mk_case (dest_some(ob'), clauses')
      else let val rty = type_of tm
               val v = variant (free_vars tm) (mk_var("v",type_of ob))
           in mk_option_case
                (mk_none rty, mk_abs(v, TypeBase.mk_case(v,clauses')), ob')
           end
    end else
 if is_let tm then
    let val (bindings,M) = dest_anylet tm
        val bindings' = zip (map fst bindings)
                            (map (partialize env o snd) bindings)
        val M' = partialize env M
    in itlist (fn (v,t) => fn body =>
         if is_some t
           then mk_anylet ([(v,dest_some t)],body)
           else mk_option_case
                  (mk_none (dest_option(type_of t)),mk_pabs(v,body), t))
        bindings' M'
    end
 else (* is_comb tm *)
 let val (f,args) = strip_comb tm
     val args' = map (partialize env) args
     val (u,d,vs) = split_args args' (free_vars tm)
     val fapp = case subst_assoc (equal f) env
                 of NONE => mk_some(list_mk_comb(f,d))
                  | SOME g => list_mk_comb(g,d)
 in
   list_mk_option_cases u fapp (type_of tm)
 end;

fun optional fvar =
 let val (fname,ty) = dest_var fvar
     val pfname = "p"^fname
     val (src,target) = strip_fun ty
     val ty' = list_mk_fun (src, mk_option target)
 in
   fvar |-> mk_var(pfname, ty')
 end;

fun indexed d fvar =
 let val (fname,ty) = dest_var fvar
     val ifname = "i"^fname
     val (src,target) = strip_fun ty
     val ty' = list_mk_fun (num::src, mk_option target)
 in
   fvar |-> mk_comb(mk_var(ifname, ty'),d)
 end;

fun mysubst theta v = Option.valOf(subst_assoc (equal v) theta);

fun mk_typed_vars name vlist tylist =
 let fun vary (away,[],vars) = rev vars
       | vary (away,ty::tyl,vars) =
          let val v = variant away (mk_var(name,ty))
          in vary (v::away,tyl,v::vars)
          end
 in Lib.with_flag
       (Globals.priming, SOME"") vary (vlist,tylist,[])
 end;

fun single x = [x];

fun new_base_cases eqns vars =
 let fun munge fns [] vars bcases = ([],bcases)
       | munge fns (h::t) vars bcases =
         let val (f,args) = strip_comb(lhs (snd(strip_forall h))) in
         if mem f fns
         then (append(single h) ## I) (munge fns t vars bcases)
         else let val h0_vars = mk_typed_vars "v" vars (tl (map type_of args))
                  val h0 = mk_eq(list_mk_comb(f,zero_tm::h0_vars),
                                 mk_none(dest_option(type_of(rhs h))))
               in (append [h0,h]##I)
                  (munge (f::fns) t (h0_vars@vars) (h0::bcases))
               end
         end
 in munge [] eqns vars []
 end;

val option_case_rewrite = Q.prove
(`option_case a g (option_case NONE f ob) =
  option_case a (\v. option_case a g (f v)) ob`,
 Cases_on `ob` THEN RW_TAC std_ss []);

val linearize_case = QCONV (SIMP_CONV std_ss [option_case_rewrite]);

fun mk_peqns ufns L R =
 let val thetaP = map optional ufns
     val L' = map (partialize thetaP) L
     val R' = map (partialize thetaP) R
     val eqns = map mk_eq (zip L' R')
 in
   map (rhs o concl o linearize_case) eqns
 end;

(*---------------------------------------------------------------------------*)
(* Run term through the partiality transformation and build the partial and  *)
(* indexed versions of the equations.                                        *)
(*---------------------------------------------------------------------------*)

fun alt_eqns tm =
 let val eqns = map (snd o strip_forall) (strip_conj tm)
     val (L,R) = unzip(map dest_eq eqns)
     val (fns,args) = unzip(map strip_comb L)
     val ufns = mk_set fns  (* unique fns, should all be variables *)
     val peqns = mk_peqns ufns L R
     (* now make ieqns *)
     val vars = all_vars tm
     val d = variant vars (mk_var("d",num))
     val thetaL = map (indexed (mk_suc d)) ufns
     val thetaR = map (indexed d) ufns
     val fns' = map (mysubst thetaL) fns
     val L' = map2 (curry list_mk_comb) fns' args
     val R' = map (partialize thetaR) R
     val ieqns1 = map mk_eq (zip L' R')
     val (ieqns2,base_cases) = new_base_cases ieqns1 (d::vars)
     val ieqns = map (rhs o concl o linearize_case) ieqns2
 in
   (peqns, ieqns, ufns, base_cases)
 end;

(*---------------------------------------------------------------------------*)
(* Input: ifn 0 v0 ... vn = NONE                                             *)
(*---------------------------------------------------------------------------*)

fun limit_spec_def base_case =
 let val (fvar,args) = strip_comb(lhs base_case)
     val args' = tl args
     val (fname,ty) = dest_var fvar
     val fconst = mk_const (fname,ty)
     val lim_name = fname^"Lim"
     val limvar = Lib.with_flag(Globals.priming,SOME"_")
                   (variant (all_vars base_case)) (mk_var(lim_name,num))
     val fapp = mk_is_some(list_mk_comb(fconst, limvar::args'))
     val tm' = list_mk_forall(args',mk_exists(limvar,fapp))
 in
   DEFCHOOSE (lim_name^"_spec", lim_name, tm')
 end
 handle e => raise wrap_exn "Index" "limit_spec_def" e;

fun pfn_def fname limspec_thm =
 let val tm = snd(dest_imp(snd(strip_forall(concl limspec_thm))))
     val ifn_app = dest_is_some tm
     val (const,args) = strip_comb ifn_app
     val args' = tl args
     val ty = list_mk_fun(map type_of args',type_of ifn_app)
     val pfn_name = "p"^fname
     val pfn_var = mk_var(pfn_name,ty)
     val deftm = mk_eq(list_mk_comb(pfn_var,args'),ifn_app)
 in
  new_definition (pfn_name^"_def",deftm)
 end
 handle e => raise wrap_exn "Index" "pfn_def" e;

fun fn_def name pfn_def =
 let val pfn_app = lhs(snd(strip_forall(concl pfn_def)))
     val (pfn,args) = strip_comb pfn_app
     val (dtys,rty) = strip_fun (type_of pfn)
     val fn_var = mk_var(name,list_mk_fun(dtys,dest_option rty))
     val lapp = list_mk_comb(fn_var,args)
     val deftm = mk_eq(lapp,mk_the pfn_app)
 in
    new_definition (name^"_def",deftm)
 end
 handle e => raise wrap_exn "Index" "fn_def" e;

fun in_dom_def name fn_def =
 let val (lapp,rapp) = dest_eq(snd(strip_forall(concl fn_def)))
     val (lfn,args) = strip_comb lapp
     val right = mk_is_some(dest_the rapp)
     val dname = "in_dom_"^name
     val dom_var = mk_var(dname,list_mk_fun(map type_of args,bool))
     val deftm = mk_eq(list_mk_comb(dom_var, args),right)
 in
   new_definition (dname^"_def",deftm)
 end
 handle e => raise wrap_exn "Index" "in_dom_def" e;

fun mk_defs tm =
 let open TotalDefn
     val (peqns, ieqns, vfns, base_cases) = alt_eqns tm
     val ivar = fst(strip_comb(lhs(snd(strip_forall(hd ieqns)))))
     val iname = fst(dest_var ivar)
     val idef = tDefine iname `^(list_mk_conj ieqns)` (WF_REL_TAC`measure FST`)
     val limspec_thms = map limit_spec_def base_cases
     val names = map (fst o dest_var) vfns
     val pfn_defs = map2 pfn_def names limspec_thms
     val fn_defs =  map2 fn_def names pfn_defs
     val dom_defs = map2 in_dom_def names fn_defs
 in
  (peqns,idef,limspec_thms,pfn_defs,fn_defs,dom_defs)
 end;

fun cross_prod [] l2 = []
  | cross_prod (h::t) l2 = map (pair h) l2 @ cross_prod t l2;

fun merge pn ((alist,b),(blist,e)) = (alist@[if pn then b else mk_neg b]@blist,e);

fun merge_paths bpaths pospaths negpaths =
  map (merge true) (cross_prod bpaths pospaths) @
  map (merge false) (cross_prod bpaths negpaths);

(*---------------------------------------------------------------------------*)
(* Collect maximal non-if terms on rhs, plus accumulate recursive calls.     *)
(*---------------------------------------------------------------------------*)

fun paths vfns tm =
 if is_cond tm
   then let val (b,t1,t2) = dest_cond tm
        in merge_paths (paths vfns b) (paths vfns t1) (paths vfns t2)
        end else
 if TypeBase.is_case tm
   then let val (cconst,ob,clauses) = TypeBase.dest_case tm
            val (pats,rhsl) = unzip clauses
            val plists = map (paths vfns) rhsl
            fun patch pat plist = map (fn (ctxt,e) => (mk_eq(ob,pat)::ctxt,e)) plist
            val patched = map2 patch pats plists
        in flatten patched
        end else
 if is_let tm
   then let val (binds, body) = dest_anylet tm
            val plist = paths vfns body
            fun patch (x,M) (ctxt,e) = (mk_eq(x,M)::ctxt, body)
        in map (fn path => itlist patch binds path) plist
       end else
 if is_comb tm
   then let val (f,_) = strip_comb tm
        in if mem f vfns
            then [([mk_is_some tm],tm)]
            else [([],tm)]
       end
 else [([],tm)];

fun list_mk_conj_imp ([],b) = b
  | list_mk_conj_imp (blist,b) = mk_imp(list_mk_conj blist,b);

(*---------------------------------------------------------------------------*)
(* Adding index pattern (0,SUC) may duplicate clauses, which is unfortunate, *)
(* because I can't then just use peqns to generate my proof obligations.     *)
(* Instead, I have to use the post-pattern match translation arising from    *)
(* idef and then change those into corresponding pfn equations. That will    *)
(* ensure that the idef will always be able to be applied as a rewrite in    *)
(* proofs. Example : ack 0 n = SOME(n+1), but pattern-match translation with *)
(* depth added results in this turning into two equations                    *)
(*                                                                           *)
(* iack (SUC d) 0 0 = SOME(0+1) and iack (SUC d) 0 (SUC n) = SOME(SUC n + 1) *)
(*                                                                           *)
(* so if we generated a pack 0 n = SOME (n+1) goal that wouldn't work because*)
(* the rewrite rules for iack are too specific to rewrite that.              *)
(*---------------------------------------------------------------------------*)

fun pgoals peqns idef =
 let fun fn_of clause = fst(strip_comb(lhs(snd(strip_forall clause))))
     val vpfns = mk_set(map fn_of peqns)
     val cpfns = map (mk_const o dest_var) vpfns
     val idefs = strip_conj(snd(strip_forall(concl idef)))
     val idefs' = map (snd o strip_forall) (tl idefs)
     val ifns = mk_set(map fn_of idefs')
     val _ = assert (fn () => length ifns = length cpfns) ()
     fun mk_rule ifn pfn = mk_thm([],``^ifn ^(mk_var("n",num)) = ^pfn``)
     val rules = map2 mk_rule ifns cpfns
     fun transform ieqn = rhs(concl(QCONV(REWRITE_CONV rules) ieqn))
     val peqns' = map transform idefs'
     val plists = map (fn eqn => (lhs eqn, paths vpfns (rhs eqn))) peqns'
     fun mk_goal left (ctxt,e) = list_mk_conj_imp(ctxt,mk_eq(left,e))
     fun mk_goals (left,list) = map (mk_goal left) list
     val raw_goals = flatten (map mk_goals plists)
 in
   raw_goals
 end;

fun test tm =
  let val (peqns,idef,limspec_thms,pfn_defs,fn_defs,dom_defs) = mk_defs tm
      val goals = pgoals peqns idef
  in
   app (fn tm => ignore(set_goal([],tm))) (rev goals);
   (peqns,idef,limspec_thms,pfn_defs,fn_defs,dom_defs)
  end;

STOP;



fun BASE_DEFINED_TAC idef limspec ifn_def_pos (asl,goal) =
 let val (ifn,args) = strip_comb(lhs goal)
     val args' = tl args
     val subgoal = mk_is_some(list_mk_comb(ifn,suc_zero::args'))
     val fact = EQT_ELIM
                  (REWRITE_CONV ([idef,IS_SOME_DEF]@map ASSUME asl) subgoal)
 in
  CHOOSE_THEN SUBST_ALL_TAC
        (MATCH_MP ifn_def_pos (MATCH_MP limspec fact))
 end (asl,goal)
 handle e => raise wrap_exn "Index" "BASE_DEFINED_TAC" e;

fun pbase_clause pfn_def idef limspec ifn_def_pos =
 REPEAT STRIP_TAC THEN REPEAT BasicProvers.VAR_EQ_TAC THEN
 PURE_REWRITE_TAC [pfn_def] THEN
 BASE_DEFINED_TAC idef limspec ifn_def_pos THEN
 ASM_REWRITE_TAC [idef]

fun precursive_clause pfn_def idef limspec = ...

val (peqns,idef,limspec_thms,pfn_defs,fn_defs,dom_defs) = test ack_tm;

(* Base case *)
val [pfn_def] = pfn_defs;
val [limspec] = limspec_thms;
val ifn_def_pos = Q.prove
(`!d m n. IS_SOME(iack d m n) ==> ?e. d = SUC e`,
 Cases THEN RW_TAC std_ss [idef]);

e (pbase_clause pfn_def idef limspec ifn_def_pos);

(* Recursive case *)
(* Recursive case *)

dropn 12;

(* factorial *)
val (peqns,idef,limspec_thms,pfn_defs,fn_defs,dom_defs) = test fact_tm;

val [pfn_def] = pfn_defs;
val [limspec] = limspec_thms;
val ifn_def_pos = Q.prove
(`!d n. IS_SOME(ifact d n) ==> ?e. d = SUC e`,
 Cases THEN RW_TAC std_ss [idef]);

(* Base case *)
e (pbase_clause pfn_def idef limspec ifn_def_pos);

(*Recursive case *)

(* 91 *)
val (peqns,idef,limspec_thms,pfn_defs,fn_defs,dom_defs) = test f91_tm;

val [pfn_def] = pfn_defs;
val [limspec] = limspec_thms;
val ifn_def_pos = Q.prove
(`!d n. IS_SOME(if91 d n) ==> ?e. d = SUC e`,
 Cases THEN RW_TAC std_ss [idef]);

(* Base case *)
e (pbase_clause pfn_def idef limspec ifn_def_pos);

(* Ack by complex patterns ... fails because of pattern expansion. *)
val (peqns,idef,limspec_thms,pfn_defs,fn_defs,dom_defs) = test ack1_tm;

(* Base case *)
val [pfn_def] = pfn_defs;
val [limspec] = limspec_thms;
val ifn_def_pos = Q.prove
(`!d m n. IS_SOME(iack d m n) ==> ?e. d = SUC e`,
 Cases THEN RW_TAC std_ss [idef]);

e (pbase_clause pfn_def idef limspec ifn_def_pos);
drop();
e (pbase_clause pfn_def idef limspec ifn_def_pos);

(* Recursive case *)
(* Recursive case *)

