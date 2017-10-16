structure Induction :> Induction =
struct

open HolKernel boolLib Rules wfrecUtils;

type thry = TypeBasePure.typeBase

val ERR = mk_HOL_ERR "Induction";

fun induct_info db s =
 Option.map (fn facts => {nchotomy = TypeBasePure.nchotomy_of facts,
                          constructors = TypeBasePure.constructors_of facts})
           (TypeBasePure.prim_get db s);

(*---------------------------------------------------------------------------*)
(*                                                                           *)
(*           [x_1,...,x_n]     ?v_1...v_n. M[v_1,...,v_n]                    *)
(*     -----------------------------------------------------------           *)
(*     ( M[x_1,...,x_n], [(x_i,?v_1...v_n. M[v_1,...,v_n]),                  *)
(*                        ...                                                *)
(*                        (x_j,?v_n. M[x_1,...,x_(n-1),v_n])] )              *)
(*                                                                           *)
(* This function is totally ad hoc. It's used in the production of the       *)
(* induction theorem. The nchotomy theorem can have clauses that look like   *)
(*                                                                           *)
(*     ?v1..vn. z = C vn..v1                                                 *)
(*                                                                           *)
(* in which the order of quantification is not the order of occurrence of the*)
(* quantified variables as arguments to C. Since we have no control over this*)
(* aspect of the nchotomy theorem, we make the correspondence explicit by    *)
(* pairing the incoming new variable with the term it gets beta-reduced into.*)
(* ------------------------------------------------------------------------- *)

(* fun assoc1 x = Lib.total(snd o Lib.first (aconv x o fst));  *)

local fun assoc1 eq item =
        let val eek = eq item
            fun assc [] = NONE
              | assc ((entry as (key,_))::rst) =
                  if eek key then SOME entry else assc rst
        in assc
        end
      fun foo NONE = raise ERR "alpha_ex_unroll" "no correspondence"
        | foo (SOME(_,v)) = v
in
fun alpha_ex_unroll xlist tm =
  let open boolSyntax
      val (qvars,body) = strip_exists tm
      val vlist = #2(strip_comb (rhs body))
      val plist = zip vlist xlist
      val args = map (C (assoc1 aconv) plist) qvars
      val args' = map foo args
      fun build ex [] = []
        | build ex (v::rst) =
           let val ex1 = beta_conv(mk_comb(rand ex, v))
           in ex1::build ex1 rst
           end
  in
    case rev (tm::build tm args')
     of nex::exl => (nex, zip args' (rev exl))
      | []       => raise ERR "alpha_ex_unroll" "empty"
  end
end;


(*---------------------------------------------------------------------------*)
(*                                                                           *)
(*             PROVING COMPLETENESS OF PATTERNS                              *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun ipartition gv (constructors,rows) =
let fun pfail s = raise ERR"ipartition.part" s
    fun part {constrs = [],   rows = [],   A} = rev A
      | part {constrs = [],   rows = _::_, A} = pfail"extra cases in defn"
      | part {constrs = _::_, rows = [],   A} = pfail"cases missing in defn"
      | part {constrs = c::crst, rows,     A} =
         let val {Name,Thy,Ty} = dest_thy_const c
             val (L,_) = strip_fun_type Ty
             fun func (row as (p::rst, rhs)) (in_group,not_in_group) =
                       let val (pc,args) = strip_comb p
                           val {Name=nm,Thy=thyn,...} = dest_thy_const pc
                       in if (nm,thyn) = (Name,Thy)
                            then ((args@rst, rhs)::in_group, not_in_group)
                            else (in_group, row::not_in_group)
                       end
               | func _ _ = pfail "func" ""
             val (in_group, not_in_group) = itlist func rows ([],[])
             val col_types = #1(wfrecUtils.gtake type_of
                                  (length L, #1(Lib.trye hd in_group)))
         in
         part{constrs = crst,
              rows = not_in_group,
              A = {constructor = c,
                   new_formals = map gv col_types,
                   group = in_group}::A}
         end
in
    part {constrs=constructors, rows=rows, A=[]}
end;

(*---------------------------------------------------------------------------*)
(* Partition rows where the first pattern is a literal (possibly a variable) *)
(* We'll just use regular term equality to make the partition.               *)
(*---------------------------------------------------------------------------*)

fun lpartition (lits,rows) =
let fun lfail s = raise ERR"lpartition.part" s
    fun lit_eq l1 l2 = if Literal.is_literal l1 then aconv l1 l2 else
                       (is_var l1 andalso is_var l2)
    fun pfun lit (row as (p::rst, rhs)) (in_group,not_in_group) =
        if lit_eq lit p then ((rst,rhs)::in_group, not_in_group)
                       else (in_group, row::not_in_group)
      | pfun _ _ _ = lfail "pfun" ""
    fun part [] [] A = rev A
      | part [] (_::_) A = lfail"extra cases in defn"
      | part (_::_) [] A = lfail"cases missing in defn"
      | part (lit::rst) rows A =
          let val (in_group, not_in_group) = itlist (pfun lit) rows ([],[])
          in  part rst not_in_group ((lit,in_group)::A)
          end
 in
     part lits rows []
 end;

fun rm x [] = [] | rm x (h::t) = if aconv x h then rm x t else h::rm x t;

fun distinct [] = []
  | distinct (h::t) = h::distinct(rm h t);

(*---------------------------------------------------------------------------*)
(* Need to handle fact that 0 is both a literal and a constructor            *)
(*---------------------------------------------------------------------------*)

type divide_ty
 = term list
    * (term list * (thm * (term, term) subst)) list
   -> {constructor : term,
       group       : (term list * (thm * (term, term) subst)) list,
       new_formals : term list} list;

fun bring_to_front_list n l = let
   val (l0, l1) = Lib.split_after n l
   val (x, l1') = (hd l1, tl l1)
  in x :: (l0 @ l1') end

fun undo_bring_to_front n l = let
   val (x, l') = (hd l, tl l)
   val (l0, l1) = Lib.split_after n l'
 in (l0 @ x::l1) end

(*
val org_in = {path=[z], rows=rows}

val in_1 = hd news
val in_2 = {path=rstp, rows=zip pat_rectangle' rights'}
val in_3 = hd news

mk in_2
v
val {path=u::rstp, rows as (p::_, _)::_} = in_3

val {path=u::rstp, rows as (p::_, _)::_} = {path=rstp, rows=zip pat_rectangle' rights'}
val mk = mk_case ty_info FV thy
mk in_1
val in

hm = mk_case ty_info FV thy {path=[z], rows=rows}

val arg0 = {path=[z], rows=rows}
val {path=rstp0, rows = rows0} = el 1 news
*)


fun mk_case_choose_column i rows =
let
  val col_i = map (fn (l, _) => el (i+1) l) rows

  val col_i_ok =
    (all is_var col_i) orelse
    (all (fn p => Literal.is_literal p orelse is_var p) col_i) orelse
    (all (fn p => not (Literal.is_pure_literal p) andalso not (is_var p)) col_i)
in
  if col_i_ok then i else mk_case_choose_column (i+1) rows
end handle HOL_ERR _ => 0

val quiet_metis = Feedback.trace ("metis", 0) (metisLib.METIS_PROVE [])
val quiet_meson = Feedback.trace ("meson", 0) (BasicProvers.PROVE [])

fun mk_case ty_info FV thy =
 let open boolSyntax
 val gv = (wfrecUtils.vary FV)
 val divide:divide_ty = ipartition gv
 fun fail s = raise ERR "mk_case" s
 fun mk{rows=[],...} = fail"no rows"
   | mk{path=[], rows = [([], (thm, bindings))]} = IT_EXISTS bindings thm
   | mk{path=rstp0, rows= rows0 as ((_::_, _)::_)} =
     let val col_index = mk_case_choose_column 0 rows0
         val rows = map (fn (pL, rhs) => (bring_to_front_list col_index pL, rhs)) rows0
         val (pat_rectangle,rights) = unzip rows
         val u_rstp = bring_to_front_list col_index rstp0
         val (u, rstp) = (hd u_rstp, tl u_rstp)
         val p = hd (fst (hd rows))
         val col0 = map (Lib.trye hd) pat_rectangle
         val pat_rectangle' = map (Lib.trye tl) pat_rectangle
     in
     if all is_var col0 (* column 0 is all variables *)
     then let val rights' = map (fn ((thm,theta),v) => (thm,theta@[u|->v]))
                                (zip rights col0)
          in mk{path=rstp, rows=zip pat_rectangle' rights'}
          end
     else
     if exists Literal.is_pure_literal col0  (* col0 matches against literals *)
     then let val lits = distinct col0
           val (litpats, varpats) = Lib.partition (not o is_var) lits
           val liteqs = map (curry mk_eq u) litpats
           fun neglits v = map (fn lit => mk_neg(mk_eq(v,lit))) litpats
           val altliteqs = map neglits varpats
           val vareqs = map (curry mk_eq u) varpats
           val var_constraints = map2
              (fn veq => fn nlits => list_mk_conj(veq::nlits)) vareqs altliteqs
           val eqs = liteqs @ var_constraints
           fun exquant tm =
             if is_conj tm
               then let val x = rhs(fst(dest_conj tm))
                    in mk_exists(x,tm)
                    end
               else tm
           val disjuncts = map exquant eqs
           val thm' = quiet_metis (list_mk_disj disjuncts)
           val subproblems = lpartition(lits,rows)
           val groups = map snd subproblems
           val geqs = zip groups eqs
           fun expnd c (pats,(th,b)) =
              if is_eq c then (pats, (SUBS[ASSUME c]th, b))
                 else let val lem = ASSUME c
                          val veq = CONJUNCT1 lem
                          val v = rhs(concl veq)
                          val constraints = CONJUNCT2 lem
                          val b' = b@[v|->v]
                      in (pats, (CONJ (SUBS [veq]th) constraints, b'))
                      end
           val news = map(fn(grp,c) => {path=rstp,rows=map (expnd c) grp}) geqs
           val recursive_thms = map mk news
           fun left_exists tm thm =
             if is_exists tm
               then let val (v,_) = dest_exists tm
                    in CHOOSE (v,ASSUME tm) thm
                    end
               else thm
           val vexl = liteqs @ map2 (curry mk_exists) varpats var_constraints
           val thms' = map2 left_exists vexl recursive_thms
           val same_concls = EVEN_ORS thms'
         in
           DISJ_CASESL thm' same_concls
         end
     else
     (* column 0 matches against constructors (and perhaps variables) *)
     let val {Thy, Tyop = ty_name,...} = dest_thy_type (type_of p)
     in
     case ty_info (Thy,ty_name)
      of NONE => fail("Not a known datatype: "^ty_name)
         (* tyinfo rqt: `constructors' must line up exactly with constrs
            in disjuncts of `nchotomy'. *)
       | SOME{constructors,nchotomy} =>
(*
  val SOME{constructors,nchotomy} = ty_info (Thy,ty_name)
*)
         let val thm'         = ISPEC u nchotomy
             val disjuncts    = strip_disj (concl thm')
             val subproblems  = divide(constructors, rows)
             val groups       = map #group subproblems
             and new_formals  = map #new_formals subproblems
             val existentials = map2 alpha_ex_unroll new_formals disjuncts
             val constraints  = map #1 existentials
             val vexl         = map #2 existentials
             fun expnd tm (pats,(th,b)) = (pats,(SUBS[ASSUME tm]th, b))
             val news = map (fn (nf,rows,c) => {path = nf@rstp,
                                                rows = map (expnd c) rows})
                            (zip3 new_formals groups constraints)
             val recursive_thms = map mk news
             val build_exists = itlist(CHOOSE o (I##ASSUME))
             val thms' = map2 build_exists vexl recursive_thms
             val same_concls = EVEN_ORS thms'
         in
           DISJ_CASESL thm' same_concls
         end
     end end
   | mk _ = fail"blunder"
in
 mk
end;

type row = term list * (thm * (term, term) subst)

fun complete_cases thy =
 let val ty_info = induct_info thy
 in fn pats =>
     let val FV0 = free_varsl pats
         val a = variant FV0 (mk_var("a",type_of(Lib.trye hd pats)))
         val z = variant (a::FV0) (mk_var("z",type_of a))
         val FV = a::z::FV0
         val a_eq_z = mk_eq(a,z)
         val ex_th0 = EXISTS (mk_exists(z,a_eq_z),a) (REFL a)
         val th0    = ASSUME a_eq_z
         val rows:row list = map (fn x => ([x], (th0,[]))) pats

         val cases_thm0 = mk_case ty_info FV thy {path=[z], rows=rows}

         fun mk_pat_pred p = list_mk_exists (free_vars_lr p, mk_eq(a, p))
         val cases_tm = list_mk_disj (map mk_pat_pred pats)
         val imp_thm = quiet_meson (mk_imp (concl cases_thm0, cases_tm))
         val cases_thm = MP imp_thm cases_thm0
     in
       GEN a (RIGHT_ASSOC (CHOOSE(z, ex_th0) cases_thm))
     end
 end;


(*---------------------------------------------------------------------------*
 * Constructing induction hypotheses: one for each recursive call.           *
 *---------------------------------------------------------------------------*)

local nonfix ^ ;   infix 9 ^  ;     infix 5 ==>
      fun (tm1 ^ tm2)   = mk_comb(tm1, tm2)
      fun (tm1 ==> tm2) = mk_imp(tm1, tm2)
      val /\ = list_mk_conj
      val diff = op_set_diff aconv
in
fun build_ih f (P,R,SV) (pat,TCs) =
 let val pat_vars = free_vars_lr pat
     val globals = (if is_var R then [R] else [])@pat_vars@SV
     fun nested tm = can(find_term (aconv f)) tm handle _ => false
     fun dest_TC tm =
         let val (cntxt,R_y_pat) = wfrecUtils.strip_imp(#2(strip_forall tm))
             val (R,y,_) = wfrecUtils.dest_relation R_y_pat
             val P_y     = if nested tm then R_y_pat ==> P^y else P^y
             val ihyp    = case cntxt of [] => P_y | _ => /\cntxt ==> P_y
             val locals  = diff (free_vars_lr ihyp) (P::globals)
         in
           (list_mk_forall(locals,ihyp), (tm,locals))
         end
 in case TCs
     of [] => (list_mk_forall(pat_vars, P^pat), [])
      |  _ => let val (ihs, TCs_locals) = unzip(map dest_TC TCs)
                  val ind_clause = /\ihs ==> P^pat
              in
                 (list_mk_forall(pat_vars,ind_clause), TCs_locals)
              end
 end
end;


(*---------------------------------------------------------------------------*
 * This function makes good on the promise made in "build_ih: it proves      *
 * each case of the induction.                                               *
 *                                                                           *
 * Input  is tm = "(!y. R y pat ==> P y) ==> P pat",                         *
 *          TCs = TC_1[pat] ... TC_n[pat]                                    *
 *          thm = ih1 /\ ... /\ ih_n ==> ih[pat]                             *
 *---------------------------------------------------------------------------*)

fun prove_case f thy (tm,TCs_locals,thm) =
 let val antc = fst(dest_imp tm)
     val thm' = SPEC_ALL thm
     fun nested tm = can(find_term (aconv f)) tm handle HOL_ERR _ => false
     fun get_cntxt TC = fst(dest_imp(#2(strip_forall(concl TC))))
     fun mk_ih ((TC,locals),th2,nested) =
         GENL locals
            (if nested
              then DISCH (get_cntxt TC) th2 handle HOL_ERR _ => th2
               else if is_imp(concl TC)
                     then IMP_TRANS TC th2
                      else MP th2 TC)
 in
 DISCH antc
   (if is_imp(concl thm') (* recursive calls in this clause *)
    then let val th1     = ASSUME antc
             val TCs     = map #1 TCs_locals
             val ylist   = map (#2 o dest_relation o #2 o
                                wfrecUtils.strip_imp o #2 o strip_forall) TCs
             val TClist  = map (fn(TC,lvs) => (SPECL (fst (strip_forall TC)) (ASSUME TC),lvs))
                                TCs_locals
             val th2list = map (C SPEC th1) ylist
             val nlist   = map nested TCs
             val triples = zip3 TClist th2list nlist
             val Pylist  = map mk_ih triples
         in
            MP thm' (LIST_CONJ Pylist)
         end
    else thm')
 end;


fun detuple newvar =
  let fun detup M =
     if pairLib.is_pair M
     then let val (M1,M2) = pairSyntax.dest_pair M
              val ((M1',vars1), (M2',vars2)) = (detup M1, detup M2)
          in (pairLib.mk_pair(M1',M2'), vars1@vars2)
          end
     else let val v = newvar (type_of M) in (v,[v]) end
 in detup
 end;

(*---------------------------------------------------------------------------*)
(* For monitoring how much time and inferences building the induction        *)
(* theorem takes.                                                            *)
(*---------------------------------------------------------------------------*)

val monitoring = ref 0;

val _ = Feedback.register_trace("tfl_ind",monitoring,1);

(*---------------------------------------------------------------------------*
 * Input : f, R, SV, and  [(pat1,TCs1),..., (patn,TCsn)]                     *
 *                                                                           *
 * Instantiates WF_INDUCTION_THM, getting Sinduct and then tries to prove    *
 * recursion induction (Rinduct) by proving the antecedent of Sinduct from   *
 * the antecedent of Rinduct.                                                *
 *---------------------------------------------------------------------------*)

(*
fun mk_induction thy {fconst, R, SV, pat_TCs_list} =
let fun f() =
let val Sinduction = UNDISCH (ISPEC R relationTheory.WF_INDUCTION_THM)
    val (pats,TCsl) = unzip pat_TCs_list
    val case_thm = complete_cases thy pats
    val domn = (type_of o (Lib.trye hd)) pats
    val P = variant (all_varsl (pats@flatten TCsl)) (mk_var("P",domn-->bool))
    val Sinduct = SPEC P Sinduction
    val Sinduct_assumf = rand ((fst o dest_imp o concl) Sinduct)
    val Rassums_TCl' = map (build_ih fconst (P,R,SV)) pat_TCs_list
    val (Rassums,TCl') = unzip Rassums_TCl'
    val Rinduct_assum = ASSUME (list_mk_conj Rassums)
    val cases = map (beta_conv o curry mk_comb Sinduct_assumf) pats
    val tasks = zip3 cases TCl' (CONJUNCTS Rinduct_assum)
    val proved_cases = map (prove_case fconst thy) tasks
    val v = variant (free_varsl (map concl proved_cases)) (mk_var("v",domn))
    val substs = map (SYM o ASSUME o curry mk_eq v) pats
    val proved_cases1 = map2 (fn th => SUBS[th]) substs proved_cases
    val abs_cases = map Rules.LEFT_ABS_VSTRUCT proved_cases1
    val dant = GEN v (DISJ_CASESL (ISPEC v case_thm) abs_cases)
    val dc = MP Sinduct dant
    val (vstruct,vars) = detuple (wfrecUtils.vary[P]) (hd pats)
    val dc' = itlist GEN vars (SPEC vstruct dc)
in
   GEN P (DISCH (concl Rinduct_assum) dc')
end
handle e => raise wrap_exn "Induction" "mk_induction" e
in
  if !monitoring > 0 then Count.apply f () else f()
end
*)


(*---------------------------------------------------------------------------*)
(* A clause of the case_thm can have one of the following forms:             *)
(*                                                                           *)
(*    ?vlist. (var = tm)                                                     *)
(*    ?vlist. (var = tm) /\ constraints  (* literal pattern *)               *)
(*                                                                           *)
(* We want to match tm against pat, to get theta, which will be applied to   *)
(* the clause. The reason for this is that "proved_cases" needs to align     *)
(* with the clauses in case_thm. In case it doesn't, match_clauses is called *)
(* to restore alignment.                                                     *)
(*---------------------------------------------------------------------------*)

fun var_pure theta = Lib.all (fn {redex,residue} => is_var residue) theta;

fun match_clause pat clause =
 let open boolSyntax
     val (V,tm) = strip_exists clause
 in case strip_conj tm
     of [] => raise ERR "match_clause" "unexpected structure in case_thm"
      | xeq::constraints =>
        let val (x,target) = dest_eq xeq
        in case Term.match_term target pat
            of ([],[]) => clause
             | (theta,[]) =>
                 if var_pure theta
                 then list_mk_exists(map (subst theta) V, subst theta tm)
                 else raise ERR "match_clause" "no match"
            | (theta,tytheta) => raise ERR "match_clause" "inequal types"
        end
 end;

fun match_clauses pats case_thm =
 let val clauses = strip_disj (concl case_thm)
     fun match [] [] = []
       | match (p1::rst) (clauses as (_::_)) =
           let open Lib
               val (cl,clauses') = trypluck (match_clause p1) clauses
           in cl::match rst clauses'
           end
       | match other wise = raise ERR "match_clauses" "different lengths"
 in
  EQ_MP (EQT_ELIM
          (AC_CONV (DISJ_ASSOC,DISJ_SYM)
               (mk_eq(concl case_thm,
                      list_mk_disj (match pats clauses)))))
       case_thm
 end
 handle e => raise wrap_exn "Induction" "match_clauses" e;

(*---------------------------------------------------------------------------*)
(* Input : f, R, SV, and  [(pat1,TCs1),..., (patn,TCsn)]                     *)
(*                                                                           *)
(* Instantiates WF_INDUCTION_THM, getting Sinduct and then tries to prove    *)
(* recursion induction (Rinduct) by proving the antecedent of Sinduct from   *)
(* the antecedent of Rinduct.                                                *)
(*---------------------------------------------------------------------------*)

(*
val {fconst, R, SV, pat_TCs_list} = {fconst=f, R=R, SV=SV, pat_TCs_list=full_pats_TCs}
val thy = facts
 *)

fun mk_induction thy {fconst, R, SV, pat_TCs_list} =
let fun f() =
let val Sinduction = UNDISCH (ISPEC R relationTheory.WF_INDUCTION_THM)
    val (pats,TCsl) = unzip pat_TCs_list
    val case_thm = complete_cases thy pats
    val domn = (type_of o (Lib.trye hd)) pats
    val P = variant (all_varsl (pats@flatten TCsl)) (mk_var("P",domn-->bool))
    val Sinduct = SPEC P Sinduction
    val Sinduct_assumf = rand ((fst o dest_imp o concl) Sinduct)
    val Rassums_TCl' = map (build_ih fconst (P,R,SV)) pat_TCs_list
    val (Rassums,TCl') = unzip Rassums_TCl'
    val Rinduct_assum = ASSUME (list_mk_conj Rassums)
    val cases = map (beta_conv o curry mk_comb Sinduct_assumf) pats
    val tasks = zip3 cases TCl' (CONJUNCTS Rinduct_assum)
    val proved_cases = map (prove_case fconst thy) tasks
    val v = variant (free_varsl (map concl proved_cases)) (mk_var("v",domn))
    val case_thm' = ISPEC v case_thm
    val case_thm'' = match_clauses pats case_thm' (* align case_thm' with pats *)
    fun mk_subst tm =
        if is_eq tm then SYM (ASSUME tm)
        else SYM (hd (CONJUNCTS (ASSUME (snd(strip_exists tm)))))
    val substs = map mk_subst (strip_disj (concl case_thm''))
    (* Now elim pats in favour of variables *)
    val proved_cases1 = map (PURE_REWRITE_RULE substs) proved_cases
    val abs_cases = map LEFT_EXISTS proved_cases1
    val dant = GEN v (DISJ_CASESL case_thm'' abs_cases)
    val dc = MP Sinduct dant
    val (vstruct,vars) = detuple (wfrecUtils.vary[P]) (hd pats)
    val dc' = itlist GEN vars (SPEC vstruct dc)
in
   GEN P (DISCH (concl Rinduct_assum) dc')
end
handle e => raise wrap_exn "Induction" "mk_induction" e
in
  if !monitoring > 0 then Count.apply f () else f()
end;

(*---------------------------------------------------------------------------*)
(*         Recursion induction tactic. Taken from tflLib.                    *)
(*                                                                           *)
(* Given a goal `!v1 ... vn. M`, and an induction theorem of the form        *)
(* returned by TFL, i.e.,                                                    *)
(*                                                                           *)
(*   !P. clause_1 /\ ... /\ clause_n                                         *)
(*          ==>                                                              *)
(*        !u1 ... uk. P vstr_1 ... vstr_j                                    *)
(*                                                                           *)
(* we use v1 ... vk to rename the varstructs vstr_1 ... vstr_j to variables  *)
(* in the goal. Thus the binding prefix of the goal is used to make the      *)
(* predicate with which P is instantiated.                                   *)
(*---------------------------------------------------------------------------*)

fun rename_tuple tm [] = (tm,[])
  | rename_tuple tm (vlist as (h::t)) =
     let open pairSyntax
     in if is_var tm then (h,t)
        else let val (p1,p2) = dest_pair tm
                 val (p1',vlist') = rename_tuple p1 vlist
                 val (p2',vlist'') = rename_tuple p2 vlist'
             in (mk_pair (p1',p2'), vlist'')
            end
     end;

fun rename_tuples [] vlist = ([],vlist)
  | rename_tuples (tmlist as (h::t)) vlist =
    let val (tuple,vlist') = rename_tuple h vlist
        val (tuples,vlist'') = rename_tuples t vlist'
    in (tuple::tuples, vlist'')
    end
    handle e => raise wrap_exn "Induction" "rename_tuples" e;

fun ndest_forall n trm =
  let fun dest (0,tm,V) = (rev V,tm)
        | dest (n,tm,V) =
           let val (Bvar,Body) = dest_forall tm
                  handle _ => raise ERR "ndest_forall"
                  "too few quantified variables in goal"
           in dest(n-1,Body, Bvar::V)
           end
  in dest(n,trm,[])
  end;

fun recInduct thm =
  let open pairLib
      val (prop,Body) = dest_forall(concl thm)
      val c = snd (strip_imp Body)
      val Pargs = snd(strip_comb(snd(strip_forall c)))
      val n = (length o #1 o strip_forall o #2 o strip_imp) Body
      fun tac (asl,w) =
       let val (V,body) = ndest_forall n w
           val (vstrl,extras) = rename_tuples Pargs V
           val _ = if not (null extras)
                     then raise ERR "recInduct" "internal error" else ()
           val P = list_mk_pabs(vstrl,body)
           val thm' = GEN_BETA_RULE (ISPEC P thm)
       in MATCH_MP_TAC thm' (asl,w)
       end
  in tac
  end
  handle e => raise wrap_exn "Induction" "recInduct" e;

(*
fun mk_vstrl [] V A = rev A
  | mk_vstrl (ty::rst) V A =
      let val (vstr,V1) = unstrip_pair ty V
      in mk_vstrl rst V1 (vstr::A)
      end;

fun recInduct thm =
  let val (prop,Body) = dest_forall(concl thm)
      val parg_tyl = #1(strip_fun (type_of prop))
      val n = (length o #1 o strip_forall o #2 o strip_imp) Body
      fun ndest_forall trm =
          let fun dest (0,tm,V) = (rev V,tm)
                | dest (n,tm,V) =
                    let val (Bvar,Body) = dest_forall tm
                    in dest(n-1,Body, Bvar::V) end
          in dest(n,trm,[])
          end
      fun tac (asl,w) =
       let val (V,body) = ndest_forall w
           val P = (list_mk_pabs(mk_vstrl parg_tyl V [],body)
                    handle HOL_ERR _ => list_mk_abs(V,body))
           val thm' = GEN_BETA_RULE (ISPEC P thm)
       in MATCH_MP_TAC thm' (asl,w)
       end
  in tac
  end
  handle e => raise wrap_exn "Induction" "recInduct" e
*)

end
