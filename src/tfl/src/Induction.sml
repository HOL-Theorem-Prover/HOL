structure Induction :> Induction =
struct

open HolKernel boolLib Rules wfrecUtils;

type thry = TypeBase.typeBase

infixr 3 -->;
infix 3 |->;
infix 4 ##;

val ERR = mk_HOL_ERR "Induction";


fun induct_info db s =
case TypeBase.get db s
 of SOME facts => SOME{nchotomy = TypeBase.nchotomy_of facts,
                       constructors = TypeBase.constructors_of facts}
  | NONE => NONE

(* -----------------------  Miscellaneous function  --------------------------
 *
 *           [x_1,...,x_n]     ?v_1...v_n. M[v_1,...,v_n]
 *     -----------------------------------------------------------
 *     ( M[x_1,...,x_n], [(x_i,?v_1...v_n. M[v_1,...,v_n]),
 *                        ...
 *                        (x_j,?v_n. M[x_1,...,x_(n-1),v_n])] )
 *
 * This function is totally ad hoc. It's used in the production of the
 * induction theorem. The nchotomy theorem can have clauses that look like
 *
 *     ?v1..vn. z = C vn..v1
 *
 * in which the order of quantification is not the order of occurrence of the
 * quantified variables as arguments to C. Since we have no control over this
 * aspect of the nchotomy theorem, we make the correspondence explicit by
 * pairing the incoming new variable with the term it gets beta-reduced into.
 * ------------------------------------------------------------------------- *)

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
  let val (qvars,body) = strip_exists tm
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



(*---------------------------------------------------------------------------*
 *                                                                           *
 *             PROVING COMPLETENESS OF PATTERNS                              *
 *                                                                           *
 *---------------------------------------------------------------------------*)

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


type divide_ty
 = term list
    * (term list * (thm * (term, term) subst)) list
   -> {constructor : term,
       group       : (term list * (thm * (term, term) subst)) list,
       new_formals : term list} list;

fun mk_case ty_info FV thy =
 let
 val divide:divide_ty = ipartition (wfrecUtils.vary FV)  (* do not eta-expand!! *)
 fun fail s = raise ERR"mk_case" s
 fun mk{rows=[],...} = fail"no rows"
   | mk{path=[], rows = [([], (thm, bindings))]} = IT_EXISTS bindings thm
   | mk{path=u::rstp, rows as (p::_, _)::_} =
     let val (pat_rectangle,rights) = unzip rows
         val col0 = map (Lib.trye hd) pat_rectangle
         val pat_rectangle' = map (Lib.trye tl) pat_rectangle
     in
     if all is_var col0 (* column 0 is all variables *)
     then let val rights' = map (fn ((thm,theta),v) => (thm,theta@[u|->v]))
                                (zip rights col0)
          in mk{path=rstp, rows=zip pat_rectangle' rights'}
          end
     else               (* column 0 is all constructors *)
     let val ty_name = (fst o dest_type o type_of) p
     in
     case ty_info ty_name
      of NONE => fail("Not a known datatype: "^ty_name)
         (* tyinfo rqt: `constructors' must line up exactly with constrs
            in disjuncts of `nchotomy'. *)
       | SOME{constructors,nchotomy} =>
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
 in mk
 end;


type row = term list * (thm * (term, term) subst)

(*---------------------------------------------------------------------------
    The fourth argument to "mk_case" says whether we are generating the
    case theorem from a set of patterns or from a type. Probably the
    first could be subsumed in the second, but in our implementation,
    generation from patterns came first.
 ---------------------------------------------------------------------------*)
 
fun complete_cases thy =
 let val ty_info = induct_info thy
 in fn pats =>
     let val FV0 = free_varsl pats
         val a = variant FV0 (mk_var("a",type_of(Lib.trye hd pats)))
         val v = variant (a::FV0) (mk_var("v",type_of a))
         val FV = a::v::FV0
         val a_eq_v = mk_eq(a,v)
         val ex_th0 = EXISTS (mk_exists(v,a_eq_v),a) (REFL a)
         val th0    = ASSUME a_eq_v
         val rows:row list = map (fn x => ([x], (th0,[]))) pats
     in
       GEN a (RIGHT_ASSOC
               (CHOOSE(v, ex_th0)
                 (mk_case ty_info FV thy {path=[v], rows=rows})))
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
             val TClist  = map (fn(TC,lvs) => (SPEC_ALL(ASSUME TC),lvs))
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


(*---------------------------------------------------------------------------*
 * Input : f, R, SV, and  [(pat1,TCs1),..., (patn,TCsn)]                     *
 *                                                                           *
 * Instantiates WF_INDUCTION_THM, getting Sinduct and then tries to prove    *
 * recursion induction (Rinduct) by proving the antecedent of Sinduct from   *
 * the antecedent of Rinduct.                                                *
 *---------------------------------------------------------------------------*)

fun mk_induction thy {fconst, R, SV, pat_TCs_list} =
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
    val Parg_ty = type_of(fst(dest_forall(concl dc)))
    val vars = map (wfrecUtils.vary[P]) (strip_prod_type Parg_ty)
    val dc' = itlist GEN vars (SPEC (fst(mk_vstruct Parg_ty vars)) dc)
in
   GEN P (DISCH (concl Rinduct_assum) dc')
end
handle HOL_ERR _ => raise ERR "mk_induction" "failed derivation";

end;
