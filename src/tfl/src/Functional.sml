structure Functional :> Functional =
struct

open HolKernel boolSyntax wfrecUtils;

type thry = TypeBasePure.typeBase

val ERR = mk_HOL_ERR "Functional";

val allow_new_clauses = ref true;

(*---------------------------------------------------------------------------
      Miscellaneous support
 ---------------------------------------------------------------------------*)

val stringize = list_to_string int_to_string ", ";

fun enumerate l = map (fn (x,y) => (y,x)) (Lib.enumerate 0 l);

fun match_term thry tm1 tm2 = Term.match_term tm1 tm2;
fun match_type thry ty1 ty2 = Type.match_type ty1 ty2;

fun match_info db s =
case TypeBasePure.prim_get db s
 of SOME facts => SOME{case_const = TypeBasePure.case_const_of facts,
                       constructors = TypeBasePure.constructors_of facts}
  | NONE => NONE


(*---------------------------------------------------------------------------
 * This datatype carries some information about the origin of a
 * clause in a function definition.
 *---------------------------------------------------------------------------*)

datatype pattern = GIVEN   of term * int
                 | OMITTED of term * int;   (* int arg is superfluous *)

fun pattern_cmp (GIVEN(_,i)) (GIVEN(_,j)) = i <= j
  | pattern_cmp all others = raise ERR "pattern_cmp" "";

fun psubst theta (GIVEN (tm,i)) = GIVEN(subst theta tm, i)
  | psubst theta (OMITTED (tm,i)) = OMITTED(subst theta tm,i);

fun dest_pattern (GIVEN (tm,i))   = ((GIVEN,i),tm)
  | dest_pattern (OMITTED (tm,i)) = ((OMITTED,i),tm);

fun pat_of (GIVEN (tm,_)) = tm
  | pat_of (OMITTED (tm,_)) = tm;

fun row_of_pat (GIVEN(_,i)) = i
  | row_of_pat (OMITTED _) = ~1;

fun dest_given (GIVEN(tm,_)) = tm
  | dest_given (OMITTED _) = raise ERR "OMITTED" "";

fun mk_omitted tm = OMITTED(tm,~1);

fun is_omitted (OMITTED _) = true
  | is_omitted otherwise   = false;

val givens = mapfilter dest_given;

(*---------------------------------------------------------------------------
 * Produce an instance of a constructor, plus genvars for its arguments.
 *---------------------------------------------------------------------------*)

fun fresh_constr ty_match (colty:hol_type) gv c =
  let val Ty = type_of c
      val (L,ty) = strip_fun_type Ty
      val ty_theta = ty_match ty colty
      val c' = inst ty_theta c
      val gvars = map (inst ty_theta o gv) L
  in (c', gvars)
  end;


(*---------------------------------------------------------------------------*
 * Goes through a list of rows and picks out the ones beginning with a       *
 * pattern = literal, or all those beginning with a variable if the pattern  *
 * is a variable.                                                            *
 *---------------------------------------------------------------------------*)

fun mk_groupl literal rows =
  let fun func (row as ((prefix, p::rst), rhs)) (in_group,not_in_group) =
               if (is_var literal andalso is_var p) orelse p = literal
               then if is_var literal
                    then (((prefix,p::rst), rhs)::in_group, not_in_group)
                    else (((prefix,rst), rhs)::in_group, not_in_group)
               else (in_group, row::not_in_group)
        | func _ _ = raise ERR "mk_groupl" ""
  in
    itlist func rows ([],[])
  end;

(*---------------------------------------------------------------------------*
 * Goes through a list of rows and picks out the ones beginning with a       *
 * pattern with constructor = c.                                             *
 *---------------------------------------------------------------------------*)

fun mk_group c rows =
  let fun func (row as ((prefix, p::rst), rhs)) (in_group,not_in_group) =
            let val (pc,args) = strip_comb p
            in if same_const pc c
               then (((prefix,args@rst), rhs)::in_group, not_in_group)
               else (in_group, row::not_in_group)
            end
        | func _ _ = raise ERR "mk_group" ""
  in
    itlist func rows ([],[])
  end;


(*---------------------------------------------------------------------------*
 * Partition the rows among literals. Not efficient.                         *
 *---------------------------------------------------------------------------*)

fun partitionl _ _ (_,_,_,[]) = raise ERR"partitionl" "no rows"
  | partitionl gv ty_match
              (constructors, colty, res_ty, rows as (((prefix,_),_)::_)) =
let  fun part {constrs = [],      rows, A} = rev A
       | part {constrs = c::crst, rows, A} =
         let val (in_group, not_in_group) = mk_groupl c rows
             val in_group' =
                 if (null in_group)  (* Constructor not given *)
                 then [((prefix, []), mk_omitted (mk_arb res_ty))]
                 else in_group
             val gvars = if is_var c then [c] else []
         in
         part{constrs = crst,
              rows = not_in_group,
              A = {constructor = c,
                   new_formals = gvars,
                   group = in_group'}::A}
         end
in part{constrs=constructors, rows=rows, A=[]}
end;


(*---------------------------------------------------------------------------*
 * Partition the rows. Not efficient.                                        *
 *---------------------------------------------------------------------------*)

fun partition _ _ (_,_,_,[]) = raise ERR"partition" "no rows"
  | partition gv ty_match
              (constructors, colty, res_ty,
               rows as (((prefix:term list,_),_)::_)) =
    let val fresh = fresh_constr ty_match colty gv
        fun part {constrs = [],      rows, A} = rev A
          | part {constrs = c::crst, rows, A} =
            let val (c',gvars) = fresh c
                val (in_group, not_in_group) = mk_group c' rows
                val in_group' =
                 if (null in_group)  (* Constructor not given *)
                 then [((prefix, #2(fresh c)), mk_omitted (mk_arb res_ty))]
                 else in_group
            in
             part{constrs = crst,
                  rows = not_in_group,
                   A = {constructor = c',new_formals = gvars,
                        group = in_group'}::A}
         end
    in part{constrs=constructors, rows=rows, A=[]}
    end;


(*---------------------------------------------------------------------------
 * Misc. routines used in mk_case
 *---------------------------------------------------------------------------*)

fun mk_patl c =
  let val L = if is_var c then 1 else 0
      fun build (prefix,tag,plist) =
          let val (args,plist') = wfrecUtils.gtake I (L, plist)
              val c' = if is_var c then hd args else c
           in (prefix,tag, c'::plist') end
  in map build
  end;

fun mk_pat c =
  let val L = length(#1(strip_fun_type(type_of c)))
      fun build (prefix,tag,plist) =
          let val (args,plist') = wfrecUtils.gtake I (L, plist)
           in (prefix,tag,list_mk_comb(c,args)::plist') end
  in map build
  end;

fun v_to_prefix (prefix, v::pats) = (v::prefix,pats)
  | v_to_prefix _ = raise ERR"mk_case" "v_to_prefix"

fun v_to_pats (v::prefix,tag, pats) = (prefix, tag, v::pats)
  | v_to_pats _ = raise ERR"mk_case""v_to_pats";


(* --------------------------------------------------------------
   Literals include numeric, string, and character literals.
   Boolean literals are the constructors of the bool type.
   Currently, literals may be any expression without free vars.
   These functions are not used at the moment, but may be someday.
   -------------------------------------------------------------- *)

(*
val is_literal = Literal.is_literal

fun is_lit_or_var tm = is_literal tm orelse is_var tm

fun is_zero_emptystr_or_var tm =
    Literal.is_zero tm orelse Literal.is_emptystring tm orelse is_var tm
*)

fun is_closed_or_var tm = is_var tm orelse null (free_vars tm)


(*---------------------------------------------------------------------------
   Reconstructed code from TypeBasePure, to avoid changing type of 'mk_case'.
  ---------------------------------------------------------------------------*)

fun case_const_of   {case_const : term, constructors : term list} = case_const
fun constructors_of {case_const : term, constructors : term list} = constructors

fun type_names ty =
  let val {Thy,Tyop,Args} = Type.dest_thy_type ty
  in (Thy,Tyop)
  end;

(*---------------------------------------------------------------------------
   Is a constant a constructor for some datatype.
  ---------------------------------------------------------------------------*)

fun is_constructor ty_info c =
  let val (_,ty) = strip_fun (type_of c)
  in case ty_info (type_names ty)
     of NONE => false
      | SOME tyinfo => op_mem same_const c (constructors_of tyinfo)
  end handle HOL_ERR _ => false;

fun is_constructor_pat ty_info tm =
    is_constructor ty_info (fst (strip_comb tm))

fun is_constructor_var_pat ty_info tm =
    is_var tm orelse is_constructor_pat ty_info tm

(*
fun mk_switch_tm1 gv v base literals =
    let val rty = type_of base
        val lty = type_of v
        fun mk_arg lit = if is_var lit then gv (lty --> rty) else gv rty
        val args = map mk_arg literals
        open boolSyntax
        fun mk_switch [] = base
          | mk_switch ((lit,arg)::litargs) =
                 if is_var lit then mk_comb(arg, v)
                 else mk_bool_case(arg, mk_switch litargs, mk_eq(v, lit))
    in list_mk_abs(args@[v], mk_switch (zip literals args))
    end
*)

fun mk_switch_tm gv v base literals =
    let val rty = type_of base
        val lty = type_of v
        val v' = last literals handle _ => gv lty
        fun mk_arg lit = if is_var lit then gv (lty --> rty) else gv rty
        val args = map mk_arg literals
        open boolSyntax
        fun mk_switch [] = base
          | mk_switch ((lit,arg)::litargs) =
                 if is_var lit then mk_comb(arg, v')
                 else mk_bool_case(arg, mk_switch litargs, mk_eq(v', lit))
        val switch = mk_switch (zip literals args)
    in list_mk_abs(args@[v], mk_literal_case (mk_abs(v',switch), v))
    end

(* under_bool_case repairs a final beta_conv for literal switches. *)

fun under_literal_case conv tm =
  if is_literal_case tm then
    let val (f,e) = dest_literal_case tm
        val (x,bdy) = dest_abs f
        val bdy' = conv bdy handle HOL_ERR _ => bdy
    in mk_literal_case (mk_abs(x, bdy'), e)
    end
  else conv tm handle HOL_ERR _ => tm

fun under_bool_case conv tm =
  if is_bool_case tm then
    let val (t,f,tst) = dest_bool_case tm
        val f' = under_bool_case conv f
    in mk_bool_case (t,f',tst)
    end
  else conv tm handle HOL_ERR _ => tm

fun under_literal_bool_case conv tm =
    under_literal_case (under_bool_case conv) tm


(*----------------------------------------------------------------------------
      Translation of pattern terms into nested case expressions.

    This performs the translation and also builds the full set of patterns.
    Thus it supports the construction of induction theorems even when an
    incomplete set of patterns is given.
 ----------------------------------------------------------------------------*)

fun mk_case ty_info ty_match FV range_ty =
 let
 fun mk_case_fail s = raise ERR "mk_case" s
 val fresh_var = wfrecUtils.vary FV
 val dividel = partitionl fresh_var ty_match
 val divide = partition fresh_var ty_match
 fun expandl literals ty ((_,[]), _) = mk_case_fail "expandl_var_row"
   | expandl literals ty (row as ((prefix, p::rst), rhs)) =
       if is_var p then
         let fun expnd l = ((prefix, l::rst), psubst[p |-> l] rhs)
         in map expnd literals
         end
       else [row]
 fun expand constructors ty ((_,[]), _) = mk_case_fail "expand_var_row"
   | expand constructors ty (row as ((prefix, p::rst), rhs)) =
       if is_var p
       then let val fresh = fresh_constr ty_match ty fresh_var
                fun expnd (c,gvs) =
                  let val capp = list_mk_comb(c,gvs)
                  in ((prefix, capp::rst), psubst[p |-> capp] rhs)
                  end
            in map expnd (map fresh constructors)  end
       else [row]
 fun mk{rows=[],...} = mk_case_fail "no rows"
   | mk{path=[], rows = ((prefix, []), rhs)::_} =  (* Done *)
        let val (tag,tm) = dest_pattern rhs
        in ([(prefix,tag,[])], tm)
        end
   | mk{path=[], rows = _::_} = mk_case_fail "blunder"
   | mk{path as u::rstp, rows as ((prefix, []), rhs)::rst} =
        mk{path = path,
           rows = ((prefix, [fresh_var(type_of u)]), rhs)::rst}
   | mk{path = u::rstp, rows as ((_, p::_), _)::_} =
     let val (pat_rectangle,rights) = unzip rows
         val col0 = map (Lib.trye hd o #2) pat_rectangle
     in
     if all is_var col0
     then let val rights' = map(fn(v,e) => psubst[v|->u] e) (zip col0 rights)
              val pat_rectangle' = map v_to_prefix pat_rectangle
              val (pref_patl,tm) = mk{path = rstp,
                                      rows = zip pat_rectangle' rights'}
          in (map v_to_pats pref_patl, tm)
          end
     else
     let val pty = type_of p
         val {Thy,Tyop,...} = dest_thy_type pty
     in
     if exists Literal.is_pure_literal col0 then  (* column has a literal *)
       let val other_var = fresh_var pty
           val constructors = rev (mk_set (rev (filter (not o is_var) col0)))
                              @ [other_var]
           val arb = mk_arb range_ty
           val switch_tm = mk_switch_tm fresh_var u arb constructors
           val nrows = flatten (map (expandl constructors pty) rows)
           val subproblems = dividel(constructors, pty, range_ty, nrows)
           val groups        = map #group subproblems
           and new_formals   = map #new_formals subproblems
           and constructors' = map #constructor subproblems
           val news = map (fn (nf,rows) => {path = nf@rstp, rows=rows})
                          (zip new_formals groups)
           val rec_calls = map mk news
           val (pat_rect,dtrees) = unzip rec_calls
           val case_functions = map list_mk_abs(zip new_formals dtrees)
           val tree = List.foldl (fn (a,tm) => beta_conv (mk_comb(tm,a)))
                                 switch_tm (case_functions@[u])
           val tree' = under_literal_bool_case beta_conv tree
           val pat_rect1 = flatten(map2 mk_patl constructors' pat_rect)
       in
          (pat_rect1,tree')
       end
     else
     if all (is_constructor_var_pat ty_info) col0 then (* col. of constrs *)
       let val {case_const,constructors} = Option.valOf(ty_info (Thy,Tyop))
           val {Name = case_const_name, Thy,...} = dest_thy_const case_const
           val nrows = flatten (map (expand constructors pty) rows)
           val subproblems = divide(constructors, pty, range_ty, nrows)
           val groups      = map #group subproblems
           and new_formals = map #new_formals subproblems
           and constructors' = map #constructor subproblems
           val news = map (fn (nf,rows) => {path = nf@rstp, rows=rows})
                          (zip new_formals groups)
           val rec_calls = map mk news
           val (pat_rect,dtrees) = unzip rec_calls
           val case_functions = map list_mk_abs(zip new_formals dtrees)
           val types = map type_of (case_functions@[u])
           val case_const' = mk_thy_const{Name = case_const_name, Thy = Thy,
                                          Ty = list_mk_fun(types, range_ty)}
           val tree = list_mk_comb(case_const', case_functions@[u])
           val pat_rect1 = flatten(map2 mk_pat constructors' pat_rect)
       in
          (pat_rect1,tree)
       end
     else
       mk_case_fail "Some patterns are not constants or variables"
     end
    end
 in mk
 end;


(*---------------------------------------------------------------------------
     Repeated variable occurrences in a pattern are not allowed.
 ---------------------------------------------------------------------------*)

fun FV_multiset tm =
   case dest_term tm
     of VAR v => [mk_var v]
      | CONST _ => []
      | COMB(Rator,Rand) => FV_multiset Rator @ FV_multiset Rand
      | LAMB(Bvar,Body) => Lib.subtract (FV_multiset Body) [Bvar]
                           (* raise ERR"FV_multiset" "lambda"; *)

fun no_repeat_vars thy pat =
 let fun check [] = true
       | check (v::rst) =
         if Lib.op_mem aconv v rst
         then raise ERR"no_repeat_vars"
              (strcat(quote(fst(dest_var v)))
                     (strcat" occurs repeatedly in the pattern "
                      (quote(Hol_pp.term_to_string pat))))
         else check rst
 in check (FV_multiset pat)
 end;


(*---------------------------------------------------------------------------
     Routines to repair the bound variable names found in cases
 ---------------------------------------------------------------------------*)

fun subst_inst (term_sub,type_sub) tm =
    Term.subst term_sub (Term.inst type_sub tm);

fun pat_match1 (pat,exp) given_pat =
 let val sub = Term.match_term pat given_pat
 in (subst_inst sub pat, subst_inst sub exp);
    sub
 end

fun pat_match2 pat_exps given_pat = tryfind (C pat_match1 given_pat) pat_exps
                                    handle HOL_ERR _ => ([],[])

fun distinguish pat_tm_mats =
    snd (List.foldr (fn ({redex:term,residue:term}, (vs,done)) =>
                         let val residue' = variant vs residue
                             val vs' = Lib.insert residue' vs
                         in (vs', {redex=redex, residue=residue'} :: done)
                         end)
                    ([],[]) pat_tm_mats)

fun reduce_mats pat_tm_mats =
    snd (List.foldl (fn (mat as {redex:term,residue:term}, (vs,done)) =>
                         if mem redex vs then (vs, done)
                         else (redex :: vs, mat :: done))
                    ([],[]) pat_tm_mats)

fun purge_wildcards term_sub = filter (fn {redex:term,residue:term} =>
        not (String.sub (fst (dest_var residue), 0) = #"_")
        handle _ => false) term_sub

fun pat_match3 pat_exps given_pats =
     ((distinguish o reduce_mats o purge_wildcards o flatten) ## flatten)
           (unzip (map (pat_match2 pat_exps) given_pats))

fun rename_case sub cs =
 if not (TypeBase.is_case cs) then subst_inst sub cs
 else
   let val (cnst,arg,pat_exps) = TypeBase.dest_case cs
       val pat_exps' = map (fn (pat,exp) =>
                            (rename_case sub pat,
                             rename_case sub exp))
                       pat_exps
       val arg' = rename_case sub arg
       val cs' = TypeBase.mk_case(arg', pat_exps')
   in cs'
   end

fun mk_functional thy eqns =
 let fun err s = raise ERR "mk_functional" s
     fun msg s = HOL_MESG ("mk_functional: "^s)
     val clauses = strip_conj eqns
     val (L,R) = unzip (map (dest_eq o snd o strip_forall) clauses)
     val (funcs,pats) = unzip(map dest_comb L)
     val fs = Lib.op_mk_set aconv funcs
     val f0 = if length fs = 1 then hd fs else err "function name not unique"
     val f  = if is_var f0 then f0 else mk_var(dest_const f0)
     val  _ = map (no_repeat_vars thy) pats
     val rows = zip (map (fn x => ([]:term list,[x])) pats)
                    (map GIVEN (enumerate R))
     val fvs = free_varsl (L@R)
     val a = variant fvs (mk_var("a", type_of(Lib.trye hd pats)))
     val FV = a::fvs
     val range_ty = type_of (Lib.trye hd R)
     val (patts, case_tm) = mk_case (match_info thy) (match_type thy)
                                     FV range_ty {path=[a], rows=rows}
     fun func (_,(tag,i),[pat]) = tag (pat,i)
       | func _ = err "error in pattern-match translation"
     val patts1 = map func patts
     val (omits,givens) = Lib.partition is_omitted patts1
     val givens' = sort pattern_cmp givens
     val patts2 = givens' @ omits
(*     val patts2 = sort (fn p1=>fn p2=> row_of_pat p1 < row_of_pat p2) patts1 *)
     val finals = map row_of_pat patts2
     val originals = map (row_of_pat o #2) rows
     val new_rows = length finals - length originals
     val clause_s = if new_rows = 1 then " clause " else " clauses "
     val _ = if new_rows > 0 then
            (msg ("\n  pattern completion has added "^
                  Int.toString new_rows^clause_s^
                  "to the original specification.");
             if !allow_new_clauses then () else
              err ("new clauses not allowed under current setting of "^
                   Lib.quote("Functional.allow_new_clauses")^" flag"))
             else ()
     fun int_eq i1 (i2:int) =  (i1=i2)
     val inaccessibles = filter(fn x => not(op_mem int_eq x finals)) originals
     fun accessible p = not(op_mem int_eq (row_of_pat p) inaccessibles)
     val patts3 = (if null inaccessibles then I else filter accessible) patts2
     val _ = if null patts3
                then err "patterns in definition aren't acceptable" else
             if null inaccessibles then ()
             else msg("\n   The following input rows (counting from zero) in\
                 \ the definition\n   are inaccessible: "
                 ^stringize inaccessibles
     ^".\n   This is because of overlapping patterns. Those rows have been ignored."
     ^ "\n   The definition is probably malformed, but we will continue anyway.")
     (* The next lines repair bound variable names in the nested case term. *)
     val (a',case_tm') =
         let val (_,pat_exps) = TypeBase.strip_case case_tm
             val pat_exps = if null pat_exps then [(a,a)] else pat_exps
             val sub = pat_match3 pat_exps pats (* better pats than givens patts3 *)
         in (subst_inst sub a, rename_case sub case_tm)
         end handle HOL_ERR _ => (a,case_tm)
     (* Ensure that the case test variable is fresh for the rest of the case *)
     val avs = subtract (all_vars case_tm') [a']
     val a'' = variant avs a'
     val case_tm'' = if a'' = a' then case_tm'
                                 else rename_case ([a' |-> a''],[]) case_tm'
 in
   {functional = list_mk_abs ([f,a''], case_tm''),
    pats = patts3}
 end;

(*---------------------------------------------------------------------------
   Given a list of (pattern,expression) pairs, mk_pattern_fn creates a term
   as an abstraction containing a case expression on the function's argument.
 ---------------------------------------------------------------------------*)

fun mk_pattern_fn thy (pes: (term * term) list) =
  let fun err s = raise ERR "mk_pattern_fn" s
      val (p0,e0) = Lib.trye hd pes
          handle HOL_ERR _ => err "empty list of (pattern,expression) pairs"
      val pty = type_of p0 and ety = type_of e0
      val (ps,es) = unzip pes
      val _ = if all (Lib.equal pty o type_of) ps then ()
              else err "patterns have varying types"
      val _ = if all (Lib.equal ety o type_of) es then ()
              else err "expressions have varying types"
      val fvar = genvar (pty --> ety)
      val eqs = list_mk_conj (map (fn (p,e) => mk_eq(mk_comb(fvar,p), e)) pes)
      val {functional,pats} = mk_functional thy eqs
      val f = snd (dest_abs functional)
   in
     f
  end

end
