structure Functional :> Functional =
struct

open HolKernel wfrecUtils boolSyntax

type term   = Term.term
type thry   = TypeBase.typeBase

infixr 3 -->;
infix 3 |->;
infix 4 ##;

fun ERR func mesg = HOL_ERR{origin_structure = "Functional",
                                origin_function = func, message = mesg};

(*---------------------------------------------------------------------------
      Miscellaneous support
 ---------------------------------------------------------------------------*)

val stringize = list_to_string int_to_string ", ";

fun enumerate l = map (fn (x,y) => (y,x)) (Lib.enumerate 0 l);

fun match_term thry tm1 tm2 = Term.match_term tm1 tm2;
fun match_type thry ty1 ty2 = Type.match_type ty1 ty2;

fun match_info db s =
case TypeBase.get db s
 of SOME facts => SOME{case_const = TypeBase.case_const_of facts,
                       constructors = TypeBase.constructors_of facts}
  | NONE => NONE


(*---------------------------------------------------------------------------
 * This datatype carries some information about the origin of a
 * clause in a function definition.
 *---------------------------------------------------------------------------*)

datatype pattern = GIVEN   of term * int
                 | OMITTED of term * int

fun psubst theta (GIVEN (tm,i)) = GIVEN(subst theta tm, i)
  | psubst theta (OMITTED (tm,i)) = OMITTED(subst theta tm, i);

fun dest_pattern (GIVEN (tm,i)) = ((GIVEN,i),tm)
  | dest_pattern (OMITTED (tm,i)) = ((OMITTED,i),tm);

val pat_of = #2 o dest_pattern;
val row_of_pat = #2 o #1 o dest_pattern;

fun not_omitted (GIVEN(tm,_)) = tm
  | not_omitted (OMITTED _) = raise ERR"not_omitted" ""
val givens = mapfilter not_omitted;


(*---------------------------------------------------------------------------
 * Produce an instance of a constructor, plus genvars for its arguments.
 *---------------------------------------------------------------------------*)

fun fresh_constr ty_match colty gv c =
  let val {Ty,...} = dest_const c
      val (L,ty) = strip_fun_type Ty
      val ty_theta = ty_match ty colty
      val c' = inst ty_theta c
      val gvars = map (inst ty_theta o gv) L
  in (c', gvars)
  end;


(*---------------------------------------------------------------------------*
 * Goes through a list of rows and picks out the ones beginning with a       *
 * pattern with constructor = Name.                                          *
 *---------------------------------------------------------------------------*)

fun mk_group Name rows =
  let fun func (row as ((prefix, p::rst), rhs)) (in_group,not_in_group) =
            let val (pc,args) = strip_comb p
            in if ((#Name(dest_const pc) = Name) handle HOL_ERR _ => false)
               then (((prefix,args@rst), rhs)::in_group, not_in_group)
               else (in_group, row::not_in_group)
            end
        | func _ _ = raise ERR "mk_group" ""
  in
    itlist func rows ([],[])
  end;


(*---------------------------------------------------------------------------*
 * Partition the rows. Not efficient.                                        *
 *---------------------------------------------------------------------------*)

fun partition _ _ (_,_,_,[]) = raise ERR"partition" "no rows"
  | partition gv ty_match
              (constructors, colty, res_ty, rows as (((prefix,_),_)::_)) =
let val fresh = fresh_constr ty_match colty gv
     fun part {constrs = [],      rows, A} = rev A
       | part {constrs = c::crst, rows, A} =
         let val (c',gvars) = fresh c
             val {Name,Ty} = dest_const c'
             val (in_group, not_in_group) = mk_group Name rows
             val in_group' =
                 if (null in_group)  (* Constructor not given *)
                 then [((prefix, #2(fresh c)), OMITTED (mk_arb res_ty, ~1))]
                 else in_group
         in
         part{constrs = crst,
              rows = not_in_group,
              A = {constructor = c',
                   new_formals = gvars,
                   group = in_group'}::A}
         end
in part{constrs=constructors, rows=rows, A=[]}
end;


(*---------------------------------------------------------------------------
 * Misc. routines used in mk_case
 *---------------------------------------------------------------------------*)

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


(*----------------------------------------------------------------------------
      Translation of pattern terms into nested case expressions.

    This performs the translation and also builds the full set of patterns.
    Thus it supports the construction of induction theorems even when an
    incomplete set of patterns is given.
 ----------------------------------------------------------------------------*)

fun mk_case ty_info ty_match FV range_ty =
 let
 fun mk_case_fail s = raise ERR"mk_case" s
 val fresh_var = wfrecUtils.vary FV
 val divide = partition fresh_var ty_match
 fun expand constructors ty ((_,[]), _) = mk_case_fail"expand_var_row"
   | expand constructors ty (row as ((prefix, p::rst), rhs)) =
       if (is_var p)
       then let val fresh = fresh_constr ty_match ty fresh_var
                fun expnd (c,gvs) =
                  let val capp = list_mk_comb(c,gvs)
                  in ((prefix, capp::rst), psubst[p |-> capp] rhs)
                  end
            in map expnd (map fresh constructors)  end
       else [row]
 fun mk{rows=[],...} = mk_case_fail"no rows"
   | mk{path=[], rows = ((prefix, []), rhs)::_} =  (* Done *)
        let val (tag,tm) = dest_pattern rhs
        in ([(prefix,tag,[])], tm)
        end
   | mk{path=[], rows = _::_} = mk_case_fail"blunder"
   | mk{path as u::rstp, rows as ((prefix, []), rhs)::rst} =
        mk{path = path,
           rows = ((prefix, [fresh_var(type_of u)]), rhs)::rst}
   | mk{path = u::rstp, rows as ((_, p::_), _)::_} =
     let val (pat_rectangle,rights) = unzip rows
         val col0 = map(Lib.trye hd o #2) pat_rectangle
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
         val ty_name = (#Tyop o dest_type) pty
     in
     case ty_info ty_name
     of NONE => mk_case_fail("Not a known datatype: "^ty_name)
      | SOME{case_const,constructors} =>
        let val case_const_name = #Name(dest_const case_const)
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
            val types = map type_of (case_functions@[u]) @ [range_ty]
            val case_const' = mk_const{Name = case_const_name,
                                       Ty   = list_mk_fun_type types}
            val tree = list_mk_comb(case_const', case_functions@[u])
            val pat_rect1 = flatten(map2 mk_pat constructors' pat_rect)
        in
            (pat_rect1,tree)
        end
     end end
 in mk
 end;


(*---------------------------------------------------------------------------
     Repeated variable occurrences in a pattern are not allowed.
 ---------------------------------------------------------------------------*)

fun FV_multiset tm =
   case (dest_term tm)
     of HolKernel.VAR v => [mk_var v]
      | HolKernel.CONST _ => []
      | HolKernel.COMB{Rator, Rand} => FV_multiset Rator @ FV_multiset Rand
      | HolKernel.LAMB _ => raise ERR"FV_multiset" "lambda";

fun no_repeat_vars thy pat =
 let fun check [] = true
       | check (v::rst) =
         if Lib.op_mem aconv v rst
         then raise ERR"no_repeat_vars"
              (concat(quote(#Name(dest_var v)))
                     (concat" occurs repeatedly in the pattern "
                      (quote(Hol_pp.term_to_string pat))))
         else check rst
 in check (FV_multiset pat)
 end;

local fun paired1{lhs,rhs} = (lhs,rhs)
      and paired2{Rator,Rand} = (Rator,Rand)
      fun err s = raise ERR "mk_functional" s
      fun msg s = HOL_MESG ("mk_functional: "^s)
in
fun mk_functional thy eqs =
 let val clauses = strip_conj eqs
     val (L,R) = unzip (map (paired1 o dest_eq o snd o strip_forall)
                              clauses)
     val (funcs,pats) = unzip(map (paired2 o dest_comb) L)
     val fs = Lib.op_mk_set aconv funcs
     val f0 = if length fs = 1 then hd fs else err "function name not unique"
     val f  = if is_var f0 then f0 else mk_var(dest_const f0)
     val _  = map (no_repeat_vars thy) pats
     val rows = zip (map (fn x => ([],[x])) pats) (map GIVEN (enumerate R))
     val fvs = free_varsl R
     val a = variant fvs (mk_var{Name="a", Ty = type_of(Lib.trye hd pats)})
     val FV = a::fvs
     val range_ty = type_of (Lib.trye hd R)
     val (patts, case_tm) = mk_case (match_info thy) (match_type thy)
                                     FV range_ty {path=[a], rows=rows}
     fun func (_,(tag,i),[pat]) = tag (pat,i)
       | func _ = err "error in pattern-match translation"
     val patts1 = map func patts
     val patts2 = sort(fn p1=>fn p2=> row_of_pat p1 < row_of_pat p2) patts1
     val finals = map row_of_pat patts2
     val originals = map (row_of_pat o #2) rows
     fun int_eq i1 (i2:int) =  (i1=i2)
     val inaccessibles = gather(fn x => not(op_mem int_eq x finals)) originals
     fun accessible p = not(op_mem int_eq (row_of_pat p) inaccessibles)
     val patts3 = (case inaccessibles of [] => patts2
                        |  _ => filter accessible patts2)
     val _ = case inaccessibles of [] => ()
             | _ => msg("The following input rows (counting from zero) are\
       \ inaccessible: "^stringize inaccessibles^".\nThey have been ignored.")
 in
   {functional = list_mk_abs ([f,a], case_tm),
    pats = patts3}
 end
end;

end;
