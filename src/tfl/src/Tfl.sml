structure Tfl :> Tfl =
struct

open Lib Exception USyntax Rules Thms Thry;

type thry = Thry.thry

infixr 3 -->;
infix 3 |->;
infix 4 ##; 

fun TFL_ERR func mesg = HOL_ERR{origin_structure = "Tfl", 
                                origin_function = func, message = mesg};

val concl = #2 o Thm.dest_thm;
val hyp = #1 o Thm.dest_thm;

fun flatten [] = []
  | flatten ([]::t) = flatten t
  | flatten ((h::t)::rst) = h::flatten(t::rst);

fun assoc1 eq item =
   let fun assc ((entry as (key,_))::rst) = 
             if eq(item,key) then SOME entry else assc rst
         | assc [] = NONE
    in assc
    end;

fun pluck p  =
  let fun remv ([],_) = raise TFL_ERR "pluck" "item not found"
        | remv (h::t, A) = if p h then (h, rev A @ t) else remv (t,h::A)
  in 
     fn L => remv(L,[])
  end;

fun zip3 [][][] = []
  | zip3 (x::l1) (y::l2) (z::l3) = (x,y,z)::zip3 l1 l2 l3
  | zip3 _ _ _ = raise TFL_ERR "zip3" "different lengths";

fun gtake f =
  let fun grab(0,rst) = ([],rst)
        | grab(n, x::rst) = 
             let val (taken,left) = grab(n-1,rst)
             in (f x::taken, left) end
        | grab _ = raise TFL_ERR "gtake" "grab.empty list"
  in grab
  end;

fun enumerate L = 
 rev(#1(rev_itlist (fn x => fn (alist,i) => ((x,i)::alist, i+1)) L ([],0)));

fun unzip3 [] = ([],[],[])
  | unzip3 ((x,y,z)::rst) = 
      let val (l1,l2,l3) = unzip3 rst
      in (x::l1, y::l2, z::l3)
      end;

fun list_to_string p delim =
  let fun stringulate [] = []
        | stringulate [x] = [p x]
        | stringulate (h::t) = p h::delim::stringulate t
  in 
    fn l => String.concat (stringulate l)
  end;

val stringize = list_to_string int_to_string ", ";


(*---------------------------------------------------------------------------
 * The next function is common to pattern-match translation and 
 * proof of completeness of cases for the induction theorem.
 *
 * "gvvariant" make variables that are guaranteed not to be in vlist and
 * furthermore, are guaranteed not to be equal to each other. The names of
 * the variables will start with "v" and end in a number.
 *---------------------------------------------------------------------------*)
local val counter = ref 0
in
fun gvvariant vlist =
  let val slist = ref (map (#Name o dest_var) vlist)
      val _ = counter := 0
      fun pass str = 
         if Lib.mem str (!slist) 
         then ( counter := !counter + 1;
                pass (concat"v" (int_to_string(!counter))))
         else (slist := str :: !slist; str)
  in 
  fn ty => mk_var{Name=pass "v",  Ty=ty}
  end
end;


(*---------------------------------------------------------------------------
 * Used in induction theorem production. This is the simple case of
 * partitioning up pattern rows by the leading constructor.
 *---------------------------------------------------------------------------*)
fun ipartition gv (constructors,rows) =
  let fun pfail s = raise TFL_ERR"partition.part" s
      fun part {constrs = [],   rows = [],   A} = rev A
        | part {constrs = [],   rows = _::_, A} = pfail"extra cases in defn"
        | part {constrs = _::_, rows = [],   A} = pfail"cases missing in defn"
        | part {constrs = c::crst, rows,     A} =
          let val {Name,Ty} = dest_const c
              val (L,_) = strip_type Ty
              fun func (row as (p::rst, rhs)) (in_group,not_in_group) =
                        let val (pc,args) = strip_comb p
                        in if (#Name(dest_const pc) = Name)
                            then ((args@rst, rhs)::in_group, not_in_group)
                            else (in_group, row::not_in_group)
                        end
                | func _ _ = pfail "func" ""
              val (in_group, not_in_group) = itlist func rows ([],[])
              val col_types = #1(gtake type_of 
                                   (length L, #1(Lib.trye hd in_group)))
          in 
          part{constrs = crst, rows = not_in_group, 
               A = {constructor = c, 
                    new_formals = map gv col_types,
                    group = in_group}::A}
          end
  in 
     part {constrs=constructors, rows=rows, A=[]}
  end;



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

(*---------------------------------------------------------------------------
 * Produce an instance of a constructor, plus genvars for its arguments.
 *---------------------------------------------------------------------------*)
fun fresh_constr ty_match colty gv c =
  let val {Ty,...} = dest_const c
      val (L,ty) = strip_type Ty
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
        | func _ _ = raise TFL_ERR "mk_group" ""
  in
    itlist func rows ([],[])
  end;

(*---------------------------------------------------------------------------*
 * Partition the rows. Not efficient.                                        *
 *---------------------------------------------------------------------------*)
fun partition _ _ (_,_,_,[]) = raise TFL_ERR"partition" "no rows"
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
                 then [((prefix, #2(fresh c)), OMITTED (ARB res_ty, ~1))]
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
  let val L = length(#1(strip_type(type_of c)))
      fun build (prefix,tag,plist) =
          let val (args,plist') = gtake I (L, plist)
           in (prefix,tag,list_mk_comb(c,args)::plist') end
  in map build 
  end;

fun v_to_prefix (prefix, v::pats) = (v::prefix,pats)
  | v_to_prefix _ = raise TFL_ERR"mk_case" "v_to_prefix"

fun v_to_pats (v::prefix,tag, pats) = (prefix, tag, v::pats)
  | v_to_pats _ = raise TFL_ERR"mk_case""v_to_pats";
 

(*----------------------------------------------------------------------------
 * Translation of pattern terms into nested case expressions.
 *
 * This performs the translation and also builds the full set of patterns. 
 * Thus it supports the construction of induction theorems even when an 
 * incomplete set of patterns is given.
 *---------------------------------------------------------------------------*)

fun mk_case ty_info ty_match FV range_ty =
 let 
 fun mk_case_fail s = raise TFL_ERR"mk_case" s
 val fresh_var = gvvariant FV 
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
                                       Ty   = list_mk_type types}
            val tree = list_mk_comb(case_const', case_functions@[u])
            val pat_rect1 = flatten(map2 mk_pat constructors' pat_rect)
        in 
            (pat_rect1,tree)
        end 
     end end
 in mk
 end;


(* Repeated variable occurrences in a pattern are not allowed. *)
fun FV_multiset tm = 
   case (dest_term tm)
     of Term.VAR v => [mk_var v]
      | Term.CONST _ => []
      | Term.COMB{Rator, Rand} => FV_multiset Rator @ FV_multiset Rand
      | Term.LAMB _ => raise TFL_ERR"FV_multiset" "lambda";

fun no_repeat_vars thy pat =
 let fun check [] = true
       | check (v::rst) =
         if (Lib.op_mem aconv v rst) 
         then raise TFL_ERR"no_repeat_vars"
              (concat(quote(#Name(dest_var v)))
                     (concat" occurs repeatedly in the pattern "
                         (quote(term_to_string (Thry.typecheck thy pat)))))
         else check rst
 in check (FV_multiset pat)
 end;

local fun paired1{lhs,rhs} = (lhs,rhs) 
      and paired2{Rator,Rand} = (Rator,Rand)
      fun mk_functional_err s = raise TFL_ERR"mk_functional" s
      fun mk_functional_msg s = Lib.mesg true ("mk_functional: "^s)
in
fun mk_functional thy eqs =
 let val clauses = strip_conj eqs
     val (L,R) = unzip (map (paired1 o dest_eq o snd o strip_forall)
                              clauses)
     val (funcs,pats) = unzip(map (paired2 o dest_comb) L)
     val fs = Lib.op_mk_set aconv funcs 
     val f = if (length fs = 1) then hd fs
             else mk_functional_err "function name not unique"
     val _ = map (no_repeat_vars thy) pats
     val rows = zip (map (fn x => ([],[x])) pats) (map GIVEN (enumerate R))
     val fvs = free_varsl R
     val a = variant fvs (mk_var{Name="a", Ty = type_of(Lib.trye hd pats)})
     val FV = a::fvs
     val ty_info = Thry.match_info thy
     val ty_match = Thry.match_type thy
     val range_ty = type_of (Lib.trye hd R)
     val (patts, case_tm) = mk_case ty_info ty_match FV range_ty 
                                    {path=[a], rows=rows}
     fun func (_,(tag,i),[pat]) = tag (pat,i) 
       | func _ = mk_functional_err "error in pattern-match translation"
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
             | _ => mk_functional_msg
                       ("The following input rows (counting from zero) are\
       \ inaccessible: "^stringize inaccessibles^".\nThey have been ignored.")
 in 
   {functional = list_mk_abs ([f,a], case_tm),
    pats = patts3}
end end;


(*----------------------------------------------------------------------------
 
                     PRINCIPLES OF DEFINITION
 
 ----------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------*
 * This basic principle of definition takes a functional M and a relation R  *
 * and specializes the following theorem                                     *
 *                                                                           *
 *    |- !M R f. (f = WFREC R M) ==> WF R ==> !x. f x = M (f%R,x) x          *
 *                                                                           *
 * to them (getting "th1", say). Then we make the definition "f = WFREC R M" *
 * and instantiate "th1" to the constant "f" (getting th2). Then we use the  *
 * definition to delete the first antecedent to th2. Hence the result in     *
 * the "corollary" field is                                                  *
 *                                                                           *
 *    |-  WF R ==> !x. f x = M (f%R,x) x                                     *
 *                                                                           *
 *---------------------------------------------------------------------------*)

fun prim_wfrec_definition thy name {R, functional} =
 let val tych = Thry.typecheck thy
     val {Bvar,...} = dest_abs functional
     val {Name,...} = dest_var Bvar  (* Intended name of definition *)
     val cor1 = ISPEC (tych functional) WFREC_COROLLARY
     val cor2 = ISPEC (tych R) cor1
     val f_eq_WFREC_R_M = (#ant o dest_imp o #Body 
                           o dest_forall o concl) cor2
     val {lhs,rhs} = dest_eq f_eq_WFREC_R_M
     val {Ty, ...} = dest_var lhs
     val def_term = mk_eq{lhs = mk_var{Name=Name,Ty=Ty}, rhs=rhs}
     val (def_thm,thy1) = Thry.make_definition thy name def_term
     val f = Lib.trye hd (snd (strip_comb (concl def_thm)))
     val cor3 = ISPEC (Thry.typecheck thy1 f) cor2
 in 
 {theory = thy1, def=def_thm, corollary=MP cor3 def_thm}
 end
 handle HOL_ERR _ => raise TFL_ERR"prim_wfrec_definition" "";


fun extraction_thms thy = 
 let val {case_rewrites,case_congs} = Thry.extract_info thy
 in (case_rewrites, case_congs@Context.read_context())
 end;


(*---------------------------------------------------------------------------
 * Pair patterns with termination conditions. The full list of patterns for
 * a definition is merged with the TCs arising from the user-given clauses.
 * There can be fewer clauses than the full list, if the user omitted some 
 * cases. This routine is used to prepare input for mk_induction.
 *---------------------------------------------------------------------------*)

fun merge full_pats TCs =
let fun insert (p,TCs) =
      let fun insrt ((x as (h,[]))::rst) = 
                 if (aconv p h) then (p,TCs)::rst else x::insrt rst
            | insrt (x::rst) = x::insrt rst
            | insrt[] = raise TFL_ERR"merge.insert" "pat not found"
      in insrt end
    fun pass ([],ptcl_final) = ptcl_final
      | pass (ptcs::tcl, ptcl) = pass(tcl, insert ptcs ptcl)
in 
  pass (TCs, map (fn p => (p,[])) full_pats)
end;

fun not_omitted (GIVEN(tm,_)) = tm
  | not_omitted (OMITTED _) = raise TFL_ERR"not_omitted" ""
val givens = mapfilter not_omitted;


(*---------------------------------------------------------------------------
        Extract termination conditions
 ---------------------------------------------------------------------------*)

fun extract FV context_congs f (proto_def,WFR) = 
 let val R = rand WFR
     val CUT_LEM = ISPECL [f,R] CUT_LEMMA
     val restr_fR = 
        let val eq = #conseq(dest_imp (concl (SPEC_ALL CUT_LEM)))
        in rator(rator(#lhs(dest_eq eq)))
        end
     fun mk_restr p = mk_comb{Rator=restr_fR, Rand=p}
 in fn (p,th) => 
      let val nested_ref = ref false
          val th' = 
            CONTEXT_REWRITE_RULE 
               (mk_restr p, f,FV@free_vars(concl th), nested_ref)
               {thms=[CUT_LEM], congs=context_congs, th=th}
      in 
         (th', Lib.op_set_diff aconv (hyp th') [proto_def,WFR],!nested_ref)
      end
end;

(*
fun extract FV context_congs f (proto_def,WFR) = 
 let val R = rand WFR
     val CUT_LEM = ISPECL [f,R] CUT_LEMMA
     val restr_fR = 
        let val eq = #conseq(dest_imp (concl (SPEC_ALL CUT_LEM)))
        in rator(rator(#lhs(dest_eq eq)))
        end
     fun mk_restr pat = mk_comb{Rator=restr_fR, Rand=p}
     val nested_tcs = ref [] : term list ref
 in fn (pat,th) => 
   let val nested_tcs := []
       val th' = 
          CONTEXT_REWRITE_RULE 
            (mk_restr pat, f,FV@free_vars(concl th), nested_tcs)
            {thms=[CUT_LEM], congs=context_congs, th=th}
       val th'' = Rules.simplify [Thms.CUT_DEF] th'
   in 
     (th'', Lib.op_set_diff aconv (hyp th'') [proto_def,WFR] @ (!nested_tcs),
      not (null (!nested_tcs)))
      end
end;
*)


(*--------------------------------------------------------------------------*
 * This is a wrapper for "prim_wfrec_definition": it builds a functional,   *
 * calls "prim_wfrec_definition", then specializes the result. This gives   *
 * a list of rewrite rules where the right hand sides are quite ugly, so we *
 * simplify to get rid of the case statements. In essence, this function    *
 * performs pre- and post-processing for patterns. As well, after           *
 * simplification, termination conditions are extracted.                    *
 *--------------------------------------------------------------------------*)

fun gen_wfrec_definition thy nm {R, eqs} =
 let val {functional,pats}  = mk_functional thy eqs
     val given_pats = givens pats
     val {def,corollary,theory} = 
           prim_wfrec_definition thy nm {R=R, functional=functional}
     val tych = Thry.typecheck theory 
     val {lhs=f,...} = dest_eq(concl def)
     val WFR = #ant(dest_imp(concl corollary))
     val corollary' = UNDISCH corollary  (* put WF R on assums *)
     val corollaries = map (C SPEC corollary' o tych) given_pats
     val (case_rewrites,context_congs) = extraction_thms thy
     val corollaries' = map (simplify case_rewrites) corollaries
     val Xtract = extract [] context_congs (tych f) (concl def,WFR)
     val (rules,TCs,_) = unzip3 (map Xtract (zip given_pats corollaries'))
     val mk_cond_rule = FILTER_DISCH_ALL(not o aconv WFR)
     val rules1 = LIST_CONJ(map mk_cond_rule rules)
     val TCs1 = map (map gen_all) TCs (* for induction *)
 in
   {theory = theory,   (* holds def, if it's needed *)
    rules = rules1,
    full_pats_TCs = merge (map pat_of pats) (zip given_pats TCs1), 
    TCs = TCs1, 
    patterns = pats}
 end;


(*---------------------------------------------------------------------------*
 * Perform the extraction without making the definition. This shows that     *
 * definition and extraction commute in some way.                            *
 *---------------------------------------------------------------------------*)

type wfrec_eqns_result = {WFR : term, 
                          SV : term list,
                          proto_def : term,
                          extracta  : (thm * term list * bool) list,
                          pats  : pattern list}

fun wfrec_eqns thy eqns =
 let val {functional,pats} = mk_functional thy eqns
     val SV = free_vars functional    (* schematic variables *)
     val {Bvar=f, Body} = dest_abs functional
     val {Bvar=x, ...} = dest_abs Body
     val {Name, Ty=fty} = dest_var f
     val (f_dty, f_rty) = Type.dom_rng fty
     val tych = Thry.typecheck thy
     val WFREC_THM0 = ISPEC (tych functional) WFREC_COROLLARY
     val R = variant (free_vars eqns) 
                     (#Bvar(dest_forall(concl WFREC_THM0)))
     val WFREC_THM = ISPECL [tych R, tych f] WFREC_THM0
     val tmp = fst(strip_imp(concl WFREC_THM))
     val proto_def = Lib.trye hd tmp
     val WFR = Lib.trye (hd o tl) tmp
     val R1 = rand WFR
     val corollary' = funpow 2 UNDISCH WFREC_THM
     val given_pats = givens pats
     val corollaries = map (C SPEC corollary' o tych) given_pats
     val (case_rewrites,context_congs) = extraction_thms thy
     val corollaries' = map (simplify case_rewrites) corollaries
     val Xtract = extract [R1] context_congs (tych f) (proto_def,WFR)
 in 
    {proto_def=proto_def, 
     SV=Lib.sort Term.term_lt SV,
     WFR=WFR, 
     pats=pats,
     extracta = map Xtract (zip given_pats corollaries')}
 end;


(*---------------------------------------------------------------------------*
 * Define the constant after extracting the termination conditions. The      *
 * wellfounded relation used in the definition is computed by using the      *
 * choice operator on the extracted conditions (plus the condition that      *
 * such a relation must be wellfounded).                                     *
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
      Need a "smart" MP. th1 can be less quantified than th2, so th2 
      has to be specialized appropriately. We assume that all the 
      "local" variables are quantified first.
 ---------------------------------------------------------------------------*)
fun ModusPonens th1 th2 = 
  let val V1 = #1(strip_forall(#ant(dest_imp(concl th1))))
      val V2 = #1(strip_forall(concl th2))
      val diff = Lib.op_set_diff Term.aconv V2 V1
      fun loop th = 
        if is_forall(concl th) 
        then let val {Bvar,Body} = dest_forall (concl th)
             in if Lib.op_mem Term.aconv Bvar diff
                then loop (SPEC Bvar th) else th
             end
        else th
  in 
    MP th1 (loop th2)
  end
  handle _ => raise TFL_ERR "ModusPonens" "failed";

fun lazyR_def thy name {proto_def,SV,WFR,pats,extracta} =
 let val R1 = rand WFR
     val f = lhs proto_def
     val (extractants,TCl_0,_) = unzip3 extracta
     fun gen_all away tm = 
        let val FV = free_vars tm
        in itlist (fn v => fn tm =>
              if mem v away then tm else mk_forall{Bvar=v,Body=tm}) FV tm
        end
     val TCs_0 = op_U aconv TCl_0
     val TCl = map (map (gen_all (R1::SV))) TCl_0
     val TCs = op_U aconv TCl
     val full_rqt = WFR::TCs
     val R2 = mk_select{Bvar=R1, Body=list_mk_conj full_rqt}
     val R2abs = rand R2
     val fvar = mk_var{Name = #Name (dest_var f),
                  Ty = itlist (curry op-->) (map type_of SV) (type_of f)}
     val fvar_app = list_mk_comb(fvar,SV)
     val (def,theory) = Thry.make_definition thy name 
                          (subst [f |-> fvar_app, R1 |-> R2] proto_def)
     val fconst = fst(strip_comb(lhs(snd(strip_forall(concl def)))))
     val tych = Thry.typecheck theory
     val disch'd = itlist (DISCH o tych) (proto_def::WFR::TCs_0) 
                          (LIST_CONJ extractants)
     val inst'd = SPEC (tych (list_mk_comb(fconst,SV)))
                       (SPEC (tych R2) (GENL [tych R1, tych f] disch'd))
     val def' = MP inst'd (SPEC_ALL def)
     val var_wits = LIST_CONJ (map (ASSUME o tych) full_rqt)
     val TC_choice_thm =
          MP (BETA_RULE(ISPECL[tych R2abs, tych R1] SELECT_AX)) var_wits
 in {theory = theory, R=R1, SV=SV,
     rules = rev_itlist (C ModusPonens) (CONJUNCTS TC_choice_thm) def',
     full_pats_TCs = merge (map pat_of pats) (zip (givens pats) TCl),
     patterns = pats}
 end;


(*---------------------------------------------------------------------------*
 *                                                                           *
 *                           INDUCTION THEOREM                               *
 *                                                                           *
 *---------------------------------------------------------------------------*)


(*------------------------  Miscellaneous function  --------------------------
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
 *---------------------------------------------------------------------------*)

fun alpha_ex_unroll xlist tm =
  let val (qvars,body) = strip_exists tm
      val vlist = #2(strip_comb (rhs body))
      val plist = zip vlist xlist
      val args = map (C (assoc1 (uncurry aconv)) plist) qvars
      val args' = map (fn SOME(_,v) => v 
                        | NONE => raise TFL_ERR"alpha_ex_unroll"
                                               "no correspondence") args
      fun build ex [] = []
        | build ex (v::rst) =
           let val ex1 = beta_conv(mk_comb{Rator=rand ex, Rand=v})
           in ex1::build ex1 rst
           end
  in 
    case (rev (tm::build tm args'))
     of nex::exl => (nex, zip args' (rev exl))
      | [] => raise TFL_ERR "alpha_ex_unroll" "empty"
  end;



(*---------------------------------------------------------------------------*
 *                                                                           *
 *             PROVING COMPLETENESS OF PATTERNS                              *
 *                                                                           *
 *---------------------------------------------------------------------------*)

type divide_ty 
 = term list 
    * (term list * (thm * (term, term) binding list)) list 
   -> {constructor : term, 
       group       : (term list * (thm * (term, term) binding list)) list,
       new_formals : term list} list;

fun mk_case ty_info FV thy =
 let 
 val divide:divide_ty = ipartition (gvvariant FV)  (* do not eta-expand!! *)
 val tych = Thry.typecheck thy
 fun tych_binding(x |-> y) = (tych x |-> tych y)
 fun fail s = raise TFL_ERR"mk_case" s
 fun mk{rows=[],...} = fail"no rows"
   | mk{path=[], rows = [([], (thm, bindings))]} = 
                         IT_EXISTS (map tych_binding bindings) thm
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
     let val ty_name = (#Tyop o dest_type o type_of) p
     in
     case ty_info ty_name
      of NONE => fail("Not a known datatype: "^ty_name)
         (* tyinfo rqt: `constructors' must line up exactly with constrs 
            in disjuncts of `nchotomy'. *) 
       | SOME{constructors,nchotomy} => 
         let val thm' = ISPEC (tych u) nchotomy
             val disjuncts    = strip_disj (concl thm')
             val subproblems  = divide(constructors, rows)
             val groups       = map #group subproblems
             and new_formals  = map #new_formals subproblems
             val existentials = map2 alpha_ex_unroll new_formals disjuncts
             val constraints  = map #1 existentials
             val vexl = map #2 existentials
             fun expnd tm (pats,(th,b)) = (pats,(SUBS[ASSUME(tych tm)]th,b))
             val news = map (fn (nf,rows,c) => {path = nf@rstp, 
                                                rows = map (expnd c) rows})
                            (zip3 new_formals groups constraints)
             val recursive_thms = map mk news
             val build_exists = itlist(CHOOSE o (tych##(ASSUME o tych)))
             val thms' = map2 build_exists vexl recursive_thms
             val same_concls = EVEN_ORS thms'
         in 
           DISJ_CASESL thm' same_concls
         end 
     end end
   | mk _ = fail"blunder"
 in mk
 end;

type row = term list * (thm * (term, term) binding list)

fun complete_cases thy =
 let val tych = Thry.typecheck thy
     fun pmk_var n ty = mk_var{Name=n,Ty=ty}
     val ty_info = Thry.induct_info thy
 in fn pats =>
 let val FV0 = free_varsl pats
     val a = variant FV0 (pmk_var "a" (type_of(Lib.trye hd pats)))
     val v = variant (a::FV0) (pmk_var "v" (type_of a))
     val FV = a::v::FV0
     val a_eq_v = mk_eq{lhs=a, rhs=v}
     val ex_th0 = EXISTS ((tych##tych) (mk_exists{Bvar=v,Body=a_eq_v},a))
                           (REFL (tych a))
     val th0 = ASSUME (tych a_eq_v)
     val rows:row list = map (fn x => ([x], (th0,[]))) pats
 in
 GEN (tych a) 
       (RIGHT_ASSOC
          (CHOOSE(tych v, ex_th0)
                (mk_case ty_info FV thy {path=[v], rows=rows})))
 end end;


(*---------------------------------------------------------------------------*
 * Constructing induction hypotheses: one for each recursive call.           *
 *---------------------------------------------------------------------------*)

local nonfix ^ ;   infix 9 ^  ;     infix 5 ==>
      fun (tm1 ^ tm2)   = mk_comb{Rator=tm1, Rand=tm2}
      fun (tm1 ==> tm2) = mk_imp{ant=tm1, conseq=tm2}
in
fun build_ih f (P,R,SV) (pat,TCs) = 
 let val pat_vars = free_vars_lr pat
     val globals = (if is_var R then [R] else [])@pat_vars@SV
     fun nested tm = can(find_term (aconv f)) tm handle _ => false
     fun dest_TC tm = 
         let val (cntxt,R_y_pat) = strip_imp(#2(strip_forall tm))
             val (R,y,_) = USyntax.dest_relation R_y_pat
             val P_y     = if nested tm then R_y_pat ==> P^y else P^y
         in case cntxt 
             of [] => (P_y, (tm,[]))
              | _  => let 
                    val imp = list_mk_conj cntxt ==> P_y
                    val lvs = op_set_diff aconv (free_vars_lr imp) globals
                    val locals = #2(pluck (aconv P) lvs) handle _ => lvs
                  in (list_mk_forall(locals,imp), (tm,locals)) end
         end
 in case TCs
     of [] => (list_mk_forall(pat_vars, P^pat), [])
      |  _ => let val (ihs, TCs_locals) = unzip(map dest_TC TCs)
                  val ind_clause = list_mk_conj ihs ==> P^pat
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
 let val tych = Thry.typecheck thy
     val antc = tych(#ant(dest_imp tm))
     val thm' = SPEC_ALL thm
     fun nested tm = can(find_term (aconv f)) tm handle HOL_ERR _ => false
     fun get_cntxt TC = tych(#ant(dest_imp(#2(strip_forall(concl TC)))))
     fun mk_ih ((TC,locals),th2,nested) =
         GENL (map tych locals)
            (if nested 
              then DISCH (get_cntxt TC) th2 handle HOL_ERR _ => th2
               else if is_imp(concl TC) 
                     then IMP_TRANS TC th2 
                      else MP th2 TC)
 in 
 DISCH antc
   (if is_imp(concl thm') (* recursive calls in this clause *)
    then let val th1 = ASSUME antc
             val TCs = map #1 TCs_locals
             val ylist = map (#2 o dest_relation o #2 o strip_imp o 
                              #2 o strip_forall) TCs
             val TClist = map (fn(TC,lvs) => (SPEC_ALL(ASSUME(tych TC)),lvs))
                              TCs_locals
             val th2list = map (C SPEC th1 o tych) ylist
             val nlist = map nested TCs
             val triples = zip3 TClist th2list nlist
             val Pylist = map mk_ih triples
         in 
            MP thm' (LIST_CONJ Pylist)
         end
    else thm')
 end;


(*---------------------------------------------------------------------------*
 *                                                                           *
 *         x = (v1,...,vn)  |- M[x]                                          *
 *    ---------------------------------------                                *
 *      ?v1 ... vn. x = (v1,...,vn) |- M[x]                                  *
 *                                                                           *
 *---------------------------------------------------------------------------*)

fun LEFT_ABS_VSTRUCT tych thm = 
  let fun CHOOSER v (tm,thm) = 
        let val ex_tm = mk_exists{Bvar=v,Body=tm}
        in (ex_tm, CHOOSE(tych v, ASSUME (tych ex_tm)) thm)
        end
      val veq = Lib.trye hd (filter (can dest_eq) (#1 (Thm.dest_thm thm)))
      val {lhs,rhs} = dest_eq veq
      val L = free_vars_lr rhs
  in snd(itlist CHOOSER L (veq,thm))
  end;

fun combize M N = mk_comb{Rator=M,Rand=N};
fun eq v tm = mk_eq{lhs=v,rhs=tm};


(*---------------------------------------------------------------------------*
 * Input : f, R, SV, and  [(pat1,TCs1),..., (patn,TCsn)]                     *
 *                                                                           *
 * Instantiates WF_INDUCTION_THM, getting Sinduct and then tries to prove    *
 * recursion induction (Rinduct) by proving the antecedent of Sinduct from   *
 * the antecedent of Rinduct.                                                *
 *---------------------------------------------------------------------------*)

fun mk_induction thy {fconst, R, SV, pat_TCs_list} =
let val tych = Thry.typecheck thy
    val Sinduction = UNDISCH (ISPEC (tych R) WF_INDUCTION_THM)
    val (pats,TCsl) = unzip pat_TCs_list
    val case_thm = complete_cases thy pats
    val domain = (type_of o (Lib.trye hd)) pats
    val P = variant (all_varsl (pats@flatten TCsl))
                    (mk_var{Name="P", Ty=domain --> bool})
    val Sinduct = SPEC (tych P) Sinduction
    val Sinduct_assumf = rand ((#ant o dest_imp o concl) Sinduct)
    val Rassums_TCl' = map (build_ih fconst (P,R,SV)) pat_TCs_list
    val (Rassums,TCl') = unzip Rassums_TCl'
    val Rinduct_assum = ASSUME (tych (list_mk_conj Rassums))
    val cases = map (beta_conv o combize Sinduct_assumf) pats
    val tasks = zip3 cases TCl' (CONJUNCTS Rinduct_assum)
    val proved_cases = map (prove_case fconst thy) tasks
    val v = variant (free_varsl (map concl proved_cases))
                    (mk_var{Name="v", Ty=domain})
    val vtyped = tych v
    val substs = map (SYM o ASSUME o tych o eq v) pats
    val proved_cases1 = map2 (fn th => SUBS[th]) substs proved_cases
    val abs_cases = map (LEFT_ABS_VSTRUCT tych) proved_cases1
    val dant = GEN vtyped (DISJ_CASESL (ISPEC vtyped case_thm) abs_cases)
    val dc = MP Sinduct dant
    val Parg_ty = type_of(#Bvar(dest_forall(concl dc)))
    val vars = map (gvvariant[P]) (strip_prod_type Parg_ty)
    val dc' = itlist (GEN o tych) vars
                       (SPEC (tych(fst(mk_vstruct Parg_ty vars))) dc)
in 
   GEN (tych P) (DISCH (tych(concl Rinduct_assum)) dc')
end 
handle HOL_ERR _ => raise TFL_ERR "mk_induction" "failed derivation";


(*---------------------------------------------------------------------------*
 *                                                                           *
 *                        POST PROCESSING                                    *
 *                                                                           *
 *---------------------------------------------------------------------------*)

fun simplify_induction thy hth ind = 
  let val tych = Thry.typecheck thy
      val (asl,_) = Thm.dest_thm ind
      val (_,tc_eq_tc') = Thm.dest_thm hth
      val tc = lhs tc_eq_tc'
      fun loop [] = ind
        | loop (asm::rst) = 
          if (can (Thry.match_term thy asm) tc)
          then UNDISCH
                 (MATCH_MP
                     (MATCH_MP simp_thm (DISCH (tych asm) ind)) 
                     hth)
         else loop rst
  in loop asl
end;


(*---------------------------------------------------------------------------
 * The termination condition is an antecedent to the rule, and an 
 * assumption to the theorem.
 *---------------------------------------------------------------------------*)
fun elim_tc tcthm (rule,induction) = 
   (MP rule (SPEC_ALL tcthm), PROVE_HYP tcthm induction)


fun postprocess{WFtac, terminator, simplifier} theory {rules,induction,TCs} =
let val tych = Thry.typecheck theory

   (*---------------------------------------------------------------------
    * Attempt to eliminate WF condition. It's the only assumption of rules
    *---------------------------------------------------------------------*)
   val (rules1,induction1)  = 
     let val thm = prove(tych(Lib.trye hd (#1(Thm.dest_thm rules))),WFtac)
     in 
       (PROVE_HYP thm rules,  PROVE_HYP thm induction)
     end 
    handle HOL_ERR _ => (rules,induction)

   (*----------------------------------------------------------------------
    * The termination condition (tc) is simplified to |- tc = tc' (there
    * might not be a change!) and then 3 attempts are made:
    *
    *   1. if |- tc = T, then eliminate it with eqT; otherwise,
    *   2. apply the terminator to tc'. If |- tc' = T then eliminate; else
    *   3. replace tc by tc' in both the rules and the induction theorem.
    *---------------------------------------------------------------------*)
   fun simplify_tc tc (r,ind) =
       let val tc_eq = simplifier (tych tc)
       in 
         elim_tc (MATCH_MP eqT tc_eq) (r,ind)
         handle HOL_ERR _ 
         => (elim_tc (MATCH_MP(MATCH_MP rev_eq_mp tc_eq)
                       (prove(tych(rhs(concl tc_eq)),terminator))) (r,ind)
            handle HOL_ERR _ 
            => (UNDISCH(MATCH_MP (MATCH_MP simp_thm r) tc_eq), 
                 simplify_induction theory tc_eq ind))
       end

   (*----------------------------------------------------------------------
    * Nested termination conditions are harder to get at, since they are
    * left embedded in the body of the induction theorem (and in rule
    * hypotheses). Our "solution" is to simplify them, and try to 
    * prove termination, but leave the application of the resulting theorem 
    * to a higher level. So things go much as in "simplify_tc": the 
    * termination condition (tc) is simplified to |- tc = tc' (there might 
    * not be a change) and then 2 attempts are made:
    *
    *   1. if |- tc = T, then return |- tc; 
    *   otherwise,
    *   2. apply the terminator to tc'. If |- tc' = T then return |- tc; 
    *   else
    *   3. return |- tc = tc'
    *---------------------------------------------------------------------*)

   fun simplify_nested_tc tc =
      let val tc_eq = simplifier (tych (#2 (strip_forall tc)))
      in
        GEN_ALL
         (MATCH_MP eqT tc_eq
          handle HOL_ERR _ => (MATCH_MP(MATCH_MP rev_eq_mp tc_eq)
                        (prove(tych(rhs(concl tc_eq)),terminator))
                  handle HOL_ERR _ => tc_eq))
      end

   (*-------------------------------------------------------------------
    * Attempt to simplify the termination conditions in each rule and 
    * in the induction theorem.
    *-------------------------------------------------------------------*)
   fun strip_imp tm = if is_neg tm then ([],tm) else USyntax.strip_imp tm
   fun loop ([],extras,R,ind) = (rev R, ind, extras)
     | loop ((r,ftcs)::rst, nthms, R, ind) =
        let val tcs = map gen_all (#1(strip_imp (concl r)))
            val extra_tcs = op_set_diff aconv ftcs tcs
            val extra_tc_thms = map simplify_nested_tc extra_tcs
            val (r1,ind1) = rev_itlist simplify_tc tcs (r,ind)
            val r2 = FILTER_DISCH_ALL(not o is_WFR) r1
        in loop(rst, nthms@extra_tc_thms, r2::R, ind1)
        end
   val rules_tcs = zip (CONJUNCTS rules1) TCs
   val (rules2,ind2,extras) = loop(rules_tcs,[],[],induction1)
in
  {induction=ind2, rules=LIST_CONJ rules2, nested_tcs=extras}
end;


(*---------------------------------------------------------------------------
 * Extract termination goals so that they can be put it into a goalstack, or 
 * have a tactic directly applied to them.
 *--------------------------------------------------------------------------*)
local fun strip_imp tm = if is_neg tm then ([],tm) else USyntax.strip_imp tm
in
fun termination_goals rules = 
 itlist (fn th => fn A =>
           let val tcl = (fst o strip_imp o #2 o strip_forall o concl) th
           in tcl@A
           end) (CONJUNCTS rules) (hyp rules)
end;

fun UNDISCH_ALL th =
  if is_imp (concl th)
  then UNDISCH_ALL(UNDISCH th)
  else th;

fun GSYM th = GENL (#1(strip_forall(concl th))) (SYM (SPEC_ALL th));

fun nested_function thy name {proto_def,SV,WFR,pats,extracta} =
 let val aux_name = name^"_aux"
     val R1 = rand WFR
     val {lhs=f,rhs=rhs_proto_def} = dest_eq proto_def
     (* make parameterized definition *)
     val {Name,Ty} = Lib.trye dest_var f
     val faux = mk_var{Name=aux_name, 
                       Ty = itlist (curry (op-->)) 
                                   (map type_of (R1::SV)) Ty}
     val (def,theory) = 
           Thry.make_definition thy aux_name
               (mk_eq{lhs=list_mk_comb(faux,R1::SV), rhs=rhs_proto_def})
     val def' = SPEC_ALL def
     val faux_capp = lhs(concl def')
     val faux_const = #1(strip_comb faux_capp)
     val tych = Thry.typecheck theory
     val (extractants,TCl_0,_) = unzip3 extracta
     val TCs_0 = op_U aconv TCl_0
     val disch'd = itlist (DISCH o tych) (proto_def::WFR::TCs_0) 
                          (LIST_CONJ extractants)
     val inst'd = GEN (tych R1)
                   (MP (SPEC (tych faux_capp) (GEN (tych f) disch'd)) def')
     fun gen_all away tm = 
        let val FV = free_vars tm
        in itlist (fn v => fn tm =>
              if mem v away then tm else mk_forall{Bvar=v,Body=tm}) FV tm
        end
     val TCl = map (map (gen_all (R1::f::SV) o subst[f |-> faux_capp])) TCl_0
     val TCs = op_U aconv TCl
     val full_rqt = WFR::TCs
     val R2 = mk_select{Bvar=R1, Body=list_mk_conj full_rqt}
     val R2abs = rand R2
     val R2inst'd = SPEC R2 inst'd
     val fvar = mk_var{Name = #Name (dest_var f),
                  Ty = itlist (curry op-->) (map type_of SV) (type_of f)}
     val fvar_app = list_mk_comb(fvar,SV)
     val (def1,theory1) = Thry.make_definition thy name
               (mk_eq{lhs=fvar_app, rhs=list_mk_comb(faux_const,R2::SV)})
     val var_wits = LIST_CONJ (map (ASSUME o tych) full_rqt)
     val TC_choice_thm =
          MP (BETA_RULE(ISPECL[tych R2abs, tych R1] SELECT_AX)) var_wits
     val elim_chosenTCs = 
           rev_itlist (C ModusPonens) (CONJUNCTS TC_choice_thm) R2inst'd
     val rules = simplify [GSYM def1] elim_chosenTCs
     val pat_TCs_list = merge (map pat_of pats) (zip (givens pats) TCl)

     (* and now induction *)

     val aux_ind = mk_induction theory1
                     {fconst=faux_const, R=R1,SV=SV,pat_TCs_list=pat_TCs_list}
     val nested_guards = op_set_diff aconv (hyp rules) (hyp aux_ind)
     val ics = strip_conj(#ant(dest_imp(#Body(dest_forall(concl aux_ind)))))
     fun dest_ic tm = if is_imp tm then strip_conj (#ant(dest_imp tm)) else []
     val ihs = Lib.flatten (map (dest_ic o snd o strip_forall) ics)
     val nested_ihs = filter (can (find_term (aconv faux_const))) ihs
     (* a nested ih is of the form 

           c1/\.../\ck ==> R a pat ==> P a

        where "aux R N" occurs in "c1/\.../\ck" or "a". In the latter case,
        we have a nested recursion; in the former, there's just a call
        to aux in the context. In both cases, we want to eliminate "R a pat"
        by assuming "c1/\.../\ck ==> R a pat" and doing some work.
     *)
     fun nested_guard tm = 
         let val ngthm = SPEC_ALL (ASSUME tm)
         in
           if is_imp (concl ngthm)
           then UNDISCH ngthm
           else ngthm
         end
     val ng_thms = map nested_guard nested_guards
     val nested_ihs' = map (Rules.simpl_conv ng_thms) nested_ihs
     fun disch_context thm = 
          if length(hyp thm) = 2
          then DISCH (#ant(dest_imp(lhs (concl thm)))) thm
          else thm
     val nested_ihs'' = map disch_context nested_ihs'
     val nested_ihs''' = map (simplify [Thms.imp_elim]) nested_ihs''
     val ind0 = simplify nested_ihs''' aux_ind
     val ind1 = UNDISCH_ALL (SPEC R2 (GEN R1 (DISCH_ALL ind0)))
     val ind2 = simplify [GSYM def1] ind1
     val ind3 = itlist PROVE_HYP (CONJUNCTS TC_choice_thm) ind2
 in 
    {rules = rules,
     ind = ind3,
     SV = SV,
     R = R1,
     theory = theory1, aux_def = def, def = def1, 
     aux_rules = inst'd,
     aux_ind = aux_ind
     }
 end;


fun mk_sum_type ty1 ty2 = Type.mk_type{Tyop="sum",Args=[ty1,ty2]}

local open Psyntax
in
fun inject ty [v] = [v]
  | inject ty (v::vs) = 
     let val {Args = [lty,rty],...} = Type.dest_type ty 
         val res = mk_comb(mk_const("INL", lty-->ty),v)
         val inr = curry mk_comb (mk_const("INR", rty-->ty))
     in
       res::map inr (inject rty vs)
     end

fun project ty M = 
 if is_vartype ty then [M]
 else case dest_type ty 
       of ("sum",[lty,rty]) =>
            mk_comb(mk_const("OUTL", type_of M-->lty),M)
            :: project rty (mk_comb(mk_const("OUTR", type_of M-->rty),M))
        |  _  => [M];
end;

(*---------------------------------------------------------------------------
     Mutual recursion. This is reduced to an ordinary definition by
     use of sum types. The n mutually recursive functions are mapped
     to a single function "mut" having domain and range be sums of 
     the domains and ranges of the given functions. The domain sum 
     has n components. The range sum has k <= n components, built from 
     the set of range types. The arguments of the left hand side of 
     the function are uniformly injected into the domain sum. On the
     right hand side, every occurrence of a function "f a" is translated
     to "OUT(mut (IN a))", where IN is the compound injection function, 
     and OUT brings the result back to the original type of "f a". 
     Finally, each rhs is injected into the range sum. 

     After that translation, "mut" is defined. And then the individual
     functions are defined. Rewriting then brings them out.

     After that, induction is easy to recover from the induction theorem
     for mut. 
 ---------------------------------------------------------------------------*)

fun mutual_function thy name eqns =
  let open Psyntax
      val dom_rng = Type.dom_rng
      val genvar = Term.genvar
      val DEPTH_CONV = Conv.DEPTH_CONV
      val BETA_CONV = Thm.BETA_CONV
      val OUTL = sumTheory.OUTL
      val OUTR = sumTheory.OUTR
      val sum_case_def = sumTheory.sum_case_def
      val CONJ = Thm.CONJ
      val eqnl = strip_conj eqns
      val (L,R) = unzip (map dest_eq eqnl)
      val fnl = mk_set (map (fst o strip_comb o lhs) eqnl)
      val (nl,tyl) = unzip (map Psyntax.dest_var fnl)
      val dom_tyl = map (fst o dom_rng) tyl
      val rng_tyl = mk_set (map (snd o dom_rng) tyl)
      val (dfront,dlast) = Lib.front_last dom_tyl
      val (rfront,rlast) = Lib.front_last rng_tyl
      val mut_dom = itlist mk_sum_type dfront dlast
      val mut_rng = itlist mk_sum_type rfront rlast
      val mut_ty = mut_dom --> mut_rng
      val mut_name = name^"union"
      val mut = mk_var(mut_name, mut_ty)
      val gvl = map genvar dom_tyl
      val gvr = map genvar rng_tyl
      val injmap = zip fnl (map2 (C (curry mk_abs)) (inject mut_dom gvl) gvl)
      fun mk_lhs_mut_app (f,arg) = 
          mk_comb(mut,beta_conv (mk_comb(assoc f injmap,arg)))
      val L1 = map (mk_lhs_mut_app o dest_comb) L
      val gv_mut_rng = genvar mut_rng
      val outfns = map (curry mk_abs gv_mut_rng) (project mut_rng gv_mut_rng)
      val ty_outs = zip rng_tyl outfns
      (* now replace each f by \x. outbar(mut(inbar x)) *)
      fun fout f = (f,assoc (#2(dom_rng(type_of f))) ty_outs)
      val RNG_OUTS = map fout fnl
      fun mk_rhs_mut (f,v) = {redex=f, 
        residue= mk_abs(v, 
           beta_conv (mk_comb(assoc f RNG_OUTS, mk_lhs_mut_app (f,v))))}
      val theta = map mk_rhs_mut (zip fnl gvl)
      val R1 = map (Term.subst theta) R
      val eqnl1 = zip L1 R1
      val rng_injmap = 
            zip rng_tyl (map2 (C (curry mk_abs)) (inject mut_rng gvr) gvr)
      fun f_rng_in f = (f,assoc (#2(dom_rng(type_of f))) rng_injmap)
      val RNG_INS = map f_rng_in fnl
      val tmp = zip (map (#1 o dest_comb) L) R1
      val R2 = map (fn (f,r) => beta_conv(mk_comb(assoc f RNG_INS, r))) tmp
      val R3 = map (rhs o concl o DEPTH_CONV BETA_CONV) R2
      val mut_eqns = list_mk_conj(map mk_eq (zip L1 R3))
      val wfrec_res = wfrec_eqns thy mut_eqns
      val nestedl = #3(unzip3 (#extracta wfrec_res))
      val is_nested = exists (fn x => (x=true)) nestedl
      val defn = 
        if is_nested
        then let val {rules,ind,aux_rules, aux_ind, theory, def,aux_def,...} 
                     = nested_function thy mut_name wfrec_res
             in
              {rules = rules,
               ind=ind,
               aux=SOME{rules=aux_rules, ind=aux_ind},
               theory=theory}
              end
        else let val {rules,R,SV,theory,full_pats_TCs,...} 
                      = lazyR_def thy mut_name wfrec_res
             val f = #1(dest_comb(lhs (concl(Lib.trye hd (CONJUNCTS rules)))))
             val ind = mk_induction theory
                         {fconst=f, R=R, SV=SV, pat_TCs_list=full_pats_TCs}
             in 
               {rules = rules, ind=ind,
                theory = theory,
                aux = NONE}
             end
      val theory1 = #theory defn
      val mut_rules = #rules defn
      val mut_const_app = #1(dest_comb(lhs(#1(dest_conj(concl mut_rules)))))
      val (mut_const,params) = strip_comb mut_const_app
      fun define_subfn fvar thy =
         let val inbar  = assoc fvar injmap
             val outbar = assoc fvar RNG_OUTS
             val x = mk_var("x", #1(dom_rng(type_of fvar)))
             val (fvarname,ty) = dest_var fvar
             val newty = itlist (curry (op-->)) (map type_of params) ty
             val fvar' = mk_var(fvarname,newty)
             val dlhs = list_mk_comb(fvar',params@[x])
             val drhs = beta_conv
                          (mk_comb(outbar,
                             mk_comb(mut_const_app,
                                beta_conv(mk_comb(inbar,x)))))
         in 
           Thry.make_definition thy fvarname (mk_eq(dlhs,drhs))
         end
      val (defns,theory2) = 
          itlist (fn f => fn (L,thy) => 
             let val (d,thy') = define_subfn f thy in (d::L,thy') end)
           fnl ([],theory1)
      fun outmaps tm = assoc (#1(dest_comb tm)) RNG_OUTS
      val mut_rules1 = LIST_CONJ 
            (map (uncurry Thm.AP_TERM) 
                 (zip (map outmaps L) (CONJUNCTS mut_rules)))
      val simp = Rules.simplify (OUTL::OUTR::map GSYM defns)
      val mut_rules2 = simp mut_rules1 (* finally *)

      (* induction *)
      val mut_ind0 = simp (#ind defn)
      val pindices = enumerate dom_tyl
      val preds = map 
         (fn (ty,i) => mk_var("P"^Lib.int_to_string i, ty-->bool)) pindices
      val Psum_case = end_itlist (fn P => fn tm => 
           let val Pty = type_of P
               val tmty = type_of tm
               val Pdom = #1(dom_rng Pty)
               val tmdom = #1(dom_rng tmty)
               val sum_ty = Pty --> tmty --> mk_sum_type Pdom tmdom --> bool
           in 
              list_mk_comb(mk_const("sum_case",sum_ty),[P,tm])
           end) preds
      val mut_ind1 = Rules.simplify [sumTheory.sum_case_def]
                           (SPEC Psum_case mut_ind0)
      val (ant,conseq) = dest_imp (concl mut_ind1)
      val tmp = UNDISCH mut_ind1
      val V = map (fn (ty,i) => mk_var("v"^Lib.int_to_string i,ty)) pindices
      val Vinj = map2 (fn f => fn v => beta_conv(mk_comb(#2 f, v))) injmap V
      val tmpl = map (fn v => GEN_ALL
                        (Rules.simplify [sum_case_def] (SPEC v tmp)))
                      Vinj
      val mut_ind2 = GENL preds (DISCH ant (LIST_CONJ  tmpl))
  in 
    { rules = mut_rules2,
      ind =  mut_ind2,
      SV = #SV wfrec_res, 
      R = rand (#WFR wfrec_res),
      union = defn,
      theory = theory2
    }
  end
     

end; (* TFL *)
