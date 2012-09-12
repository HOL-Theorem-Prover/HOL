structure HolKernel =
struct

  open Feedback Globals Lib Rank Kind Type Term Thm Theory Definition


(*---------------------------------------------------------------------------
     Miscellaneous other stuff that builds on top of kernel facilities.
 ---------------------------------------------------------------------------*)

infixr ==>;  infixr -->;  infix |->;  infix :>=: :=:;

val ERR = mk_HOL_ERR "HolKernel";

(*---------------------------------------------------------------------------
          General term operations
 ---------------------------------------------------------------------------*)

fun dest_monop c e M =
 let val (c1,N) = with_exn dest_comb M e
 in if same_const c c1 then N else raise e end

local fun dest tm =
       let val (Rator,N) = dest_comb tm
           val (c,M) = dest_comb Rator
       in (c,(M,N)) end
in
fun dest_binop c e tm =
   let val (c1,pair) = with_exn dest tm e
   in if same_const c c1 then pair else raise e end
end

fun dest_triop p e M =
  let val (f,z) = with_exn dest_comb M e
      val (x,y) = dest_binop p e f
  in (x,y,z)
  end;

(*---------------------------------------------------------------------------*)
(* Take a binder apart. Fails on paired binders.                             *)
(*---------------------------------------------------------------------------*)

local
  fun dest M =
    let val (c,Rand) = dest_comb M
    in (c,dest_abs Rand) end
in
fun dest_binder c e M =
  let val (c1,p) = with_exn dest M e
  in if same_const c c1 then p else raise e end
end

local fun dest M = let val (c,Rand) = dest_comb M in (c,dest_tyabs Rand) end
in
fun dest_tybinder c e M =
  let val (c1,p) = with_exn dest M e
  in if same_const c c1 then p else raise e end
end


local fun dest M =
       let val (Rator,Rand) = dest_comb M in (dest_thy_const Rator,Rand) end
in
fun sdest_monop (name,thy) e M =
 let val ({Name,Thy,...},Rand) = with_exn dest M e
 in if Name=name andalso Thy=thy then Rand else raise e
 end;
end

local fun dest tm =
       let val (Rator,N) = dest_comb tm
           val (c,M) = dest_comb Rator
       in (dest_thy_const c,(M,N))
       end
in
fun sdest_binop (name,thy) e tm =
   let val ({Name,Thy,...},pair) = with_exn dest tm e
   in if Name=name andalso Thy=thy then pair else raise e
   end
end;

local fun dest M =
       let val (c, Rand) = dest_comb M
       in (dest_thy_const c,dest_abs Rand)
       end
in
fun sdest_binder (name,thy) e M =
  let val ({Name,Thy,...}, p) = with_exn dest M e
  in if Name=name andalso Thy=thy then p else raise e
  end
end;

local fun dest M =
       let val (c, Rand) = dest_comb M
       in (dest_thy_const c,dest_tyabs Rand)
       end
in
fun sdest_tybinder (name,thy) e M =
  let val ({Name,Thy,...}, p) = with_exn dest M e
  in if Name=name andalso Thy=thy then p else raise e
  end
end;

fun single x = [x];

(* Breaks term down until binop no longer occurs at top level in result list *)

fun strip_binop dest =
 let fun strip A [] = rev A
       | strip A (h::t) =
          case dest h
           of NONE => strip (h::A) t
            | SOME(c1,c2) => strip A (c1::c2::t)
 in strip [] o single
 end;

(* For right-associative binary operators. Tail recursive. *)

fun spine_binop dest =
 let fun strip A tm =
       case dest tm
         of NONE => rev (tm::A)
          | SOME (l,r) => strip (l::A) r
 in strip []
 end;

(* for left-associative binary operators.  Tail recursive *)
fun lspine_binop dest = let
  fun strip A tm =
      case dest tm of
        NONE => tm :: A
      | SOME (l,r) => strip (r::A) l
in
  strip []
end;

(* For right-associative binary operators. Tail recursive. *)

fun list_mk_rbinop mk_binop alist =
    case List.rev alist of
      [] => raise ERR "list_mk_rbinop" "empty list"
    | h::t => rev_itlist mk_binop t h

(* For left-associative binary operators. Tail recursive. *)

fun list_mk_lbinop _ [] = raise ERR "list_mk_lbinop" "empty list"
  | list_mk_lbinop mk_binop (h::t) = rev_itlist (C mk_binop) t h;

fun mk_binder c f (p as (Bvar,_)) =
   mk_comb(Term.inst[alpha |-> type_of Bvar] c, mk_abs p)
   handle HOL_ERR {message,...} => raise ERR f message;

fun mk_tybinder c f (p as (Bvar,_)) =
   mk_comb(Term.inst_kind[kappa |-> kind_of Bvar] c, mk_tyabs p)
   handle HOL_ERR {message,...} => raise ERR f message;

fun list_mk_fun (dtys, rty) = List.foldr op--> rty dtys

val strip_fun =
  let val dest = total dom_rng
      fun strip acc ty =
          case dest ty
            of SOME (d,r) => strip (d::acc) r
             | NONE => (rev acc, ty)
  in strip []
  end;

fun list_mk_all_abs (vars,tm) =
  foldr (fn (inL tyv, tm) => mk_tyabs(tyv,tm)
          | (inR   v, tm) => mk_abs(v,tm))
        tm vars

fun strip_all_abs tm =
  if is_abs tm then
    let val (v,body1) = dest_abs tm
        val (vs,body) = strip_all_abs body1
    in (inR v::vs,body)
    end
  else if is_tyabs tm then
    let val (a,body1) = dest_tyabs tm
        val (vs,body) = strip_all_abs body1
    in (inL a::vs,body)
    end
  else ([],tm)

fun list_mk_all_comb (f,args) =
  foldl (fn (inL ty, f) => mk_tycomb(f,ty)
          | (inR tm, f) => mk_comb(f,tm))
        f args

fun strip_all_comb tm =
  let
    fun strip acc tm =
        let val (f,x) = dest_comb tm
        in strip (inR x::acc) f
        end
      handle HOL_ERR _ =>
        let val (f,a) = dest_tycomb tm
        in strip (inL a::acc) f
        end
      handle HOL_ERR _ => (tm,acc)
  in strip [] tm
  end

datatype lambda
   = VAR    of string * hol_type
   | CONST  of {Name:string, Thy:string, Ty:hol_type}
   | COMB   of term * term
   | TYCOMB of term * hol_type
   | LAMB   of term * term
   | TYLAMB of hol_type * term;

fun dest_term M =
  COMB  (dest_comb M)   handle HOL_ERR _ =>
  TYCOMB(dest_tycomb M) handle HOL_ERR _ =>
  LAMB  (dest_abs M)    handle HOL_ERR _ =>
  TYLAMB(dest_tyabs M)  handle HOL_ERR _ =>
  VAR   (dest_var M)    handle HOL_ERR _ =>
  CONST (dest_thy_const M);


datatype omega_type
   = TYVAR of string * kind
   | TYCONST of {Thy:string, Tyop:string, Kind:kind}
   | TYAPP  of hol_type * hol_type
   | TYUNIV of hol_type * hol_type
   | TYEXIS of hol_type * hol_type
   | TYABS  of hol_type * hol_type;

fun destruct_type Ty =
  TYAPP   (dest_app_type     Ty) handle HOL_ERR _ =>
  TYUNIV  (dest_univ_type    Ty) handle HOL_ERR _ =>
  TYEXIS  (dest_exist_type   Ty) handle HOL_ERR _ =>
  TYABS   (dest_abs_type     Ty) handle HOL_ERR _ =>
  TYVAR   (dest_var_type     Ty) handle HOL_ERR _ =>
  TYCONST (dest_thy_con_type Ty);

fun is_omega th = Lib.exists Term.is_omega (hyp th) orelse Term.is_omega (concl th)


(*---------------------------------------------------------------------------*
 * Used to implement natural deduction style discharging of hypotheses. All  *
 * hypotheses alpha-convertible to the dischargee are removed.               *
 *---------------------------------------------------------------------------*)

fun disch(w,wl) = List.filter (not o Term.aconv w) wl;


(*---------------------------------------------------------------------------*
 * Search a term for a sub-term satisfying the predicate P. If application   *
 * of P raises an exception, that propagates to the caller. Therefore,       *
 * P should be a total predicate: otherwise, the caller won't know whether   *
 * the search failed because the sought-for subterm is not there, or because *
 * P failed.                                                                 *
 *---------------------------------------------------------------------------*)

fun find_term P =
 let fun find_tm tm =
      if P tm then tm else
      if is_abs tm then find_tm (body tm) else
      if is_comb tm
         then let val (Rator,Rand) = dest_comb tm
              in find_tm Rator handle HOL_ERR _ => find_tm Rand
              end
      else
      if is_tyabs tm then find_tm (snd (dest_tyabs tm)) else
      if is_tycomb tm then find_tm (fst (dest_tycomb tm))
         else raise ERR "find_term" ""
 in find_tm
 end;

(* ----------------------------------------------------------------------
    bvk_find_term :
     (term list * term -> bool) -> (term -> 'a) -> term -> 'a option

    [bvk_find_term P k tm] searches tm for a sub-term satisfying P and
    calls the continuation k on the first that it finds.  If k
    succeeds on this sub-term, the result is wrapped in SOME.  If k
    raises a HOL_ERR exception, control returns to bvk_find_term,
    which continues to look for a sub-term satisfying P.  Other
    exceptions are returned to the caller. If there is no sub-term
    that both satisfies P and which k operates on successfully, the
    result is NONE.

    The search order is top-down, left-to-right (i.e., rators of combs
    are examined before rands).

    As with find_term, P should be total.  In addition, P is given not
    just the sub-term of interest, but also the stack of bound
    variables that have scope over the sub-term, with the innermost
    bound variables appearing earlier in the list.

    abvk_find_term :
     ((hol_type, term)Lib.sum list * term -> bool) -> (term -> 'a) -> term -> 'a option

    abvk_find_term is the same as bvk_find_term, except that P's first argument
    is a stack of bound type variables or term variables, possibly a mixture
    of both, that have scope over the sub-term, with the innermost
    bound type variables or term variables appearing earlier in the list.
   ---------------------------------------------------------------------- *)

local
datatype action = SEARCH of term | POP
in
fun bvk_find_term P k t = let
  fun search bvs actions =
      case actions of
        [] => NONE
      | POP :: alist => search (tl bvs) alist
      | SEARCH t :: alist => let
        in
          if P (bvs, t) then
            SOME (k t) handle HOL_ERR _ => subterm bvs alist t
          else subterm bvs alist t
        end
  and subterm bvs alist t =
      case dest_term t of
        COMB(t1, t2) => search bvs (SEARCH t1 :: SEARCH t2 :: alist)
      | LAMB(bv, t) => search (bv::bvs) (SEARCH t :: POP :: alist)
      | TYCOMB(tm, ty) => search bvs (SEARCH tm :: alist)
      | TYLAMB(bv, t) => search bvs (SEARCH t :: POP :: alist)
      | _ => search bvs alist
in
  search [] [SEARCH t]
end

fun abvk_find_term P k t = let
  fun search bvs actions =
      case actions of
        [] => NONE
      | POP :: alist => search (tl bvs) alist
      | SEARCH t :: alist => let
        in
          if P (bvs, t) then
            SOME (k t) handle HOL_ERR _ => subterm bvs alist t
          else subterm bvs alist t
        end
  and subterm bvs alist t =
      case dest_term t of
        COMB(t1, t2) => search bvs (SEARCH t1 :: SEARCH t2 :: alist)
      | LAMB(bv, t) => search (inR bv::bvs) (SEARCH t :: POP :: alist)
      | TYCOMB(tm, ty) => search bvs (SEARCH tm :: alist)
      | TYLAMB(bv, t) => search (inL bv::bvs) (SEARCH t :: POP :: alist)
      | _ => search bvs alist
in
  search [] [SEARCH t]
end
end (* local *)



(*---------------------------------------------------------------------------
 * find_terms: (term -> bool) -> term -> term list
 *
 *  Find all subterms in a term that satisfy a given predicate p.
 *
 * Added TFM 88.03.31
 *---------------------------------------------------------------------------*)

fun find_terms P =
 let fun accum tl tm =
      let val tl' = if P tm then tm::tl else tl
      in accum tl' (body tm)
         handle HOL_ERR _ =>
          if is_comb tm
          then let val (r1,r2) = dest_comb tm
               in accum (accum tl' r1) r2
               end
          else if is_tycomb tm then accum tl' (fst (dest_tycomb tm))
          else if is_tyabs tm then accum tl' (snd (dest_tyabs tm))
          else tl'
      end
 in accum []
 end;

(* ----------------------------------------------------------------------
    find_maximal_terms[l]

    finds sub-terms within a term, but doesn't look into sub-terms that
    match the provided predicate.  The find_maximal_termsl version
    returns the terms as a list rather than a set.
   ---------------------------------------------------------------------- *)

fun find_maximal_terms P t = let
  fun recurse acc tlist =
      case tlist of
        [] => acc
      | t::ts =>
        if P t then recurse (HOLset.add(acc, t)) ts
        else
          case dest_term t of
            COMB(f,x) => recurse acc (f::x::ts)
          | LAMB(v,b) => recurse acc (b::ts)
          | TYCOMB(f,ty) => recurse acc (f::ts)
          | TYLAMB(ty,b) => recurse acc (b::ts)
          | _ => recurse acc ts
in
  recurse empty_tmset [t]
end

fun find_maximal_termsl P t = HOLset.listItems (find_maximal_terms P t)

(* ----------------------------------------------------------------------
    term_size

    Returns a term's size.  There's no logical significance to this
    number, but it can be useful.
   ---------------------------------------------------------------------- *)

fun term_size t = let
  fun recurse acc tlist =
      case tlist of
        [] => acc
      | t::ts =>
        case dest_term t of
          COMB(f, x) => recurse acc (f::x::ts)
        | LAMB(v,b) => recurse (1 + acc) (b::ts)
        | TYCOMB(f, ty) => recurse (1 + acc) (f::ts)
        | TYLAMB(ty,b)  => recurse (1 + acc) (b::ts)
        | _ => recurse (1 + acc) ts
in
  recurse 0 [t]
end

(*---------------------------------------------------------------------------
 * Subst_occs
 * Put a new variable in tm2 at designated (and free) occurrences of redex.
 * Rebuilds the entire term.
 *---------------------------------------------------------------------------*)

local
fun splice ({redex,...}:{redex:term,residue:term}) v occs tm2 =
   let fun graft (r as {occs=[], ...}) = r
         | graft {tm, occs, count} =
          if term_eq redex tm
          then if (List.hd occs=count+1)
               then {tm=v, occs=List.tl occs, count=count+1}
               else {tm=tm, occs=occs, count=count+1}
          else if (is_comb tm)
               then let val (Rator, Rand) = dest_comb tm
                        val {tm=Rator', occs=occs', count=count'} =
                                        graft {tm=Rator,occs=occs,count=count}
                        val {tm=Rand', occs=occs'', count=count''} =
                                        graft {tm=Rand,occs=occs',count=count'}
                    in {tm=mk_comb(Rator', Rand'),
                        occs=occs'', count=count''}
                    end
               else if is_abs tm
                    then let val (Bvar,Body) = dest_abs tm
                             val {tm, count, occs} =
                                        graft{tm=Body,count=count,occs=occs}
                         in {tm=mk_abs(Bvar, tm),
                             count=count, occs=occs}
                         end
               else if (is_tycomb tm)
                    then let val (Rator, Rand) = dest_tycomb tm
                             val {tm, occs, count} =
                                        graft{tm=Rator,occs=occs,count=count}
                         in {tm=mk_tycomb(tm, Rand),
                             occs=occs, count=count}
                         end
               else if is_tyabs tm
                    then let val (Bvar,Body) = dest_tyabs tm
                             val {tm, count, occs} =
                                        graft{tm=Body,count=count,occs=occs}
                         in {tm=mk_tyabs(Bvar, tm),
                             count=count, occs=occs}
                         end
                    else {tm=tm, occs=occs, count=count}
   in #tm(graft {tm=tm2, occs=occs, count=0})
   end

fun rev_itlist3 f L1 L2 L3 base_value =
 let fun rev_it3 (a::rst1) (b::rst2) (c::rst3) base =
             rev_it3 rst1 rst2 rst3 (f a b c base)
       | rev_it3 [] [] [] base = base
       | rev_it3 _ _ _ _ = raise ERR "rev_itlist3"
                                  "not all lists have same size"
 in rev_it3 L1 L2 L3 base_value
 end

val sort = Lib.sort (Lib.curry (op <=) : int -> int -> bool)
in
fun subst_occs occ_lists tm_subst tm =
   let val occ_lists' = map sort occ_lists
       val (new_vars,theta) =
               Lib.itlist (fn {redex,residue} => fn (V,T) =>
                         let val v = genvar(type_of redex)
                         in (v::V,  (v |-> residue)::T)  end)
                      tm_subst ([],[])
       val template = rev_itlist3 splice tm_subst new_vars occ_lists' tm
   in subst theta template
   end
end;

end
