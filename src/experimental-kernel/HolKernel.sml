structure HolKernel =
struct

  open Feedback Globals Lib Kind Type Term Thm Theory Definition


(*---------------------------------------------------------------------------
     Miscellaneous other stuff that builds on top of kernel facilities.
 ---------------------------------------------------------------------------*)

infixr ==>;  infixr -->;  infix |->;

val ERR = mk_HOL_ERR "HolKernel";

val kernelid = "expknl"

(*---------------------------------------------------------------------------
       Type antiquotations (required in term parser)
 ---------------------------------------------------------------------------*)

fun ty_antiq ty = mk_var("ty_antiq",ty)

fun dest_ty_antiq tm =
  case with_exn dest_var tm (ERR "dest_ty_antiq" "not a type antiquotation")
   of ("ty_antiq",Ty) => Ty
    |  _ => raise ERR "dest_ty_antiq" "not a type antiquotation";

val is_ty_antiq = Lib.can dest_ty_antiq


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

local fun dest M = let val (c,Rand) = dest_comb M in (c,dest_abs Rand) end
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

fun list_mk_rbinop _ [] = raise ERR "list_mk_rbinop" "empty list"
  | list_mk_rbinop mk_binop alist =
       let val rlist = List.rev alist
           val h = List.hd rlist
           and t = List.tl rlist
       in rev_itlist mk_binop t h
       end;

fun mk_binder c f (p as (Bvar,_)) =
   mk_comb(inst[alpha |-> type_of Bvar] c, mk_abs p)
   handle HOL_ERR {message,...} => raise ERR f message;

fun mk_tybinder c f (p as (Bvar,_)) =
   mk_comb(inst_kind[kappa |-> kind_of Bvar] c, mk_tyabs p)
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


datatype lambda
   = VAR   of string * hol_type
   | CONST of {Name:string, Thy:string, Ty:hol_type}
   | COMB  of term * term
   | LAMB  of term * term
   | TYCOMB of term * hol_type
   | TYLAMB of hol_type * term;

fun dest_term M =
  COMB(dest_comb M)     handle HOL_ERR _ =>
  LAMB(dest_abs M)      handle HOL_ERR _ =>
  TYCOMB(dest_tycomb M) handle HOL_ERR _ =>
  TYLAMB(dest_tyabs M)  handle HOL_ERR _ =>
  VAR (dest_var M)      handle HOL_ERR _ =>
  CONST(dest_thy_const M);


datatype omega_type
   = TYVAR of string * kind * int (* rank *)
   | TYCONST of {Thy:string, Tyop:string, Kind:kind, Rank:int}
   | TYAPP  of hol_type * hol_type
   | TYUNIV of hol_type * hol_type
   | TYABS  of hol_type * hol_type;

fun destruct_type Ty =
  TYAPP   (dest_app_type     Ty) handle HOL_ERR _ =>
  TYUNIV  (dest_univ_type    Ty) handle HOL_ERR _ =>
  TYABS   (dest_abs_type     Ty) handle HOL_ERR _ =>
  TYVAR   (dest_var_type     Ty) handle HOL_ERR _ =>
  TYCONST (dest_thy_con_type Ty);


(*---------------------------------------------------------------------------*
 * Used to implement natural deduction style discharging of hypotheses. All  *
 * hypotheses alpha-convertible to the dischargee are removed.               *
 *---------------------------------------------------------------------------*)

fun disch(w,wl) = Lib.gather (not o Term.aconv w) wl;


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
