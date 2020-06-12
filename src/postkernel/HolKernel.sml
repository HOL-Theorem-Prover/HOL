structure HolKernel =
struct

  open Feedback Globals Lib Type Term Thm Theory
  open Definition


(*---------------------------------------------------------------------------
     Miscellaneous other stuff that builds on top of kernel facilities.
 ---------------------------------------------------------------------------*)

infixr -->;  infix |->;

local
  val ERR = mk_HOL_ERR "HolKernel"
in

(*---------------------------------------------------------------------------
          General term operations
 ---------------------------------------------------------------------------*)

fun dest_monop c e M =
   let
      val (c1, N) = with_exn dest_comb M e
   in
      if same_const c c1 then N else raise e
   end

local
   fun dest tm =
      let
         val (Rator, N) = dest_comb tm
         val (c, M) = dest_comb Rator
      in
         (c, (M, N))
      end
in
   fun dest_binop c e tm =
      let
         val (c1, pair) = with_exn dest tm e
      in
         if same_const c c1 then pair else raise e
      end
end

fun dest_triop p e M =
   let
      val (f, z) = with_exn dest_comb M e
      val (x, y) = dest_binop p e f
   in
      (x, y, z)
   end

(*---------------------------------------------------------------------------*)
(* Take a binder apart. Fails on paired binders.                             *)
(*---------------------------------------------------------------------------*)

local
   fun dest M = let val (c, Rand) = dest_comb M in (c, dest_abs Rand) end
in
   fun dest_binder c e M =
      let
         val (c1, p) = with_exn dest M e
      in
         if same_const c c1 then p else raise e
      end
end

local
   fun dest M =
      let val (Rator, Rand) = dest_comb M in (dest_thy_const Rator, Rand) end
in
   fun sdest_monop (name, thy) e M =
      let
         val ({Name, Thy, ...}, Rand) = with_exn dest M e
      in
         if Name = name andalso Thy = thy then Rand else raise e
      end
end

local
   fun dest tm =
      let
         val (Rator, N) = dest_comb tm
         val (c, M) = dest_comb Rator
      in
         (dest_thy_const c, (M, N))
      end
in
   fun sdest_binop (name, thy) e tm =
      let
         val ({Name, Thy, ...}, pair) = with_exn dest tm e
      in
         if Name = name andalso Thy = thy then pair else raise e
      end
end

local
   fun dest M =
       let val (c, Rand) = dest_comb M
       in (dest_thy_const c, dest_abs Rand)
       end
in
   fun sdest_binder (name, thy) e M =
      let
         val ({Name, Thy, ...}, p) = with_exn dest M e
      in
         if Name = name andalso Thy = thy then p else raise e
      end
end

(* Breaks term down until binop no longer occurs at top level in result list *)

fun strip_binop_opt dest =
   let
      fun strip A [] = rev A
        | strip A (h :: t) =
            case dest h of
               NONE => strip (h :: A) t
             | SOME (c1, c2) => strip A (c1 :: c2 :: t)
   in
      strip [] o Lib.list_of_singleton
   end

fun strip_binop dest = strip_binop_opt (total dest);

(* For right-associative binary operators,
  or such as dest_abs, SPEC_VAR, dom_rng, dest_imp. Tail recursive. *)

local
fun spine_binop' dest =
   let
      fun strip A tm =
         case dest tm of
            NONE => (tm, A)
          | SOME (l, r) => strip (l :: A) r
   in
      strip []
   end
in
fun spine_binop dest tm = rev ((op ::) (spine_binop' dest tm)) ;

fun strip_gen_left_opt dest t =
  let val (tm, A) = spine_binop' dest t in (rev A, tm) end ;
end (* local fun spine_binop' *)

fun strip_gen_left dest = strip_gen_left_opt (total dest) ;

(* For left-associative binary operators.  Tail recursive *)

fun strip_gen_right_opt dest =
   let
     fun strip A tm =
         case dest tm of
           NONE => (tm, A)
         | SOME (l, r) => strip (r :: A) l
   in
      strip []
   end

fun lspine_binop dest tm = (op ::) (strip_gen_right_opt dest tm) ;

fun strip_gen_right dest = strip_gen_right_opt (total dest) ;

(* For right-associative binary operators. Tail recursive. *)

fun list_mk_rbinop mk_binop alist =
   case List.rev alist of
      [] => raise ERR "list_mk_rbinop" "empty list"
    | h :: t => rev_itlist mk_binop t h

(* For left-associative binary operators. Tail recursive. *)

fun list_mk_lbinop _ [] = raise ERR "list_mk_lbinop" "empty list"
  | list_mk_lbinop mk_binop (h :: t) = rev_itlist (C mk_binop) t h

fun mk_binder c f (p as (Bvar, _)) =
   mk_comb (inst [alpha |-> type_of Bvar] c, mk_abs p)
   handle HOL_ERR {message, ...} => raise ERR f message

fun list_mk_fun (dtys, rty) = List.foldr op--> rty dtys

val strip_fun =
   let
      val dest = total dom_rng
      fun strip acc ty =
         case dest ty of
            SOME (d, r) => strip (d :: acc) r
          | NONE => (rev acc, ty)
   in
      strip []
   end

val strip_comb =
   let
      val destc = total dest_comb
      fun strip rands M =
         case destc M of
            NONE => (M, rands)
          | SOME (Rator, Rand) => strip (Rand :: rands) Rator
   in
      strip []
   end

fun dest_quadop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4]) =>
         if same_const t c then (t1, t2, t3, t4) else raise e
    | _ => raise e

local
   val mk_aty = list_mk_rbinop (Lib.curry Type.-->)
   val args = fst o strip_fun o Term.type_of
in
   fun list_mk_icomb tm xs =
      let
         val tyl = mk_aty (Lib.with_exn List.take (args tm, List.length xs)
                                        (ERR "" "too many arguments"))
         val tyr = mk_aty (List.map Term.type_of xs)
      in
         Term.list_mk_comb (Term.inst (Type.match_type tyl tyr) tm, xs)
      end
      handle HOL_ERR {message, ...} => raise ERR "list_mk_icomb" message

   fun syntax_fns
      {n: int, make: term -> 'a -> term, dest: term -> exn -> term -> 'b}
      thy name =
      let
         val ERR = Feedback.mk_HOL_ERR (thy ^ "Syntax")
         val tm = Term.prim_mk_const {Name = name, Thy = thy}
         val () =
            ignore (List.length (args tm) = n
                    orelse raise ERR "syntax_fns" "bad number of arguments")
         val d = dest tm (ERR ("dest_" ^ name) "")
      in
         (tm,
          fn v => Lib.with_exn (make tm) v (ERR ("mk_" ^ name) ""): term,
          d: term -> 'b,
          can d)
      end
end

fun mk_monop tm = list_mk_icomb tm o Lib.list_of_singleton
fun mk_binop tm = list_mk_icomb tm o Lib.list_of_pair
fun mk_triop tm = list_mk_icomb tm o Lib.list_of_triple
fun mk_quadop tm = list_mk_icomb tm o Lib.list_of_quadruple

val syntax_fns1 = syntax_fns {n = 1, make = mk_monop, dest = dest_monop}
val syntax_fns2 = syntax_fns {n = 2, make = mk_binop, dest = dest_binop}
val syntax_fns3 = syntax_fns {n = 3, make = mk_triop, dest = dest_triop}
val syntax_fns4 = syntax_fns {n = 4, make = mk_quadop, dest = dest_quadop}

(*---------------------------------------------------------------------------*
 * Used to implement natural deduction style discharging of hypotheses. All  *
 * hypotheses alpha-convertible to the dischargee are removed.               *
 *---------------------------------------------------------------------------*)

fun disch (w, wl) = List.filter (not o Term.aconv w) wl

(*---------------------------------------------------------------------------*
 * Search a term for a sub-term satisfying the predicate P. If application   *
 * of P raises an exception, that propagates to the caller. Therefore,       *
 * P should be a total predicate: otherwise, the caller won't know whether   *
 * the search failed because the sought-for subterm is not there, or because *
 * P failed.                                                                 *
 *---------------------------------------------------------------------------*)

fun find_term P =
   let
      fun find_tm tm =
         if P tm
            then tm
         else if is_abs tm
            then find_tm (body tm)
         else case Lib.total dest_comb tm of
                 SOME (Rator, Rand) =>
                    (find_tm Rator handle HOL_ERR _ => find_tm Rand)
               | NONE => raise ERR "find_term" ""
   in
      find_tm
   end


local
   datatype action = SEARCH of term | POP
in
   fun gen_find_term f t =
      let
        fun search bvs actions =
           case actions of
              [] => NONE
            | POP :: alist => search (tl bvs) alist
            | SEARCH t :: alist => (case f (bvs, t) of
                                        NONE => subterm bvs alist t
                                      | x => x)
        and subterm bvs alist t =
           case dest_term t of
              COMB (t1, t2) => search bvs (SEARCH t1 :: SEARCH t2 :: alist)
            | LAMB (bv, t) => search (bv :: bvs) (SEARCH t :: POP :: alist)
            | _ => search bvs alist
   in
      search [] [SEARCH t]
   end
   fun gen_find_terms f t =
       let
         fun search bvs actions acc =
             case actions of
                 [] => acc
               | POP :: alist => search (tl bvs) alist acc
               | SEARCH t :: alist =>
                 (case f (bvs, t) of
                      NONE => subterm bvs alist acc t
                    | SOME x => subterm bvs alist (x::acc) t)
         and subterm bvs alist acc t =
             case dest_term t of
                 COMB(t1, t2) => search bvs (SEARCH t1 :: SEARCH t2 :: alist)
                                        acc
               | LAMB (bv, t) => search (bv::bvs) (SEARCH t :: POP :: alist) acc
               | _ => search bvs alist acc
       in
         search [] [SEARCH t] []
       end
end (* local *)

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
   ---------------------------------------------------------------------- *)

fun bvk_find_term P k =
    gen_find_term (fn x => if P x then SOME (k (#2 x)) handle HOL_ERR _ => NONE
                           else NONE)

(*---------------------------------------------------------------------------
 * find_terms: (term -> bool) -> term -> term list
 *
 *  Find all subterms in a term that satisfy a given predicate p.
 *
 * Added TFM 88.03.31
 *---------------------------------------------------------------------------*)

fun find_terms P =
   let
      open Uref
      val tms = Uref.new []
      fun find_tms tm =
         (if P tm then tms := tm :: (!tms) else ()
          ; find_tms (body tm)
            handle HOL_ERR _ =>
               case Lib.total dest_comb tm of
                  SOME (r1, r2) => (find_tms r1; find_tms r2)
                | NONE => ())
   in
      fn tm =>
         let
            val r = (find_tms tm; (!tms))
         in
            tms := []; r
         end
   end

(* ----------------------------------------------------------------------
    find_maximal_terms[l]

    finds sub-terms within a term, but doesn't look into sub-terms that
    match the provided predicate.  The find_maximal_termsl version
    returns the terms as a list rather than a set.
   ---------------------------------------------------------------------- *)

fun find_maximal_terms P t =
   let
      fun recurse acc tlist =
         case tlist of
            [] => acc
          | t :: ts =>
               if P t
                  then recurse (HOLset.add (acc, t)) ts
               else case dest_term t of
                       COMB (f, x) => recurse acc (f :: x :: ts)
                     | LAMB (v, b) => recurse acc (b :: ts)
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

fun term_size t =
   let
      fun recurse acc tlist =
         case tlist of
            [] => acc
          | t :: ts =>
              (case dest_term t of
                  COMB (f, x) => recurse acc (f :: x :: ts)
                | LAMB (v, b) => recurse (1 + acc) (b :: ts)
                | _ => recurse (1 + acc) ts)
   in
      recurse 0 [t]
   end

(*---------------------------------------------------------------------------
 * Subst_occs
 * Put a new variable in tm2 at designated (and free) occurrences of redex.
 * Rebuilds the entire term.
 *---------------------------------------------------------------------------*)

local
fun splice ({redex, ...}:{redex:term, residue:term}) v occs tm2 =
   let fun graft (r as {occs=[], ...}) = r
         | graft {tm, occs, count} =
          if term_eq redex tm
          then if (List.hd occs = count + 1)
               then {tm=v, occs=List.tl occs, count=count+1}
               else {tm=tm, occs=occs, count=count+1}
          else if (is_comb tm)
               then let val (Rator, Rand) = dest_comb tm
                        val {tm=Rator', occs=occs', count=count'} =
                                        graft {tm=Rator, occs=occs, count=count}
                        val {tm=Rand', occs=occs'', count=count''} =
                                        graft {tm=Rand, occs=occs', count=count'}
                    in {tm=mk_comb (Rator', Rand'),
                        occs=occs'', count=count''}
                    end
               else if is_abs tm
                    then let val (Bvar, Body) = dest_abs tm
                             val {tm, count, occs} =
                                        graft{tm=Body, count=count, occs=occs}
                         in {tm=mk_abs (Bvar, tm),
                             count=count, occs=occs}
                         end
                    else {tm=tm, occs=occs, count=count}
   in #tm (graft {tm=tm2, occs=occs, count=0})
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
       val (new_vars, theta) =
               Lib.itlist (fn {redex, residue} => fn (V, T) =>
                         let val v = genvar (type_of redex)
                         in (v::V,  (v |-> residue)::T)  end)
                      tm_subst ([],[])
       val template = rev_itlist3 splice tm_subst new_vars occ_lists' tm
   in subst theta template
   end
end

(*---------------------------------------------------------------------------
       Higher order matching (from jrh via Michael Norrish - June 2001)
 ---------------------------------------------------------------------------*)

local
  exception NOT_FOUND
  fun find_residue red [] = raise NOT_FOUND
    | find_residue red ({redex, residue}::rest) =
        if aconv red redex then residue else find_residue red rest
  fun find_residue_eq red [] = raise NOT_FOUND
    | find_residue_eq red ({redex, residue}::rest) =
        if red = redex then residue else find_residue_eq red rest
  fun in_dom x [] = false
    | in_dom x ({redex, residue}::rest) = aconv x redex orelse in_dom x rest
  fun in_domeq x [] = false
    | in_domeq x ({redex,residue}::rest) = x = redex orelse in_domeq x rest

  (* for terms *)
  fun safe_insert (n as {redex, residue}) l =
    let
      val z = find_residue redex l
    in
      if aconv residue z then l
      else failwith "match: safe_insert"
    end handle NOT_FOUND => n::l

  fun safe_inserteq (n as {redex,residue}) l =
    let
      val z = find_residue redex l
    in
      if residue = z then l
      else failwith "match: safe_insert"
    end handle NOT_FOUND => n::l
  val mk_dummy = let
    val name = fst (dest_var (genvar Type.alpha))
  in fn ty => mk_var (name, ty)
  end


  fun term_pmatch lconsts env vtm ctm (sofar as (insts, homs)) =
    if is_var vtm then let
        val ctm' = find_residue vtm env
      in
        if aconv ctm' ctm then sofar else failwith "term_pmatch"
      end handle NOT_FOUND =>
                 if HOLset.member (lconsts, vtm) then
                   if aconv ctm vtm then sofar
                   else
                     failwith "term_pmatch: can't instantiate local constant"
                 else (safe_insert (vtm |-> ctm) insts, homs)
    else if is_const vtm then let
        val {Thy = vthy, Name = vname, Ty = vty} = dest_thy_const vtm
        val {Thy = cthy, Name = cname, Ty = cty} = dest_thy_const ctm
      in
        if vname = cname andalso vthy = cthy then
          if cty = vty then sofar
          else (safe_insert (mk_dummy vty |-> mk_dummy cty) insts, homs)
        else failwith "term_pmatch"
      end
    else if is_abs vtm then let
        val (vv, vbod) = dest_abs vtm
        val (cv, cbod) = dest_abs ctm
        val (_, vty) = dest_var vv
        val (_, cty) = dest_var cv
        val sofar' = (safe_insert (mk_dummy vty |-> mk_dummy cty) insts, homs)
      in
        term_pmatch lconsts ((vv |-> cv)::env) vbod cbod sofar'
      end
    else let
        val vhop = repeat rator vtm
      in
        if is_var vhop andalso not (HOLset.member (lconsts, vhop)) andalso
           not (in_dom vhop env)
        then let
            val vty = type_of vtm
            val cty = type_of ctm
            val insts' = if vty = cty then insts
                         else safe_insert (mk_dummy vty |-> mk_dummy cty) insts
          in
            (insts', (env, ctm, vtm)::homs)
          end
        else let
            val (lv, rv) = dest_comb vtm
            val (lc, rc) = dest_comb ctm
            val sofar' = term_pmatch lconsts env lv lc sofar
          in
            term_pmatch lconsts env rv rc sofar'
          end
      end

(*
fun get_type_insts avoids L =
 let val avtys = itlist (fn ty => fn (p,o) => (ty-->p, ty-->o))
                        avoids (bool,bool)
     val (pat,ob) = itlist (fn {redex,residue} => fn (pat,ob) =>
                               (type_of redex-->pat, type_of residue-->ob))
                         L avtys

 in match_type pat ob
 end

fun get_type_insts avoids L =
 let val tytheta = itlist (fn {redex,residue} =>
          match_type_in_context (snd (dest_var redex)) (type_of residue))
                     L []
 in if null (intersect avoids (map #residue tytheta))
    then tytheta
    else raise ERR "get_type_insts" "attempt to bind fixed type variable"
 end
*)
fun get_type_insts avoids L (tyS, Id) =
 itlist (fn {redex, residue} => fn Theta =>
          raw_match_type (snd (dest_var redex)) (type_of residue) Theta)
       L (tyS, union avoids Id)

fun separate_insts tyavoids insts = let
  val (realinsts, patterns) = partition (is_var o #redex) insts
  val betacounts =
      if null patterns then []
      else
        itlist (fn {redex = p, ...} =>
                   fn sof => let
                        val (hop, args) = strip_comb p
                      in
                        safe_inserteq (hop |-> length args) sof
                      end handle HOL_ERR _ =>
                                 (HOL_WARNING "" ""
                                  "Inconsistent patterning in h.o. match";
                                  sof))
        patterns []
  val tyins = get_type_insts tyavoids realinsts ([],[])
in
  (betacounts,
   mapfilter (fn {redex = x, residue = t} => let
                   val x' = let val (xn, xty) = dest_var x
                            in
                              mk_var (xn, type_subst (#1 tyins) xty)
                            end
                 in
                   if aconv t x' then failwith "" else {redex = x', residue = t}
                 end) realinsts,
   tyins)
end

val tmmem = op_mem aconv
fun tyenv_in_dom x (env, idlist) = mem x idlist orelse in_domeq x env
fun tyenv_find_residue x (env, idlist) = if mem x idlist then x
                                         else find_residue_eq x env
fun tyenv_safe_insert (t as {redex, residue}) (E as (env, idlist)) = let
  val existing = tyenv_find_residue redex E
in
  if existing = residue then E else failwith "Type bindings clash"
end handle NOT_FOUND => if redex = residue then (env, redex::idlist)
                        else (t::env, idlist)

fun beta_normalise0 t = let
  val bn0 = beta_normalise0
  fun bn1 t = case bn0 t of NONE => SOME t | x => x
in
  case dest_term t of
    COMB (t1, t2) => let
    in
      case Lib.total beta_conv t of
        NONE => let
        in
          case bn0 t1 of
            NONE => Option.map (fn t2' => mk_comb (t1, t2')) (bn0 t2)
          | SOME t1' => bn1 (mk_comb (t1', t2))
        end
      | SOME t' => bn1 t'
    end
  | LAMB (v, t) => Option.map (fn t' => mk_abs (v, t')) (bn0 t)
  | x => NONE
end

fun beta_normalise t = case beta_normalise0 t of NONE => t | SOME x => x

fun all_abconv [] [] = true
  | all_abconv [] _ = false
  | all_abconv _ [] = false
  | all_abconv (h1::t1) (h2::t2) =
     aconv (beta_normalise h1) (beta_normalise h2) andalso all_abconv t1 t2

fun term_homatch tyavoids lconsts tyins (insts, homs) = let
  (* local constants of both terms and types never change *)
  val term_homatch = term_homatch tyavoids lconsts
in
  if null homs then insts
  else let
      val (env, ctm, vtm) = hd homs
    in
      if is_var vtm then
        if aconv ctm vtm then term_homatch tyins (insts, tl homs)
        else let
            val newtyins =
                tyenv_safe_insert (snd (dest_var vtm) |-> type_of ctm) tyins
            val newinsts = (vtm |-> ctm)::insts
          in
            term_homatch newtyins (newinsts, tl homs)
          end
      else (* vtm not a var *) let
          val (vhop, vargs) = strip_comb vtm
          val afvs = free_varsl vargs
          val inst_fn = Term.inst (fst tyins)
        in
          (let
             val tmins =
                 map (fn a =>
                         (inst_fn a |->
                                  (find_residue a env
                                   handle NOT_FOUND =>
                                          find_residue a insts
                                   handle NOT_FOUND =>
                                          if HOLset.member (lconsts, a)
                                          then a
                                          else failwith ""))) afvs
             val pats0 = map inst_fn vargs
             val pats = map (Term.subst tmins) pats0
             val vhop' = inst_fn vhop
             val ictm = list_mk_comb (vhop', pats)
             val ni = let
               val (chop, cargs) = strip_comb ctm
             in
               if all_abconv cargs pats then
                 if aconv chop vhop then insts
                 else safe_insert (vhop |-> chop) insts
               else let
                   val ginsts = map (fn p => (p |->
                                                (if is_var p then p
                                                 else genvar (type_of p))))
                                    pats
                   val ctm' = Term.subst ginsts ctm
                   val gvs = map #residue ginsts
                   val abstm = list_mk_abs (gvs, ctm')
                   val vinsts = safe_insert (vhop |-> abstm) insts
                   val icpair = (list_mk_comb (vhop', gvs) |-> ctm')
                 in
                   icpair::vinsts
                 end
             end
           in
             term_homatch tyins (ni, tl homs)
           end) handle HOL_ERR _ => let
                         val (lc, rc) = dest_comb ctm
                         val (lv, rv) = dest_comb vtm
                         val pinsts_homs' =
                             term_pmatch lconsts env rv rc
                                         (insts, (env, lc, lv)::(tl homs))
                         val tyins' =
                             get_type_insts tyavoids
                                            (fst pinsts_homs')
                                            ([], [])
                       in
                         term_homatch tyins' pinsts_homs'
                       end
        end
    end
end

in

fun ho_match_term0 tyavoids lconsts vtm ctm = let
  val pinsts_homs = term_pmatch lconsts [] vtm ctm ([], [])
  val tyins = get_type_insts tyavoids (fst pinsts_homs) ([], [])
  val insts = term_homatch tyavoids lconsts tyins pinsts_homs
in
  separate_insts tyavoids insts
end

fun ho_match_term tyavoids lconsts vtm ctm = let
  val (bcs, tmins, tyins) = ho_match_term0 tyavoids lconsts vtm ctm
in
  (tmins, #1 tyins)
end handle e => raise (wrap_exn "HolKernel" "ho_match_term" e)

end (* local *)

val sort_vars =
  Portable.pull_prefix o map (fn n => equal n o #1 o dest_var)

end
end
