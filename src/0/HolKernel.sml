structure HolKernel =
struct
  structure Type = Type
  structure Term = Term
  structure Tag  = Tag
  structure Thm  = Thm
  structure Theory = Theory
  structure Definition = Definition

  open Feedback Globals Lib Type Term Thm Theory Definition


(*---------------------------------------------------------------------------
     Miscellaneous other stuff that builds on top of kernel facilities.
 ---------------------------------------------------------------------------*)

local val ERR = mk_HOL_ERR "HolKernel"
      infix |->
      infixr -->
in

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

local fun dest M =
       let val (Rator,Rand) = dest_comb M in (dest_thy_const Rator,Rand) end
in
fun dest_monop (name,thy) e M =
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
fun dest_binop (name,thy) e tm =
   let val ({Name,Thy,...},pair) = with_exn dest tm e
   in if Name=name andalso Thy=thy then pair else raise e
   end
end;

fun single x = [x];

fun strip_binop dest =
 let fun strip A [] = rev A
       | strip A (h::t) =
          case dest h
           of NONE => strip (h::A) t
            | SOME(c1,c2) => strip A (c1::c2::t)
 in strip [] o single
 end;

fun mk_binder c f (p as (Bvar,_)) =
   mk_comb(inst[alpha |-> type_of Bvar] c, mk_abs p)
   handle HOL_ERR {message,...} => raise ERR f message;


local fun dest M =
       let val (c, Rand) = dest_comb M
       in (dest_thy_const c,dest_abs Rand)
       end
in
fun dest_binder (name,thy) e M =
  let val ({Name,Thy,...}, p) = with_exn dest M e
  in if Name=name andalso Thy=thy then p else raise e
  end
end;

fun strip_binder dest =
  let fun strip A M =
       case dest M
        of NONE => (List.rev A, M)
         | SOME(Bvar,Body) => strip (Bvar::A) Body
  in strip []
  end

fun list_mk_fun (dtys, rty) = List.foldr op--> rty dtys
val strip_fun = strip_binder (total dom_rng);

fun list_mk_abs(V,t) = itlist(curry mk_abs) V t;
val strip_abs = strip_binder (total dest_abs);

local val destc = total dest_comb
in
val strip_comb =
 let fun strip rands M =
      case destc M
       of NONE => (M, rands)
        | SOME(Rator,Rand) => strip (Rand::rands) Rator
 in strip []
 end
end;


datatype lambda
   = VAR   of string * hol_type
   | CONST of {Name:string, Thy:string, Ty:hol_type}
   | COMB  of term * term
   | LAMB  of term * term;

fun dest_term M =
  COMB(dest_comb M) handle HOL_ERR _ =>
  LAMB(dest_abs M)  handle HOL_ERR _ =>
  VAR (dest_var M)  handle HOL_ERR _ =>
  CONST(dest_thy_const M);

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
          else tl'
      end
 in accum []
 end;

(*---------------------------------------------------------------------------
 * Subst_occs
 * Put a new variable in tm2 at designated (and free) occurrences of redex.
 * Rebuilds the entire term.
 *---------------------------------------------------------------------------*)

local
fun splice ({redex,...}:{redex:term,residue:term}) v occs tm2 =
   let fun graft (r as {occs=[], ...}) = r
         | graft {tm, occs, count} =
          if redex = tm
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

fun thm_free_vars th =
  let val (asl,c) = dest_thm th in free_varsl (c::asl) end;


(*---------------------------------------------------------------------------
       Higher order matching (from jrh via Michael Norrish - June 2001)
 ---------------------------------------------------------------------------*)

local
  exception NOT_FOUND
  fun find_residue red [] = raise NOT_FOUND
    | find_residue red ({redex,residue}::rest) = if red = redex then residue
                                                 else find_residue red rest
  fun in_dom x [] = false
    | in_dom x ({redex,residue}::rest) = (x = redex) orelse in_dom x rest
  fun safe_insert (n as {redex,residue}) l = let
    val z = find_residue redex l
  in
    if residue = z then l
    else failwith "match: safe_insert"
  end handle NOT_FOUND => n::l  (* binding not there *)
  fun safe_inserta (n as {redex,residue}) l = let
    val z = find_residue redex l
  in
    if aconv residue z then l
    else failwith "match: safe_inserta"
  end handle NOT_FOUND => n::l
  val mk_dummy = let
    val name = fst(dest_var(genvar Type.alpha))
  in fn ty => mk_var(name, ty)
  end


  fun term_pmatch lconsts env vtm ctm (sofar as (insts,homs)) =
    if is_var vtm then let
        val ctm' = find_residue vtm env
      in
        if ctm' = ctm then sofar else failwith "term_pmatch"
      end handle NOT_FOUND =>
                 if mem vtm lconsts then
                   if ctm = vtm then sofar
                   else
                     failwith "term_pmatch: can't instantiate local constant"
                 else (safe_inserta (vtm |-> ctm) insts, homs)
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
        val (vv,vbod) = dest_abs vtm
        val (cv,cbod) = dest_abs ctm
        val (_, vty) = dest_var vv
        val (_, cty) = dest_var cv
        val sofar' = (safe_insert(mk_dummy vty |-> mk_dummy cty) insts, homs)
      in
        term_pmatch lconsts ((vv |-> cv)::env) vbod cbod sofar'
      end
    else let
        val vhop = repeat rator vtm
      in
        if is_var vhop andalso not (mem vhop lconsts) andalso
           not (in_dom vhop env)
        then let
            val vty = type_of vtm
            val cty = type_of ctm
            val insts' = if vty = cty then insts
                         else safe_insert (mk_dummy vty |-> mk_dummy cty) insts
          in
            (insts', (env,ctm,vtm)::homs)
          end
        else let
            val (lv,rv) = dest_comb vtm
            val (lc,rc) = dest_comb ctm
            val sofar' = term_pmatch lconsts env lv lc sofar
          in
            term_pmatch lconsts env rv rc sofar'
          end
      end

fun type_match vty cty sofar =
    if is_vartype vty then
      if vty = cty orelse (find_residue vty sofar = cty handle _ => false)
      then sofar
      else (vty |-> cty)::sofar
    else let
        val {Thy = vthy, Tyop = vop, Args = vargs} = dest_thy_type vty
        val {Thy = cthy, Tyop = cop, Args = cargs} = dest_thy_type cty
      in
        if vop = cop andalso cthy = vthy then
          itlist2 type_match vargs cargs sofar
        else failwith "type_match"
      end

fun get_type_insts insts =
    itlist (fn {redex = x, residue = t} =>
               type_match (snd (dest_var x)) (type_of t))
           insts

fun separate_insts insts = let
  val (realinsts, patterns) = partition (is_var o #redex) insts
  val betacounts =
      if patterns = [] then []
      else
        itlist (fn {redex = p,...} =>
                   fn sof => let
                        val (hop,args) = strip_comb p
                      in
                        safe_insert (hop |-> length args) sof
                      end handle _ =>
                                 (HOL_WARNING "" ""
                                  "Inconsistent patterning in h.o. match";
                                  sof))
        patterns []
  val tyins = get_type_insts realinsts []
in
  (betacounts,
   mapfilter (fn {redex = x, residue = t} => let
                   val x' = let val (xn,xty) = dest_var x
                            in
                              mk_var(xn, type_subst tyins xty)
                            end
                 in
                   if t = x' then failwith "" else {redex = x', residue = t}
                 end) realinsts,
   tyins)
end

fun term_homatch lconsts tyins (insts, homs) =
    if homs = [] then insts
    else let
        val (env,ctm,vtm) = hd homs
      in
        if is_var vtm then
          if ctm = vtm then term_homatch lconsts tyins (insts, tl homs)
          else let
              val newtyins =
                  safe_insert (snd (dest_var vtm) |-> type_of ctm) tyins
              val newinsts = (vtm |-> ctm)::insts
            in
              term_homatch lconsts newtyins (newinsts, tl homs)
            end
        else (* vtm not a var *) let
            val (vhop, vargs) = strip_comb vtm
            val afvs = free_varsl vargs
            val inst_fn = Term.inst tyins
          in
            (let
               val tmins =
                   map (fn a => (inst_fn a |->
                                         (find_residue a env
                                          handle _ =>
                                                 find_residue a insts
                                          handle _ =>
                                                 if mem a lconsts then a
                                                 else failwith ""))) afvs
               val pats0 = map inst_fn vargs
               val pats = map (Term.subst tmins) pats0
               val vhop' = inst_fn vhop
               val ictm = list_mk_comb(vhop', pats)
               val ni = let
                 val (chop,cargs) = strip_comb ctm
               in
                 if cargs = pats then
                   if chop = vhop then insts
                   else safe_inserta (vhop |-> chop) insts
                 else let
                     val ginsts = map (fn p => (p |->
                                                (if is_var p then p
                                                 else genvar(type_of p))))
                                      pats
                     val ctm' = Term.subst ginsts ctm
                     val gvs = map #residue ginsts
                     val abstm = list_mk_abs(gvs,ctm')
                     val vinsts = safe_inserta (vhop |-> abstm) insts
                     val icpair = (list_mk_comb(vhop',gvs) |-> ctm')
                   in
                     icpair::vinsts
                   end
               end
             in
               term_homatch lconsts tyins (ni,tl homs)
             end) handle _ => let
                           val (lc,rc) = dest_comb ctm
                           val (lv,rv) = dest_comb vtm
                           val pinsts_homs' =
                               term_pmatch lconsts env rv rc
                               (insts, (env,lc,lv)::(tl homs))
                           val tyins' = get_type_insts (fst pinsts_homs') []
                         in
                           term_homatch lconsts tyins' pinsts_homs'
                         end
          end
      end

in

fun ho_match_term0 lconsts vtm ctm = let
  val pinsts_homs = term_pmatch lconsts [] vtm ctm ([], [])
  val tyins = get_type_insts (fst pinsts_homs) []
  val insts = term_homatch lconsts tyins pinsts_homs
in
  separate_insts insts
end

fun ho_match_term lconsts vtm ctm = let
  val (bcs, tmins, tyins) = ho_match_term0 lconsts vtm ctm
in
  (tmins, tyins)
end handle e => raise (wrap_exn "HolKernel" "ho_match_term" e)

end;


(*
datatype theory
     = THEORY of {name : string,
                  types : (string * int),
                  consts : (string * hol_type) list,
                  parents : theory list,
                  axioms : thm list,
                  definitions : thm list,
                  theorems : thm list,
                  extras : (ppstream -> unit) list};

fun dest_theory() =
  THEORY
    {name = current_theory(),
     types = types(),
     consts = constants(),
     parents = parents(),
     axioms = axioms(),
     definitions = definitions(),
     theorems = theorems()};

end ;



(*--------------------------------------------------------------------------*
 * Print a theory for the user.                                             *
 *--------------------------------------------------------------------------*)

val CONSISTENT   = Portable.CONSISTENT
val INCONSISTENT = Portable.INCONSISTENT;

fun pp_theory {pp_thm,pp_type} ppstrm thy =
let
  val {thid,con_wrt_disk,facts,overwritten,adjoin} = thy
  val {add_string,add_break,begin_block,end_block, add_newline,
       flush_ppstream,...} = Portable.with_ppstream ppstrm
  val pp_thm = pp_thm ppstrm
  val pp_type = pp_type ppstrm
  fun vblock(header, ob_pr, obs) =
    ( begin_block CONSISTENT 4;
     add_string (header^":");
     add_newline();
     Portable.pr_list ob_pr
     (fn () => ()) add_newline obs;
     end_block(); add_newline(); add_newline())
  fun pr_thm (heading, ths) =
    vblock(heading, (fn (s,th) =>
                     (begin_block CONSISTENT 0; add_string s; add_break(1,0);
                      pp_thm th; end_block())),  ths)
  val thyname = thyid_name thid
  fun pp_consistency b =
    add_string ("Theory "^(Lib.quote thyname)^" is "^
                (if b then "consistent" else "inconsistent")^" with disk.\n")
  val (A,D,T) = unkind facts
  val types = thy_types thyname
  val constants = Lib.mapfilter dconst (thy_constants thyname)
in
    begin_block CONSISTENT 0;
    add_string ("Theory: "^thyname);
    add_newline();   add_newline() ;
    vblock ("Parents", add_string, map thyid_name (Graph.fringe()))
      ;
    vblock ("Type constants",
            (fn (name,arity) =>
                (add_string name; add_string (" "^Lib.int_to_string arity))),
            rev types)
      ;
    vblock ("Term constants",
             (fn (name,htype)
              => (begin_block CONSISTENT 0;
                  add_string (name^" ");
                  add_break(3,0);
                  pp_type htype;
                  end_block())),
                 rev constants)
      ;
    pr_thm ("Axioms", A);
    pr_thm ("Definitions", D);
    pr_thm ("Theorems", T);
    pp_consistency con_wrt_disk;
    end_block();
    flush_ppstream()
 end;


fun print_theory_to_outstream printers outstream =
  let val def_Cons = Portable.defaultConsumer()
      val consumer = {consumer = Portable.outputc outstream,
                      flush = #flush def_Cons,
                      linewidth = #linewidth def_Cons}
      val stream = Portable.mk_ppstream consumer
      val _ = pp_theory printers stream (theCT())
      val _ = Portable.flush_out outstream
  in outstream end

fun print_theory_to_file printers file =
    let val outfile = Portable.open_out file
    in Portable.close_out (print_theory_to_outstream printers outfile)
    end

fun print_theory0 printers =
   pp_theory printers (Portable.mk_ppstream
                       (Portable.defaultConsumer()))
   (theCT())


*)

end (* local open Feedback *)
end;
