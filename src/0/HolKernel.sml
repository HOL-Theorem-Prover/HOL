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
in

 (*---------------------------------------------------------------------------
       Type antiquotations (required in term parser)
  ---------------------------------------------------------------------------*)

fun ty_antiq ty = mk_var{Name="ty_antiq",Ty=ty}

fun dest_ty_antiq tm = 
     case (dest_var tm handle HOL_ERR _ 
            => raise ERR "dest_ty_antiq" "not a type antiquotation")
      of {Name="ty_antiq",Ty} => Ty
       |  _ => raise ERR "dest_ty_antiq" "not a type antiquotation";

val is_ty_antiq = Lib.can dest_ty_antiq


(*---------------------------------------------------------------------------
          General destructor operations
 ---------------------------------------------------------------------------*)

local fun dest M =
       let val {Rator,Rand} = dest_comb M in (dest_thy_const Rator,Rand) end
in
fun dest_monop (name,thy) e M =
 let val ({Name,Thy,...},Rand) = dest M handle HOL_ERR _ => raise e
 in if Name=name andalso Thy=thy then Rand else raise e
 end;
end

local fun dest tm = 
       let val {Rator,Rand=N} = dest_comb tm
           val {Rator=c,Rand=M} = dest_comb Rator
       in (dest_thy_const c,(c,M,N))
       end
in
fun dest_binop (name,thy) e tm =
   let val ({Name,Thy,...},triple) = dest tm handle HOL_ERR _ => raise e
   in if Name=name andalso Thy=thy then triple else raise e
   end
end;

fun mk_binder c f (p as {Bvar,...}) =
   mk_comb{Rator=inst[alpha |-> type_of Bvar] c, Rand=mk_abs p}
   handle HOL_ERR {message,...} => raise ERR f message;


local fun dest M = 
       let val {Rator=c, Rand} = dest_comb M
       in (dest_thy_const c,dest_abs Rand)
       end
in
fun dest_binder (name,thy) e M =
  let val ({Name,Thy,...}, r) = dest M handle HOL_ERR _ => raise e
  in if Name=name andalso Thy=thy then r else raise e
  end
end;

fun strip_binder dest =
  let fun strip A M =
       case dest M
        of NONE => (List.rev A, M)
         | SOME{Bvar,Body} => strip (Bvar::A) Body
  in strip []
  end


datatype lambda 
   = VAR   of {Name  : string, Ty : hol_type}
   | CONST of {Name  : string, Thy : string, Ty : hol_type}
   | COMB  of {Rator : term, Rand : term}
   | LAMB  of {Bvar  : term, Body : term};

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
      if is_abs tm then find_tm (#Body(dest_abs tm)) else 
      if is_comb tm 
         then find_tm (#Rator(dest_comb tm)) handle HOL_ERR _ => 
              find_tm (#Rand(dest_comb tm))
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
      in if is_abs tm then accum tl' (#Body(dest_abs tm)) else 
         if is_comb tm 
            then accum (accum tl' (#Rator(dest_comb tm)))
                       (#Rand(dest_comb tm))
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
               then let val {Rator, Rand} = dest_comb tm
                        val {tm=Rator', occs=occs', count=count'} =
                                        graft {tm=Rator,occs=occs,count=count}
                        val {tm=Rand', occs=occs'', count=count''} =
                                        graft {tm=Rand,occs=occs',count=count'}
                    in {tm=mk_comb{Rator=Rator', Rand=Rand'},
                        occs=occs'', count=count''}
                    end
               else if is_abs tm
                    then let val {Bvar,Body} = dest_abs tm
                             val {tm, count, occs} =
                                        graft{tm=Body,count=count,occs=occs}
                         in {tm=mk_abs{Bvar=Bvar, Body=tm},
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
       Higher order matching (from jrh via Don Syme)
 ---------------------------------------------------------------------------*)

local val list_mk_fun = itlist (curry (op -->))
      fun acc_strip_comb M rands =
        let val {Rator,Rand} = dest_comb M 
        in acc_strip_comb Rator (Rand::rands) 
        end handle HOL_ERR _ => (M,rands)
      val list_mk_abs = itlist(fn v=>fn b=>mk_abs{Bvar=v, Body=b})
      exception NOT_FOUND
      fun rev_assoc_nf x l = 
        Lib.rev_assoc x l handle HOL_ERR _ => raise NOT_FOUND
      fun safe_insert (n as (y,x)) l =
        let val z = rev_assoc_nf x l
        in if y = z then l else failwith "match: safe_insert"
        end handle NOT_FOUND => n::l  (* binding not there *)
      fun safe_inserta (n as (y,x)) l =
        let val z = rev_assoc_nf x l
        in if aconv y z then l else failwith "match: safe_inserta"
        end handle NOT_FOUND => n::l
      val mk_dummy =
        let val name = #Name(dest_var(genvar Type.alpha))
        in fn tm => mk_var{Name=name, Ty=type_of tm}
        end
in
fun ho_match_term lconsts = 
 let fun match_term' env vtm ctm sofar =
   case dest_term vtm
    of VAR _ => 
       (let val ctm' = rev_assoc_nf vtm env
        in if ctm' = ctm then sofar else failwith "match: match_term"
        end handle NOT_FOUND  (* vtm is a free var *)
        => if mem vtm lconsts 
           then if ctm=vtm then sofar
                else failwith "match_term': can't instantiate local constant"
           else 
           if exists (can (C assoc env)) (free_vars ctm)
           then failwith"match: free vars don't match terms with bound vars"
           else if vtm=ctm then sofar else safe_inserta (ctm,vtm) sofar
       )
     | CONST{Name,Thy,...} => 
           let val {Name=name,Thy=thy,...} = dest_thy_const ctm
                   handle HOL_ERR _ => failwith "match: match_term" 
           in if Name=name andalso Thy=thy
              then safe_inserta (mk_dummy ctm,mk_dummy vtm) sofar
              else failwith "match: match_term" 
           end 
     | LAMB {Bvar=vv,Body=vbod} =>
           let val {Bvar=cv,Body=cbod} = dest_abs ctm
               val sofar' = safe_inserta (mk_dummy cv,mk_dummy vv) sofar
           in match_term' (insert (cv,vv) env) vbod cbod sofar' 
           end
     | COMB _ =>
        let val (vhop,vargs) = acc_strip_comb vtm []
            val (chop,cargs) = acc_strip_comb ctm []
        in (if not (is_var vhop) 
                orelse mem vhop lconsts 
                orelse can (C rev_assoc env) vhop
            then fail()
            else let val vargs' = map (C rev_assoc env) vargs
                 in if vargs' = cargs 
                    then safe_inserta (chop,vhop) sofar
                    else safe_inserta (list_mk_abs vargs' ctm, vhop) sofar
                 end
           ) handle HOL_ERR _ 
             => itlist2 (match_term' env) vargs cargs 
                        (match_term' env vhop chop sofar)
                handle HOL_ERR{message="lists of different length",...}
                 => let val {Rator=lv,Rand=rv} = dest_comb vtm
                        val {Rator=lc,Rand=rc} = dest_comb ctm
                    in match_term' env rv rc (match_term' env lv lc sofar)
                    end
        end
 in 
 fn vtm => fn ctm =>
   let val rawins = match_term' [] vtm ctm []
       val (cins,vins) = unzip rawins
       val tytheta = match_type(list_mk_fun (map type_of vins) bool)
                               (list_mk_fun (map type_of cins) bool)
       val tmtheta0 = map2 (fn x => fn y => (x |-> y)) vins cins 
   in (norm_subst tytheta tmtheta0, tytheta)
   end 
 end
 handle e => raise (wrap_exn "HolKernel" "ho_match_term" e)
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
