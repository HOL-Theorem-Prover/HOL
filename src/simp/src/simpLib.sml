(*===========================================================================*)
(* FILE          : simpLib.sml                                               *)
(* DESCRIPTION   : A programmable, contextual, conditional simplifier        *)
(*                                                                           *)
(* AUTHOR        : Donald Syme                                               *)
(*                 Based loosely on original HOL rewriting by                *)
(*                 Larry Paulson et al,                                      *)
(*                 and not-so-loosely on the Isabelle simplifier.            *)
(*===========================================================================*)

structure simpLib :> simpLib =
struct

infix |> oo;

open HolKernel boolLib liteLib Trace Cond_rewr Travrules Traverse Ho_Net;

local open markerTheory in end;

fun ERR x      = STRUCT_ERR "simpLib" x ;
fun WRAP_ERR x = STRUCT_WRAP "simpLib" x;

fun option_cases f e (SOME x) = f x
  | option_cases f e NONE = e;

fun f oo g = fn x => flatten (map f (g x));

(*---------------------------------------------------------------------------*)
(* Representation of conversions manipulated by the simplifier.              *)
(*---------------------------------------------------------------------------*)

type convdata = {name  : string,
                 key   : (term list * term) option,
                 trace : int,
                 conv  : (term list -> term -> thm) -> term list -> conv};

(*---------------------------------------------------------------------------*)
(* Make a rewrite rule into a conversion.                                    *)
(*---------------------------------------------------------------------------*)

datatype control = UNBOUNDED | BOUNDED of int ref

(* boolean argument to c is whether or not the rewrite is bounded *)
fun appconv (c,UNBOUNDED) tm     = c false tm
  | appconv (c,BOUNDED(ref 0)) _ = failwith "exceeded rewrite bound"
  | appconv (c,BOUNDED r) tm     = c true tm before Portable.dec r;

fun dest_tagged_rewrite thm = let
  val (th, n) = DEST_BOUNDED thm
in
  (BOUNDED (ref n), th)
end handle HOL_ERR _ => (UNBOUNDED, thm)

fun mk_rewr_convdata thm =
 let val (tag,thm') = dest_tagged_rewrite thm
     val th = SPEC_ALL thm'
 in
   SOME {name  = "<rewrite>",
         key   = SOME (free_varsl (hyp th), lhs(#2 (strip_imp(concl th)))),
         trace = 100, (* no need to provide extra tracing here;
                         COND_REWR_CONV provides enough tracing itself *)
         conv  = appconv (COND_REWR_CONV th, tag)} before
   trace(2, LZ_TEXT(fn () => "New rewrite: " ^ thm_to_string th))
   handle HOL_ERR _ =>
          (trace (2, LZ_TEXT(fn () =>
                                thm_to_string th ^
                                " dropped (conversion to rewrite failed)"));
           NONE)
 end

(*---------------------------------------------------------------------------*)
(* Composable simpset fragments                                              *)
(*---------------------------------------------------------------------------*)

datatype ssfrag = SSFRAG of
   {name   : string option,
    convs  : convdata list,
    rewrs  : thm list,
    ac     : (thm * thm) list,
    filter : (thm -> thm list) option,
    dprocs : Traverse.reducer list,
    congs  : thm list};

(*---------------------------------------------------------------------------*)
(* Operation on ssdata values                                                *)
(*---------------------------------------------------------------------------*)

fun named_rewrites s rewrs =
   SSFRAG {name=SOME s,
           convs=[],rewrs=rewrs,filter=NONE,ac=[],dprocs=[],congs=[]};

fun rewrites rewrs =
   SSFRAG {name=NONE,
           convs=[],rewrs=rewrs,filter=NONE,ac=[],dprocs=[],congs=[]};

fun dproc_ss dproc =
   SSFRAG {name=NONE,
           convs=[],rewrs=[],filter=NONE,ac=[],dprocs=[dproc],congs=[]};

fun ac_ss aclist =
   SSFRAG {name=NONE,
           convs=[],rewrs=[],filter=NONE,ac=aclist,dprocs=[],congs=[]};

fun conv_ss conv =
   SSFRAG {name=NONE,
           convs=[conv],rewrs=[],filter=NONE,ac=[],dprocs=[],congs=[]};

fun D (SSFRAG s) = s;

fun merge_names list =
  itlist (fn (SOME x) =>
              (fn NONE => SOME x
                | SOME y => SOME (x^", "^y))
           | NONE =>
              (fn NONE => NONE
                | SOME y => SOME y))
         list NONE;

(*---------------------------------------------------------------------------*)
(* Possibly need to suppress duplicates in the merge?                        *)
(*---------------------------------------------------------------------------*)

fun merge_ss (s:ssfrag list) =
    SSFRAG {name=merge_names (map (#name o D) s),
            convs=flatten (map (#convs o D) s),
             rewrs=flatten (map (#rewrs o D) s),
            filter=SOME (end_foldr (op oo) (mapfilter (the o #filter o D) s))
                    handle HOL_ERR _ => NONE,
                ac=flatten (map (#ac o D) s),
	    dprocs=flatten (map (#dprocs o D) s),
	     congs=flatten (map (#congs o D) s)};


(*---------------------------------------------------------------------------*)
(* Simpsets and basic operations on them. Simpsets contain enough            *)
(* information to spark off term traversal quickly and efficiently. In       *)
(* theory the net need not be stored (and the code would look neater if it   *)
(* wasn't), but in practice it has to be.                                    *)
(* --------------------------------------------------------------------------*)

type net = ((term list -> term -> thm) -> term list -> conv) net;

abstype simpset =
     SS of {mk_rewrs    : (thm -> thm list),
            ssfrags     : ssfrag list,
            initial_net : net,
            dprocs      : reducer list,
            travrules   : travrules,
            limit       : int option}
with

 val empty_ss = SS {mk_rewrs=fn x => [x],
                    ssfrags = [], limit = NONE,
                    initial_net=empty_net,
                    dprocs=[],travrules=EQ_tr};

 fun ssfrags_of (SS x) = #ssfrags x;

  (* ---------------------------------------------------------------------
   * USER_CONV wraps a bit of tracing around a user conversion.
   *
   * net_add_convs (internal function) adds conversions to the
   * initial context net.
   * ---------------------------------------------------------------------*)

 fun USER_CONV {name,key,trace=trace_level,conv} =
  let val trace_string1 = "trying "^name^" on"
      val trace_string2 = name^" ineffectual"
      val trace_string3 = name^" left term unchanged"
      val trace_string4 = name^" raised an unusual exception (ignored)"
  in fn solver => fn stack => fn tm =>
      let val _ = trace(trace_level+2,REDUCE(trace_string1,tm))
          val thm = conv solver stack tm
      in
        trace(trace_level,PRODUCE(tm,name,thm));
        thm
      end
      handle e as HOL_ERR _ =>
             (trace (trace_level+2,TEXT trace_string2); raise e)
           | e as Conv.UNCHANGED =>
             (trace (trace_level+2,TEXT trace_string3); raise e)
           | e => (trace (trace_level, TEXT trace_string4); raise e)
  end;

 val any = mk_var("x",Type.alpha);

 fun net_add_conv (data as {name,key,trace,conv}:convdata) =
     enter (option_cases #1 [] key,
            option_cases #2 any key,
            USER_CONV data);

(* itlist is like foldr, so that theorems get added to the context starting
   from the end of the list *)
 fun net_add_convs net convs = itlist net_add_conv convs net;


 (* ---------------------------------------------------------------------
  * mk_simpset
  * ---------------------------------------------------------------------*)

 fun mk_ac p A =
   let val (a,b,c) = Drule.MK_AC_LCOMM p
   in a::b::c::A
   end handle HOL_ERR _ => A;

 fun ac_rewrites aclist = Lib.itlist mk_ac aclist [];

 fun same_frag (SSFRAG{name=SOME n1, ...}) (SSFRAG{name=SOME n2, ...}) = n1=n2
   | same_frag other wise = false;

 fun add_to_ss
    (f as SSFRAG {convs,rewrs,filter,ac,dprocs,congs,...},
     SS {mk_rewrs=mk_rewrs',ssfrags,travrules,initial_net,dprocs=dprocs',
         limit})
  = let val mk_rewrs = case filter of SOME f => f oo mk_rewrs' | _ => mk_rewrs'
        val rewrs' = flatten (map mk_rewrs (ac_rewrites ac@rewrs))
        val newconvdata = convs @ List.mapPartial mk_rewr_convdata rewrs'
        val net = net_add_convs initial_net newconvdata
        val TRAVRULES{relations,...} = travrules
    in
       SS {mk_rewrs=mk_rewrs,
           ssfrags = Lib.op_insert same_frag f ssfrags,
           initial_net=net, limit = limit,
           dprocs=dprocs @ dprocs',
           travrules=merge_travrules [travrules,mk_travrules relations congs]}
    end;

 val mk_simpset = foldl add_to_ss empty_ss;

 fun op ++ (ss,ssdata) = add_to_ss (ssdata,ss)

 fun limit n (SS {mk_rewrs,ssfrags,travrules,initial_net,dprocs,limit}) =
     SS {mk_rewrs = mk_rewrs, ssfrags = ssfrags, travrules = travrules,
         initial_net = initial_net, dprocs = dprocs, limit = SOME n}

 fun unlimit (SS {mk_rewrs,ssfrags,travrules,initial_net,dprocs,limit}) =
     SS {mk_rewrs = mk_rewrs, ssfrags = ssfrags, travrules = travrules,
         initial_net = initial_net, dprocs = dprocs, limit = NONE}

 fun wk_mk_travrules (rels, congs) = let
   fun cong2proc th = let
     open Opening Travrules
     fun mk_refl rel t = let
       val PREORDER(_,_,refl) = find_relation rel rels
     in
       refl t
     end
   in
     CONGPROC mk_refl th
   end
 in
   TRAVRULES {relations = rels,
              congprocs = [],
              weakenprocs = map cong2proc congs}
 end

 fun add_weakener (rels,congs,dp) simpset = let
   val SS {mk_rewrs,ssfrags,travrules,initial_net,dprocs,limit} = simpset
 in
   SS {mk_rewrs = mk_rewrs, ssfrags = ssfrags,
       travrules = merge_travrules [travrules, wk_mk_travrules(rels,congs)],
       initial_net = initial_net, dprocs = dprocs, limit = limit} ++
   SSFRAG{convs = [], rewrs = [], filter = NONE, ac = [], dprocs = [dp],
          congs = [], name = NONE}
end

(* ----------------------------------------------------------------------
    add_relsimp : {trans,refl,weakenings,subsets} -> simpset -> simpset

    trans and refl are the transitivity and reflexivity theorems for the
    relation.  weakenings are theorems for turning (at least) equality goals
    into goals over the new relation.  subsets are theorems that help the
    munger: they say that certain forms imply rules for the relation.  For
    example, if using RTC R as the relation, then RTC_R, which states
      !x y. R x y ==> RTC R x y
    is a good subset theorem
   ---------------------------------------------------------------------- *)

fun dest_binop t = let
  val (fx,y) = dest_comb t
  val (f,x) = dest_comb fx
in
  (f,x,y)
end
datatype munge_action = TH of thm | POP
fun munge base subsets asms (thlistlist, n) = let
  val munge = munge base subsets
in
  case thlistlist of
    [] => n
  | [] :: rest => munge asms (rest, n)
  | (TH th :: ths) :: rest => let
    in
      case CONJUNCTS (SPEC_ALL th) of
        [] => raise Fail "munge: Can't happen"
      | [th] => let
          open Net
        in
          if is_imp (concl th) then
            munge (#1 (dest_imp (concl th)) :: asms)
                  ((TH (UNDISCH th)::POP::ths)::rest, n)
          else
            case total dest_binop (concl th) of
              SOME (R,from,to) => let
                fun foldthis (t,th) = DISCH t th
                fun insert (t,th0) n = let
                  val (bound,th) = dest_tagged_rewrite th0
                in
                  Net.insert (t, (bound, List.foldl foldthis th asms)) n
                end
              in
                if aconv R base then
                  munge asms (ths :: rest, insert (from,th) n)
                else
                  case List.find (fn (t,_) => aconv R t) subsets of
                    NONE => munge asms (ths :: rest, n)
                  | SOME (_, sub_th) =>
                    munge asms (ths :: rest, insert (from,MATCH_MP sub_th th) n)
              end
            | NONE => munge asms (ths :: rest, n)
        end
      | thlist => munge asms (map TH thlist :: ths :: rest, n)
    end
  | (POP :: ths) :: rest => munge (tl asms) (ths::rest, n)
end

fun po_rel (Travrules.PREORDER(r,_,_)) = r

fun mk_reducer rel_t subsets initial_rewrites = let
  exception redExn of (control * thm) Net.net
  fun munge_subset_th th = let
    val (_, impn) = strip_forall (concl th)
    val (a, _) = dest_imp impn
    val (f, _, _) = dest_binop a
  in
    (f, th)
  end
  val subsets = map munge_subset_th subsets
  fun addcontext (ctxt, thms) = let
    val n = case ctxt of redExn n => n
                       | _ => raise ERR ("mk_reducer.addcontext",
                                         "Wrong sort of ctxt")
    val n' = munge rel_t subsets [] ([map TH thms], n)
  in
    redExn n'
  end
  val initial_ctxt = addcontext (redExn Net.empty, initial_rewrites)
  fun applythm solver t (bound, th) = let
    fun dec() = case bound of
                  BOUNDED (r as ref n) =>
                    if n > 0 then r := n - 1
                    else raise ERR ("mk_reducer.applythm",
                                    "Bound exceeded on rwt.")
                | UNBOUNDED => ()
    val matched = PART_MATCH (lhand o #2 o strip_imp) th t
    open Trace
    fun do_sideconds th =
        if is_imp (concl th) then let
          val (h,c) = dest_imp (concl th)
          val _ = trace(3,SIDECOND_ATTEMPT h)
          val scond = solver h
          val _ = trace(2,SIDECOND_SOLVED scond)
        in
          do_sideconds (MP th scond)
        end
      else (dec(); trace(2,REWRITING(t,th)); th)
  in
    do_sideconds matched
  end

  fun apply {solver,context,stack,relation} t = let
    val _ = aconv (po_rel relation) rel_t orelse
            raise ERR ("mk_reducer.apply", "Wrong relation")
    val n = case context of redExn n => n
                          | _ => raise ERR ("apply", "Wrong sort of ctxt")
    val matches = Net.match t n
  in
    tryfind (applythm (solver stack) t) matches
  end
in
  Traverse.REDUCER {name = SOME ("reducer for "^term_to_string rel_t),
                    addcontext = addcontext,
                    apply = apply,
                    initial = initial_ctxt}
end

val equality_po = let
  open Travrules
  val TRAVRULES {relations,...} = EQ_tr
in
  hd relations
end

fun add_relsimp {refl,trans,weakenings,subsets,rewrs} ss = let
  val rel_t = #1 (dest_binop (#2 (strip_forall (concl refl))))
  val rel_po = Travrules.mk_preorder (trans,refl)
  val reducer = mk_reducer rel_t subsets rewrs
in
  add_weakener ([rel_po, equality_po], weakenings, reducer) ss
end

(*---------------------------------------------------------------------------*)
(* SIMP_QCONV : simpset -> thm list -> conv                                  *)
(*---------------------------------------------------------------------------*)

 exception CONVNET of net;

 fun rewriter_for_ss (SS{mk_rewrs,travrules,initial_net,...}) =
   let fun addcontext (context,thms) =
        let val net = (raise context) handle CONVNET net => net
        in CONVNET (net_add_convs net
                       (List.mapPartial mk_rewr_convdata
                         (flatten (map mk_rewrs thms))))
        end
       fun apply {solver,context,stack,relation} tm =
         let val net = (raise context) handle CONVNET net => net
         in tryfind (fn conv => conv solver stack tm) (lookup tm net)
         end
   in REDUCER {name=SOME"rewriter_for_ss",
               addcontext=addcontext, apply=apply,
               initial=CONVNET initial_net}
   end;

 fun traversedata_for_ss (ss as (SS ssdata)) =
      {rewriters=[rewriter_for_ss ss],
       dprocs= #dprocs ssdata,
       relation= boolSyntax.equality,
       travrules= #travrules ssdata,
       limit = #limit ssdata};

 fun SIMP_QCONV ss = TRAVERSE (traversedata_for_ss ss);

end (* abstype for SS *)

val Cong = markerLib.Cong
val AC   = markerLib.AC;

local open markerSyntax markerLib
  fun is_AC thm = same_const(fst(strip_comb(concl thm))) AC_tm
  fun is_Cong thm = same_const(fst(strip_comb(concl thm))) Cong_tm

  fun process_tags ss thl =
    let val (Congs,rst) = Lib.partition is_Cong thl
        val (ACs,rst') = Lib.partition is_AC rst
    in
     if null Congs andalso null ACs then (ss,thl)
     else ((ss ++ SSFRAG{name=SOME"Cong and/or AC",
                         ac=map unAC ACs, congs=map unCong Congs,
                         convs=[],rewrs=[],filter=NONE,dprocs=[]}), rst')
    end
in
fun SIMP_CONV ss l tm =
  let val (ss', l') = process_tags ss l
  in TRY_CONV (SIMP_QCONV ss' l') tm
  end;

fun SIMP_PROVE ss l t =
  let val (ss', l') = process_tags ss l
  in EQT_ELIM (SIMP_QCONV ss' l' t)
  end;

infix &&;

fun (ss && thl) =
  let val (ss',thl') = process_tags ss thl
  in ss' ++ rewrites thl'
  end;

end;

(*---------------------------------------------------------------------------*)
(*   SIMP_TAC      : simpset -> thm list -> tactic                           *)
(*   ASM_SIMP_TAC  : simpset -> thm list -> tactic                           *)
(*   FULL_SIMP_TAC : simpset -> thm list -> tactic                           *)
(*                                                                           *)
(* FAILURE CONDITIONS                                                        *)
(*                                                                           *)
(* These tactics never fail, though they may diverge.                        *)
(* --------------------------------------------------------------------------*)


fun SIMP_RULE ss l = CONV_RULE (SIMP_CONV ss l)

fun ASM_SIMP_RULE ss l th = SIMP_RULE ss (l@map ASSUME (hyp th)) th;

fun SIMP_TAC ss l = markerLib.ABBRS_THEN (CONV_TAC o SIMP_CONV ss) l;

fun ASM_SIMP_TAC ss =
   markerLib.ABBRS_THEN
    (fn thl => fn gl as (asl,_) =>
         SIMP_TAC ss (markerLib.LLABEL_RESOLVE thl asl) gl);


fun FULL_SIMP_TAC ss l =
 let fun drop n (asms,g) =
	let val l = length asms
	    fun f asms = MAP_EVERY ASSUME_TAC
                          (rev (fst (split_after (l-n) asms)))
        in
          if (n > l) then ERR ("drop", "Bad cut off number")
	  else POP_ASSUM_LIST f (asms,g)
	end

     (* differs only in that it doesn't call DISCARD_TAC *)
     val STRIP_ASSUME_TAC' =
           REPEAT_TCL STRIP_THM_THEN
            (fn th => FIRST [CONTR_TAC th, ACCEPT_TAC th, ASSUME_TAC th])
     fun simp_asm (t,l') = SIMP_RULE ss (l'@l) t::l'
     fun f asms = MAP_EVERY STRIP_ASSUME_TAC' (foldl simp_asm [] asms)
                  THEN drop (length asms)
 in
  markerLib.ABBRS_THEN (fn l => ASSUM_LIST f THEN ASM_SIMP_TAC ss l) l
 end

fun track f x =
 let val _ = (used_rewrites := [])
     val res = Lib.with_flag(track_rewrites,true) f x
 in used_rewrites := rev (!used_rewrites)
  ; res
 end;

(* ----------------------------------------------------------------------
    creating per-type ssdata values
   ---------------------------------------------------------------------- *)

fun type_ssfrag ty =
 let val {Thy,Tyop,...} = dest_thy_type ty
     val tyname = Thy^"$"^Tyop
     val {rewrs, convs} = TypeBase.simpls_of ty
in
  SSFRAG {name=SOME ("Datatype "^tyname),
          convs = convs, rewrs = rewrs, filter = NONE,
          dprocs = [], ac = [], congs = []}
end


(*---------------------------------------------------------------------------*)
(* Pretty printers for ssfrags and simpsets                                  *)
(*---------------------------------------------------------------------------*)

val CONSISTENT   = Portable.CONSISTENT
val INCONSISTENT = Portable.INCONSISTENT;

fun D (SSFRAG s) = s;
fun dest_reducer (Traverse.REDUCER x) = x;

fun merge_names list =
  itlist (fn (SOME x) =>
              (fn NONE => SOME x
                | SOME y => SOME (x^", "^y))
           | NONE =>
              (fn NONE => NONE
                | SOME y => SOME y))
         list NONE;

fun dest_convdata {name,key as SOME(_,tm),trace,conv} = (name,SOME tm)
  | dest_convdata {name,...} = (name,NONE);

fun pp_ssfrag ppstrm (SSFRAG {name,convs,rewrs,ac,dprocs,congs,...}) =
 let open Portable
     val name = (case name of SOME s => s | NONE => "<anonymous>")
     val convs = map dest_convdata convs
     val dps = case merge_names (map (#name o dest_reducer) dprocs)
                of NONE => []
                 | SOME n => [n]
     val {add_string,add_break,begin_block,end_block, add_newline,
          flush_ppstream,...} = Portable.with_ppstream ppstrm
     val pp_thm = pp_thm ppstrm
     val pp_term = Parse.term_pp_with_delimiters Hol_pp.pp_term ppstrm
     fun pp_thm_pair (th1,th2) =
        (begin_block CONSISTENT 0;
         pp_thm th1; add_break(2,0); pp_thm th2;
         end_block())
     fun pp_conv_info (n,SOME tm) =
          (begin_block CONSISTENT 0;
           add_string (n^", keyed on pattern"); add_break(2,0); pp_term tm;
           end_block())
       | pp_conv_info (n,NONE) = add_string n
     fun nl2() = (add_newline();add_newline());
     fun vspace l = if null l then () else nl2();
     fun vblock(header, ob_pr, obs) =
       if null obs then ()
       else
        ( begin_block CONSISTENT 3;
          add_string (header^":");
          add_newline();
          Portable.pr_list ob_pr
            (fn () => ()) add_newline obs;
          end_block();
          add_break(1,0))
 in
  begin_block CONSISTENT 0;
  add_string ("Simplification set: "^name);
  add_newline();
  vblock("Conversions",pp_conv_info,convs);
  vblock("Decision procedures",add_string,dps);
  vblock("Congruence rules",pp_thm,congs);
  vblock("AC rewrites",pp_thm_pair,ac);
  vblock("Rewrite rules",pp_thm,rewrs);
  end_block ()
 end

fun pp_simpset ppstrm ss =
  let open Portable
      val pp_ssfrag = pp_ssfrag ppstrm
 in pr_list pp_ssfrag (fn () => ()) (fn () => add_newline ppstrm)
            (rev (ssfrags_of ss))
 end;

end (* struct *)
