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


fun appconv (c,th,UNBOUNDED) tm     = c tm
  | appconv (c,th,BOUNDED(ref 0)) _ = failwith "exceeded rewrite bound"
  | appconv (c,th,BOUNDED r) tm     = c tm before Portable.dec r;

fun dest_tagged_rewrite thm = let
  val (th, n) = DEST_BOUNDED thm
in
  (BOUNDED (ref n), th)
end handle HOL_ERR _ => (UNBOUNDED, thm)

fun mk_rewr_convdata thm =
 let val (tag,thm') = dest_tagged_rewrite thm
     val th = SPEC_ALL thm'
 in
   SOME {name   = "<rewrite>",
         key   = SOME (free_varsl (hyp th), lhs(#2 (strip_imp(concl th)))),
         trace = 100, (* no need to provide extra tracing here;
                         COND_REWR_CONV provides enough tracing itself *)
         conv  = appconv (COND_REWR_CONV th, th, tag)} before
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
   {convs  : convdata list,
    rewrs  : thm list,
    ac     : (thm * thm) list,
    filter : (thm -> thm list) option,
    dprocs : Traverse.reducer list,
    congs  : thm list};

(*---------------------------------------------------------------------------*)
(* Operation on ssdata values                                                *)
(*---------------------------------------------------------------------------*)

fun rewrites rewrs =
   SSFRAG {convs=[],rewrs=rewrs,filter=NONE,ac=[],dprocs=[],congs=[]};

fun dproc_ss dproc =
   SSFRAG {convs=[],rewrs=[],filter=NONE,ac=[],dprocs=[dproc],congs=[]};

fun ac_ss aclist =
   SSFRAG {convs=[],rewrs=[],filter=NONE,ac=aclist,dprocs=[],congs=[]};

fun conv_ss conv =
   SSFRAG {convs=[conv],rewrs=[],filter=NONE,ac=[],dprocs=[],congs=[]};

fun D (SSFRAG s) = s;

fun merge_ss (s:ssfrag list) =
    SSFRAG {convs=flatten (map (#convs o D) s),
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
            initial_net : net,
            dprocs      : reducer list,
            travrules   : travrules}
with

 val empty_ss = SS {mk_rewrs=fn x => [x],
                    initial_net=empty_net,
                    dprocs=[],travrules=mk_travrules []};

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


 fun add_to_ss
    (SSFRAG {convs,rewrs,filter,ac,dprocs,congs},
     SS {mk_rewrs=mk_rewrs',travrules,initial_net,dprocs=dprocs'})
  = let val mk_rewrs = case filter of SOME f => f oo mk_rewrs' | _ => mk_rewrs'
        val rewrs' = flatten (map mk_rewrs (ac_rewrites ac@rewrs))
        val newconvdata = convs @ List.mapPartial mk_rewr_convdata rewrs'
        val net = net_add_convs initial_net newconvdata
    in
       SS {mk_rewrs=mk_rewrs,
	initial_net=net,
             dprocs=dprocs @ dprocs',
          travrules=merge_travrules [travrules,mk_travrules congs]}
    end;

 val mk_simpset = foldl add_to_ss empty_ss;

(*---------------------------------------------------------------------------*)
(* SIMP_QCONV : simpset -> thm list -> conv                                  *)
(*---------------------------------------------------------------------------*)

  fun op ++ (ss,ssdata) = add_to_ss (ssdata,ss);

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
    in REDUCER {addcontext=addcontext, apply=apply,
                initial=CONVNET initial_net}
    end;

  fun traversedata_for_ss (ss as (SS ssdata)) =
      {rewriters=[rewriter_for_ss ss],
       dprocs= #dprocs ssdata,
       relation= boolSyntax.equality,
       travrules= merge_travrules [EQ_tr,#travrules ssdata]};

  fun SIMP_QCONV ss =
      TRAVERSE (traversedata_for_ss ss);

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
     else ((ss ++ SSFRAG{ac=map unAC ACs, congs=map unCong Congs,
                        convs=[],rewrs=[],filter=NONE,dprocs=[]}), rst')
    end
in
fun SIMP_CONV ss l =
  let val (ss', l') = process_tags ss l
  in TRY_CONV (SIMP_QCONV ss' l') 
  end;

fun SIMP_PROVE ss l =
  let val (ss', l') = process_tags ss l
  in EQT_ELIM o SIMP_QCONV ss' l'
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

fun SIMP_RULE ss l = CONV_RULE (SIMP_CONV ss l);
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

(* ----------------------------------------------------------------------
    creating per-type ssdata values
   ---------------------------------------------------------------------- *)

fun type_ssfrag ty = let
  val {rewrs, convs} = TypeBase.simpls_of ty
in
  SSFRAG {convs = convs, rewrs = rewrs, filter = NONE,
           dprocs = [], ac = [], congs = []}
end


(* ---------------------------------------------------------------------
 * Pretty printer for Simpsets
 * ---------------------------------------------------------------------*)

(*
 open PP

 fun pp_simpset pp_thm_flags ppstrm (SS ssdata) =
    let val {add_string,add_break,begin_block,end_block,add_newline,...} =
               PPExtra.with_ppstream ppstrm
        val how_many_rewrs = length (#rewrs ssdata)
        val how_many_convs = length (#convdata ssdata)
        val how_many_dprocs = length (#dprocs ssdata)
    in begin_block PP.CONSISTENT 0;
       add_string("Number of rewrite rules = "^
		  int_to_string how_many_rewrs^" (use dest_ss to see them)");
       add_newline();
       add_string("Conversions:");
       add_newline();
       if (how_many_convs = 0)
       then (add_string "<no conversions>")
       else ( begin_block PP.INCONSISTENT 0;
              PPExtra.pr_list (fn x => add_string (#name x))
                      (fn () => add_string",")
                      (fn () => add_break(1,0))
                      (#convdata ssdata);
              end_block());
       add_newline();
       add_string("Number of conversions = "^int_to_string how_many_convs);
       add_newline();
       pp_travrules pp_thm_flags ppstrm (#travrules ssdata);

       add_string("Decision Procedures: ");
       if (how_many_dprocs = 0)
       then (add_string "<none>")
       else ( begin_block PP.INCONSISTENT 0;
              PPExtra.pr_list (fn REDUCER dproc => add_string (quote (#name
						      dproc)))
                      (fn () => add_string",")
                      (fn () => add_break(1,0)) (#dprocs ssdata);
              end_block());
       add_newline();

       end_block()
     end;
*)

end (* struct *)
