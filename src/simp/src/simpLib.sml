(* =====================================================================
 * FILE          : simpLib.sml
 * DESCRIPTION   : A programmable, contextual, conditional simplifier for hol90
 *
 * AUTHOR        : Donald Syme
 *                 Based loosely on original HOL rewriting by
 *                 Larry Paulson et al,
 *                 and not-so-loosely on the Isabelle simplifier.
 * ===================================================================== *)

structure simpLib :> simpLib =
struct

type term = Term.term
type thm = Thm.thm;
type conv = Abbrev.conv;
type tactic = Abbrev.tactic;

open HolKernel boolLib liteLib Trace Cond_rewr Travrules Traverse Ho_Net;

infix |>;
infix THEN

fun ERR x      = STRUCT_ERR "simpLib" x ;
fun WRAP_ERR x = STRUCT_WRAP "simpLib" x;

   (* ---------------------------------------------------------------------
    * simpsets and basic operations on them
    *
    * Simpsets contain enough information to spark off term traversal
    * quickly and efficiently.  In theory the net need not be stored
    * (and the code would look neater if it wasn't), but in practice
    * it has to be.
    * ---------------------------------------------------------------------*)


   type convdata = {name: string,
                    key: (term list * term) option,
                    trace: int,
                    conv: (term list -> term -> thm) -> term list -> conv};

  datatype ssdata = SIMPSET of
    {convs: convdata list,
     rewrs: thm list,
     ac: (thm * thm) list,
     filter: (thm -> thm list) option,
     dprocs: Traverse.reducer list,
     congs: thm list};

   val equality = boolSyntax.equality

   (* ---------------------------------------------------------------------
    * net_add_convs (internal function)
    *
    * Add conversions to the initial context net.
    *
    * USER_CONV wraps a bit of tracing around a user conversion.
    * ---------------------------------------------------------------------*)

   type net = ((term list -> term -> thm) -> term list -> conv) net;
   abstype simpset =
     SS of {mk_rewrs: (thm -> thm list),
            initial_net : net,
            dprocs: reducer list,
            travrules: travrules} with

   fun USER_CONV {name,key,trace=trace_level,conv} =
   let val trace_string1 = "trying "^name^" on"
       val trace_string2 = name^" ineffectual"
   in fn solver => fn stack => fn tm =>
	   let val _ = trace(trace_level+2,REDUCE(trace_string1,tm))
               val thm = conv solver stack tm
	   in
              trace(trace_level,PRODUCE(tm,name,thm));
              thm
	   end
           handle e as HOL_ERR _
           => (trace (trace_level+2,TEXT trace_string2); raise e)
   end;

   val any = (--`x:'a`--);
   fun option_cases f e (SOME x) = f x
     | option_cases f e NONE = e;

   fun net_add_conv (data as {name,key,trace,conv}:convdata) =
         enter (option_cases #1 [] key,
		option_cases #2 any key,
		USER_CONV data);

   fun net_add_convs net convs =
       itlist net_add_conv convs net;

   fun mk_rewr_convdata th =
        {name="<rewrite>",
         key=SOME (free_varsl (hyp th), lhs(#2 (strip_imp(concl th)))),
         trace=3,
         conv=COND_REWR_CONV th};

   (* ---------------------------------------------------------------------
    * mk_simpset
    * ---------------------------------------------------------------------*)

   infix oo;
   fun f oo g = fn x => flatten (map f (g x));

fun PROVE_LCOMM (assoc,sym) =
  let val a' = SPEC_ALL assoc
       val s' = SPEC_ALL sym
      val thm1 = CONV_RULE (RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV s')))) a'
   in CONV_RULE (RAND_CONV(REWR_CONV (GSYM a'))) thm1
  end;


val empty_ss = SS {mk_rewrs=fn x => [x],
		   initial_net=empty_net,
		   dprocs=[],travrules=mk_travrules []};
fun add_to_ss
    (SIMPSET {convs,rewrs,filter,ac,dprocs,congs},
     SS {mk_rewrs=mk_rewrs',travrules,initial_net,dprocs=dprocs'}) =
    let val mk_rewrs =
	case filter of
            SOME f => f oo mk_rewrs' | NONE => mk_rewrs'
	val rewrs' =
            map (fn (assoc,sym) => GSYM assoc) ac @
	    map (fn (assoc,sym) => sym) ac @
	    map (fn (assoc,sym) => PROVE_LCOMM (assoc,sym)) ac @
	    flatten (map mk_rewrs rewrs)
	val newconvdata = convs @ map mk_rewr_convdata rewrs'
	val net = net_add_convs initial_net newconvdata
    in SS {mk_rewrs=mk_rewrs,
	initial_net = net,
	dprocs= dprocs @ dprocs',
	travrules = merge_travrules [travrules,mk_travrules congs]}
    end;

val mk_simpset = foldl add_to_ss empty_ss;


fun rewrites rewrs =
  SIMPSET {convs=[],rewrs=rewrs,filter=NONE,ac=[],dprocs=[],congs=[]};
fun dproc_ss dproc =
  SIMPSET {convs=[],rewrs=[],filter=NONE,ac=[],dprocs=[dproc],congs=[]};
fun D (SIMPSET s) = s;
fun merge_ss s =
  SIMPSET {convs=flatten (map (#convs o D) s),
	   rewrs=flatten (map (#rewrs o D) s),
	   filter=SOME (end_foldr (op oo) (mapfilter (the o #filter o D) s))
                  handle HOL_ERR _ => NONE,
	   ac=flatten (map (#ac o D) s),
	   dprocs=flatten (map (#dprocs o D) s),
	   congs=flatten (map (#congs o D) s)};

   (* ---------------------------------------------------------------------
    * SIMP_CONV : simpset -> thm list -> conv
    * ---------------------------------------------------------------------*)

fun op ++ (ss,ssdata) = add_to_ss (ssdata,ss);

   exception CONVNET of net;
   fun rewriter_for_ss (ss as SS{mk_rewrs,travrules,initial_net,...}) =
      let fun addcontext (context,thms) =
	  let val net = (raise context) handle CONVNET net => net
          in CONVNET (net_add_convs net (map mk_rewr_convdata
					 (flatten (map mk_rewrs thms))))
	  end;
          fun apply {solver,context,stack} tm =
	      let val net = (raise context) handle CONVNET net => net
	      in tryfind (fn conv => conv solver stack tm) (lookup tm net)
	      end
      in REDUCER {addcontext=addcontext,
		  initial=CONVNET initial_net,
		  apply=apply}
      end;

   fun SIMP_QCONV (ss as (SS ssdata)) =
      TRAVERSE {rewriters= [rewriter_for_ss ss],
		dprocs= #dprocs ssdata,
		relation= equality,
		travrules= merge_travrules [EQ_tr,#travrules ssdata]};

 end (* abstype for SS *)

   fun SIMP_CONV ss l = TRY_CONV (SIMP_QCONV ss l);
   fun SIMP_PROVE ss l = EQT_ELIM o SIMP_QCONV ss l;

   (* ---------------------------------------------------------------------
    * SIMP_TAC : simpset -> tactic
    * ASM_SIMP_TAC : simpset -> tactic
    * FULL_SIMP_TAC : simpset -> tactic
    *
    * FAILURE CONDITIONS
    *
    * These tactics never fail, though they may diverge.
    * ---------------------------------------------------------------------*)

   fun SIMP_TAC ss l = CONV_TAC (SIMP_CONV ss l);
   fun ASM_SIMP_TAC ss l (asms,gl) = SIMP_TAC ss (l@map ASSUME asms) (asms,gl);

   fun SIMP_RULE ss l = CONV_RULE (SIMP_CONV ss l);
   fun ASM_SIMP_RULE ss l th = SIMP_RULE ss (l@map ASSUME (hyp th)) th;


   fun FULL_SIMP_TAC ss l =
       let fun drop n (asms,g) =
	   let val l = length asms
	       fun f asms =
		   MAP_EVERY ASSUME_TAC (rev (fst (split_after (l-n) asms)))
	   in if (n > l) then ERR ("drop", "Bad cut off number")
	      else POP_ASSUM_LIST f (asms,g)
	   end

           (* differs only in that it doesn't call DISCARD_TAC *)
           val STRIP_ASSUME_TAC' =
	       (REPEAT_TCL STRIP_THM_THEN)
	       (fn th => FIRST [CONTR_TAC th, ACCEPT_TAC th, ASSUME_TAC th])
	   fun simp_asm (t,l') = SIMP_RULE ss (l'@l) t::l'
	   fun f asms =
	       MAP_EVERY STRIP_ASSUME_TAC' (foldl simp_asm [] asms)
	       THEN drop (length asms)
       in ASSUM_LIST f THEN ASM_SIMP_TAC ss l
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
