(* ===================================================================== 
 * FILE          : Ho_Net.sml                                               
 * DESCRIPTION   : Implementation of term nets, from GTT.
 *                                                                       
 * AUTHOR        : Somebody in the ICL group.                            
 * DATE          : August 26, 1991                                       
 * MODIFIED      : Sept 5, 1992, to use deBruijn representation          
 *
 * MODIFIED	: Donald Syme, 1995, to add assumption-bound variables.
 *  
 * Assumption bound variables are for storing rewrites like
 *  [x=0] |- x = 0.
 * Since "x" is free in the assumptions, this rewrite should only match
 * terms which are exactly "x" on the left.  The old termnets chose this
 * rewrite to try to rewrite every term!!
 *
 * This only becomes really important when you have contextual rewriting.
 *
 * I'm sure all this code could be made faster.  The Isabelle term-nets
 * are no doubt much superior.  Also, this is compiled against the
 * public, not private Term structure.  The private might be faster.
 *
 * MODIFIED    : Donald Syme, November 1995, to be keyed up to higher order
 *               matching, based on JRH's code from GTT.  
 * ===================================================================== *)

structure Ho_Net :> Ho_Net =
struct


open HolKernel boolSyntax;

infix ##;

val ERR = mk_HOL_ERR "Ho_Net";

(*--------------------------------------------------------------------
 * Labels ascribed to head-operators of terms.
 *-------------------------------------------------------------------*)

datatype term_label 
   = Vnet 
   | FVnet of string * int 
   | Cnet of string * string * int
   | Lnet of int;            

fun remove p [] = raise ERR "remove" ""
  | remove p (h::t) = 
      if p(h) then (h,t) 
      else let val (y,n) = remove p t in (y,h::n) end;

fun stored_label (fvars,tm) =
  let val (oper,args) = strip_comb tm 
      val args' = map (fn x => (fvars,x)) args
  in case dest_term oper 
      of CONST {Name,Thy,...} => (Cnet(Name,Thy,length args),args')
       | LAMB {Body,Bvar} => (Lnet(length args),
                              (subtract fvars [Bvar],Body)::args')
       | VAR {Name,...} => 
          if mem oper fvars then (FVnet(Name,length args),args') else (Vnet,[])
       | _ => fail()
    end;

fun label_for_lookup tm =
  let val (oper,args) = strip_comb tm 
  in case dest_term oper 
      of CONST {Name,Thy,...} => (Cnet(Name,Thy,length args),args)
       | LAMB {Body,Bvar} => (Lnet(length args),Body::args)
       | VAR {Name,...} => (FVnet(Name,length args),args)
       | _ => fail()
  end;

datatype 'a net = NODE of (term_label * 'a net) list * 'a list

val empty_net = NODE ([],[]);

fun net_update (elem,tms,NODE(edges,tips)) =
   case tms 
    of [] => NODE(edges,elem::tips)
     | tm::rtms =>
        let val (label,ntms) = stored_label tm
            val (child,others) =
                  (snd ## I) (remove (fn (x,y) => x = label) edges)
                  handle HOL_ERR _ => (empty_net,edges)
            val new_child = net_update(elem,ntms @ rtms,child)
        in NODE ((label,new_child)::others,tips)
        end;

fun follow (tms,NODE(edges,tips)) =
   case tms 
    of [] => tips
     | tm::rtms =>
        let val (label,ntms) = label_for_lookup tm
            val collection =
              let val child = assoc label edges 
              in follow(ntms @ rtms, child)
              end handle HOL_ERR _ => []
        in
            (collection @ follow(rtms,assoc Vnet edges)
              handle HOL_ERR _ => collection)
        end;

fun enter (fvars,tm,elem) net = net_update(elem,[(fvars,tm)],net);

fun lookup tm net = follow([tm],net);

fun merge_nets (NODE (l1,thms1),NODE (l2,thms2)) =
    let fun add_node (p as (lab,net)) l =
	let val ((lab',net'),rest) = remove (fn (x,y) => x = lab) l
	in (lab',merge_nets (net,net'))::rest
	end
        handle HOL_ERR _ => p::l
    in NODE (itlist add_node l2 (itlist add_node l1 []),thms1@thms2)
    end;

end (* struct *)
