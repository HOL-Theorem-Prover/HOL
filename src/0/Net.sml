(* ===================================================================== *)
(* FILE          : net.sml                                               *)
(* DESCRIPTION   : Implementation of term nets, from the group at ICL.   *)
(*                 Thanks! A term net is a database, keyed by terms.     *)
(*                 Term nets were initially implemented by Larry Paulson *)
(*                 for Cambridge LCF.                                    *)
(*                                                                       *)
(* AUTHOR        : Somebody in the ICL group.                            *)
(* DATE          : August 26, 1991                                       *)
(* MODIFIED      : Sept 5, 1992, to use deBruijn representation          *)
(* Modified      : September 23, 1997, Ken Larsen                        *)
(* ===================================================================== *)

structure Net :> Net =
struct
open Lib


(*---------------------------------------------------------------------------
 * Tags for lambda term constructors.
 *---------------------------------------------------------------------------*)
datatype term_label = V | Cnst of string | Cmb | Lam;

(*---------------------------------------------------------------------------
 * Term nets.
 *---------------------------------------------------------------------------*)
datatype 'a net = TIP of 'a list
                | NODE of (term_label * 'a net) list;


fun NET_ERR function message = 
Exception.HOL_ERR{origin_structure = "Net",
                  origin_function = function,
                  message = message};

local val dummy = Term.mk_var{Name ="dummy",Ty = Type.mk_vartype"'x"}
      val break_abs_ref = ref (fn _:Term.term => {Bvar=dummy,Body=dummy})
in
  val _ = Term.Net_init break_abs_ref
  val break_abs = !break_abs_ref
end;


(*---------------------------------------------------------------------------
 * A bit convoluted, since we really only want to see the top constructor 
 * for the term. Unfortunately, doing that for Abs requires a full traversal 
 * to replace the bound variable with a free one. Therefore we make separate
 * checks for abstractions and bound variables.
 *---------------------------------------------------------------------------*)
fun label_of tm =
   if (Term.is_abs tm) then Lam
   else if (Term.is_bvar tm) then V
        else case (Term.dest_term tm)
             of Term.COMB _ => Cmb
              | Term.CONST{Name,...} => Cnst Name
              | _ => V;

val empty_net = NODE [];
fun is_empty_net (NODE []) = true | is_empty_net _ = false;

fun get_edge label =
   let fun get (NODE edges) = 
              (case (Lib.assoc1 label edges)
                 of SOME (_,net) => net
                  | NONE => empty_net)
         | get (TIP _) = raise NET_ERR "get_edge" "tips have no edges"
   in get
   end;

(*---------------------------------------------------------------------------
 * Reading from a term net.
 *---------------------------------------------------------------------------*)
fun follow tm net =
 let val nets = 
       case (label_of tm)
       of (label as Cnst _) => [get_edge label net] 
        | V   => [] 
        | Lam => follow (#Body(break_abs tm)) (get_edge Lam net)
        | Cmb => let val {Rator,Rand} = Term.dest_comb tm
                 in Lib.itlist(fn i => fn A => (follow Rator i @ A))
                              (follow Rand (get_edge Cmb net)) []
                 end
 in Lib.gather (not o is_empty_net) (get_edge V net::nets)
 end;

fun lookup tm net = itlist (fn (TIP L) => (fn A => (L@A)) | (NODE _) => I)
                           (follow tm net)  [];

(*---------------------------------------------------------------------------
 * Adding to a term net.
 *---------------------------------------------------------------------------*)
fun overwrite (p as (a,_)) = 
  let fun over [] = [p]
        | over ((q as (x,_))::rst) = if (a=x) then p::rst else q::over rst
  in over 
  end;

fun get_tip_list (TIP L) = L
  | get_tip_list (NODE _) = [];

fun net_update elem =
let fun update _ _ (TIP _) = raise NET_ERR "net_update" "cannot update a tip"
      | update defd tm (net as (NODE edges)) =
           let fun exec_defd [] net = TIP (elem::get_tip_list net)
                 | exec_defd (h::rst) net = update rst h net
               val label = label_of tm
               val child = get_edge label net
               val new_child = 
                 case label
                   of Cmb => let val {Rator, Rand} = Term.dest_comb tm
                             in update (Rator::defd) Rand child
                             end
                    | Lam => update defd (#Body(break_abs tm)) child
                    | _   => exec_defd defd child 
           in NODE (overwrite (label,new_child) edges)
           end
in  update
end;

fun enter (tm,elem) net = net_update elem [] tm net;

end; (* NET *)
