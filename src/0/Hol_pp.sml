(* ===================================================================== *)
(* FILE          : hol_pp.sml                                            *)
(* DESCRIPTION   : Implements prettyprinters for HOL terms and types.    *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* REVISED       : To accomodate ppstreams, November 12, 1992            *)
(*                 Made extensible on March 2, 1994 by Richard Boulton.  *)
(* Modified      : September 23, 1997, Ken Larsen                        *)
(* ===================================================================== *)

structure Hol_pp :> Hol_pp =
struct

open Term;
open Type;
open Lib;

open Portable_PrettyPrint;

fun pp_type ppstrm ty = 
   if (!Globals.max_print_depth = 0)
   then add_string ppstrm " ... "
   else Type.pp_type ppstrm ty (!Globals.max_print_depth);

val pp_term = Term.pp_term;

fun pp_self_parsing_type ppstrm ty = 
   ( begin_block ppstrm CONSISTENT 0;
     add_string ppstrm ((!Globals.type_pp_prefix)^"`:"); 
     Type.pp_type ppstrm ty  (!Globals.max_print_depth); 
     add_string ppstrm ("`"^(!Globals.type_pp_suffix)); 
     end_block ppstrm
   ) handle e => (Lib.say "\nError in attempting to print an HOL type!\n";
                  raise e);

fun pp_self_parsing_term ppstrm tm = 
  ( begin_block ppstrm CONSISTENT 0;
    add_string ppstrm ((!Globals.term_pp_prefix)^"`"); 
    Term.pp_term ppstrm tm; 
    add_string ppstrm ("`"^(!Globals.term_pp_suffix));
    end_block ppstrm
  ) handle e => (Lib.say "\nError in attempting to print an HOL term!\n";
                 raise e);
  
fun P f x y z = f y z x;

fun type_to_string ty =
   pp_to_string (!Globals.linewidth) 
                   (P Type.pp_type (!Globals.max_print_depth))
                   ty;

fun term_to_string tm = pp_to_string (!Globals.linewidth) Term.pp_term tm

fun print_type ty = Portable.output(Portable.std_out,type_to_string ty);
fun print_term tm = Portable.output(Portable.std_out,term_to_string tm);

end; (* HOL_PP *)
