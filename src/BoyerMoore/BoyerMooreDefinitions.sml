(****************************************************************************)
(* FILE          : definitions.sml                                          *)
(* DESCRIPTION   : Using definitions.                                       *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 6th June 1991                                            *)
(*                                                                          *)
(* TRANSLATED BY : R.J.Boulton                                              *)
(* DATE          : 4th October 1995                                         *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 4th October 1995                                         *)
(****************************************************************************)

structure BoyerMooreDefinitions =
struct

local

open HolKernel Parse basicHol90Lib Psyntax BoyerMooreSupport;

fun failwith function =
   raise HOL_ERR {origin_structure = "BoyerMooreDefinitions",
                  origin_function = function,
                  message = ""};

in

(*--------------------------------------------------------------------------*)
(* recursive_calls : string -> term -> term list                            *)
(*                                                                          *)
(* Function to compute the occurrences of applications of a constant in a   *)
(* term. The first argument is the name of the constant. The second         *)
(* argument is the term to be examined. If there are no occurrences, an     *)
(* empty list is returned. The function assumes that the term does not      *)
(* contain abstractions.                                                    *)
(*--------------------------------------------------------------------------*)

fun recursive_calls name tm =
   let val (f,args) = strip_comb tm
   in  if (#Name (Rsyntax.dest_const f) = name handle HOL_ERR _ => false)
       then [tm]
       else itlist append (map (recursive_calls name) args) []
   end
   handle HOL_ERR _ => [];

(*--------------------------------------------------------------------------*)
(* is_subterm : term -> term -> bool                                        *)
(*                                                                          *)
(* Function to compute whether one term is a subterm of another.            *)
(*--------------------------------------------------------------------------*)

fun is_subterm subterm tm =
   if (tm = subterm)
   then true
   else ((is_subterm subterm (rator tm)) orelse (is_subterm subterm (rand tm)))
        handle HOL_ERR _ => false;

(*--------------------------------------------------------------------------*)
(* no_new_terms : term -> term -> bool                                      *)
(*                                                                          *)
(* Function to determine whether all of the arguments of an application     *)
(* (--`f x1 ... xn`--) are subterms of a term.                              *)
(*--------------------------------------------------------------------------*)

fun no_new_terms app tm =
   let val args = #2 (strip_comb app)
   in  itlist (fn x => fn y => x andalso y)
          (map (fn arg => is_subterm arg tm) args) true
   end
   handle HOL_ERR _ => failwith "no_new_terms";

(*--------------------------------------------------------------------------*)
(* hide_fun_call : term -> term -> term                                     *)
(*                                                                          *)
(* Function to replace occurrences of a particular function call in a term  *)
(* with a genvar, so that `no_new_terms' can be used to look for arguments  *)
(* in a term less the original call.                                        *)
(*--------------------------------------------------------------------------*)

fun hide_fun_call app tm =
   let val var = genvar (type_of app)
   in  subst [(var,app)] tm
   end;

(*--------------------------------------------------------------------------*)
(* is_explicit_value : term -> bool                                         *)
(*                                                                          *)
(* Function to compute whether a term is an explicit value. An explicit     *)
(* value is either T or F or an application of a shell constructor to       *)
(* explicit values. A `bottom object' corresponds to an application to no   *)
(* arguments. I have also made numeric constants explicit values, since     *)
(* they are equivalent to some number of applications of SUC to 0.          *)
(*--------------------------------------------------------------------------*)

fun is_explicit_value tm =
   let fun is_explicit_value' constructors tm =
          (is_T tm) orelse (is_F tm) orelse
          ((is_const tm) andalso (type_of tm = (==`:num`==))) orelse
          let val (f,args) = strip_comb tm
          in  (mem (#Name (Rsyntax.dest_const f)) constructors
               handle HOL_ERR _ => false) andalso
              (forall (is_explicit_value' constructors) args)
          end
   in  is_explicit_value' (BoyerMooreShells.all_constructors ()) tm
   end;

(*--------------------------------------------------------------------------*)
(* more_explicit_values : term -> term -> bool                              *)
(*                                                                          *)
(* Returns true if and only if a new function call (second argument) has    *)
(* more arguments that are explicit values than the old function call       *)
(* (first argument).                                                        *)
(*--------------------------------------------------------------------------*)

fun more_explicit_values old_call new_call =
   let val (f1,args1) = strip_comb old_call
       and (f2,args2) = strip_comb new_call
   in  if (f1 = f2)
       then let val n1 = length (filter is_explicit_value args1)
                and n2 = length (filter is_explicit_value args2)
            in  n2 > n1
            end
       else failwith ""
   end
   handle HOL_ERR _ => failwith "more_explicit_values";

(*--------------------------------------------------------------------------*)
(* good_properties : term list -> term -> term -> term -> bool              *)
(*                                                                          *)
(* Function to determine whether the recursive calls in the expansion of a  *)
(* function call have good properties. The first argument is a list of      *)
(* assumptions currently being made. The second argument is the original    *)
(* call. The third argument is the (simplified) expansion of the call, and  *)
(* the fourth argument is the term currently being processed and which      *)
(* contains the function call.                                              *)
(*--------------------------------------------------------------------------*)

(* Boyer and Moore's heuristic
fun good_properties assumps call body_of_call tm =
   let fun in_assumps tm [] = false
         | in_assumps tm (assump::assumps) =
          if (is_subterm tm assump)
          then true
          else in_assumps tm assumps
   in  let val name = #Name (Rsyntax.dest_const (#1 (strip_comb call)))
           and body_less_call = hide_fun_call call tm
           val rec_calls = recursive_calls name body_of_call
           val bools = map (fn rc => (no_new_terms rc body_less_call) orelse
                                     (in_assumps rc assumps) orelse
                                     (more_explicit_values call rc)) rec_calls
       in  itlist (fn x => fn y => x andalso y) bools true
       end
       handle HOL_ERR _ => failwith "good_properties"
   end;
*)

(* For HOL implementation, the restricted form of definitions allows all   *)
(* recursive calls to be considered to have good properties.               *)

fun good_properties (assumps : term list) (call : term)
       (body_of_call : term) (tm : term) = true;

end;

end; (* BoyerMooreDefinitions *)
