(* ===================================================================== 
 * DESCRIPTION   : Implementation of term nets, from GTT.
 * MODIFIED	: Donald Syme, 1995, to add local constants
 *  
 * Local constants: For rewrites like
 *  [x=0] |- x = 0.
 * "x" is free in the assumptions, so this rewrite should only match
 * terms which are exactly "x" on the left.  The old termnets chose this
 * rewrite for any matching term.
 *
 * MODIFIED    : Donald Syme, November 1995, to be keyed up to higher order
 *               matching, based on JRH's code from GTT.  
 * ===================================================================== *)

signature Ho_net =
sig
 type 'a net
 val empty_net : 'a net
 val enter :Term.term list * Term.term * 'a -> 'a net -> 'a net
 val lookup : Term.term -> 'a net -> 'a list
 val merge_nets :  'a net * 'a net -> 'a net
end (* sig *)
