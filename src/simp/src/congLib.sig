(* ========================================================================= *)
(* Simplification of terms similar to SIMP_CONV but regarding arbitrary      *)
(* preorders instead of just equality                                        *)
(* Created by Thomas Tuerk, March 2006                                       *)
(* ========================================================================= *)

signature congLib =
sig
  include congLibFn where type reducer = Traverse.reducer
                      and type simpset = simpLib.simpset
end
