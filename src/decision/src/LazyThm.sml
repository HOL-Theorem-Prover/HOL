(****************************************************************************)
(* FILE          : lazy_thm.sml                                             *)
(* DESCRIPTION   : Abstract datatype for lazy theorems.                     *)
(*                                                                          *)
(* AUTHOR        : R.J.Boulton                                              *)
(* DATE          : 4th October 1991                                         *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 20th August 1996                                         *)
(****************************************************************************)

structure LazyThm :> LazyThm =
struct

open Thm Exception Lib;

type term  = Term.term
type thm   = Thm.thm

fun failwith function = raise HOL_ERR{origin_structure = "LazyThm",
                                      origin_function = function,
                                      message = ""};

fun upto from to =
   if (from > to) then []
   else from::upto (from + 1) to;

(*==========================================================================*)
(* Datatype for controlling the generation of theorems.                     *)
(*                                                                          *)
(*    Lazy    Don't generate theorems immediately but retain the ability to *)
(*            do so, i.e., build a proof.                                   *)
(*                                                                          *)
(*    Eager   Generate theorems immediately. This corresponds to the normal *)
(*            operation of HOL except that a lazy theorem is obtained.      *)
(*            However, no inference is required to obtain a real theorem    *)
(*            from the lazy one.                                            *)
(*                                                                          *)
(*    Draft   Don't generate theorems and don't retain the ability to do so.*)
(*==========================================================================*)

datatype proof_mode = Lazy | Eager | Draft;

(*--------------------------------------------------------------------------*)
(* proof_mode : proof_mode ref                                              *)
(*                                                                          *)
(* Mode of operation is initially set to Eager.                             *)
(*--------------------------------------------------------------------------*)

val proof_mode = ref Eager;

(*--------------------------------------------------------------------------*)
(* set_proof_mode : proof_mode -> proof_mode                                *)
(* get_proof_mode : unit -> proof_mode                                      *)
(*                                                                          *)
(* Functions for modifying and reading the current proof mode.              *)
(*--------------------------------------------------------------------------*)

fun set_proof_mode mode =
   let val old_mode = !proof_mode
   in  proof_mode := mode; old_mode
   end
and get_proof_mode () = !proof_mode;

(*==========================================================================*)
(* Auxiliary definitions                                                    *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* apply_proof_fun : (unit -> thm) -> thm                                   *)
(* apply_proof_fun : (unit -> thm list) -> thm list                         *)
(*                                                                          *)
(* Generates a theorem by executing a proof.                                *)
(*--------------------------------------------------------------------------*)

fun apply_proof_fun f = f ();

(*--------------------------------------------------------------------------*)
(* check_consistent : ((term list * term) -> 'a) -> ('a * thm) -> thm       *)
(*                                                                          *)
(* Checks that a theorem corresponds to an abstract structure for it.       *)
(*--------------------------------------------------------------------------*)

fun check_consistent from_goal (struc,th) =
   if (from_goal (dest_thm th) = struc)
   then th
   else failwith
           "check_consistent -- theorem generated does not match structure";

(*--------------------------------------------------------------------------*)
(* dummy_proof : unit -> thm                                                *)
(*                                                                          *)
(* Dummy proof for draft mode operation. Constructing a parameterless       *)
(* function around TRUTH is an attempt to save memory. The idea is that all *)
(* lazy theorems should `point to' this one function (when in draft mode)   *)
(* rather than them each having their own.                                  *)
(*--------------------------------------------------------------------------*)

val dummy_proof = fn () => boolTheory.TRUTH;

(*==========================================================================*)
(* Underlying representation type for lazy theorems.                        *)
(*==========================================================================*)

datatype lazy_thm_rep = Lazy_thm of unit -> thm
                      | Proved_thm of thm;

val Dummy_thm = Lazy_thm dummy_proof;

(*==========================================================================*)
(* Underlying representation type for lists of lazy theorems.               *)
(*==========================================================================*)

datatype lazy_thms_rep = Lazy_thms of unit -> thm list
                       | Proved_thms of thm list;

val Dummy_thms = Lazy_thms (fn () => []);

(*==========================================================================*)
(* Abstract datatype for lazy theorems.                                     *)
(*                                                                          *)
(* mk_lazy_thm          : ('a * (unit -> thm)) -> 'a lazy_thm               *)
(* mk_proved_lazy_thm   : ('a * thm) -> 'a lazy_thm                         *)
(* dest_lazy_thm        : 'a lazy_thm -> 'a                                 *)
(* prove_lazy_thm       : (term list * term -> ''a) -> ''a lazy_thm -> thm  *)
(* restructure_lazy_thm : ('a -> 'b) -> 'a lazy_thm -> 'b lazy_thm          *)
(* apply_rule1          : ('a -> 'b) * (thm -> thm) ->                      *)
(*                        'a lazy_thm -> 'b lazy_thm                        *)
(* apply_rule2          : ('a -> 'b -> 'c) * (thm -> thm -> thm) ->         *)
(*                        'a lazy_thm -> 'b lazy_thm -> 'c lazy_thm         *)
(* apply_rule3          : ('a -> 'b -> 'c -> 'd) *                          *)
(*                        (thm -> thm -> thm -> thm) ->                     *)
(*                        'a lazy_thm -> 'b lazy_thm -> 'c lazy_thm ->      *)
(*                        'd lazy_thm                                       *)
(* apply_rulen          : ('a list -> 'b) * (thm list -> thm) ->            *)
(*                        'a lazy_thm list -> 'b lazy_thm                   *)
(* apply_rule1_multi_result : ('a -> 'b list) * (thm -> thm list) ->        *)
(*                            'a lazy_thm -> 'b lazy_thm list               *)
(*==========================================================================*)

abstype 'a lazy_thm = LazyThm of 'a * (lazy_thm_rep ref)
with

local

fun mk_lazy_thm_rep f =
   (case (get_proof_mode ())
    of Lazy  => Lazy_thm f
     | Eager => Proved_thm (apply_proof_fun f)
     | Draft => Dummy_thm);

fun mk_lazy_thms_rep f =
   (case (get_proof_mode ())
    of Lazy  => Lazy_thms f
     | Eager => Proved_thms (apply_proof_fun f)
     | Draft => Dummy_thms);

fun prove_lazy_thm_rep cell =
   (case !cell
    of Lazy_thm f =>
          let val th = apply_proof_fun f
          in  cell := Proved_thm th; th
          end
     | Proved_thm th => th);

fun prove_lazy_thms_rep cell =
   (case !cell
    of Lazy_thms f =>
          let val ths = apply_proof_fun f
          in  cell := Proved_thms ths; ths
          end
     | Proved_thms ths => ths);

in

fun mk_lazy_thm (struc,f) = LazyThm (struc,ref (mk_lazy_thm_rep f));

fun mk_proved_lazy_thm (struc,th) = LazyThm (struc,ref (Proved_thm th));

fun dest_lazy_thm (LazyThm (struc,_)) = struc;

fun prove_lazy_thm from_goal (LazyThm (struc,cell)) =
   check_consistent from_goal (struc,prove_lazy_thm_rep cell);

fun restructure_lazy_thm f (LazyThm (struc,cell)) = LazyThm (f struc,cell);

fun apply_rule1 (rule,RULE) (LazyThm (struc,cell)) =
   LazyThm (rule struc,
            ref (mk_lazy_thm_rep (fn () => RULE (prove_lazy_thm_rep cell))));

fun apply_rule2 (rule,RULE)
       (LazyThm (struc1,cell1)) (LazyThm (struc2,cell2)) =
   LazyThm (rule struc1 struc2,
            ref (mk_lazy_thm_rep (fn () => RULE (prove_lazy_thm_rep cell1)
                                                (prove_lazy_thm_rep cell2))));

fun apply_rule3 (rule,RULE) (LazyThm (struc1,cell1))
       (LazyThm (struc2,cell2)) (LazyThm (struc3,cell3)) =
   LazyThm (rule struc1 struc2 struc3,
            ref (mk_lazy_thm_rep (fn () => RULE (prove_lazy_thm_rep cell1)
                                                (prove_lazy_thm_rep cell2)
                                                (prove_lazy_thm_rep cell3))));

fun apply_rulen (rule,RULE) lths =
   let val (strucs,cells) = split (map (fn LazyThm x => x) lths)
   in  LazyThm (rule strucs,
                ref (mk_lazy_thm_rep
                        (fn () => RULE (map prove_lazy_thm_rep cells))))
   end;

fun apply_rule1_multi_result (rule,RULE) (LazyThm (struc,cell)) =
   let val strucs = rule struc
       val cell' =
          ref (mk_lazy_thms_rep (fn () => RULE (prove_lazy_thm_rep cell)))
   in  map (fn n => LazyThm
                       (el n strucs,
                        ref (mk_lazy_thm_rep
                                (fn () => el n (prove_lazy_thms_rep cell')))))
           (upto 1 (length strucs))
   end

end;

end;

(*==========================================================================*)
(* Type of pre-theorems.                                                    *)
(*==========================================================================*)

type pre_thm = (term list * term) lazy_thm;

(*--------------------------------------------------------------------------*)
(* mk_pre_thm        : ((term list * term) * (unit -> thm)) -> pre_thm      *)
(* mk_proved_pre_thm : thm -> pre_thm                                       *)
(* dest_pre_thm      : pre_thm -> (term list * term)                        *)
(* prove_pre_thm     : pre_thm -> thm                                       *)
(*--------------------------------------------------------------------------*)

val mk_pre_thm = mk_lazy_thm
and mk_proved_pre_thm = fn th => mk_proved_lazy_thm (dest_thm th,th)
and dest_pre_thm = (dest_lazy_thm : pre_thm -> (term list * term))
and prove_pre_thm = prove_lazy_thm (fn x => x);

(*--------------------------------------------------------------------------*)
(* hyp   : pre_thm -> term list                                             *)
(* concl : pre_thm -> term                                                  *)
(*--------------------------------------------------------------------------*)

val hyp   = #1 o dest_pre_thm
and concl = #2 o dest_pre_thm;

(*--------------------------------------------------------------------------*)
(* apply_to_concl : (term -> term) -> term list * term -> term list * term  *)
(*--------------------------------------------------------------------------*)

fun apply_to_concl f (hyps,conc) = (hyps,f conc);

end; (* LazyThm *)
