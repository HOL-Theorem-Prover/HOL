(* ========================================================================= *)
(* FILE          : hhExportLib.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(*                     Cezary Kaliszyk, University of Innsbruck              *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportLib :> hhExportLib =
struct

open HolKernel boolLib aiLib hhTranslate

(* -------------------------------------------------------------------------
   TPTP reserved names
   ------------------------------------------------------------------------- *)

val ttype = "$tType"
val otype = "$o"

(* -------------------------------------------------------------------------
   Writer shortcuts
   ------------------------------------------------------------------------- *)

fun os oc s = TextIO.output (oc,s)

fun osn oc s = TextIO.output (oc,s ^ "\n")

fun oiter_aux oc sep f l = case l of
    []     => ()
  | [a]    => f oc a
  | a :: m => (f oc a; os oc sep; oiter_aux oc sep f m)

fun oiter oc sep f l = oiter_aux oc sep f l

(* -------------------------------------------------------------------------
   Tools
   ------------------------------------------------------------------------- *)

fun type_vars_in_term tm =
  type_varsl (map type_of (find_terms is_const tm @ all_vars tm))

fun strip_funty_aux ty =
  if is_vartype ty then [ty] else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if Thy = "min" andalso Tyop = "fun" then
        let val (tya,tyb) = pair_of_list Args in
          tya :: strip_funty_aux tyb
        end
      else [ty]
    end

fun strip_funty_n n ty =
  if is_vartype ty orelse n <= 0 then [ty] else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if Thy = "min" andalso Tyop = "fun" then
        let val (tya,tyb) = pair_of_list Args in
          tya :: strip_funty_n (n-1) tyb
        end
      else [ty]
    end

fun strip_funty ty = case strip_funty_aux ty of
    [] => raise ERR "strip_funty" ""
  | x => (last x, butlast x)







end (* struct *)
