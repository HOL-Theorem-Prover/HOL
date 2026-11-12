structure datatypeSimpLib :> datatypeSimpLib =
struct

open HolKernel boolLib


(* ThmSetData registers the attribute as a side effect of creating the
   set, so `[datatype_simp]` parses from the moment this structure is
   linked in -- which is everywhere the datatype package is. *)
val {getDB = datatype_simps, export = export_datatype_simp,
     temp_export = temp_export_datatype_simp, ...} =
    ThmSetData.export_list {settype = "datatype_simp", initial = []}

val add_datatype_simp = temp_export_datatype_simp

(* Off by default would make the attribute inert; this exists so that
   a shape change can be bisected without unpicking the theorem set. *)
val normalising = ref true
val _ = Feedback.register_btrace ("datatype_simp", normalising)

(* The simpset is built per call: the theorem set grows as theories are
   loaded, and a set built once would freeze whatever was tagged first. *)
fun normalise_conv () =
    simpLib.SIMP_CONV
      (simpLib.++ (boolSimps.bool_ss, boolSimps.UNWIND_ss))
      (boolTheory.PULL_EXISTS :: datatype_simps())

fun normalise_induction ind =
    if not (!normalising) then ind
    else
      case Lib.total
             (CONV_RULE (STRIP_QUANT_CONV
                           (LAND_CONV (QCONV (normalise_conv ()))))) ind of
          SOME th => th
        | NONE =>
          (HOL_MESG "datatype_simp: the induction principle was left as \
                    \the construction stated it; a tagged theorem would \
                    \not rewrite it";
           ind)

end (* struct *)
