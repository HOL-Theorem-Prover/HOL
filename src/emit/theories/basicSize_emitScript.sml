open HolKernel boolLib bossLib Parse;
open EmitML basicSizeTheory;
open option_emitTheory num_emitTheory;

val _ = new_theory "basicSize_emit";

val defs =
  map DEFN [bool_size_def, pair_size_def, one_size_def, option_size_def];

val _ = eSML "basicSize"
  (MLSIG "type num = numML.num" ::
   MLSIG "type 'a  option = 'a optionML.option" ::
   MLSIG "type ('a,'b) sum = ('a,'b) sumML.sum" ::
   OPEN ["num","sum","option"] ::
   defs);

val _ = eCAML "basicSize" (MLSIGSTRUCT ["type num = NumML.num"] @ defs);

val _ = export_theory ();
