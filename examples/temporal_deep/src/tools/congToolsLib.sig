signature congToolsLib =
sig

  val preorder_refl_thm : Travrules.preorder -> Abbrev.thm;
  val preorder_trans_thm : Travrules.preorder -> Abbrev.thm;

  val mk_list_as_set_congruence_relation_cs: Abbrev.thm -> Travrules.preorder ->
    congLib.congsetfrag
end

