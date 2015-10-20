signature sptreeLib =
sig
  val add_sptree_compset : computeLib.compset -> unit
  val domain_CONV : Conv.conv
  val foldi_CONV : Conv.conv
  val toAList_CONV : Conv.conv
  val SPTREE_CONV : Conv.conv
end
