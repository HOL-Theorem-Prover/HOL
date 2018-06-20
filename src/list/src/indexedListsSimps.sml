structure indexedListsSimps :> indexedListsSimps =
struct

open Lib simpLib indexedListsTheory;

val indexedLists_ss = merge_ss [listSimps.LIST_ss,
 rewrites
  [MAPi_def,FOLDRi_def,findi_def,delN_def,fupdLast_def,LIST_RELi_thm]];

val add_indexedLists_compset =
   computeLib.add_thms
     [MAPi_compute,MAPi_ACC_def,MAP2i_compute,MAP2ia_def,FOLDRi_def,findi_def,
      delN_def, fupdLast_def]

end
