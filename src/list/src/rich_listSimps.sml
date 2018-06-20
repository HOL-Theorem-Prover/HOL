structure rich_listSimps :> rich_listSimps =
struct

open Lib simpLib rich_listTheory;

val RICH_LIST_ss = merge_ss [listSimps.LIST_ss,
 rewrites
  [SNOC, MAP_FLAT, MAP_FILTER, MAP_SNOC, FLAT_REVERSE, FLAT_APPEND,
   IS_PREFIX, IS_SUFFIX, REPLICATE, SEG, SEG_REVERSE, SEG_SNOC,
   FIRSTN, LASTN, BUTFIRSTN, BUTLASTN, NOT_NIL_SNOC, NOT_SNOC_NIL,
   SNOC_11, ELL]];

val add_rich_list_compset =
   computeLib.add_thms
     [rich_listTheory.AND_EL_DEF,
      rich_listTheory.BUTLASTN_compute,
      numLib.SUC_RULE rich_listTheory.COUNT_LIST_AUX_def,
      rich_listTheory.COUNT_LIST_compute,
      numLib.SUC_RULE rich_listTheory.ELL,
      rich_listTheory.IS_SUBLIST,
      rich_listTheory.IS_SUFFIX_compute,
      rich_listTheory.LASTN_compute,
      rich_listTheory.LIST_ELEM_COUNT_DEF,
      rich_listTheory.OR_EL_DEF,
      rich_listTheory.PREFIX_DEF,
      numLib.SUC_RULE rich_listTheory.REPLICATE,
      rich_listTheory.SCANL,
      rich_listTheory.SCANR,
      rich_listTheory.SEG_compute,
      rich_listTheory.SPLITL_def,
      rich_listTheory.SPLITP_compute,
      rich_listTheory.SPLITP_AUX_def,
      rich_listTheory.SPLITR_def,
      rich_listTheory.SUFFIX_DEF,
      rich_listTheory.TL_T_def,
      rich_listTheory.UNZIP_FST_DEF,
      rich_listTheory.UNZIP_SND_DEF
     ]

end
