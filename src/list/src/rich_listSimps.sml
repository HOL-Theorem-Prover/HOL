structure rich_listSimps :> rich_listSimps =
struct

open Lib simpLib rich_listTheory;

val RICH_LIST_ss = merge_ss [listSimps.LIST_ss,
 rewrites
  [SNOC, MAP_FLAT, MAP_FILTER, MAP_SNOC, FLAT_REVERSE, FLAT_APPEND,
   IS_PREFIX, IS_SUFFIX, REPLICATE, SEG, SEG_REVERSE, SEG_SNOC,
   FIRSTN, LASTN, BUTFIRSTN, BUTLASTN, NOT_NIL_SNOC, NOT_SNOC_NIL,
   SNOC_11, ELL]];

end;
