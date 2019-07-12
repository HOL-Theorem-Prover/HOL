signature finite_mapLib =
sig

  include Abbrev


  (*Expands FEVERY into a conjunction

  ``FEVERY P (FEMPTY |+ (x1, y1) |+ (x2, y2) |+ (x3, y3) |+ (x4, y4))``

  gets for example expanded to

   |- FEVERY P (X |+ (x1,y1) |+ (x2,y2) |+ (x3,y3) |+ (x4,y4)) <=>

                                                  P (x4,y4)  /\
                                 (~(x3 = x4)  ==> P (x3,y3)) /\
                   (~((x2 = x3) \/ (x2 = x4)) ==> P (x2,y2)) /\
      (~((x1 = x2) \/ (x1 = x3) \/ (x1 = x4)) ==> P (x1,y1))
  *)
  val fevery_EXPAND_CONV : Abbrev.conv


  (*Simplies fupdate - sequences by removing the ones that are masked by
    later appearances.

  ``f |+ (x1, y1) |+ (x2, y2) |+ (x1, y3) |+ (x4, y4)``

  gets for example simplied to to

   |- (f |+ (x1, y1) |+ (x2, y2) |+ (x1, y3) |+ (x4, y4)) =
      (f |+             (x2, y2) |+ (x1, y3) |+ (x4, y4))

  *)
  val fupdate_NORMALISE_CONV : Abbrev.conv

  val add_finite_map_compset : computeLib.compset -> unit

end
