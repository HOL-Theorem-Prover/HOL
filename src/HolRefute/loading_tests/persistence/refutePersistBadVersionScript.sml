Theory refutePersistBadVersion
Ancestors
  refutePersistOld
Libs
  ThyDataSexp

(* Deliberately corrupt fixture: compiled theories can carry data written
   by another producer.  Assert rejection through the public Refute API. *)
val data = ThyDataSexp.new
  {thydataty = "Refute.structural_registrations.deltas",
   merge = ThyDataSexp.append_merge, load = fn _ => (),
   other_tds = fn (s, _) => SOME s};
val _ = #export data (ThyDataSexp.List
  [ThyDataSexp.List [ThyDataSexp.Int 2,
    ThyDataSexp.String "refutePersistBadVersion", ThyDataSexp.Int 0,
    ThyDataSexp.List []]]);
