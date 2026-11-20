fun same_option (NONE,NONE) = true
  | same_option (SOME a,SOME b) = Portable.pointer_eq (a,b)
  | same_option _ = false;
val _ = check "ordinary load preserves foreign handler records"
  (foreign_attribute_before = ThmAttribute.is_attribute "split" andalso
   same_option (foreign_exporter_before,
                ThmSetData.data_exportfns {settype="split"}));

val _ = check "ordinary load preserves listener functions and order"
  (ListPair.allEq (fn ((n,f),(m,g)) =>
     n = m andalso Portable.pointer_eq (f,g))
     (listeners_before,List.filter (fn (n,_) =>
       List.exists (fn (old,_) => n = old) listeners_before)
       (Listener.listeners Theory.delta_hook)));
val added_listeners = List.filter (fn (n,_) =>
  not (List.exists (fn (old,_) => n = old) listeners_before))
  (Listener.listeners Theory.delta_hook);
(* These are precisely the listeners installed by generic markerLib,
   in Listener's most-recent-first order. *)
val legacy_listeners =
  ["markerLib.no_suspended_in_DB",
   "ThmSetData.onload.suspension.resumptions.parents",
   "ThmSetData.onload.suspension.resumptions.deltas",
   "ThmSetData.onload.suspension.theorems.parents",
   "ThmSetData.onload.suspension.theorems.deltas"];
val expected_new = List.filter (fn n =>
  not (List.exists (fn (old,_) => n = old) listeners_before)) legacy_listeners;
val _ = check "ordinary load adds only unchanged legacy marker listeners"
  (map #1 added_listeners = expected_new);
val _ = check "ordinary load installs no private persistence listener"
  (not (List.exists (fn (n,_) => n = "splitLib.persistence.onload")
    (Listener.listeners Theory.delta_hook)));
