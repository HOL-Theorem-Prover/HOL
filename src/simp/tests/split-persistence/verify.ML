open Parse boolLib simpExtLib splitLib;
val bool_ss = lift_simpset boolSimps.bool_ss;
val expected = if scenario = "parent" then
                 ["splitParent$drop","splitParent$keep"]
               else ["splitChild$drop","splitParent$keep"];
val _ = check "imported named rules reflect ancestor ADD/REMOVE"
  (map #1 (named_split_thms ()) = expected);
val _ = List.app (fn (key,th) =>
  case String.fields (equal #"$") key of
      [thy,name] => check ("imported theorem identity: " ^ key)
                     (Portable.pointer_eq (th, DB.fetch thy name))
    | _ => die "malformed split key") (named_split_thms ());
val _ = check "removed theorem remains available in DB"
  (can (DB.fetch "splitParent") "transient");
val _ = check "same-theory REMOVE serialized with writing theory"
  (List.exists (fn SplitData.Remove s => s = "splitParent$transient"
                | _ => false)
     (SplitData.theory_data "splitParent"));
val _ = if scenario = "parent" then () else
  check "ancestor REMOVE retains fully resolved key in descendant"
    (List.exists (fn SplitData.Remove s => s = "splitParent$drop"
                  | _ => false)
       (SplitData.theory_data "splitChild"));
val registered = Context.snapshot ();
val _ = enable_split_attribute ();
val _ = check "opt-in after import preserves registration and data"
  (Portable.pointer_eq (registered,Context.snapshot ()) andalso
   map #1 (named_split_thms ()) = expected);

(* Disable TypeBase so persistent controls cannot pass through that route.
   All imported aliases must be excluded, not just an equal theorem. *)
val goal : goal = ([], “P (if b then x:'a else y) : bool”);
val ss = (bool_ss ++ split_ss) && [simpMarkerLib.ExclX "case:bool"];
fun unchanged ss = case #1 (runtac (VALID (SIMP_TAC ss [])) goal) of
    [([],tm)] => aconv tm (#2 goal)
  | _ => false;
val _ = check "imported persistent rules really split"
  (not (unchanged ss));
val excluded = ss &&
  map (fn key => simpMarkerLib.ExclX ("split:" ^ key)) expected;
val _ = check "named retractions suppress all imported aliases"
  (unchanged excluded);
val one_left = ss &&
  [simpMarkerLib.ExclX ("split:" ^ hd expected)];
val _ = check "one named retraction does not remove an equal alias"
  (not (unchanged one_left));
val _ = check "local exclusions leave persistent store unchanged"
  (map #1 (named_split_thms ()) = expected);

val _ = check "exported markers record simpMarker theory dependency"
  (List.exists (equal "simpMarker") (Theory.ancestry "splitParent") andalso
   same_const (rator (concl (DB.fetch "splitParent" "split_marker")))
              (prim_mk_const {Thy="simpMarker",Name="Split"}) andalso
   simpMarkerLib.destExclX (DB.fetch "splitParent" "exclusion_marker") = SOME "case:bool");
