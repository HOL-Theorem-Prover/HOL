(* Run both after a fresh exported import and in a separately restored heap.
   Disable TypeBase so every successful split must use the persisted aliases. *)
open Parse boolLib simpExtLib splitLib;
val bool_ss = lift_simpset boolSimps.bool_ss;
val expected = ["splitChild$drop","splitParent$keep"];
val _ = check "persisted aliases reflect ordered ancestor retraction"
  (map #1 (named_split_thms ()) = expected);
val _ = List.app (fn (key,th) =>
  case String.fields (equal #"$") key of
      [thy,name] => check ("persistent DB identity: " ^ key)
        (Portable.pointer_eq (th,DB.fetch thy name))
    | _ => die "bad persisted key") (named_split_thms ());
val ss = (bool_ss ++ split_ss) && [markerLib.ExclX "case:bool"];
val goal : goal = ([“P (x:'a):bool”,“P (y:'a):bool”],
                  “P (if b then x:'a else y):bool”);
fun unchanged ss =
  case #1 (runtac (VALID (SIMP_TAC ss [])) ([],#2 goal)) of
      [([],g)] => aconv g (#2 goal)
    | _ => false;
val _ = check "persistent rules split with TypeBase disabled"
  (not (unchanged ss));
val single = ss && [markerLib.ExclX ("split:" ^ hd expected)];
val excluded = ss && map (fn key =>
  markerLib.ExclX ("split:" ^ key)) expected;
val _ = check "one retraction retains the equal alias" (not (unchanged single));
val _ = check "all retractions disable persistent splitting"
  (unchanged excluded);
val (subgoals,justify) = runtac (VALID (ASM_SIMP_TAC single [])) goal;
val _ = check "persistent-only tactic closes the goal" (null subgoals);
val theorem = justify [];
val _ = check "persistent-only tactic validates full conclusion and hypotheses"
  (aconv (concl theorem) (#2 goal) andalso
   HOLset.equal (HOLset.fromList Term.compare (hyp theorem),
                 HOLset.fromList Term.compare (#1 goal)));
val _ = check "proof and local exclusions preserve persistent registry"
  (map #1 (named_split_thms ()) = expected);
val _ = check "persistent proof lifecycle emits no warnings" (null (!warnings));
