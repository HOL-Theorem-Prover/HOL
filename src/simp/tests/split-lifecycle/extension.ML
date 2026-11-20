open Parse boolLib simpExtLib splitLib;
val bool_ss = lift_simpset boolSimps.bool_ss;

val rule = type_split_of bool;
val tm = “P (if b then x:'a else y) : bool”;
val cv = SPLIT_CONV [rule] tm;
val _ = check "local split conversion has a closed, correctly headed proof"
  (null (hyp cv) andalso aconv (lhs (concl cv)) tm andalso
   not (aconv (rhs (concl cv)) tm));
fun same_concls (ths1,ths2) = length ths1 = length ths2 andalso
  ListPair.allEq (fn (a,b) => aconv (concl a) (concl b)) (ths1,ths2);
val _ = check "goal_split_rules on a COND goal gives the bool type rules"
  (same_concls (splitLib.goal_split_rules [tm],
                splitLib.type_split_rules bool));
val local_ss = (add_split rule bool_ss ++ split_ss) &&
  [markerLib.ExclX "case:bool"];
val (goals,_) = runtac (VALID (SIMP_TAC local_ss [])) ([],tm);
val _ = check "explicit extension splitting works under foreign ownership"
  (case goals of [([],g)] => not (aconv g tm) | _ => false);
val _ = check "local extension use leaves persistence uninitialized"
  (null (named_split_thms ()) andalso no_private ());
val _ = List.app (fn name => check ("qualified extension marker: " ^ name)
  (same_const (Parse.Term [QUOTE ("marker$" ^ name)])
     (prim_mk_const {Thy="marker",Name=name}))) ["Split","ExcludeX"];
val entry = Context.snapshot ();
val entry_hooks = hooks ();
val outcome = Exn.capture enable_split_attribute ();
val _ = if owner = "attribute" orelse owner = "set" then
  (check "explicit opt-in rejects foreign owner without Context mutation"
     (Portable.pointer_eq (entry,Context.snapshot ()) andalso
      (case outcome of Exn.Exn (HOL_ERR e) =>
         Feedback.top_structure_of e = "splitLib" andalso
         Feedback.top_function_of e = "enable_split_attribute" andalso
         Feedback.message_of e = "settype or attribute split already exists"
       | _ => false));
   check "rejected opt-in preserves exact listeners"
     (same_hooks entry_hooks (hooks ())))
  else
    let
      val _ = check "explicit opt-in succeeds"
        (case outcome of Exn.Res () => true | _ => false)
      val owned = Context.snapshot ()
      val _ = enable_split_attribute ()
      val _ = check "duplicate opt-in preserves Context"
        (Portable.pointer_eq (owned,Context.snapshot ()))
      val _ = ThmAttribute.local_attribute
        {name="local",attrname="split",args=[],thm=rule}
      val live = Context.snapshot ()
      val dispatcher = valOf
        (Listener.remove_listener Theory.delta_hook private_name)
      val without = hooks ()
      val _ = enable_split_attribute ()
      val _ = check "owned opt-in repairs missing exact dispatcher"
        (Portable.pointer_eq (live,Context.snapshot ()) andalso
         (case List.find (fn (n,_) => n = private_name) (hooks ()) of
              SOME (_,f) => Portable.pointer_eq (dispatcher,f)
            | NONE => false) andalso
         same_hooks without (List.filter (fn (n,_) => n <> private_name)
           (hooks ())) andalso length (named_split_thms ()) = 1)
      val _ = Context.restore entry
      val _ = check "rewind deactivates dispatcher and registration"
        (null (named_split_thms ()) andalso
         not (ThmAttribute.is_attribute "split"))
      val _ = check "inactive dispatcher accepts TheoryLoaded"
        (null (Listener.call_listener Theory.delta_hook
          (TheoryDelta.TheoryLoaded (Theory.current_theory ()))))
      val _ = enable_split_attribute ()
      val _ = check "reinitialize after rewind has no stale local rules"
        (null (named_split_thms ()))
    in Context.restore entry end;
