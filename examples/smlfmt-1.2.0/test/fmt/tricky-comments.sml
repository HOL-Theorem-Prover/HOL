val x =
  (* try first *)
  case foobar of
    (* yo *)
    Foo f => f (* hello *)
  | Bar b => b (* world *)


val _ =
  (* try to activate first *)
  if not (isActivated tab) then
    setTabState tab (Usable (Activated NONE))
  else (* if activated, try to relocate *)
  case getTabState tab of

  (* activated but not placed *)
    Usable (Activated NONE) =>
      let
        val desired = blah blah
      in
        setTabState tab (Usable (Activated (SOME desired)))
      end

  (* activated and already placed *)
  | Usable (Activated (SOME i)) =>
      let
        val desired = blah blah
      in
        setTabState tab (Usable (Activated (SOME desired)))
      end

  | Other => bad (* bad! *)

  | _ => (* how could we get here?? *)
      raise Fail "bad tab"


val _ = (* hello *)
  Seq.iterate annConcat
    (* huh *) (Seq.nth all 0)
    (Seq.map (*okay*) withBreak (*huh*) (Seq.drop all 1))