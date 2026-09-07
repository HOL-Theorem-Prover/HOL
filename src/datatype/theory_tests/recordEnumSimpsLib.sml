structure recordEnumSimpsLib =
struct

  open simpLib BasicProvers

  (* Force srw_ss initialisation (and its ARITH_ss merge) at
     library-load time so the recordEnumSimps{A,B}Script tests
     exercise BasicProvers' TypeBase hook against an already-live
     simpset, which was the regression this test was written to
     catch.  Previously done via a load-time Q.prove, which now
     trips the CT-none check. *)
  val _ = srw_ss() ++ numSimps.ARITH_ss

end
