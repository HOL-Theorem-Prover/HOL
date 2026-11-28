val _ = splitLib.enable_split_attribute ();
val owned_context = Context.snapshot ();
val _ = splitLib.enable_split_attribute ();
val _ = check "owned prelude initialization is idempotent"
  (Portable.pointer_eq (owned_context,Context.snapshot ()));
