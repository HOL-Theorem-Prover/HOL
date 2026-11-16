(* A small independently mutable regression for explicit dispatcher repair. *)
open HolKernel testutils

fun check label ok = (tprint label; if ok then OK () else die label)
val _ = Theory.new_theory "split_listener_repair"
val name = "splitLib.persistence.onload"
fun init () = SplitData.initialize {validate=fn _ => ()}
val _ = init ()
val _ = ThmAttribute.local_attribute
  {name="local",attrname="split",args=[],thm=boolTheory.TRUTH}
val entry = Context.snapshot ()
val dispatcher = valOf (Listener.remove_listener Theory.delta_hook name)
val _ = init ()
val _ = List.app (fn (file,dir) =>
  print ("OBS repair.loaded.path=" ^ OS.Path.concat (dir,file) ^ "\n"))
  (Binarymap.listItems (Meta.fileDirMap ()))
val _ = check "explicit initialization repairs missing dispatcher identity"
  (case List.find (fn (n,_) => n = name)
     (Listener.listeners Theory.delta_hook) of
       SOME (_,f) => Portable.pointer_eq (f,dispatcher)
     | NONE => false)
val _ = check "dispatcher repair preserves exact Context and live rules"
  (Portable.pointer_eq (entry,Context.snapshot ()) andalso
   (case SplitData.named_rules () of
        [(key,th)] => key = "split_listener_repair$local" andalso
          Portable.pointer_eq (th,boolTheory.TRUTH)
      | _ => false))
val _ = Listener.remove_listener Theory.delta_hook name
val foreign_calls = ref 0
fun foreign _ = foreign_calls := !foreign_calls + 1
val _ = Theory.register_hook (name,foreign)
val result = Exn.capture init ()
val _ = check "repair never replaces a foreign dispatcher"
  ((case result of Exn.Exn (HOL_ERR e) =>
      Feedback.top_structure_of e = "SplitData" andalso
      Feedback.top_function_of e = "initialize"
    | _ => false) andalso
   Portable.pointer_eq (entry,Context.snapshot ()) andalso
   (case List.find (fn (n,_) => n = name)
      (Listener.listeners Theory.delta_hook) of
        SOME (_,f) => Portable.pointer_eq (f,foreign)
      | _ => false) andalso !foreign_calls = 0)
val _ = print "OBS repair=pass\n"
val _ = OS.Process.exit OS.Process.success
