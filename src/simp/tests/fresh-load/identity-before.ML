(* Native ownership inspection only. *)

(* Presence only; the selftest's attribute_identity checks which handler
   answers by dispatching to it. *)
val foreign_attribute_before = ThmAttribute.is_attribute "split";
val foreign_exporter_before = ThmSetData.data_exportfns {settype="split"};

val listeners_before = Listener.listeners Theory.delta_hook;
