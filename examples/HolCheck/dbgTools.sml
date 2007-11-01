structure dbgTools = struct

local 

open Globals HolKernel Parse PrimitiveBddRules DerivedBddRules Binaryset

val dbg = ref 0

val _ = Feedback.register_trace("HolCheckDBG",dbg,3)

val vis = ref (empty String.compare)
val visp = ref (empty String.compare)
val visee = ref (empty String.compare)
val saee = ref false
val tmcb = ref (Binarymap.mkDict String.compare)
val tmlcb = ref (Binarymap.mkDict String.compare)
val thcb = ref (Binarymap.mkDict String.compare)
val thlcb = ref (Binarymap.mkDict String.compare)
val sbdd = ref false

fun set_pfx s k = foldr (fn (v,av) => if String.isPrefix v k then true else av) false s

fun show s = (member(!vis,s) orelse set_pfx (!visp) s)
 
fun showe s f = (!saee orelse member(!visee,s) orelse member(!visee,s^f))

fun printer s p = (print ("["^s^"]\n"); with_flag (show_types,(!dbg)>1) with_flag (show_assums,(!dbg)>2) p (); print "\n")

in 

fun DEN s f = if (!dbg)>0 andalso showe s f then print ("\n> > > > > > > > ["^s^"."^f^"]\n") else ()
fun DEX s f = if (!dbg)>0 andalso showe s f then print ("\n< < < < < < < < ["^s^"."^f^"]\n") else ()
fun DTM s t = if (!dbg)>0 andalso show s then (printer (s^":TM") (fn _ => print_term t)) else ()
fun DTH s t = if (!dbg)>0 andalso show s then (printer (s^":TH") (fn _ => print_thm t)) else ()
fun DTY s t = if (!dbg)>0 andalso show s then (printer (s^":TY") (fn _ => print_type t)) else ()
fun DST s =   if (!dbg)>0 andalso show s then printer s (fn _ => ()) else ()
fun DBD s b = if (!dbg)>0 andalso (!sbdd) andalso show s then (printer (s^":BD") (fn _ => bdd.printset b)) else ()
fun DNM s i = if (!dbg)>0 andalso show s then (printer (s^":NM") (fn _ => print (int_to_string i))) else ()
fun DTB s t = if (!dbg)>0 andalso show s then (printer (s^":TB") (fn _ => print_term  (getTerm t))) else ()

(* default behaviour is to not show any messages. Use sm/sp to enable single/groups of messages *)
fun sm s = if (!dbg)>0 then (vis:= add(!vis,s)) else ()  (* unhide messages from s *)

fun sp s = if (!dbg)>0 then (visp := add(!visp,s)) else () (* show all with prefix s *)
fun hp s = if (!dbg)>0 then (visp := delete(!visp,s)) else () (* hide all with prefix s *)

fun se s = if(!dbg)>0 then (visee := add(!visee,s)) else () (* show entry/exit for these *) 
							     
fun he s = if(!dbg)>0 then (visee := delete(!visee,s)) else () (* hide entry/exit for these  *) 

fun sae() = if (!dbg)>0 then saee := true else () (* show all entry/exit *)

fun hae() = if (!dbg)>0 then saee := false else () (* show no entry/exit *)

fun sb t = if (!dbg)>0 then sbdd := t else () (* enable/disable DBD calls *)

(* however, after a run, may need to reset to default if rerun is done within same session *)
fun reset() = if (!dbg)>0 then (vis := (empty String.compare); visp := (empty String.compare);
				tmcb := (Binarymap.mkDict String.compare);
				thcb := (Binarymap.mkDict String.compare);
				thlcb := (Binarymap.mkDict String.compare)
				) else ()

(* allow code to register call backs that I can use after a run to recover run-time values*)
fun CBTM s tm = if (!dbg)>0  then (tmcb:= (Binarymap.insert(!tmcb,s,Susp.delay (fn _ => (tm:term))))) else ()
fun cbtm s = if (!dbg)>0 then Susp.force(Binarymap.find(!tmcb,s)) else failwith "No debug info"

fun CBTH s th = if (!dbg)>0  then (thcb:= (Binarymap.insert(!thcb,s,Susp.delay (fn _ => (th:thm))))) else ()
fun cbth s = if (!dbg)>0 then Susp.force(Binarymap.find(!thcb,s)) else failwith "No debug info"

fun CBTHL s thl = if (!dbg)>0  then (thlcb:= (Binarymap.insert(!thlcb,s,Susp.delay (fn _ => (thl:thm list))))) else ()
fun cbthl s = if (!dbg)>0 then Susp.force(Binarymap.find(!thlcb,s)) else failwith "No debug info"

fun CBTML s tml = if (!dbg)>0  then (tmlcb:= (Binarymap.insert(!tmlcb,s,Susp.delay (fn _ => (tml:term list))))) else ()
fun cbtml s = if (!dbg)>0 then Susp.force(Binarymap.find(!tmlcb,s)) else failwith "No debug info"

end
end