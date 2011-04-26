structure profTools =
struct

local

open Binarymap Binaryset

val find = Binarymap.find
val app = Binarymap.app
val foldr = Binarymap.foldr

val cnt = ref (mkDict String.compare) (* counters *)
val tim = ref (mkDict String.compare) (* timers *)
val hid = ref (empty String.compare) (* hidden *)

val prf = ref false

(* set profile tracing on/off; turn off debugging infrastructure if profiling is switched on *)
fun set_prf n =
    let val _ = (prf:= not (n=0))
    in if (!prf) then (Feedback.set_trace "HolCheckDBG" 0;Feedback.set_trace "HolCheckDBGLZ" 0) else () end
	handle _ => ()(* handle is for when dbgTools is unloaded *)

fun get_prf () = if !prf then 1 else 0

val _ = Feedback.register_ftrace("HolCheckPRF",(get_prf,set_prf),1)

(* counters *)

fun incc s = if !prf then let val _ = (cnt:=insert(!cnt,s,1+find(!cnt,s))) handle ex => (cnt:=insert(!cnt,s,1)) in () end else ()

fun prc s = if !prf then print (s^".count = "^(Int.toString(find(!cnt,s)))^"\n") else ()

fun prlc l = if !prf then List.app prc l else ()

fun prac() = if !prf then app (fn (s,c) => prc s) (!cnt) else ()

fun resc s = if !prf then (cnt :=  (insert(!cnt,s,0))) else ()

fun reslc l = if !prf then List.app resc l else ()

fun resac()  = if !prf then (cnt :=  (mkDict String.compare)) else ()

in

(* timers (also have their own call count and inference count) *)

local open Timer Real Count in

local open Int in fun addI x y = x + y end (*FIXME: stupid hack to access Int.+ *)

(* start timer s, if already present, do not reset the aggregates *)
fun bgt s =  if !prf then let val (t,mtr,(utot,stot,gtot),ptot) = find(!tim,s)
			  in  ((tim := insert(!tim,s,(startCPUTimer(),Count.mk_meter(),(utot,stot,gtot),ptot))); incc s) end
			  handle ex => ((tim := insert(!tim,s,(startCPUTimer(),Count.mk_meter(),(0.0,0.0,0.0),0))); incc s)
	     else ()

(* update aggregates for timer s *)
fun ent s =
    if !prf then let val (t,mtr,(utot,stot,gtot),ptot) = find(!tim,s) handle ex => Feedback.failwith("profTools.ent: Not Found")
		     val {usr=ut,sys=st} = checkCPUTimer t
                     val gt = checkGCTime t
		     val {prims=p,...} = read mtr
		 in (tim := insert(!tim,s,(t,mtr,(utot+(Time.toReal ut),stot+(Time.toReal st),gtot+(Time.toReal gt)),addI ptot p))) end
    else ()

fun prt s = (* print info for timer s if not hidden*)
    if !prf
    then if not (member(!hid,s))
	 then let val (_,_,(utot,stot,gtot),ptot) = find(!tim,s)
		  val _ = print (StringCvt.padRight #" " 25 s)
		  val _ = print ("count = "^(Int.toString(find(!cnt,s)))^"\t")
		  val _ = print ("time=("^(fmt (StringCvt.FIX (SOME 3)) utot)^","^(fmt (StringCvt.FIX (SOME 3)) stot)^","^
				 (fmt (StringCvt.FIX (SOME 3)) gtot)^")\t\t")
		  val _ = print ("total="^(fmt (StringCvt.FIX (SOME 3)) (utot+stot))^"\t")
		  val avg = (fmt (StringCvt.FIX (SOME 4)) ((utot+stot)/(fromInt(find(!cnt,s))))) handle Div => "NA"
		  val _ = print ("avg = "^avg^"\t")
		  val _ = print ("inf = "^Int.toString(ptot)^"\n")
	      in () end
	 else ()
    else ()

fun prlt l = if !prf then List.app prt l else () (* print list of visible timers *)

fun prat() = if !prf then app (fn (s,c) => prt s) (!tim) else () (* print all visible timers *)

(* print all visible timers, sorting on nth column (skipping the times triple column) *)
fun sprat n =
    if (!prf) then
	let val comp_fun = fn ((s1,(_,_,(utot1,stot1,gtot1),ptot1,avg1)),(s2,(_,_,(utot2,stot2,gtot2),ptot2,avg2))) =>
			      case n of
				  0 => String.compare (s1,s2)
				| 1 => Int.compare (find(!cnt,s1),find(!cnt,s2))
				| 2 => Real.compare(utot1+stot1,utot2+stot2)
				| 3 => Real.compare(avg1,avg2)
				| 4 => Int.compare(ptot1,ptot2)
				| _ => String.compare (s1,s2)
	    val l = List.map (fn (s,(t,mt,(utot,stot,gtot),ptot)) =>
				 (s,(t,mt,(utot,stot,gtot),ptot,(utot+stot)/(fromInt(find(!cnt,s))))))
			     (Binarymap.listItems (!tim))
	    val sl = Listsort.sort comp_fun l
	in List.app (fn (s,c) => prt s) sl end
    else ()

fun rest s = if !prf then ((tim := insert(!tim,s,(startCPUTimer(),Count.mk_meter(),(0.0,0.0,0.0),0))); resc s) else () (* reset *)

fun reslt l = if !prf then List.app rest l else () (* reset list *)

fun resat() = if !prf then ((tim := (mkDict String.compare)); resac()) else () (* reset all*)

fun ht s =if !prf then  (hid := add(!hid,s)) else () (* hide timer s *)

fun uht s = if !prf then (hid := delete(!hid,s)) else () handle NotFound => () (* unhide timer *)

fun hp s = if !prf (*hide prefix*)
	   then (hid := (foldr (fn (k,_,st) => if String.isPrefix s k then add(st,k) else st) (!hid) (!tim)))
	   else ()

fun uhp s = if !prf (*unhide prefix*)
	    then (hid := (foldl (fn (k,st) => if String.isPrefix s k then delete(st,k) else st) (!hid) (!hid)))
	    else ()

fun ha() = if !prf then  (hid := (foldr (fn (k,_,st) => add(st,k)) (!hid) (!tim))) else () (* hide all *)

fun uha() = if !prf then (hid := (empty String.compare)) else () (* unhide all *)

fun sp s = if !prf then (ha(); uhp s) else () (*hide all but those with prefix s *)

fun prap s = if !prf then (sp s;prat()) else () (* print only the ones with prefix s *)

fun prapl l = if !prf then (List.app sp l;prat()) else () (* print only the ones with prefixes in l *)

end

end
end
