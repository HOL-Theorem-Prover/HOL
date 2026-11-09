(* An AncestryData instance whose apply_delta counts its calls (breaking
   the contract on apply_delta only to observe when it runs).  The
   lazyAnc* theories record deltas in it, and lazyAncC and lazyAncD read
   the values. *)
structure lazyAncestryLib =
struct

val applied = ref 0
val anc =
    AncestryData.fullmake
      {adinfo = {tag = "lazyAnc", initial_values = [("min", [])],
                 apply_delta = fn d => fn l => (applied := !applied + 1;
                                                d :: l)},
       uptodate_delta = fn (_:string) => true,
       sexps = {dec = ThyDataSexp.string_decode, enc = ThyDataSexp.String},
       globinfo = {apply_to_global = fn d => fn l => d :: l,
                   thy_finaliser = NONE, initial_value = []}}

fun record d = (#record_delta anc d; #update_global_value anc (fn l => d :: l))

fun check name expected l =
    if Option.map (Listsort.sort String.compare) l = SOME expected then ()
    else raise Fail ("lazyAnc: unexpected value for " ^ name)

end
