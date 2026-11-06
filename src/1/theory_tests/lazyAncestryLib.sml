(* Two AncestryData instances over the same deltas: "lazyAncE" computes
   each theory's value when the theory is loaded, "lazyAncL" when the
   value is first read.  The lazyAnc* theories record each delta in
   both, and lazyAncC checks that they agree. *)
structure lazyAncestryLib =
struct

val lazy_applied = ref 0
fun mk mkf tag apply_delta =
    mkf {adinfo = {tag = tag, initial_values = [("min", [])],
                   apply_delta = apply_delta},
         uptodate_delta = fn (_:string) => true,
         sexps = {dec = ThyDataSexp.string_decode, enc = ThyDataSexp.String},
         globinfo = {apply_to_global = fn d => fn l => d :: l,
                     thy_finaliser = NONE, initial_value = []}}
val eager = mk AncestryData.fullmake "lazyAncE" (fn d => fn l => d :: l)
val lazy = mk AncestryData.lazy_fullmake "lazyAncL"
              (fn d => fn l => (lazy_applied := !lazy_applied + 1; d :: l))

fun record d =
    (#record_delta eager d; #update_global_value eager (fn l => d :: l);
     #record_delta lazy d; #update_global_value lazy (fn l => d :: l))

end
