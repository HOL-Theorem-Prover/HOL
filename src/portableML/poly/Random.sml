(* Random -- Moscow ML library 1995-04-23, 1999-02-24 *)
structure Random :> Random =
struct

type generator = {seedref : real ref}

(* Generating random numbers.  Paulson, page 96 *)

val a = 16807.0
val m = 2147483647.0

fun nextrand seed =
   let
      val t = a * seed
   in
      t - m * real (floor (t / m))
   end

fun newgenseed seed = {seedref = ref (nextrand seed)}

fun getrealtime () =
   let
      val t = Time.now ()
      val micro_s = Time.toMicroseconds t
      val sec = micro_s div 1000000
      val usec = micro_s mod 1000000
   in
      {sec = sec, usec = usec}
   end

fun newgen () =
   let
      val {sec, usec} = getrealtime ()
   in
      newgenseed (Real.fromLargeInt sec + Real.fromLargeInt usec)
   end

fun random {seedref} =
  let
    val seed = !seedref
  in
    (seedref := nextrand seed; seed / m)
  end

fun randomlist (n, {seedref}) =
   let
      val seed0 = !seedref
      fun h 0 seed res = (seedref := seed; res)
        | h i seed res = h (i - 1) (nextrand seed) (seed / m :: res)
   in
      h n seed0 []
   end

fun range (min, max) =
   if min > max
      then raise Fail "Random.range: empty range"
   else fn {seedref} =>
         let
            val seed = !seedref
         in
           (seedref := nextrand seed
            ; min + floor (real (max - min) * seed / m))
         end

fun rangelist (min, max) =
   if min > max
      then raise Fail "Random.rangelist: empty range"
   else fn (n, {seedref}) =>
           let
              fun h 0 seed res = (seedref := seed; res)
                | h i seed res =
                    h (i - 1) (nextrand seed)
                      (min + floor (real (max - min) * seed / m) :: res)
           in
              h n (!seedref) []
           end

end
