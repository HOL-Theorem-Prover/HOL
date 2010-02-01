structure LoadableThyData :> LoadableThyData =
struct

type ut = UniversalType.t
type t = { value : ut,
           read : string -> ut,
           write : ut -> string,
           merge : ut * ut -> ut}


fun 'a make {merge=m, read_update, write_update} = let
  val (mk : 'a -> ut,dest) = UniversalType.embed()
  fun vdest v = valOf (dest v)
  val read = mk o read_update
  val write = write_update o vdest
  fun merge (v1,v2) = mk(m(vdest v1, vdest v2))
  fun make a = {value = mk a, read = read, write = write,
                merge = merge}
  fun tdest ({value,...}:t) = dest value
in
  {mk=make,dest = tdest}
end

fun read_update ({read,write,merge,value}:t) s = let
  val utval = read s
in
  {value = utval, read = read, write = write, merge = merge}
end

fun write_update ({write,value,...}:t) = write value

fun merge ({read,write,value,merge}:t, t2:t) = let
  val v1 = value and v2 = #value t2
  val v = merge (v1,v2)
in
  {value=v,read = read, write = write, merge = merge}
end

end (* struct *)
