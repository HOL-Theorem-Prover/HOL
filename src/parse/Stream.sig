(* Stream: signature for a lazy stream.*)

signature Stream =
 sig 
type 'xa stream
     val streamify : (unit -> 'a) -> 'a stream
     val cons : 'a * 'a stream -> 'a stream
     val get : 'a stream -> 'a * 'a stream
end
