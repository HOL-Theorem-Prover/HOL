structure Token :> Token =
struct
  datatype ('a,'b) token = TOKEN of LRTable.term * ('a * 'b * 'b)
  val sameToken = fn (TOKEN (t,_),TOKEN(t',_)) => t=t'
end
