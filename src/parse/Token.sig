signature Token =
sig
  datatype ('a,'b) token = TOKEN of LRTable.term * ('a * 'b * 'b)
  val sameToken : ('a,'b) token * ('a,'b) token -> bool
end
