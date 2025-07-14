structure ThreadLocal :> ThreadLocal =
struct

  type 'a t = 'a Universal.tag
  val new = Universal.tag
  val get = Thread.getLocal
  val set = Thread.setLocal

end
