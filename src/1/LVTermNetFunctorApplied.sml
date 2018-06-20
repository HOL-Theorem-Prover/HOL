structure LVTermNetFunctorApplied =
struct

structure PMDataSet = struct
  type value = int
  type t = value HOLset.set
  val empty = HOLset.empty Int.compare
  val insert = HOLset.add
  val fold = HOLset.foldl
  val listItems = HOLset.listItems
  fun filter P s =
      fold (fn (v,a) => if P v then insert(a,v) else a)
           empty
           s
  val numItems = HOLset.numItems
end

structure PrintMap = LVTermNetFunctor(PMDataSet)

end
