signature TABLE = 
sig
   type key
   type 'a table
   val empty : 'a table
   val enter : 'a table * key * 'a -> 'a table
   val look  : 'a table * key -> 'a
   val peek  : 'a table * key -> 'a option 
   val numItems : 'a table -> int
   val remove : 'a table * key -> 'a table * 'a
   val addList : 'a table * key list * 'a list -> 'a table
   val listItems : 'a table -> 'a list
   val listKeys :  'a table -> int list
end

functor IntMapTable (type key
		     val getInt: key -> int) : TABLE =
struct
  type key = key
  type 'a table = (int,'a) Binarymap.dict
  val empty = Binarymap.mkDict (fn (k1:int,k2:int) => if k1 > k2 then GREATER 
				else if k1 = k2 then EQUAL
				else LESS);
  fun enter(t,k,a) = Binarymap.insert(t,getInt k,a)
  fun look(t,k) = Binarymap.find(t,getInt k)
  fun peek(t,k) = Binarymap.peek(t,getInt k)
  val numItems = Binarymap.numItems
  fun remove(t,k) = Binarymap.remove(t,getInt k)
  fun addList (t,kl,vl) = #1 (List.foldl 
	(fn (v,(t,kl)) => (enter(t,hd kl,v),tl kl)) (t,kl) vl)
  fun listKeys (t:'a table) = List.map (fn (k,v) => k) (Binarymap.listItems t)
  fun listItems (t:'a table) = List.map (fn (k,v) => v) (Binarymap.listItems t)
end
