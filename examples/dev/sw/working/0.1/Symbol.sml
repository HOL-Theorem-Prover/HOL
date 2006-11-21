signature SYMBOL =
sig
  eqtype symbol
  val newSymbol : string -> symbol
  val name : symbol -> string
  val index : symbol -> int
  val mkSymbol : string -> int -> symbol
  type 'a table
  val empty : 'a table
  val enter : 'a table * symbol * 'a -> 'a table
  val look  : 'a table * symbol -> 'a
end

structure Symbol :> SYMBOL =
struct

  type symbol = string * int

  structure H = Polyhash

  exception Symbol
  val nextsym = ref 0
  val sizeHint = 128
  val hashtable : (string,int) H.hash_table = 
		H.mkTable(H.hash, op = ) (sizeHint,Symbol)
  
  fun newSymbol name =
      case H.peek hashtable name
       of SOME i => (name,i)
        | NONE => let val i = !nextsym
	           in nextsym := i+1;
		      H.insert hashtable (name,i);
		      (name,i)
		  end
  fun mkSymbol name index = 
	(name,index) : symbol

  fun name(s,n) = s
  fun index(s,n) = n

  structure Table = IntMapTable(type key = symbol
				fun getInt(s,n) = n)

  type 'a table= 'a Table.table
  val empty = Table.empty
  val enter = Table.enter
  val look = Table.look
end
