(* Database.sml *)

datatype component = 
    Str					(* structure                       *)
  | Exc of string			(* exception constructor with name *)
  | Typ of string			(* type constructor with name      *)
  | Val of string			(* value with name                 *)
  | Con of string			(* value constructor with name	   *)
  | Term of string * string option	(* term and optional kind          *)

(* An entry consist of a component and the name of its structure: *)

type entry = { comp : component, file : string, line : int }

(* Table represented by ordered binary tree, where key is lowercase: *)

datatype 'contents table =
    Empty
  | Node of string * 'contents * 'contents table * 'contents table

(* The database is a table of sorted lists of entries: *)

type database = entry list table

fun writebase(filename, db) =
    let val os = BasicIO.open_out_bin filename
    in Nonstdio.output_value os db; BasicIO.close_out os end

fun readbase filename =
    let open BasicIO
	prim_type in_channel 
	type instream_  = { closed: bool, ic: in_channel } ref
	prim_val input_value_ : in_channel -> 'a = 1 "intern_val"
	prim_val fromI : instream -> instream_   = 1 "identity"
        fun input_value is =
	    let val ref {closed, ic} = fromI is in
		if closed then
		    raise SysErr("Input stream is closed", NONE)
		else
		    input_value_ ic
	    end
	val is = open_in_bin filename
	val db = input_value is : database
    in close_in is; db end

(* Make sure tilde gets collated as a symbol, before "A": *)

fun caseless(#"~", #"~") = EQUAL
  | caseless(#"~", c2) = 
    if Char.toLower c2 < #"a" then GREATER else LESS
  | caseless(c1, #"~") = 
    if Char.toLower c1 < #"a" then LESS else GREATER
  | caseless(c1, c2) = Char.compare(Char.toLower c1, Char.toLower c2)

val keycompare = String.collate caseless

fun lookup(db : database, sought : string) =
    let fun look Empty                      = []
	  | look (Node(key, value, t1, t2)) =
	    case keycompare(sought, key) of
		LESS    => look t1
	      | GREATER => look t2
	      | EQUAL   => value
    in look db end

(* Extract the name from an entry: *)

fun getname ({comp, file, ...} : entry) =
    case comp of
	Str    => file
      | Exc id => id
      | Typ id => id
      | Val id => id
      | Con id => id
      | Term (id, _) => id

