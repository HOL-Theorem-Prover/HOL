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

fun fromList (entries : entry list) = let
  val caseless = String.collate caseless
  fun compname (e1, e2) =
    caseless (getname e1, getname e2)
  val entries = Listsort.sort compname entries
  infix THEN
  fun (comp1 THEN comp2) arg =
    case comp1 arg of
      EQUAL => comp2 arg
    | res   => res
  fun kindof Str     = "structure"
    | kindof (Val _) = "val"
    | kindof (Typ _) = "type"
    | kindof (Exc _) = "exn"
    | kindof (Con _) = "con"
    | kindof (Term (_, NONE)) = ""
    | kindof (Term (_, SOME kind)) = kind
  fun kindCompare (e1 as {comp=c1, ...}, e2 as {comp=c2, ...}) =
    String.compare(kindof c1, kindof c2)
  fun nameCompare (e1, e2) =
    String.compare(getname e1, getname e2)
  fun fileCompare (e1, e2) = String.compare(#file e1, #file e2)
  val entryCompare = kindCompare THEN nameCompare THEN fileCompare
  fun toLower s = let
    open Char CharVector
  in
    tabulate(size s, fn i => toLower(sub(s, i)))
  end
  (* Lump together names that differ only in capitalization;
     then sort each lump using entryCompare                   *)
  fun lump [] = []
    | lump (x1 :: xr) = let
        fun mkLump lumpname lump = (toLower (getname lumpname),
                                    Listsort.sort entryCompare lump)
        fun h lump1name lump1 []       = [mkLump lump1name lump1]
          | h lump1name lump1 (x1::xr) =
          if compname(x1, lump1name) = EQUAL then
            h lump1name (x1 :: lump1) xr
          else
            mkLump lump1name lump1 :: h x1 [x1] xr
      in
        h x1 [x1] xr
      end
  val lumps = lump entries : (string * entry list) list
  fun mkOrderedTree xs = let
    fun h 0 xs = (Empty, xs)
      | h n xs = let
          val m = n div 2
          val (t1, (key, value), yr) =
            (case h m xs of
               (t,p::y) => (t,p,y)
             | _       => raise Fail "Imposible!")
          val (t2, zs)                 = h (n-m-1) yr
        in
          (Node(key, value, t1, t2), zs)
        end
  in
    #1 (h (length xs) xs)
  end
in
  mkOrderedTree lumps
end

