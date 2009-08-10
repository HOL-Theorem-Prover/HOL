(* Database.sml *)
structure Database :> Database = struct


(* For unknown reasons, BinIO.inputN is raising Subscript exceptions *)
local
fun myInputN' (is, 0) = []
  | myInputN' (is, n) =
  case BinIO.input1 is of
    NONE => []
  | SOME v => v :: myInputN' (is, n-1);
in
fun myInputN (is, n) = Word8Vector.fromList (myInputN' (is, n))
end;

fun writeInt32 os i =
  let
    val w = Word32.fromInt i
    fun w32tow8 w = Word8.fromInt (Word32.toInt w)
  in
    (BinIO.output1 (os, w32tow8 w);
     BinIO.output1 (os, w32tow8 (Word32.>> (w, 0w8)));
     BinIO.output1 (os, w32tow8 (Word32.>> (w, 0w16)));
     BinIO.output1 (os, w32tow8 (Word32.>> (w, 0w24))))
  end;

fun readInt32 is =
  let
    val v = myInputN (is, 4)
    fun w8tow32 i s =
      Word32.<< (Word32.fromInt (Word8.toInt (Word8Vector.sub (v, i))), s)
  in
    Word32.toInt (Word32.orb (w8tow32 0 0w0,
                  Word32.orb (w8tow32 1 0w8,
                  Word32.orb (w8tow32 2 0w16,
                              w8tow32 3 0w24))))
  end;

fun writeString os s =
  (writeInt32 os (String.size s);
   BinIO.output (os, Byte.stringToBytes s));

fun readString is =
  let val len = readInt32 is in
    Byte.bytesToString (myInputN (is, len))
  end;

fun writeList write os l =
  let
    fun f [] =
        BinIO.output1 (os, 0w0)
      | f (e::t) =
        (BinIO.output1 (os, 0w1);
         write os e;
         writeList write os t)
  in
    f (List.rev l)
  end;

fun readList read is acc =
  let val tag = BinIO.input1 is in
    case tag of
         SOME 0w0 => acc
       | _ => readList read is (read is :: acc)
  end;

datatype component =
    Str					(* structure                       *)
  | Exc of string			(* exception constructor with name *)
  | Typ of string			(* type constructor with name      *)
  | Val of string			(* value with name                 *)
  | Con of string			(* value constructor with name	   *)
  | Term of string * string option	(* term and optional kind          *)

fun writeComponent os Str =
    BinIO.output1 (os, 0w0)
  | writeComponent os (Exc s) =
    (BinIO.output1 (os, 0w1);
     writeString os s)
  | writeComponent os (Typ s) =
    (BinIO.output1 (os, 0w2);
     writeString os s)
  | writeComponent os (Val s) =
    (BinIO.output1 (os, 0w3);
     writeString os s)
  | writeComponent os (Con s) =
    (BinIO.output1 (os, 0w4);
     writeString os s)
  | writeComponent os (Term (s, NONE)) =
    (BinIO.output1 (os, 0w5);
     writeString os s)
  | writeComponent os (Term (s1, SOME s2)) =
    (BinIO.output1 (os, 0w6);
     writeString os s1;
     writeString os s2);

fun readComponent is =
  let val tag = BinIO.input1 is in
    case tag of
         SOME 0w0 => Str
       | SOME 0w1 => Exc (readString is)
       | SOME 0w2 => Typ (readString is)
       | SOME 0w3 => Val (readString is)
       | SOME 0w4 => Con (readString is)
       | SOME 0w5 => Term (readString is, NONE)
       | _ =>
           let
             val s1 = readString is
             val s2 = readString is
           in
             Term (s1, SOME s2)
           end
  end;

(* An entry consist of a component and the name of its structure: *)

type entry = { comp : component, file : string, line : int }

fun writeEntry os (e:entry) =
  (writeComponent os (#comp e);
   writeString os (#file e);
   writeInt32 os (#line e));

fun readEntry is =
  let
    val c = readComponent is
    val f = readString is
    val l = readInt32 is
  in
    {comp = c, file = f, line = l}
  end;

(* Table represented by ordered binary tree, where key is lowercase: *)

datatype 'contents table =
    Empty
  | Node of string * 'contents * 'contents table * 'contents table

fun writeTable os Empty =
    BinIO.output1 (os, 0w0)
  | writeTable os (Node (s, el, t1, t2)) =
    (BinIO.output1 (os, 0w1);
     writeString os s;
     writeList writeEntry os el;
     writeTable os t1;
     writeTable os t2);

fun readTable is =
  let val tag = BinIO.input1 is in
    case tag of
         SOME 0w0 => Empty
       | _ =>
           let
             val s = readString is
             val c = readList readEntry is []
             val t1 = readTable is
             val t2 = readTable is
           in
             Node (s, c, t1, t2)
           end
  end;

(* The database is a table of sorted lists of entries: *)

type database = entry list table

fun writebase(filename, db) =
  let val os = BinIO.openOut filename in
    writeTable os db;
    BinIO.closeOut os
  end;

fun readbase filename =
  let
    val is = BinIO.openIn filename
    val t = readTable is
  in
    BinIO.closeIn is;
    t
  end;

(* Make sure tilde and | and \ are collated as symbols, before "A": *)

fun caseless(#"~", #"~")  = EQUAL
  | caseless(#"|", #"|")  = EQUAL
  | caseless(#"\\", #"\\") = EQUAL
  | caseless(#"\\", #"~") = LESS
  | caseless(#"\\", #"|") = LESS
  | caseless(#"|", #"~")  = LESS
  | caseless(#"~", #"|")  = GREATER
  | caseless(#"~", #"\\")  = GREATER
  | caseless(#"|", #"\\")  = GREATER
  | caseless(#"~", c2) = if Char.toLower c2 < #"a" then GREATER else LESS
  | caseless(c1, #"~") = if Char.toLower c1 < #"a" then LESS else GREATER
  | caseless(#"|", c2) = if Char.toLower c2 < #"a" then GREATER else LESS
  | caseless(c1, #"|") = if Char.toLower c1 < #"a" then LESS else GREATER
  | caseless(#"\\", c2) = if Char.toLower c2 < #"a" then GREATER else LESS
  | caseless(c1, #"\\") = if Char.toLower c1 < #"a" then LESS else GREATER
  | caseless(c1, c2) = Char.compare(Char.toLower c1, Char.toLower c2);

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
      | Term (id, _) => case String.tokens (fn c => c = #".") id
                         of [strName,vName] => vName
                          | other => id;

end
