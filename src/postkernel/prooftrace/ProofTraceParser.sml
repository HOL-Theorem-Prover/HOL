structure ProofTraceParser :> ProofTraceParser = struct

fun decompressGzip (filename: string): Word8Vector.vector = let
  val proc = Unix.execute ("/usr/bin/gzip", ["-dc", filename])
  val (instream, outstream) = Unix.streamsOf proc
  val _ = TextIO.closeOut outstream
  fun readLoop acc =
    case TextIO.inputN (instream, 65536) of
      "" => (Unix.reap proc; Word8Vector.concat (rev acc))
    | s  => readLoop (Byte.stringToBytes s :: acc)
  in readLoop [] end;

datatype obj = OBytes of string | OObj of Word8VectorSlice.slice | OOther
type 'a ptr = Word64.word
type ('a,'A) gparser = 'a ptr -> 'A
type 'a parser = ('a, 'a) gparser
type root = unit
type heap = obj DArray.darray
val heapSize = DArray.size
val castPtr = I

fun parse filename = let
  val vec = decompressGzip filename
  val root = Word8Vector.length vec - 8
  fun get64 start = let
    fun b i = Word64.fromInt (Word8.toInt (Word8Vector.sub (vec, start + i)))
    open Word64 infix orb <<
    in
      b 0           orb (b 1 << 0w8)  orb (b 2 << 0w16) orb (b 3 << 0w24) orb
      (b 4 << 0w32) orb (b 5 << 0w40) orb (b 6 << 0w48) orb (b 7 << 0w56)
    end
  val out = DArray.new (3, OOther)
  fun process start = if start >= root then () else let
    val header = get64 start
    val flags = Word64.>>(header, 0w56)
    val len = Word64.toInt (Word64.andb(header, 0wxFFFFFFFFFFFFFF))
    val obj = case Word64.andb(flags, 0w3) of
      0w0 => OObj (Word8VectorSlice.slice (vec, start + 8, SOME (len*8)))
    | 0w1 => let
      val blen = Word64.toInt (get64 (start + 8))
      in OBytes (Byte.bytesToString (Word8VectorSlice.vector
        (Word8VectorSlice.slice (vec, start + 16, SOME blen)))) end
    | _ => OOther
    val _ = DArray.push (out, obj)
    in process (start + 8 * (len + 1)) end
  in process 0; (get64 root, out) end

fun int w = Int.fromLarge (Word64.toLargeIntX w div 2)
fun ptr w = Word64.toInt (Word64.>>(w, 0w1)) - 1

fun get64 slice start = let
  fun b i = Word64.fromInt (Word8.toInt (Word8VectorSlice.sub (slice, start + i)))
  open Word64 infix orb <<
  in
    b 0           orb (b 1 << 0w08) orb (b 2 << 0w16) orb (b 3 << 0w24) orb
    (b 4 << 0w32) orb (b 5 << 0w40) orb (b 6 << 0w48) orb (b 7 << 0w56)
  end

datatype 'a any = Int of int | Bytes of string | Obj of 'a list | Other
fun any objs p w =
  if Word64.andb(w, 0w1) = 0w1 then Int (int w) else
  case DArray.sub (objs, ptr w) of
    OBytes b => Bytes b
  | OOther => Other
  | OObj slice => let
    fun build (i, acc) = if i = 0 then acc else case i - 8 of i =>
      build (i, p (get64 slice i) :: acc)
    in Obj (build (Word8VectorSlice.length slice, [])) end

fun obj' objs p = case DArray.sub (objs, p) of
  OObj slice => slice
| _ => raise Fail "parse error"
fun obj objs w = obj' objs (ptr w)
fun arg c n w = get64 (obj c w) (8*n)

fun shVariant c w = let
  val slice = obj c w
  fun build (i, acc) = if i = 0 then (int (get64 slice 0), acc) else
    build (i - 8, get64 slice i :: acc)
  in build (Word8VectorSlice.length slice - 8, []) end

local
  fun tuple c p w = p (obj c w, 0)
  infixr 9 <>
  fun (p <> q) (slice, i) = (p (get64 slice i), q (slice, i + 8))
  fun t1 p (slice, i) = p (get64 slice i)
in
  fun tuple2 c (p1,p2) = tuple c (p1 <> t1 p2)
  fun tuple3 c (p1,p2,p3) = tuple c (p1 <> p2 <> t1 p3)
  fun tuple4 c (p1,p2,p3,p4) = tuple c (p1 <> p2 <> p3 <> t1 p4)
end

fun option _ _ 0w0 = NONE
  | option c p w = SOME (p (arg c 0 w))

fun appList _ _ 0w1 = ()
  | appList c go w = case tuple2 c (I, I) w of (a, b) => (go a; appList c go b)

fun appSet c go w = let
  fun go' w = case get64 (obj c w) of f =>
    case f 0 of 0w3 => () | _ => (go' (f 16); go (f 8); go' (f 24))
  in go' (get64 (obj c w) 8) end

fun str objs w = case DArray.sub (objs, ptr w) of
  OBytes slice => slice
| _ => raise Fail "str: parse error"

type ident = string * string
fun ident c w = tuple2 c (str c, str c) (arg c 0 (arg c 0 w))

datatype sh_type =
  Tyapp of ident ptr * hol_type list ptr
| Tyv of string

fun shType c w = case get64 (obj c w) of f =>
  case f 0 of
    0w1 => Tyapp (arg c 0 (f 8), f 16)
  | 0w3 => Tyv (str c (f 8))
  | _ => raise Fail "shType: parse error"

datatype sh_term =
  Abs of term ptr * term ptr
| Bv of int
| Clos of term Subst.subs ptr * term ptr
| Comb of term ptr * term ptr
| Const of ident ptr * hol_type ptr
| Fv of string * hol_type ptr

fun shTerm c w = case get64 (obj c w) of f =>
  case f 0 of
    0w1 => Abs (f 8, f 16)
  | 0w3 => Bv (int (f 8))
  | 0w5 => Clos (f 8, f 16)
  | 0w7 => Comb (f 8, f 16)
  | 0w9 => Const (f 8, arg c 1 (f 16))
  | 0w11 => Fv (str c (f 8), f 16)
  | _ => raise Fail "shTerm: parse error"

datatype 'a sh_subs =
  Cons of 'a Subst.subs ptr * 'a ptr
| Id
| Lift of int * 'a Subst.subs ptr
| Shift of int * 'a Subst.subs ptr

fun shSubs c w = case get64 (obj c w) of f =>
  case f 0 of
    0w1 => Cons (f 8, f 16)
  | 0w3 => Id
  | 0w5 => Lift (int (f 8), f 16)
  | 0w7 => Shift (int (f 8), f 16)
  | _ => raise Fail "shSubs: parse error"

type proof = unit
fun shThm c w = case get64 (obj c w) of f => (f 8, f 16, arg c 0 (f 24))

fun shRoot c w = case get64 (obj c w) of f =>
  { theory = str c (f 0),
    parents = f 8,
    types = f 16,
    constants = f 24,
    all_thms = f 32,
    mldeps = f 40 }

fun shThmInfo c w = {private = arg c 2 w = 0w3}

end
