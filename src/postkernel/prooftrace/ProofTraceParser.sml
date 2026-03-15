structure ProofTraceParser :> ProofTraceParser = struct

open Lib Type Term Thm RawTheory_dtype

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
type heap = Word8Vector.vector * int vector
fun heapSize (_, ptrs) = Vector.length ptrs
val castPtr = I
fun isPtr w = Word64.andb(w, 0w1) = 0w0

fun get64 vec start = let
  fun b i = Word64.fromInt (Word8.toInt (Word8Vector.sub (vec, start + i)))
  open Word64 infix orb <<
  in b 0          orb (b 1 << 0w08) orb (b 2 << 0w16) orb (b 3 << 0w24) orb
    (b 4 << 0w32) orb (b 5 << 0w40) orb (b 6 << 0w48) orb (b 7 << 0w56) end

fun get56 vec start = let
  fun b i = Word.fromInt (Word8.toInt (Word8Vector.sub (vec, start + i)))
  open Word infix orb <<
  val w = b 0     orb (b 1 << 0w8)  orb (b 2 << 0w16) orb (b 3 << 0w24) orb
    (b 4 << 0w32) orb (b 5 << 0w40) orb (b 6 << 0w48)
  in Word.toInt w end

fun parse filename = let
  val vec = decompressGzip filename
  val root = Word8Vector.length vec - 8
  val out = DArray.new (64, 0)
  fun process start = if start >= root then () else
    (DArray.push (out, start); process (start + 8 * (get56 vec start + 1)))
  in process 0; (get64 vec root, (vec, DArray.vector out)) end

datatype flags = FBytes of int | FObj of int | FOther
fun flags vec start =
  case Word8.andb(Word8Vector.sub (vec, start + 7), 0w3) of
    0w0 => FObj (get56 vec start)
  | 0w1 => FBytes (get56 vec start)
  | _ => FOther

fun int w = Int.fromLarge (Word64.toLargeIntX w div 2)
fun ptr w = Word64.toInt (Word64.>>(w, 0w1)) - 1

datatype 'a any = Int of int | Bytes of Word8VectorSlice.slice | Obj of 'a list | Other
fun any (vec, ptrs) p w =
  if Word64.andb (w, 0w1) = 0w1 then Int (int w) else
  case Vector.sub (ptrs, ptr w) of start =>
  case flags vec start of
    FBytes n => Bytes (Word8VectorSlice.slice (vec, start, SOME (8*n)))
  | FOther => Other
  | FObj n => let
    fun build (i, acc) = if i = start then acc else case i - 8 of i =>
      build (i, p (get64 vec i) :: acc)
    in Obj (build (start + 8 * n, [])) end

fun obj' (vec, ptrs) p =
  case Vector.sub (ptrs, p) of start =>
  case flags vec start of
    FObj n => (start + 8, n)
  | _ => raise Fail "parse error"
fun obj c w = obj' c (ptr w)
fun arg' (c as (vec, _)) w = case #1 (obj c w) of start => fn n => get64 vec (start + n)
fun arg c n w = arg' c w (8*n)

fun shVariant (c as (vec, _)) w = let
  val (start, n) = obj c w
  fun build (i, acc) = if i = start then (int (get64 vec i), acc) else
    build (i - 8, get64 vec i :: acc)
  in build (start + 8 * (n - 1), []) end

local
  fun tuple c p w = p (#1 c, #1 (obj c w))
  infixr 9 <>
  fun (p <> q) (vec, i) = (p (get64 vec i), q (vec, i + 8))
  fun t1 p (vec, i) = p (get64 vec i)
in
  fun tuple2 c (p1,p2) = tuple c (p1 <> t1 p2)
  fun tuple3 c (p1,p2,p3) = tuple c (p1 <> p2 <> t1 p3)
  fun tuple4 c (p1,p2,p3,p4) = tuple c (p1 <> p2 <> p3 <> t1 p4)
end

fun option _ _ 0w0 = NONE
  | option c p w = SOME (p (arg' c w 0))

fun list c go w = let
  fun build (0w1, acc) = rev acc
    | build (w, acc) = case tuple2 c (I, I) w of (a, b) => (build (b, go a :: acc))
  in build (w, []) end

fun appList _ _ 0w1 = ()
  | appList c go w = case tuple2 c (I, I) w of (a, b) => (go a; appList c go b)

fun appSet c go w = let
  fun go' w = case arg' c w of f =>
    case f 0 of 0w3 => () | _ => (go' (f 16); go (f 8); go' (f 24))
  in go' (arg' c w 8) end

fun str (vec, ptrs) w = let
  val start = Vector.sub (ptrs, ptr w)
  val _ = case flags vec start of FBytes _ => () | _ => raise Fail "str: parse error"
  val n = Word64.toInt (get64 vec (start + 8))
  open Word8VectorSlice
  in Byte.bytesToString (vector (slice (vec, start + 16, SOME n))) end

type ident = string * string
fun ident c w = tuple2 c (str c, str c) (arg c 0 (arg c 0 w))

datatype sh_type =
  Tyapp of ident ptr * hol_type list ptr
| Tyv of string

fun shType c w = case arg' c w of f =>
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

fun shTerm c w = case arg' c w of f =>
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

fun shSubs c w = case arg' c w of f =>
  case f 0 of
    0w1 => Cons (f 8, f 16)
  | 0w3 => Id
  | 0w5 => Lift (int (f 8), f 16)
  | 0w7 => Shift (int (f 8), f 16)
  | _ => raise Fail "shSubs: parse error"

type proof = unit
fun shThm c w = case arg' c w of f => (f 8, f 16, arg c 0 (f 24))

fun shRoot c w = case arg' c w of f =>
  { types = f 0,
    mldeps = f 8,
    theory = str c (f 16),
    parents = f 24,
    all_thms = f 32,
    anon_thms = f 40,
    constants = f 48 }

fun shThmInfo c w = {private = arg c 2 w = 0w3}

end
