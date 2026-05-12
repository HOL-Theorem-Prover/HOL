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

(* Heap is a two-variant datatype so the parser can read either the legacy
   64-bit PolyML heap dump or the 32-bit narrow format produced by the
   recoder in Tracing.sml directly, without inflating the 32-bit form into
   a 64-bit byte vector. Each variant carries the raw decompressed bytes
   plus a vector of object-start byte offsets. *)
type heap_data = Word8Vector.vector * int vector
datatype heap = Heap64 of heap_data | Heap32 of heap_data

fun heapSize (Heap64 (_, ptrs)) = Vector.length ptrs
  | heapSize (Heap32 (_, ptrs)) = Vector.length ptrs

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

(* Read a 32-bit little-endian word, sign-extended to 64 bits. Tag-bit
   preservation and negative int decoding both rely on sign extension. *)
fun get32_se vec start = let
  fun b i = Word64.fromInt (Word8.toInt (Word8Vector.sub (vec, start + i)))
  val raw = let open Word64 infix orb <<
            in b 0 orb (b 1 << 0w8) orb (b 2 << 0w16) orb (b 3 << 0w24)
            end
in
  if Word64.andb (raw, 0wx80000000) = 0w0 then raw
  else Word64.orb (raw, 0wxFFFFFFFF00000000)
end

fun get24 vec start = let
  fun b i = Word.fromInt (Word8.toInt (Word8Vector.sub (vec, start + i)))
  open Word infix orb <<
  val w = b 0 orb (b 1 << 0w8) orb (b 2 << 0w16)
  in Word.toInt w end

fun is_32bit_magic raw =
  Word8Vector.length raw >= 4 andalso
  Word8Vector.sub (raw, 0) = 0wxFF andalso
  Word8Vector.sub (raw, 1) = 0w0 andalso
  Word8Vector.sub (raw, 2) = 0w0 andalso
  Word8Vector.sub (raw, 3) = 0w0

(* Parse: detects the magic byte, builds a ptrs vector with the right word
   size, and returns the appropriate heap variant. Both variants share the
   same public API — sh* functions dispatch internally. *)
fun parse filename = let
  val raw = decompressGzip filename
in
  if is_32bit_magic raw then let
    val vec = raw
    val root = Word8Vector.length vec - 4   (* last 4 bytes = root tagptr *)
    val out = DArray.new (64, 0)
    fun process start =
      if start >= root then ()
      else (DArray.push (out, start);
            process (start + 4 * (get24 vec start + 1)))
    val () = process 4   (* skip 4-byte magic at start *)
    val rootPtr = get32_se vec root
  in (rootPtr, Heap32 (vec, DArray.vector out)) end
  else let
    val vec = raw
    val root = Word8Vector.length vec - 8
    val out = DArray.new (64, 0)
    fun process start =
      if start >= root then ()
      else (DArray.push (out, start);
            process (start + 8 * (get56 vec start + 1)))
    val () = process 0
    val rootPtr = get64 vec root
  in (rootPtr, Heap64 (vec, DArray.vector out)) end
end

datatype flags = FBytes of int | FObj of int | FOther

(* Variant-aware flags reader. For 64-bit headers flags are byte 7, length
   is bytes 0..6. For 32-bit headers flags are byte 3, length bytes 0..2.
   The int returned is in the variant's own word unit (8-byte words for
   Heap64, 4-byte words for Heap32). *)
fun flags_of h start = case h of
    Heap64 (vec, _) =>
      (case Word8.andb(Word8Vector.sub (vec, start + 7), 0w3) of
         0w0 => FObj (get56 vec start)
       | 0w1 => FBytes (get56 vec start)
       | _ => FOther)
  | Heap32 (vec, _) =>
      (case Word8.andb(Word8Vector.sub (vec, start + 3), 0w3) of
         0w0 => FObj (get24 vec start)
       | 0w1 => FBytes (get24 vec start)
       | _ => FOther)

fun int w = Int.fromLarge (Word64.toLargeIntX w div 2)
fun ptr w = Word64.toInt (Word64.>>(w, 0w1)) - 1

(* any returns a tagged view of a word. For pointers it dereferences to a
   list of child words. The list walk uses variant-specific word sizes. *)
datatype 'a any = Int of int | Bytes of Word8VectorSlice.slice | Obj of 'a list | Other
fun any h p w =
  if Word64.andb (w, 0w1) = 0w1 then Int (int w)
  else case h of
    Heap64 (vec, ptrs) => let
      val start = Vector.sub (ptrs, ptr w)
    in case flags_of h start of
         FBytes n => Bytes (Word8VectorSlice.slice (vec, start + 8, SOME (8*n)))
       | FOther => Other
       | FObj n =>
           let fun build (i, acc) = if i = start + 8 then acc
                 else case i - 8 of j => build (j, p (get64 vec j) :: acc)
           in Obj (build (start + 8 * (n+1), [])) end
    end
  | Heap32 (vec, ptrs) => let
      val start = Vector.sub (ptrs, ptr w)
    in case flags_of h start of
         FBytes n => Bytes (Word8VectorSlice.slice (vec, start + 4, SOME (4*n)))
       | FOther => Other
       | FObj n =>
           let fun build (i, acc) = if i = start + 4 then acc
                 else case i - 4 of j => build (j, p (get32_se vec j) :: acc)
           in Obj (build (start + 4 * (n+1), [])) end
    end

(* obj'_Regular: given an object pointer index, check the object is a
   Regular, and return (data_start, n_words) where data_start is the byte
   offset just past the header. *)
fun obj' h p = case h of
    Heap64 (vec, ptrs) =>
      (case Vector.sub (ptrs, p) of start =>
       case flags_of h start of
         FObj n => (start + 8, n)
       | _ => raise Fail "parse error")
  | Heap32 (vec, ptrs) =>
      (case Vector.sub (ptrs, p) of start =>
       case flags_of h start of
         FObj n => (start + 4, n)
       | _ => raise Fail "parse error")
fun obj h w = obj' h (ptr w)

(* arg' returns a byte-offset-indexed reader whose indices are in the 64-bit
   reference frame. For 64-bit heaps this is a straight read; for 32-bit
   heaps the byte offset is halved (since all structural offsets are
   multiples of 8) and the value is sign-extended from 32 bits. *)
fun arg' h w =
  let val (start, _) = obj h w in
  case h of
    Heap64 (vec, _) => (fn byte_offset => get64 vec (start + byte_offset))
  | Heap32 (vec, _) => (fn byte_offset => get32_se vec (start + byte_offset div 2))
  end
fun arg h n w = arg' h w (8*n)

fun scan_widths h = let
  val max_ptr = ref 0
  val max_int = ref 0
  val max_obj_len = ref 0
  val (vec, ptrs, word_bytes, read_word_at, read_len_at, flags_byte) =
    case h of
      Heap64 (v, p) => (v, p, 8, get64 v, get56 v, 7)
    | Heap32 (v, p) => (v, p, 4, get32_se v, get24 v, 3)
  val sz = Vector.length ptrs
  fun loop k =
    if k >= sz then () else let
      val start = Vector.sub (ptrs, k)
      val len = read_len_at start
      val flags = Word8.andb (Word8Vector.sub (vec, start + flags_byte), 0w3)
    in
      if len > !max_obj_len then max_obj_len := len else ();
      (* Regular (flags=0): data is tagptr array; Bytes (flags=1): skip; others empty *)
      if flags = 0w0 then let
        fun visit i =
          if i >= len then () else let
            val w = read_word_at (start + word_bytes * (i + 1))
          in
            (if Word64.andb (w, 0w1) = 0w1 then
               let val n = int w
                   val a = if n < 0 then ~n else n
               in if a > !max_int then max_int := a else () end
             else
               let val p = ptr w
               in if p > !max_ptr then max_ptr := p else () end);
            visit (i + 1)
          end
      in visit 0 end
      else ();
      loop (k + 1)
    end
in loop 0;
   {max_ptr = !max_ptr, max_int = !max_int, max_obj_len = !max_obj_len}
end

fun shVariant h w = let
  val (start, n) = obj h w
  val (word_bytes, read) = case h of
      Heap64 (vec, _) => (8, get64 vec)
    | Heap32 (vec, _) => (4, get32_se vec)
  fun build (i, acc) =
    if i = start then (int (read i), acc)
    else build (i - word_bytes, read i :: acc)
in build (start + word_bytes * (n - 1), []) end

(* Tuple-reader combinators. Parser state carries the byte vector, the
   current byte offset within an object, the word size in bytes, and a
   reader function — allowing a single set of combinators to handle both
   heap variants. *)
local
  infixr 9 <>
  fun tuple h p w =
    let val (start, _) = obj h w in
    case h of
      Heap64 (vec, _) => p (vec, start, 8, get64 vec)
    | Heap32 (vec, _) => p (vec, start, 4, get32_se vec)
    end
  fun (p <> q) (vec, i, wb, rd) = (p (rd i), q (vec, i + wb, wb, rd))
  fun t1 p (vec, i, wb, rd) = p (rd i)
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

(* Read a PolyML string object: the object data starts with an 8-byte
   length word followed by that many raw bytes. The length word is always
   stored as 8 bytes in both variants (the recoder preserves bytes
   verbatim for Bytes-kind objects), so we can use get64 on both sides —
   the only difference is the header size. *)
fun str h w = let
  val pidx = ptr w
  val (vec, start, data_off) = case h of
      Heap64 (v, p) => (v, Vector.sub (p, pidx), 8)
    | Heap32 (v, p) => (v, Vector.sub (p, pidx), 4)
  val _ = case flags_of h start of FBytes _ => () | _ => raise Fail "str: parse error"
  val n = Word64.toInt (get64 vec (start + data_off))
  open Word8VectorSlice
  in Byte.bytesToString (vector (slice (vec, start + data_off + 8, SOME n))) end

type ident = string * string
fun ident c w = tuple2 c (str c, str c) (arg c 0 (arg c 0 w))

fun thmId c w = case arg' c w of f =>
  case f 0 of
    0w1 => SavedAnon (int (f 8))
  | 0w3 => SavedName (str c (f 8))
  | _ => raise Fail "thmId: parse error"

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

datatype sh_proof =
  ABS_prf of term ptr * thm ptr
| ALPHA_prf of term ptr * term ptr
| AP_TERM_prf of term ptr * thm ptr
| AP_THM_prf of thm ptr * term ptr
| ASSUME_prf of term ptr
| Axiom_prf
| BETA_CONV_prf of term ptr
| Beta_prf of thm ptr
| CCONTR_prf of term ptr * thm ptr
| CHOOSE_prf of term ptr * thm ptr * thm ptr
| CONJUNCT1_prf of thm ptr
| CONJUNCT2_prf of thm ptr
| CONJ_prf of thm ptr * thm ptr
| DISCH_prf of term ptr * thm ptr
| DISJ1_prf of thm ptr * term ptr
| DISJ2_prf of term ptr * thm ptr
| DISJ_CASES_prf of thm ptr * thm ptr * thm ptr
| Def_const_list_prf of thm ptr * term list ptr
| Def_const_prf of term ptr * term ptr
| Def_spec_prf of thm ptr * term list ptr
| Def_tyop_prf of hol_type list ptr * thm ptr * hol_type ptr
| Disk_prf of string * thm_id ptr
| EQ_IMP_RULE1_prf of thm ptr
| EQ_IMP_RULE2_prf of thm ptr
| EQ_MP_prf of thm ptr * thm ptr
| EXISTS_prf of term ptr * term ptr * thm ptr
| Exported_prf of string * thm_id ptr
| GENL_prf of term list ptr * thm ptr
| GEN_ABS_prf of term option ptr * term list ptr * thm ptr
| GEN_prf of term ptr * thm ptr
| INST_TYPE_prf of (hol_type,hol_type)Lib.subst ptr * thm ptr
| INST_prf of (term,term)Lib.subst ptr * thm ptr
| MK_COMB_prf of thm ptr * thm ptr
| MP_prf of thm ptr * thm ptr
| Mark_prf of string * thm ptr
| Mk_abs_prf of thm ptr * term ptr * thm ptr
| Mk_comb_prf of thm ptr * thm ptr * thm ptr
| NOT_ELIM_prf of thm ptr
| NOT_INTRO_prf of thm ptr
| REFL_prf of term ptr
| SPEC_prf of term ptr * thm ptr
| SUBST_prf of (term,thm)Lib.subst ptr * term ptr * thm ptr
| SYM_prf of thm ptr
| Specialize_prf of term ptr * thm ptr
| TRANS_prf of thm ptr * thm ptr
| compute_prf of (compute_args * thm list) ptr * term ptr
| deductAntisym_prf of thm ptr * thm ptr
| deleted_prf
| save_dep_prf of thm ptr

fun shProof c w = case arg' c w of f =>
  case f 0 of
    0w01 => ABS_prf            (f 8, f 16)
  | 0w03 => ALPHA_prf          (f 8, f 16)
  | 0w05 => AP_TERM_prf        (f 8, f 16)
  | 0w07 => AP_THM_prf         (f 8, f 16)
  | 0w09 => ASSUME_prf         (f 8)
  | 0w11 => Axiom_prf
  | 0w13 => BETA_CONV_prf      (f 8)
  | 0w15 => Beta_prf           (f 8)
  | 0w17 => CCONTR_prf         (f 8, f 16)
  | 0w19 => CHOOSE_prf         (f 8, f 16, f 24)
  | 0w21 => CONJUNCT1_prf      (f 8)
  | 0w23 => CONJUNCT2_prf      (f 8)
  | 0w25 => CONJ_prf           (f 8, f 16)
  | 0w27 => DISCH_prf          (f 8, f 16)
  | 0w29 => DISJ1_prf          (f 8, f 16)
  | 0w31 => DISJ2_prf          (f 8, f 16)
  | 0w33 => DISJ_CASES_prf     (f 8, f 16, f 24)
  | 0w35 => Def_const_list_prf (f 8, f 16)
  | 0w37 => Def_const_prf      (f 8, f 16)
  | 0w39 => Def_spec_prf       (f 8, f 16)
  | 0w41 => Def_tyop_prf       (f 8, f 16, f 24)
  | 0w43 => Disk_prf           (str c (f 8), f 16)
  | 0w45 => EQ_IMP_RULE1_prf   (f 8)
  | 0w47 => EQ_IMP_RULE2_prf   (f 8)
  | 0w49 => EQ_MP_prf          (f 8, f 16)
  | 0w51 => EXISTS_prf         (f 8, f 16, f 24)
  | 0w53 => Exported_prf       (str c (f 8), f 16)
  | 0w55 => GENL_prf           (f 8, f 16)
  | 0w57 => GEN_ABS_prf        (f 8, f 16, f 24)
  | 0w59 => GEN_prf            (f 8, f 16)
  | 0w61 => INST_TYPE_prf      (f 8, f 16)
  | 0w63 => INST_prf           (f 8, f 16)
  | 0w65 => MK_COMB_prf        (f 8, f 16)
  | 0w67 => MP_prf             (f 8, f 16)
  | 0w69 => Mark_prf           (str c (f 8), f 16)
  | 0w71 => Mk_abs_prf         (f 8, f 16, f 24)
  | 0w73 => Mk_comb_prf        (f 8, f 16, f 24)
  | 0w75 => NOT_ELIM_prf       (f 8)
  | 0w77 => NOT_INTRO_prf      (f 8)
  | 0w79 => REFL_prf           (f 8)
  | 0w81 => SPEC_prf           (f 8, f 16)
  | 0w83 => SUBST_prf          (f 8, f 16, f 24)
  | 0w85 => SYM_prf            (f 8)
  | 0w87 => Specialize_prf     (f 8, f 16)
  | 0w89 => TRANS_prf          (f 8, f 16)
  | 0w91 => compute_prf        (f 8, f 16)
  | 0w93 => deductAntisym_prf  (f 8, f 16)
  | 0w95 => deleted_prf
  | 0w97 => save_dep_prf       (f 8)
  | _ => raise Fail "shProof: parse error"

fun shComputeArgs c w = case arg' c w of f =>
  { num_type = f 0,
    char_eqns = f 8,
    cval_type = f 16,
    cval_terms = f 24 }

end
