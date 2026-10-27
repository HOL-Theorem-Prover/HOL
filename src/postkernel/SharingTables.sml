structure SharingTables :> SharingTables =
struct

open Term Type DB_dtype RawTheoryReader
infix |>
fun x |> f = f x

exception SharingTables of string

type id = {Thy : string, Other : string}
fun id_compare ({Other = id1, Thy = thy1}, {Other = id2, Thy = thy2}) =
    case String.compare(id1, id2) of
      EQUAL => String.compare(thy1, thy2)
    | x => x

structure Idtab = Table(
  type key = id
  val ord = id_compare
  fun pp ({Thy, Other} : id) = HOLPP.add_string (Thy ^ "$" ^ Other)
)
type 'a idtab = 'a Idtab.table

type 'a sexppr = 'a -> HOLsexp.t

(* ----------------------------------------------------------------------
    string sharing table
   ---------------------------------------------------------------------- *)

type stringtable =
     {size : int, map : int Symtab.table, list : string list}
type idtable = {idsize : int,
                idmap : int idtab,
                idlist : (int * int) list}

val empty_strtable : stringtable =
    {size = 0, map = Symtab.empty, list = []}

local
  open HOLsexp
in
fun enc_strtable (strtable : stringtable) =
    tagged_encode "string-table" (list_encode String)
                  (List.rev (#list strtable))
fun enc_idtable (idtable : idtable) =
    tagged_encode "id-table" (list_encode (pair_encode(Integer,Integer)))
                  (List.rev (#idlist idtable))
fun dec_ids strv =
    Option.map (Vector.fromList o
                map (fn (i,j) => {Thy = Vector.sub(strv,i),
                                  Other = Vector.sub(strv,j)})) o
    tagged_decode "id-table" (list_decode (pair_decode(int_decode,int_decode)))

end (* local *)


fun new_string s (strtable as {size,list,map}:stringtable) =
    case Symtab.lookup map s of
        SOME i => (i, strtable)
      | NONE => (size, {size = size + 1,
                        list = s :: list,
                        map = Symtab.update (s, size) map})

(* ----------------------------------------------------------------------
    IDs (also known as Theory-X pairs, where X is a Name for a constant,
    or Tyops for types)
   ---------------------------------------------------------------------- *)


fun make_shared_id (id as {Thy,Other} : id) (strtable, idtable) =
    case Idtab.lookup (#idmap idtable) id of
      SOME i => (i, strtable, idtable)
    | NONE => let
        val {idsize, idmap, idlist} = idtable
        val (thyi, strtable) = new_string Thy strtable
        val (otheri, strtable) = new_string Other strtable
      in
        (idsize, strtable,
         {idsize = idsize + 1, idmap = Idtab.update (id, idsize) idmap,
          idlist = (thyi,otheri) :: idlist})
      end

val empty_idtable : idtable = {idsize = 0,
                               idmap = Idtab.empty,
                               idlist = []}


fun build_id_vector strings intpairs =
    Vector.fromList
      (map (fn (thyi,otheri) => {Thy = Vector.sub(strings,thyi),
                                 Other = Vector.sub(strings,otheri)})
           intpairs)


(* ----------------------------------------------------------------------
    Types
   ---------------------------------------------------------------------- *)

open RawTheory_dtype

type typetable = {tysize : int,
                  tymap : int Typetab.table,
                  tylist : raw_type list}

local
  open HOLsexp
in

val enc_tytable : typetable encoder =
    tagged_encode "type-table" (list_encode raw_type_encode) o List.rev o
    #tylist

end (* local *)

fun make_raw_type ty strtable idtable table =
    case Typetab.lookup (#tymap table) ty of
      SOME i => (i, strtable, idtable, table)
    | NONE => let
      in
        if is_vartype ty then let
            val {tysize, tymap, tylist} = table
          in
            (tysize, strtable, idtable,
             {tysize = tysize + 1,
              tymap = Typetab.update (ty, tysize) tymap,
              tylist = TYV (dest_vartype ty) :: tylist})
          end
        else let
            val {Thy, Tyop, Args} = dest_thy_type ty
            val (id, strtable0, idtable0) =
                make_shared_id {Thy = Thy, Other = Tyop} (strtable, idtable)
            fun foldthis (tyarg, (results, strtable, idtable, table)) = let
              val (result, strtable', idtable', table') =
                  make_raw_type tyarg strtable idtable table
            in
              (result::results, strtable', idtable', table')
            end
            val (newargs, strtable', idtable', table') =
                List.foldr foldthis ([], strtable0, idtable0, table) Args
            val {tysize, tymap, tylist} = table'
          in
            (tysize, strtable', idtable',
             {tysize = tysize + 1,
              tymap = Typetab.update (ty, tysize) tymap,
              tylist = TYOP {opn = id, args = newargs} :: tylist})
          end
      end

val empty_tytable : typetable =
    {tysize = 0, tymap = Typetab.empty, tylist = [] }

fun build_type_vector idv shtylist = let
  fun build1 (shty, (n, tymap)) =
      case shty of
        TYV s => (n + 1, Inttab.update (n, Type.mk_vartype s) tymap)
      | TYOP {opn,args} => let
          fun mapthis i =
              case Inttab.lookup tymap i of
                  SOME t => t
                | NONE =>
                  raise SharingTables ("build_type_vector: (" ^
                                       String.concatWith " "
                                             (map Int.toString args) ^
                                       "), " ^ Int.toString i ^
                                       " not found")
          val args = map mapthis args
          val {Thy,Other} = Vector.sub(idv, opn)
        in
          (n + 1,
           Inttab.update
             (n, Type.mk_thy_type {Thy = Thy, Tyop = Other, Args = args}) tymap)
        end
  val (_, tymap) = List.foldl build1 (0, Inttab.empty) shtylist
in
  Vector.fromList (map #2 (Inttab.dest tymap))
end

(* ----------------------------------------------------------------------
    Terms
   ---------------------------------------------------------------------- *)

type termtable = {termsize : int,
                  termmap : int Termtab.table,
                  termlist : raw_term list}

local
  open HOLsexp
in

val enc_tmtable : termtable encoder =
    tagged_encode "term-table" (list_encode raw_term_encode) o
    List.rev o #termlist
end (* local *)

val empty_termtable : termtable =
    {termsize = 0, termmap = Termtab.empty, termlist = [] }

fun make_raw_term tm (tables as (strtable,idtable,tytable,tmtable)) =
    case Termtab.lookup (#termmap tmtable) tm of
      SOME i => (i, tables)
    | NONE => let
      in
        if is_var tm then let
            val (s, ty) = dest_var tm
            val (ty_i, strtable, idtable, tytable) =
                make_raw_type ty strtable idtable tytable
            val {termsize, termmap, termlist} = tmtable
          in
            (termsize,
             (strtable, idtable, tytable,
              {termsize = termsize + 1,
               termmap = Termtab.update (tm, termsize) termmap,
               termlist = TMV (s, ty_i) :: termlist}))
          end
        else if is_const tm then let
            val {Thy,Name,Ty} = dest_thy_const tm
            val (id_i, strtable, idtable) =
                make_shared_id {Thy = Thy, Other = Name} (strtable, idtable)
            val (ty_i, strtable, idtable, tytable) =
                make_raw_type Ty strtable idtable tytable
            val {termsize, termmap, termlist} = tmtable
          in
            (termsize,
             (strtable, idtable, tytable,
              {termsize = termsize + 1,
               termmap = Termtab.update (tm, termsize) termmap,
               termlist = TMC (id_i, ty_i) :: termlist}))
          end
        else if is_comb tm then let
            val (f, x) = dest_comb tm
            val (f_i, tables) = make_raw_term f tables
            val (x_i, tables) = make_raw_term x tables
            val (strtable, idtable, tytable, tmtable) = tables
            val {termsize, termmap, termlist} = tmtable
          in
            (termsize,
             (strtable, idtable, tytable,
              {termsize = termsize + 1,
               termmap = Termtab.update (tm, termsize) termmap,
               termlist = TMAp(f_i, x_i) :: termlist}))
          end
        else  (* must be an abstraction *) let
            val (v, body) = dest_abs tm
            val (v_i, tables) = make_raw_term v tables
            val (body_i, tables) = make_raw_term body tables
            val (strtable, idtable, tytable, tmtable) = tables
            val {termsize, termmap, termlist} = tmtable
          in
            (termsize,
             (strtable, idtable, tytable,
              {termsize = termsize + 1,
               termmap = Termtab.update (tm, termsize) termmap,
               termlist = TMAbs(v_i, body_i) :: termlist}))
          end
      end

fun build_term_vector idv tyv shtmlist = let
  fun lookup tmmap i =
      case Inttab.lookup tmmap i of
          SOME t => t
        | NONE => raise SharingTables ("build_term_vector: " ^
                                       Int.toString i ^ " not found")
  fun build1 (shtm, (n, tmmap)) =
      case shtm of
        TMV (s, tyn) => (n + 1,
                         Inttab.update
                            (n, mk_var(s, Vector.sub(tyv, tyn))) tmmap)
      | TMC (idn, tyn) => let
          val {Thy, Other} = Vector.sub(idv, idn)
          val ty = Vector.sub(tyv, tyn)
        in
          (n + 1, Inttab.update
                    (n, mk_thy_const {Name = Other, Thy = Thy,
                                      Ty = ty}) tmmap)
        end
      | TMAp (f_n, xn) =>
        (n + 1, Inttab.update
                  (n, mk_comb(lookup tmmap f_n, lookup tmmap xn)) tmmap)
      | TMAbs (vn, bodyn) =>
        (n + 1, Inttab.update
                  (n, mk_abs(lookup tmmap vn, lookup tmmap bodyn)) tmmap)
  val (_, tmmap) = List.foldl build1 (0, Inttab.empty) shtmlist
in
  Vector.fromList (map #2 (Inttab.dest tmmap))
end

(* ----------------------------------------------------------------------
    sharing table data more abstractly
   ---------------------------------------------------------------------- *)

type extract_data =
 {named_terms : (string * Term.term) list,
  unnamed_terms : Term.term list,
  named_types : (string * Type.hol_type) list,
  unnamed_types : Type.hol_type list,
  theorems : (string * Thm.thm * thminfo) list}

datatype sharing_data_in = SDI of {strtable : stringtable,
                                   idtable : idtable,
                                   tytable : typetable,
                                   tmtable : termtable,
                                   exp : extract_data}

fun empty_in exp = SDI{strtable = empty_strtable,
                       idtable = empty_idtable,
                       tytable = empty_tytable,
                       tmtable = empty_termtable,
                       exp = exp}

fun add_strings strs (SDI {strtable,idtable,tytable,tmtable,exp}) =
    let fun str1 (s, tab) = #2 (new_string s tab)
        val strtable = List.foldl str1 strtable strs
    in
      SDI{strtable = strtable, idtable = idtable, tytable = tytable,
          tmtable = tmtable, exp = exp}
    end

fun add_types tys (SDI{strtable,idtable,tytable,tmtable,exp}) =
    let
      fun dotypes (ty, (strtable, idtable, tytable)) = let
        val (_, strtable, idtable, tytable) =
            make_raw_type ty strtable idtable tytable
      in
        (strtable, idtable, tytable)
      end
      val (strtable,idtable,tytable) =
          List.foldl dotypes (strtable, idtable, tytable) tys
    in
      SDI{strtable = strtable, idtable = idtable, tytable = tytable,
          tmtable = tmtable, exp = exp}
    end

(* Which compound subterms get an entry in the term table of a theory file.

   Only abstraction-free compound terms are candidates: the table identifies
   alpha-equivalent terms (Term.compare ignores bound variable names), so a
   shared lambda would come back with the bound variable names of its first
   occurrence, and scripts can depend on those names (strip_tac, for one).

   A candidate with n >= 2 references (a reference is one place in the graph
   of distinct subterms that mentions it) is shared when the characters saved,
   (n - 1) * (length of its expansion - length of a reference), exceed the
   size of the table entries it needs: its own, plus those of any descendants
   that are not in the table yet (an entry names its children by index).
   Children come before parents.  HOL_SHARE_SUBTERMS=0 turns this off.

   Identifying equal subterms by Term.compare costs time proportional to the
   size of the terms compared whenever two equal subterms are different heap
   objects, which is quadratic on deep terms.  Instead the distinct subterms
   are numbered ("hash-consed") in one bottom-up walk over the term tree: a
   compound term is identified by the pair of the numbers of its two
   children.  The walk also records, for every position of the tree in
   pre-order, the number and the size of the subterm there, so the writer can
   decide at each position whether to write a reference, without hashing again.
   All per-node storage is in byte arrays (32-bit entries), which the garbage
   collector does not scan. *)
val share_subterms =
    case OS.Process.getEnv "HOL_SHARE_SUBTERMS" of
        SOME "0" => false
      | _ => true

val ref_len = 4        (* "%123" *)
val entry_len = 13     (* "(ap 123 456)" and a separator *)

structure HashCons =
struct

(* 32-bit little-endian words in a byte array, indexed by word *)
fun get32 (a : Word8Array.array, i) =
    let fun b k = Word8.toInt (Word8Array.sub (a, 4 * i + k))
    in b 0 + 256 * (b 1 + 256 * (b 2 + 256 * b 3)) end
fun set32 (a : Word8Array.array, i, v) =
    let fun put (k, x) =
            Word8Array.update (a, 4 * i + k, Word8.fromInt (x mod 256))
    in put (0, v); put (1, v div 256); put (2, v div 65536);
       put (3, v div 16777216) end

(* growable arrays of 32-bit words, in byte arrays *)
structure PA =
struct
  type t = Word8Array.array ref
  fun new () : t = ref (Word8Array.array (4096, 0w0))
  fun cap (a : t) = Word8Array.length (!a) div 4
  fun ensure (a : t) i =
      if i >= cap a then
        let val b = Word8Array.array (4 * Int.max (2 * cap a, i + 1), 0w0)
        in Word8Array.copy {src = !a, dst = b, di = 0}; a := b end
      else ()
  fun get (a : t) i =
      if i < cap a then get32 (!a, i)
      else 0
  fun set (a : t) i v =
      (ensure a i;
       set32 (!a, i, v))
  fun clear (a : t) = a := Word8Array.array (4096, 0w0)
end

(* low 3 bits: 0 atom, 1 comb, 3 abs, 4 bv; bit 3: contains an abstraction *)
val kind = ref (Word8Array.array (1, 0w0))
fun kset i k =
    (if i >= Word8Array.length (!kind) then
       let val b = Word8Array.array
                     (Int.max (2 * Word8Array.length (!kind), i + 1), 0w0)
       in Word8Array.copy {src = !kind, dst = b, di = 0}; kind := b end
     else ();
     Word8Array.update (!kind, i, Word8.fromInt k))
fun kget i =
    if i < Word8Array.length (!kind)
    then Word8.toInt (Word8Array.sub (!kind, i)) else 0
fun kindof i = kget i mod 8
fun abof i = kget i >= 8

val ca = PA.new () and cb = PA.new ()
val n = ref 0

fun newnode k a b abflag =
    let val i = !n
    in
      kset i (k + (if abflag then 8 else 0));
      PA.set ca i a; PA.set cb i b; n := i + 1; i
    end
fun aof i = PA.get ca i
fun bof i = PA.get cb i

(* hash table of node ids (id + 1; 0 = empty), keyed by (tag, a, b) *)
val slots = PA.new ()
val hsize = ref 0
val hcount = ref 0
fun hhash tag a b size =
    let val w = Word.orb (Word.<< (Word.fromInt tag, 0w60),
                          Word.orb (Word.<< (Word.fromInt a, 0w30),
                                    Word.fromInt b))
    in Word.toInt (Word.andb (Word.>> (Word.* (w, 0wx9E3779B97F4A7), 0w17),
                              Word.fromInt (size - 1))) end
fun hrebuild newsize =
    let
      val old = !hsize
      val oldslots = !slots
      val ns = Word8Array.array (4 * newsize, 0w0)
      fun put i =       (* insert node i into the new slot array *)
          let
            val tag = kindof i
            val s0 = hhash (if tag = 3 then 1 else 0) (aof i) (bof i) newsize
            fun probe s =
                if get32 (ns, s) = 0 then s
                          else probe ((s + 1) mod newsize)
          in
            set32 (ns, probe s0, i + 1)
          end
      fun scan s = if s >= old then ()
                   else (let val v = get32 (oldslots, s)
                         in if v <> 0 then put (v - 1) else () end;
                         scan (s + 1))
    in
      scan 0; slots := ns; hsize := newsize
    end
fun hfind tag a b create =
    let
      val _ = if !hsize = 0 then (slots := Word8Array.array (4 * 1048576, 0w0);
                                  hsize := 1048576)
              else if 2 * (!hcount + 1) > !hsize then hrebuild (2 * !hsize)
              else ()
      val size = !hsize
      val arr = !slots
      val nodetag = if tag = 1 then 3 else 1
      fun probe s =
          let val v = get32 (arr, s)
          in
            if v = 0 then
              let val id = create ()
              in set32 (arr, s, id + 1);
                 hcount := !hcount + 1; id end
            else if kindof (v - 1) = nodetag andalso aof (v - 1) = a andalso
                    bof (v - 1) = b
            then v - 1
            else probe ((s + 1) mod size)
          end
    in probe (hhash tag a b size) end

val atoms = ref (Termtab.empty : int Termtab.table)
val atomlist = ref ([] : term list)
val bvs = ref (Array.array (16, ~1))
val tys = ref (Typetab.empty : int Typetab.table)
val ntys = ref 0
val lastty = ref (NONE : (hol_type * int) option)
val tbl = PA.new ()        (* table index + 1, 0 = none *)
val pids = PA.new () and psize = PA.new ()
val top = ref 0
(* root and its base position *)
val roots = ref ([] : (term * int) list)

val abuckets = ref (Array.array (65536, [] : (term * int) list))

fun reset () =
    (n := 0; hcount := 0; hsize := 0; PA.clear slots;
     abuckets := Array.array (65536, []); atomlist := [];
     bvs := Array.array (16, ~1);
     tys := Typetab.empty; ntys := 0; lastty := NONE;
     PA.clear tbl; PA.clear pids; PA.clear psize; PA.clear ca; PA.clear cb;
     kind := Word8Array.array (1, 0w0); top := 0; roots := [])

(* atoms: hash of the name, then a short bucket checked by pointer equality
   and Term.compare *)
fun strhash str =
    let val n = size str
        fun go i h = if i >= n then h
                     else go (i + 1) (Word.xorb (Word.* (h, 0w31),
                                                 Word.fromInt
                                                   (Char.ord
                                                      (String.sub (str, i)))))
    in go 0 0w5381 end
fun atomhash t =
    Word.toInt (Word.andb (strhash (if is_const t then #Name (dest_thy_const t)
                                    else #1 (dest_var t)), 0wxFFFF))
fun atomid t =
    let
      val h = atomhash t
      val bucket = Array.sub (!abuckets, h)
      fun find [] = NONE
        | find ((t', i) :: r) =
          if Portable.pointer_eq (t, t') orelse Term.compare (t, t') = EQUAL
          then SOME i else find r
    in
      case find bucket of
          SOME i => i
        | NONE => let val i = newnode 0 0 0 false
                  in Array.update (!abuckets, h, (t, i) :: bucket);
                     atomlist := t :: !atomlist; i end
    end
fun bvid j =
    let
      val _ = if j >= Array.length (!bvs) then
                let val b = Array.array
                              (Int.max (2 * Array.length (!bvs), j + 1), ~1)
                in Array.copy {src = !bvs, dst = b, di = 0}; bvs := b end
              else ()
      val v = Array.sub (!bvs, j)
    in
      if v >= 0 then v
      else let val i = newnode 4 j 0 false in Array.update (!bvs, j, i); i end
    end
fun typeid ty =
    case !lastty of
        SOME (t, i) => if Portable.pointer_eq (t, ty) then i else typeid2 ty
      | NONE => typeid2 ty
and typeid2 ty =
    let val i = case Typetab.lookup (!tys) ty of
                    SOME i => i
                  | NONE => let val i = !ntys
                            in
                              tys := Typetab.update (ty, i) (!tys);
                              ntys := i + 1; i
                            end
    in lastty := SOME (ty, i); i end
fun combid a b =
    hfind 0 a b (fn () => newnode 1 a b (abof a orelse abof b))
fun absid tyi bi =
    hfind 1 tyi bi (fn () => newnode 3 tyi bi true)

(* the callbacks of Term.raw_fold: each node records its id and the size of
   its subtree at its position *)
fun setp p id sz = (PA.set pids p id; PA.set psize p sz; id)
val callbacks =
    {atom = fn p => fn t => setp p (atomid t) 1,
     bv = fn p => fn j => setp p (bvid j) 1,
     comb = fn p => fn a => fn b =>
               let val sa = PA.get psize (p + 1)
                   val sb = PA.get psize (p + 1 + sa)
               in setp p (combid a b) (1 + sa + sb) end,
     abs = fn p => fn v => fn bi =>
              setp p (absid (typeid (type_of v)) bi)
                   (2 + PA.get psize (p + 2))}

fun walk_root t =
    let
      val base = !top
      val id = Term.raw_fold callbacks base t
      val sz = PA.get psize base
    in
      top := base + sz; roots := (t, base) :: !roots; id
    end

fun add_terms tms sdi =
    let
      val SDI{tmtable = {termsize = ts0, ...}, ...} = sdi
      (* a new export starts from an empty table; later calls extend it *)
      val _ = if ts0 = 0 then reset () else ()
      val _ = atomlist := []
      val rootids = map walk_root tms
      val nn = !n
      val refs = PA.new ()
      fun bump i = PA.set refs i (PA.get refs i + 1)
      val _ = app bump rootids
      fun back i = if i < 0 then ()
                   else (if kindof i = 1 andalso PA.get refs i > 0
                         then (bump (aof i); bump (bof i)) else ();
                         back (i - 1))
      val _ = back (nn - 1)
      val expand = PA.new () and bring = PA.new ()
      val intable = Word8Array.array (nn + 1, 0w0)
      fun isin c = Word8Array.sub (intable, c) <> 0w0
      fun elen c = if kindof c = 1 andalso not (isin c) then PA.get expand c
                   else ref_len
      fun bringcost c = if kindof c = 1 andalso not (isin c)
                        then PA.get bring c else 0
      (* post-order of first visit over comb edges from the roots *)
      val seen = Word8Array.array (nn + 1, 0w0)
      val order = PA.new ()
      val norder = ref 0
      fun dfs i =
          if kindof i = 1 andalso Word8Array.sub (seen, i) = 0w0 then
            (Word8Array.update (seen, i, 0w1); dfs (aof i); dfs (bof i);
             PA.set order (!norder) i; norder := !norder + 1)
          else ()
      val _ = app dfs rootids
      val shared = PA.new ()
      val nshared = ref 0
      fun decide k =
          if k >= !norder then ()
          else
            let val i = PA.get order k
            in
              (if not (abof i) then
                 let
                   val el = elen (aof i) + elen (bof i) + 2
                   val bc = entry_len + bringcost (aof i) + bringcost (bof i)
                   val r = PA.get refs i
                 in
                   PA.set expand i el; PA.set bring i bc;
                   if r >= 2 andalso (r - 1) * (el - ref_len) > bc
                   then (Word8Array.update (intable, i, 0w1);
                         PA.set shared (!nshared) i; nshared := !nshared + 1)
                   else ()
                 end
               else ());
              decide (k + 1)
            end
      val _ = decide 0
      val SDI{strtable, idtable, tytable, tmtable, exp} = sdi
      val atomsl = Listsort.sort Term.compare (!atomlist)
      val (strtable, idtable, tytable, tmtable) =
          List.foldl (fn (t, tabs) => #2 (make_raw_term t tabs))
                     (strtable, idtable, tytable, tmtable) atomsl
      val _ = app (fn t => PA.set tbl (atomid t)
                                  (valOf (Termtab.lookup (#termmap tmtable) t)
                                   + 1))
                  atomsl
      val ts = ref (#termsize tmtable)
      val tl = ref (#termlist tmtable)
      fun addEntry i =
          let val x = PA.get tbl i
          in
            if x > 0 then x - 1
            else
              let
                val ia = addEntry (aof i)
                val ib = addEntry (bof i)
                val idx = !ts
              in
                tl := TMAp (ia, ib) :: !tl; ts := idx + 1;
                PA.set tbl i (idx + 1); idx
              end
          end
      fun entries k = if k >= !nshared then ()
                      else (ignore (addEntry (PA.get shared k));
                            entries (k + 1))
      val _ = entries 0
    in
      SDI {strtable = strtable, idtable = idtable, tytable = tytable,
              tmtable = {termsize = !ts, termmap = #termmap tmtable,
                         termlist = !tl},
              exp = exp}
    end

(* the writer: pre-order walk over the recorded positions *)
fun tblidx i = PA.get tbl i - 1
fun pid p = PA.get pids p
fun psz p = PA.get psize p

fun write tm =
    let
      val base =
          case List.find (fn (o', _) => Portable.pointer_eq (o', tm))
                         (!roots) of
              SOME (_, base) => base
            | NONE => (* not a root of any add_terms call: walk it now *)
              let val _ = walk_root tm
                  val (_, base) = hd (!roots)
              in base end
      fun shared p = let val x = tblidx (pid p)
                     in if x >= 0 then SOME x else NONE end
    in Term.write_raw_at {shared = shared, size = psz} base tm end


end (* HashCons *)

fun add_terms_plain tms (SDI{strtable,idtable,tytable,tmtable,exp}) =
    let
      val atoms = Term.all_atomsl tms empty_tmset |> HOLset.listItems
      val (strtable,idtable,tytable,tmtable) =
          List.foldl (fn (t,tables) => #2 (make_raw_term t tables))
                     (strtable,idtable,tytable,tmtable)
                     atoms
    in
      SDI{strtable = strtable, idtable = idtable, tytable = tytable,
          tmtable = tmtable, exp = exp}
    end

fun add_terms tms sdi =
    if share_subterms then HashCons.add_terms tms sdi
    else add_terms_plain tms sdi

fun thm_atoms acc th = Term.all_atomsl (Thm.concl th :: Thm.hyp th) acc

fun thml_atoms thlist acc =
    case thlist of
      [] => acc
    | (th::ths) => thml_atoms ths (thm_atoms acc th)

fun enc_dep findstr ((s,n),dl) =
    let open HOLsexp
        fun f (thy,l) = Cons(findstr thy, list_encode Integer l)
    in
      list_encode f ((s,[n]) :: dl)
    end

fun dest_dep d =
    case d of
        Dep.DEP_SAVED (did,thydl) => (did,thydl)
      | Dep.DEP_UNSAVED dl => raise SharingTables "Can't encode unsaved dep"

fun enc_tag findstr tag =
    let open HOLsexp
        val dep = Tag.dep_of tag
        val ocl = #1 (Tag.dest_tag tag)
    in
      pair_encode(enc_dep findstr o dest_dep, list_encode String) (dep,ocl)
    end

fun path_strings ps = let val {arcs,vol,...} = OS.Path.fromString ps
                      in
                        vol :: arcs
                      end

fun thminfo_strings ({loc,...}: thminfo) =
    case loc of
        Unknown => []
      | Located {scriptpath,...} => path_strings scriptpath


fun thm_strings (_ (* name *),th,i) =
    let val (sn, dl) = dest_dep (Tag.dep_of (Thm.tag th) )
    in
      #1 sn :: map #1 dl @ thminfo_strings i
    end

fun build_sharing_data (ed : extract_data) =
    let
      val {named_types, named_terms, unnamed_types, unnamed_terms, theorems} =
          ed
      val sdi = empty_in ed
                         |> add_types (map #2 named_types)
                         |> add_types unnamed_types
      val tms =
          List.concat (map (fn (_, th, _) => Thm.concl th :: Thm.hyp th)
                           theorems) @
          unnamed_terms @ map #2 named_terms
    in
      sdi |> add_terms tms
          |> add_strings (map #1 theorems)
          |> add_strings (List.concat (map thm_strings theorems))
    end

fun write_string (SDI{strtable,...}) s =
    case Symtab.lookup (#map strtable) s of
        SOME i => i
      | NONE => raise SharingTables
                        ("write_string: can't find \"" ^ s ^ "\"")
fun write_type (SDI{tytable,...}) ty =
    case Typetab.lookup (#tymap tytable) ty of
        SOME i => i
      | NONE => raise SharingTables "write_type: can't find type"
fun write_term (SDI{tmtable,...}) tm =
    if share_subterms then HashCons.write tm
    else
      Term.write_raw
        (fn t => case Termtab.lookup (#termmap tmtable) t of
                     SOME i => i
                   | NONE => raise SharingTables "write_term: can't find term")
        tm
      handle Feedback.HOL_ERR _ =>
             raise SharingTables "write_term: can't find term"

fun enc_thminfo findstr {private,loc,class} =
    let open HOLsexp
        val privtag = Integer (if private then 1 else 0)
        val classtag = Integer (case class of Axm => 0 | Def => 1 | Thm => 2)
    in
      case loc of
          Unknown => List [classtag, privtag]
        | Located{scriptpath,linenum,exact} =>
          let val {vol,arcs,...} = OS.Path.fromString scriptpath
              val tag = Integer (if exact then 1 else 0)
          in
            List (classtag :: privtag :: tag :: Integer linenum ::
                  map findstr (vol::arcs))
          end
    end

fun enc_sdata (sd as SDI{strtable,idtable,tytable,tmtable,exp}) =
    let
      open HOLsexp
      val {unnamed_types,named_types,unnamed_terms,named_terms,theorems} = exp
      val find_str = Integer o write_string sd
      val ty_encode = Integer o write_type sd
      val tm_encode = String o write_term sd

      fun enc_thm(s,th,info) =
          let
            val (tag, asl, w) = (Thm.tag th, Thm.hyp th, Thm.concl th)
            val i = case Symtab.lookup (#map strtable) s of
                        SOME i => i
                      | NONE => raise SharingTables
                                        ("enc_thm: can't find \"" ^ s ^ "\"")
          in
            pair4_encode
              (Integer,
               enc_tag find_str,
               enc_thminfo find_str,
               list_encode tm_encode)
              (i, tag, info, w::asl)
          end
    in

      tagged_encode "core-data" (
        pair_encode (
          tagged_encode "tables" (
            pair4_encode(enc_strtable,enc_idtable,enc_tytable,enc_tmtable)
          ),
          tagged_encode "exports" (
            pair3_encode(
              pair_encode( (* types *)
                list_encode ty_encode,
                list_encode (pair_encode(String,ty_encode))
              ),
              pair_encode( (* terms *)
                list_encode tm_encode,
                list_encode (pair_encode(String,tm_encode))
              ),
              list_encode enc_thm
            )
          )
        )
      ) ((strtable,idtable,tytable,tmtable),
         ((unnamed_types, named_types), (unnamed_terms, named_terms), theorems))
    end

type sharing_data_out =
     (string Vector.vector * id Vector.vector * Type.hol_type Vector.vector *
      Term.term Vector.vector * extract_data)


fun mapdepinfo f ({me = (a,i),deps}:'a raw_dep) : 'b raw_dep =
    {me = (f a, i), deps = map (fn (a,l) => (f a, l)) deps}

fun translatepath slist =
    let
      val isAbs = case slist of
                      _ :: s :: _ => size s < 2 orelse
                                     String.substring(s,0,2) <> "$("
                    | _ => true
    in
      case slist of
          [] => OS.Path.toString {arcs = [], isAbs = true, vol = ""}
        | v::arcs => OS.Path.toString {arcs = arcs, isAbs = isAbs, vol = v}
    end

fun translate_loc f rloc =
    case rloc of
        rlUnknown => Unknown
      | rlLocated {path,linenum,exact} =>
        Located {
          scriptpath=translatepath (map f path), linenum = linenum,
          exact = exact
        }

fun read_thm strv tmvector (thmrec:string raw_thm) =
    let
      val {name,deps,tags,class,private,loc,concl,hyps} = thmrec
      val getstr = (fn i => Vector.sub(strv,i))
      val loc' = translate_loc getstr loc
      val dd = (#me deps, #deps deps)
      val terms = map (Term.read_raw tmvector) (concl::hyps)
      val thminfo = {private=private,loc=loc',class=class}
      val thy = #1 (#me deps)
    in
      (name, Thm.disk_thm (thy,Thm.SavedName name) ((dd,tags), terms), thminfo)
    end


val prsexp = HOLPP.pp_to_string 70 HOLsexp.printer
fun force s dec t =
    case dec t of
        NONE => raise SharingTables ("Couldn't decode \""^s^"\": "^prsexp t)
      | SOME t => t

fun dec_sdata {before_types,before_terms,tables,exports} =
    let
      val {stringt = strv, idt = intplist, typet = shtylist,
           termt = shtmlist} = tables
      val {unnamed_types = raw_untys, named_types = raw_nmtys,
           unnamed_terms = raw_untms, named_terms = raw_nmtms,
           thms = rawthms} = exports
      fun sub v i = Vector.sub(v,i)
      val _ = before_types ()
      val idv = build_id_vector strv intplist
      val tyv = build_type_vector idv shtylist
      val _ = before_terms tyv
      val tmv = build_term_vector idv tyv shtmlist
      val untys = map (fn i => Vector.sub(tyv,i)) raw_untys
      val nmtys = map (fn (s,i) => (s, Vector.sub(tyv,i))) raw_nmtys
      val untms = map (Term.read_raw tmv) raw_untms
      val nmtms = map (fn {name,encoded_term} =>
                          (name, Term.read_raw tmv encoded_term))
                      raw_nmtms
      val thms = map (read_thm strv tmv) rawthms
    in
      (strv,idv,tyv,tmv,
       {named_types = nmtys, unnamed_types = untys,
        named_terms = nmtms, unnamed_terms = untms,
        theorems = thms})
    end

fun export_from_sharing_data (_, _, _, _, exp) = exp
fun read_term (_,_,_,tmv,_) = Term.read_raw tmv
fun read_string (strv,_,_,_,_) i = Vector.sub(strv,i)

end; (* struct *)
