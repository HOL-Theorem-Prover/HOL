
signature VECTOR =
sig
  type 'a vector = 'a Vector.vector
  val maxLen : int
  val fromList : 'a list -> 'a vector
  val tabulate : int * (int -> 'a) -> 'a vector
  val length : 'a vector -> int
  val sub : 'a vector * int -> 'a
  val update : 'a vector * int * 'a -> 'a vector
  val concat : 'a vector list -> 'a vector
  val appi : (int * 'a -> unit) -> 'a vector -> unit
  val app  : ('a -> unit) -> 'a vector -> unit
  val mapi : (int * 'a -> 'b) -> 'a vector -> 'b vector
  val map  : ('a -> 'b) -> 'a vector -> 'b vector
  val foldli : (int * 'a * 'b -> 'b) -> 'b -> 'a vector -> 'b
  val foldri : (int * 'a * 'b -> 'b) -> 'b -> 'a vector -> 'b
  val foldl  : ('a * 'b -> 'b) -> 'b -> 'a vector -> 'b
  val foldr  : ('a * 'b -> 'b) -> 'b -> 'a vector -> 'b
  val findi : (int * 'a -> bool)
                -> 'a vector -> (int * 'a) option
  val find  : ('a -> bool) -> 'a vector -> 'a option
  val exists : ('a -> bool) -> 'a vector -> bool
  val all : ('a -> bool) -> 'a vector -> bool
  val collate : ('a * 'a -> order) -> 'a vector * 'a vector -> order
end

structure MosmlVector = Vector
structure MosmlArray = Array

structure Vector :> VECTOR =
struct
  structure V = MosmlVector
  open V
  fun update (v,i,e) =
      tabulate (length v, (fn j => if j = i then e else sub(v,j)))
  fun appi f v = V.appi f (v,0,NONE)
  fun mapi f v = V.mapi f (v,0,NONE)
  fun foldli f b v = V.foldli f b (v,0,NONE)
  fun foldri f b v = V.foldri f b (v,0,NONE)
  fun findi P v = let
    val sz = length v
    fun recurse i =
        if i < sz then let
            val pr = (i,sub(v,i))
          in
            if P pr then SOME pr else recurse (i + 1)
          end
        else NONE
  in
    recurse 0
  end
  fun find P v = Option.map #2 (findi (P o #2) v)
  fun exists P v = isSome (find P v)
  fun all P v = not (exists (not o P) v)
  fun collate cmp (a1, a2) = let
    val sz1 = length a1 and sz2 = length a2
    fun recurse i =
        if i < sz1 then
          if i < sz2 then
            case cmp(sub(a1,i), sub(a2,i)) of
              EQUAL => recurse (i + 1)
            | x => x
          else GREATER
        else if i < sz2 then LESS
        else EQUAL
  in
    recurse 0
  end

end

signature VECTOR_SLICE = sig
  type 'a slice
  val length : 'a slice -> int
  val sub : 'a slice * int -> 'a
  val full : 'a Vector.vector -> 'a slice
  val slice : 'a Vector.vector * int * int option -> 'a slice
  val subslice : 'a slice * int * int option -> 'a slice
  val base : 'a slice -> 'a Vector.vector * int * int
  val vector : 'a slice -> 'a Vector.vector
  val concat : 'a slice list -> 'a Vector.vector
  val isEmpty : 'a slice -> bool
  val getItem : 'a slice -> ('a * 'a slice) option
  val appi : (int * 'a -> unit) -> 'a slice -> unit
  val app  : ('a -> unit) -> 'a slice -> unit
  val mapi : (int * 'a -> 'b) -> 'a slice -> 'b Vector.vector
  val map  : ('a -> 'b) -> 'a slice -> 'b Vector.vector
  val foldli : (int * 'a * 'b -> 'b) -> 'b -> 'a slice -> 'b
  val foldri : (int * 'a * 'b -> 'b) -> 'b -> 'a slice -> 'b
  val foldl  : ('a * 'b -> 'b) -> 'b -> 'a slice -> 'b
  val foldr  : ('a * 'b -> 'b) -> 'b -> 'a slice -> 'b
  val findi : (int * 'a -> bool)
                -> 'a slice -> (int * 'a) option
  val find  : ('a -> bool) -> 'a slice -> 'a option
  val exists : ('a -> bool) -> 'a slice -> bool
  val all : ('a -> bool) -> 'a slice -> bool
  val collate : ('a * 'a -> order)
                  -> 'a slice * 'a slice -> order
end

structure VectorSlice :> VECTOR_SLICE =
struct
  type 'a slice = ('a Vector.vector * int * int)
  val vlen = Vector.length
  val vsub = Vector.sub
  fun length (v,i,sz) = sz
  fun isEmpty (v,i,sz) = sz = 0
  fun sub ((v,i,sz), j) = if j < 0 orelse sz <= j then raise Subscript
                          else vsub(v, i + j)
  fun getItem (v,i,sz) = if sz = 0 then NONE
                         else SOME (vsub(v,i), (v,i+1,sz-1))
  fun full v = (v,0,vlen v)
  fun slice (v,i,NONE) = if i < 0 orelse vlen v < i then raise Subscript
                         else (v,i,vlen v - i)
    | slice (v,i,SOME sz) = if i < 0 orelse sz < 0 orelse vlen v < i + sz then
                              raise Subscript
                            else (v,i,sz)
  fun subslice ((v,i,sz), j, NONE) = if j < 0 orelse sz < j then raise Subscript
                                     else (v,i+j,sz - j)
    | subslice ((v,i,sz), j, SOME sz') =
      if j < 0 orelse sz' < 0 orelse sz < j + sz' then raise Subscript
      else (v,i+j,sz')
  fun base v : 'a slice = v
  fun vector (sl as (v,i,sz)) = Vector.tabulate(sz, (fn i => sub(sl, i)))
  fun concat sls =
      case sls of
        [] => Vector.fromList []
      | [sl] => vector sl
      | _ => let
          val combinedsz = List.foldl (fn (sl,a) => a + length sl) 0 sls
                           handle Overflow => raise Size
          val _ = if combinedsz > Vector.maxLen then raise Size else ()
          val sls_r = ref sls
          val i_r = ref 0
          fun tabthis i = let
            val sl = hd (!sls_r)
          in
            if i - !i_r >= length sl then
              (i_r := !i_r + length sl;
               sls_r := tl (!sls_r);
               tabthis i)
            else sub(sl, i - !i_r)
          end
        in
          Vector.tabulate(combinedsz, tabthis)
        end

  fun appi f sl = let
    fun recurse i = if i < length sl then (f(i, sub(sl,i)); recurse (i + 1))
                    else ()
  in
    recurse 0
  end
  fun app f = appi (f o #2)

  fun mapi f sl = Vector.tabulate(length sl, (fn i => f(i,sub(sl,i))))
  fun map f = mapi (f o #2)
  fun foldli f b sl = let
    val sz = length sl
    fun recurse acc i = if i < sz then recurse (f(i,sub(sl,i),acc)) (i + 1)
                        else acc
  in
    recurse b 0
  end
  fun foldri f b sl = let
    fun recurse acc i = if i < 0 then acc
                        else recurse (f(i,sub(sl,i),acc)) (i - 1)
  in
    recurse b (length sl - 1)
  end
  fun foldl f = foldli (fn (_,e,b) => f (e,b))
  fun foldr f = foldri (fn (_,e,b) => f (e,b))
  fun findi P v = let
    val sz = length v
    fun recurse i =
        if i < sz then let
            val pr = (i,sub(v,i))
          in
            if P pr then SOME pr else recurse (i + 1)
          end
        else NONE
  in
    recurse 0
  end
  fun find P v = Option.map #2 (findi (P o #2) v)
  fun exists P v = isSome (find P v)
  fun all P v = not (exists (not o P) v)
  fun collate cmp (a1, a2) = let
    val sz1 = length a1 and sz2 = length a2
    fun recurse i =
        if i < sz1 then
          if i < sz2 then
            case cmp(sub(a1,i), sub(a2,i)) of
              EQUAL => recurse (i + 1)
            | x => x
          else GREATER
        else if i < sz2 then LESS
        else EQUAL
  in
    recurse 0
  end

end


signature ARRAY =
sig
  type 'a array = 'a Array.array
  type 'a vector = 'a Vector.vector
  val maxLen : int
  val array : int * 'a -> 'a array
  val fromList : 'a list -> 'a array
  val tabulate : int * (int -> 'a) -> 'a array
  val length : 'a array -> int
  val sub : 'a array * int -> 'a
  val update : 'a array * int * 'a -> unit
  val vector : 'a array -> 'a vector
  val copy    : {src : 'a array, dst : 'a array, di : int} -> unit
  val copyVec : {src : 'a vector, dst : 'a array, di : int} -> unit
  val appi : (int * 'a -> unit) -> 'a array -> unit
  val app  : ('a -> unit) -> 'a array -> unit
  val modifyi : (int * 'a -> 'a) -> 'a array -> unit
  val modify  : ('a -> 'a) -> 'a array -> unit
  val foldli : (int * 'a * 'b -> 'b) -> 'b -> 'a array -> 'b
  val foldri : (int * 'a * 'b -> 'b) -> 'b -> 'a array -> 'b
  val foldl  : ('a * 'b -> 'b) -> 'b -> 'a array -> 'b
  val foldr  : ('a * 'b -> 'b) -> 'b -> 'a array -> 'b
  val findi : (int * 'a -> bool)
              -> 'a array -> (int * 'a) option
  val find  : ('a -> bool) -> 'a array -> 'a option
  val exists : ('a -> bool) -> 'a array -> bool
  val all : ('a -> bool) -> 'a array -> bool
  val collate : ('a * 'a -> order)
                -> 'a array * 'a array -> order
end

structure Array :> ARRAY =
struct
  type 'a vector = 'a Vector.vector
  structure A = MosmlArray
  open A

  fun vector a = extract(a, 0, NONE)
  fun copy {di,dst,src} =
      A.copy {src = src, si = 0, len = NONE, dst = dst, di = di}
  fun copyVec {di,dst,src} =
      A.copyVec {src = src, si = 0, len = NONE, dst = dst, di = di}
  fun appi f a = A.appi f (a, 0, NONE)
  fun modifyi f a = A.modifyi f (a, 0, NONE)
  fun foldli f b a = A.foldli f b (a, 0, NONE)
  fun foldri f b a = A.foldri f b (a, 0, NONE)
  fun findi P a = let
    val sz = length a
    fun recurse i =
        if i < sz then let val pr = (i, sub(a,i))
                       in
                         if P pr then SOME pr else recurse (i + 1)
                       end
        else NONE
  in
    recurse 0
  end
  fun find P a = Option.map #2 (findi (P o #2) a)
  fun exists P a = isSome (find P a)
  fun all P a = not (exists (not o P) a)
  fun collate cmp (a1, a2) = let
    val sz1 = length a1 and sz2 = length a2
    fun recurse i =
        if i < sz1 then
          if i < sz2 then
            case cmp(sub(a1,i), sub(a2,i)) of
              EQUAL => recurse (i + 1)
            | x => x
          else GREATER
        else if i < sz2 then LESS
        else EQUAL
  in
    recurse 0
  end
end

signature ARRAY_SLICE =
sig
    type 'a slice
    val length : 'a slice -> int
    val sub : 'a slice * int -> 'a
    val update : 'a slice * int * 'a -> unit
    val full : 'a Array.array -> 'a slice
    val slice : 'a Array.array * int * int option -> 'a slice
    val subslice : 'a slice * int * int option -> 'a slice
    val base : 'a slice -> 'a Array.array * int * int
    val vector : 'a slice -> 'a Vector.vector
    val copy    : {
                      src : 'a slice,
                      dst : 'a Array.array,
                      di : int
                    } -> unit
    val copyVec : {
                      src : 'a VectorSlice.slice,
                      dst : 'a Array.array,
                      di : int
                    } -> unit
    val isEmpty : 'a slice -> bool
    val getItem : 'a slice -> ('a * 'a slice) option
    val appi : (int * 'a -> unit) -> 'a slice -> unit
    val app  : ('a -> unit) -> 'a slice -> unit
    val modifyi : (int * 'a -> 'a) -> 'a slice -> unit
    val modify  : ('a -> 'a) -> 'a slice -> unit
    val foldli : (int * 'a * 'b -> 'b) -> 'b -> 'a slice -> 'b
    val foldri : (int * 'a * 'b -> 'b) -> 'b -> 'a slice -> 'b
    val foldl  : ('a * 'b -> 'b) -> 'b -> 'a slice -> 'b
    val foldr  : ('a * 'b -> 'b) -> 'b -> 'a slice -> 'b
    val findi : (int * 'a -> bool)
                  -> 'a slice -> (int * 'a) option
    val find  : ('a -> bool) -> 'a slice -> 'a option
    val exists : ('a -> bool) -> 'a slice -> bool
    val all : ('a -> bool) -> 'a slice -> bool
    val collate : ('a * 'a -> order)
                    -> 'a slice * 'a slice -> order
end

structure ArraySlice :> ARRAY_SLICE =
struct

  type 'a slice = ('a Array.array * int * int)

  val vlen = Array.length
  val vsub = Array.sub
  fun length (v,i,sz) = sz
  fun isEmpty (v,i,sz) = sz = 0
  fun sub ((v,i,sz), j) = if j < 0 orelse sz <= j then raise Subscript
                          else vsub(v, i + j)
  fun update((a,i,sz),j,e) = Array.update(a,i + j,e)

  fun getItem (v,i,sz) = if sz = 0 then NONE
                         else SOME (vsub(v,i), (v,i+1,sz-1))
  fun full v = (v,0,vlen v)
  fun slice (v,i,NONE) = if i < 0 orelse vlen v < i then raise Subscript
                         else (v,i,vlen v - i)
    | slice (v,i,SOME sz) = if i < 0 orelse sz < 0 orelse vlen v < i + sz then
                              raise Subscript
                            else (v,i,sz)
  fun subslice ((v,i,sz), j, NONE) = if j < 0 orelse sz < j then raise Subscript
                                     else (v,i+j,sz - j)
    | subslice ((v,i,sz), j, SOME sz') =
      if j < 0 orelse sz' < 0 orelse sz < j + sz' then raise Subscript
      else (v,i+j,sz')
  fun base v : 'a slice = v
  fun vector (sl as (v,i,sz)) = Vector.tabulate(sz, (fn i => sub(sl, i)))

  fun copy {di,dst,src = src as (a,i,sz)} =
      if di < 0 orelse vlen dst < di + sz then raise Subscript
      else let
          fun back2front j = if j < 0 then ()
                             else (Array.update(dst,j + di,sub(src,j));
                                   back2front (j - 1))
          fun front2back j = if j < sz then (Array.update(dst,j+di,sub(src,j));
                                             front2back (j + 1))
                             else ()
        in
          if a = dst then
            if i = di then ()
            else if i < di then back2front (sz - 1)
            else (* di < i *) front2back 0
          else front2back 0
        end

  fun copyVec {di,dst,src} =
      if di < 0 orelse vlen dst < di + VectorSlice.length src then
        raise Subscript
      else let
          val sub = VectorSlice.sub
          val sz = VectorSlice.length src
          fun front2back j = if j < sz then (Array.update(dst,j+di,sub(src,j));
                                             front2back (j + 1))
                             else ()
        in
          front2back 0
        end



  fun appi f sl = let
    fun recurse i = if i < length sl then (f(i, sub(sl,i)); recurse (i + 1))
                    else ()
  in
    recurse 0
  end
  fun app f = appi (f o #2)

  fun modifyi f sl = let
    val sz = length sl
    fun recurse i = if i < sz then
                      (update(sl,i,f(i,sub(sl,i))); recurse (i + 1))
                    else ()
  in
    recurse 0
  end
  fun modify f = modifyi (f o #2)

  fun foldli f b sl = let
    val sz = length sl
    fun recurse acc i = if i < sz then recurse (f(i,sub(sl,i),acc)) (i + 1)
                        else acc
  in
    recurse b 0
  end
  fun foldri f b sl = let
    fun recurse acc i = if i < 0 then acc
                        else recurse (f(i,sub(sl,i),acc)) (i - 1)
  in
    recurse b (length sl - 1)
  end
  fun foldl f = foldli (fn (_,e,b) => f (e,b))
  fun foldr f = foldri (fn (_,e,b) => f (e,b))
  fun findi P v = let
    val sz = length v
    fun recurse i =
        if i < sz then let
            val pr = (i,sub(v,i))
          in
            if P pr then SOME pr else recurse (i + 1)
          end
        else NONE
  in
    recurse 0
  end
  fun find P v = Option.map #2 (findi (P o #2) v)
  fun exists P v = isSome (find P v)
  fun all P v = not (exists (not o P) v)
  fun collate cmp (a1, a2) = let
    val sz1 = length a1 and sz2 = length a2
    fun recurse i =
        if i < sz1 then
          if i < sz2 then
            case cmp(sub(a1,i), sub(a2,i)) of
              EQUAL => recurse (i + 1)
            | x => x
          else GREATER
        else if i < sz2 then LESS
        else EQUAL
  in
    recurse 0
  end



end



signature OS_PROCESS =
sig
    type status
    val success : status
    val failure : status
    val isSuccess : status -> bool
    val system : string -> status
    val atExit : (unit -> unit) -> unit
    val exit : status -> 'a
    val terminate : status -> 'a
    val getEnv : string -> string option
    val sleep : Time.time -> unit
end

signature OS_PATH =
sig

exception Path
exception InvalidArc

val parentArc : string
val currentArc : string

val fromString : string -> {isAbs : bool, vol : string, arcs : string list}
val toString : {isAbs : bool, vol : string, arcs : string list} -> string

val validVolume : {isAbs : bool, vol : string} -> bool

val getVolume : string -> string
val getParent : string -> string

val splitDirFile : string -> {dir : string, file : string}
val joinDirFile : {dir : string, file : string} -> string
val dir  : string -> string
val file : string -> string

val splitBaseExt : string -> {base : string, ext : string option}
val joinBaseExt : {base : string, ext : string option} -> string
val base : string -> string
val ext  : string -> string option

val mkCanonical : string -> string
val isCanonical : string -> bool
val mkAbsolute : {path : string, relativeTo : string}
                   -> string
val mkRelative : {path : string, relativeTo : string}
                   -> string
val isAbsolute : string -> bool
val isRelative : string -> bool
val isRoot : string -> bool

val concat : string * string -> string

val fromUnixPath : string -> string
val toUnixPath : string -> string

end



structure String = struct
  open String
  fun concatWith sep l = let
    fun clist l acc =
        case l of
          h1 :: (t as _::_) => clist t (sep :: h1 :: acc)
        | x => x @ acc
  in
    concat (List.rev (clist l []))
  end
  fun isSubstring p t = let
    (* following
         http://www.iti.fh-flensburg.de/lang/algorithmen/pattern/bmen.htm
    *)
    open Int
    val m = size p
    val n = size t

    val occ = let
      val occarray = Array.array (Char.ord Char.maxChar + 1, ~1)
      fun recurse i =
          if i >= m then ()
          else let
              val c = String.sub(p,i)
            in
              Array.update(occarray, Char.ord c, i);
              recurse (i + 1)
            end
      val _ = recurse 0
    in
      fn c => Array.sub(occarray, Char.ord c)
    end
    val f = Array.array(m+1,0)
    val s = Array.array(m+1,0)
    val bmPreprocess1 as () = let
      val i = ref m and j = ref (m + 1)
      val _ = Array.update(f,!i,!j)
    in
      while (!i > 0) do
        (while !j <= m andalso String.sub(p,!i-1) <> String.sub(p,!j-1) do
           (if Array.sub(s,!j) = 0 then Array.update(s,!j,(!j) - !i) else ();
            j := Array.sub(f,!j));
         i := !i - 1;
         j := !j - 1;
         Array.update(f,!i,!j))
    end
    val bmPreprocess2 as () = let
      val i = ref 0 and j = ref (Array.sub(f,0))
    in
      while (!i <= m) do
        (if Array.sub(s,!i) = 0 then Array.update(s,!i,!j) else ();
         if !i = !j then j := Array.sub(f,!j) else ();
         i := !i + 1)
    end
    exception Done of int
    val i = ref 0 and j = ref 0
  in
    (while !i <= n - m do
       (j := m - 1;
        while (!j >= 0 andalso String.sub(p,!j) = String.sub(t,!i + !j)) do
          j := !j - 1;
        if !j < 0 then raise Done (!i)
        else i := !i + Int.max(Array.sub(s,!j + 1),
                               !j - occ (String.sub(t,!i + !j))));
     false) handle Done _ => true
  end

  fun isSuffix small big = let
    open Int
    fun check i j =
        i < 0 orelse
        (0 <= j andalso
         String.sub(small,i) = String.sub(big,j) andalso
         check (i - 1) (j - 1))
  in
    check (size small - 1) (size big - 1)
  end

end

signature SUBSTRING =
sig
  type substring
  eqtype char
  eqtype string

  val sub : substring * int -> char
  val size : substring -> int
  val base : substring -> string * int * int
  val extract   : string * int * int option -> substring
  val substring : string * int * int -> substring
  val full : string -> substring
  val string : substring -> string
  val isEmpty : substring -> bool
  val getc : substring -> (char * substring) option
  val first : substring -> char option
  val triml : int -> substring -> substring
  val trimr : int -> substring -> substring
  val slice : substring * int * int option -> substring
  val concat : substring list -> string
  val concatWith : string -> substring list -> string
  val explode : substring -> char list
  val isPrefix    : string -> substring -> bool
  val isSubstring : string -> substring -> bool
  val isSuffix    : string -> substring -> bool
  val compare : substring * substring -> order
  val collate : (char * char -> order) -> substring * substring -> order
  val splitl : (char -> bool) -> substring -> substring * substring
  val splitr : (char -> bool) -> substring -> substring * substring
  val splitAt : substring * int -> substring * substring
  val dropl : (char -> bool) -> substring -> substring
  val dropr : (char -> bool) -> substring -> substring
  val takel : (char -> bool) -> substring -> substring
  val taker : (char -> bool) -> substring -> substring
  val position : string -> substring -> substring * substring
  val span : substring * substring -> substring
  val translate : (char -> string) -> substring -> string
  val tokens : (char -> bool) -> substring -> substring list
  val fields : (char -> bool) -> substring -> substring list
  val app : (char -> unit) -> substring -> unit
  val foldl : (char * 'a -> 'a) -> 'a -> substring -> 'a
  val foldr : (char * 'a -> 'a) -> 'a -> substring -> 'a
end

structure Substring :> SUBSTRING
            where type substring = Substring.substring
            and type string = String.string
            and type char = Char.char =
struct
  open Substring
  type char = Char.char
  type string = String.string
  val full = all
  fun concatWith sep sslist = let
    fun clist l =
        case l of
          h1 :: (t as _ :: _) => h1 :: full sep :: clist t
        | x => x
  in
    concat (clist sslist)
  end

  fun isSubstring s ss = String.isSubstring s (string ss)
  fun isSuffix s ss = String.isSuffix s (string ss)

end

structure TextIO = struct
  open TextIO
  val inputLine = fn is => case inputLine is of
                             "" => NONE
                           | s => SOME s
end

signature MONO_VECTOR =
sig
  type vector
  type elem
  val maxLen : int
  val fromList : elem list -> vector
  val tabulate : int * (int -> elem) -> vector
  val length : vector -> int
  val sub : vector * int -> elem
  val update : vector * int * elem -> vector
  val concat : vector list -> vector
  val appi : (int * elem -> unit) -> vector -> unit
  val app  : (elem -> unit) -> vector -> unit
  val mapi : (int * elem -> elem) -> vector -> vector
  val map  : (elem -> elem) -> vector -> vector
  val foldli : (int * elem * 'a -> 'a) -> 'a -> vector -> 'a
  val foldri : (int * elem * 'a -> 'a) -> 'a -> vector -> 'a
  val foldl  : (elem * 'a -> 'a) -> 'a -> vector -> 'a
  val foldr  : (elem * 'a -> 'a) -> 'a -> vector -> 'a
  val findi : (int * elem -> bool)
              -> vector -> (int * elem) option
  val find  : (elem -> bool) -> vector -> elem option
  val exists : (elem -> bool) -> vector -> bool
  val all : (elem -> bool) -> vector -> bool
  val collate : (elem * elem -> order)
                -> vector * vector -> order
end

structure CharVector :> MONO_VECTOR
                          where type vector = String.string
                          and type elem = char =
struct
  open CharVector
  fun update(s,i,c) = if i < 0 orelse i >= size s then raise Subscript
                      else String.extract(s,0,SOME i) ^ str c ^
                           (if i = size s - 1 then ""
                            else String.extract(s,i+1,NONE))
  fun appi f s = CharVector.appi f (s,0,NONE)
  fun mapi f s = CharVector.mapi f (s,0,NONE)
  fun foldli f acc s = CharVector.foldli f acc (s,0,NONE)
  fun foldri f acc s = CharVector.foldri f acc (s,0,NONE)
  fun findi P s = let
    val sz = size s
    fun recurse i =
        if i = sz then NONE
        else let
            val c = String.sub (s, i)
            val pair = (i,c)
          in
            if P pair then SOME pair
            else recurse (i + 1)
          end
  in
    recurse 0
  end
  fun find P s = let
    val sz = size s
    fun recurse i =
        if i = sz then NONE
        else let
            val c = String.sub(s,i)
          in
            if P c then SOME c else recurse (i + 1)
          end
  in
    recurse 0
  end
  fun exists P s = isSome (find P s)
  fun all P = not o exists (not o P)
  val collate = String.collate
end

signature MONO_VECTOR_SLICE =
sig
  type elem
  type vector
  type slice
  val length : slice -> int
  val sub : slice * int -> elem
  val full : vector -> slice
  val slice : vector * int * int option -> slice
  val subslice : slice * int * int option -> slice
  val base : slice -> vector * int * int
  val vector : slice -> vector
  val concat : slice list -> vector
  val isEmpty : slice -> bool
  val getItem : slice -> (elem * slice) option
  val appi : (int * elem -> unit) -> slice -> unit
  val app  : (elem -> unit) -> slice -> unit
  val mapi : (int * elem -> elem) -> slice -> vector
  val map  : (elem -> elem) -> slice -> vector
  val foldli : (int * elem * 'b -> 'b) -> 'b -> slice -> 'b
  val foldr  : (elem * 'b -> 'b) -> 'b -> slice -> 'b
  val foldl  : (elem * 'b -> 'b) -> 'b -> slice -> 'b
  val foldri : (int * elem * 'b -> 'b) -> 'b -> slice -> 'b
  val findi : (int * elem -> bool) -> slice -> (int * elem) option
  val find  : (elem -> bool) -> slice -> elem option
  val exists : (elem -> bool) -> slice -> bool
  val all : (elem -> bool) -> slice -> bool
  val collate : (elem * elem -> order) -> slice * slice -> order
end

structure CharVectorSlice :> MONO_VECTOR_SLICE
                               where type slice = Substring.substring
                                 and type vector = String.string
                                 and type elem = char =
struct
  type elem = char
  type slice = Substring.substring
  type vector = String.string
  open Substring
  val length = size
  val subslice = slice
  val slice = extract
  val vector = string
  val getItem = getc
  fun appi f ss = let
    val sz = size ss
    fun recurse i =
        if i = sz then ()
        else (f (i,sub(ss,i)); recurse (i + 1))
  in
    recurse 0
  end
  fun mapi f ss = let
    val sz = size ss
    fun recurse acc i =
        if i = sz then acc
        else recurse (f(i,sub(ss,i)) :: acc) (i + 1)
  in
    String.implode (List.rev (recurse [] 0))
  end
  fun map f ss = mapi (fn (i,c) => f c) ss
  fun foldli f acc ss = let
    val sz = size ss
    fun recurse i acc =
        if i = sz then acc
        else recurse (i + 1) (f(i,sub(ss,i),acc))
  in
    recurse 0 acc
  end
  fun foldri f init seq = let
    val len = length seq
    fun loop (i, b) =
        if i = ~1 then b
        else loop(i-1,f(i,sub(seq,i),b))
  in
    loop(len-1,init)
  end
  fun findi P ss = let
    val sz = length ss
    fun loop i =
        if i = sz then NONE
        else let
            val c = sub(ss,i)
            val pr = (i,c)
          in
            if P pr then SOME pr else loop (i + 1)
          end
  in
    loop 0
  end
  fun find P ss = Option.map #2 (findi (fn (i,c) => P c) ss)
  fun exists P ss = isSome (find P ss)
  fun all P = not o (exists (not o P))

end;

structure Word8Vector :> MONO_VECTOR
                           where type elem = Word8.word
                             and type vector = Word8Vector.vector =
struct
  open Word8Vector
  type vector = Word8Vector.vector
  fun update (v,i,e) =
      tabulate (length v, (fn j => if j = i then e else sub(v,j)))
  fun appi f v = Word8Vector.appi f (v, 0, NONE)
  fun mapi f v = Word8Vector.mapi f (v, 0, NONE)
  fun foldli f a v = Word8Vector.foldli f a (v, 0, NONE)
  fun foldri f a v = Word8Vector.foldri f a (v, 0, NONE)

  fun findi P v = let
    val sz = length v
    fun loop i =
        if i = sz then NONE
        else let
            val c = sub(v,i)
            val pr = (i,c)
          in
            if P pr then SOME pr else loop (i + 1)
          end
  in
    loop 0
  end
  fun find P v = Option.map #2 (findi (fn (i,c) => P c) v)
  fun exists P v = isSome (find P v)
  fun all P = not o (exists (not o P))

  fun collate wcmp (v1, v2) = let
    val sz1 = length v1 and sz2 = length v2
    fun loop i =
        if i = sz1 then if i = sz2 then EQUAL else LESS
        else if i = sz2 then GREATER
        else
          case wcmp (sub(v1,i), sub(v2,i)) of
            EQUAL => loop (i + 1)
          | x => x
  in
    loop 0
  end
end

structure OS =
struct
  open OS
  structure Process : OS_PROCESS =
  struct
    open Process
    fun isSuccess x = (x = success)
    fun unixSleep t = ignore (system ("sleep "^Time.toString t))
    fun winSleep delay = let
      fun start_timer() = let
        val timer = Timer.startRealTimer()
      in
        (fn () => Timer.checkRealTimer timer
            handle Time.Time => Time.zeroTime)
      end
      val t = start_timer()
      fun loop () = if Time.>= (t(), delay) then ()
                    else loop()
    in
      loop()
    end
    val sleep = if Systeml.isUnix then unixSleep else winSleep
  end

  structure Path : OS_PATH = struct
    structure MP = Path
    open Path

    (* inspired by the mlton 20070826 approach *)
    val isWindows = MP.validVolume {isAbs = true, vol = "c:"}
    val slash = if isWindows then "\\" else "/"
    infix 9 sub
    val op sub = String.sub

    exception InvalidArc
    fun mkAbsolute{relativeTo, path} = MP.mkAbsolute(relativeTo,path)
    fun mkRelative{relativeTo, path} = MP.mkRelative(relativeTo,path)
    fun isRoot path =
        case fromString path of
          {isAbs = true, arcs = [""], ...} => true
        | _ => false

    fun fromUnixPath s =
        if not isWindows then s
        else if Char.contains s (slash sub 0) then raise InvalidArc
        else String.translate (fn c => if c = #"/" then slash else str c) s

    fun toUnixPath s =
        if not isWindows then s
        else
          let
            val {arcs, isAbs, vol} = fromString s
          in
            if vol <> "" then raise Path
            else (if isAbs then "/" else "") ^ String.concatWith "/" arcs
          end

  end (* structure Path *)
end

structure Real =
struct
  open Real
  structure Math = Math
end

exception Option = Option.Option