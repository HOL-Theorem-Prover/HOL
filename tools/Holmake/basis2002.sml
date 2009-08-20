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
                           where type elem = Word8.word =
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
