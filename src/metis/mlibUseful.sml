(* ========================================================================= *)
(* ML UTILITY FUNCTIONS                                                      *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

structure mlibUseful :> mlibUseful =
struct

infixr 0 oo ## |-> ==;

(* ------------------------------------------------------------------------- *)
(* Exceptions, profiling and tracing.                                        *)
(* ------------------------------------------------------------------------- *)

exception Error of string;
exception Bug of string;

fun Error_to_string (Error message) =
  "\nError: " ^ message ^ "\n"
  | Error_to_string _ = raise Bug "Error_to_string: not an Error exception";

fun Bug_to_string (Bug message) =
  "\nBug: " ^ message ^ "\n"
  | Bug_to_string _ = raise Bug "Bug_to_string: not a Bug exception";

fun report (e as Error _) = Error_to_string e
  | report (e as Bug _) = Bug_to_string e
  | report _ = raise Bug "report: not an Error or Bug exception";

fun assert b e = if b then () else raise e;

fun try f a = f a
  handle h as Error _ => (print (Error_to_string h); raise h)
       | b as Bug _ => (print (Bug_to_string b); raise b)
       | e => (print "\ntry: strange exception raised\n"; raise e);

fun total f x = SOME (f x) handle Error _ => NONE;

fun can f = Option.isSome o total f;

fun partial (e as Error _) f x = (case f x of SOME y => y | NONE => raise e)
  | partial _ _ _ = raise Bug "partial: must take an Error exception";

fun timed f a =
  let
    val tmr = Timer.startCPUTimer ()
    val res = f a
    val {usr,sys,...} = Timer.checkCPUTimer tmr
  in
    (Time.toReal usr + Time.toReal sys, res)
  end;

local
  val MIN = 1.0;

  fun several n t f a =
    let
      val (t',res) = timed f a
      val t = t + t'
      val n = n + 1
    in
      if t > MIN then (t / Real.fromInt n, res) else several n t f a
    end;
in
  fun timed_many f a = several 0 0.0 f a
end;

val trace_level = ref 1;

val traces : {module : string, alignment : int -> int} list ref = ref [];

local
  val MAX = 10;
  fun query m l =
    let val t = List.find (fn {module, ...} => module = m) (!traces)
    in case t of NONE => MAX | SOME {alignment, ...} => alignment l
    end;
in
  fun tracing {module = m, level = l} =
    let val t = !trace_level
    in 0 < t andalso (MAX <= t orelse MAX <= l orelse query m l <= t)
    end;
end;

val trace = print;

(* ------------------------------------------------------------------------- *)
(* Combinators                                                               *)
(* ------------------------------------------------------------------------- *)

fun C f x y = f y x;

fun I x = x;

fun K x y = x;

fun S f g x = f x (g x);

fun W f x = f x x;

fun f oo g = fn x => f o (g x);

fun funpow 0 _ x = x | funpow n f x = funpow (n - 1) f (f x);

(* ------------------------------------------------------------------------- *)
(* Booleans                                                                  *)
(* ------------------------------------------------------------------------- *)

fun bool_to_string true = "true"
  | bool_to_string false = "false";

fun non f = not o f;

fun bool_compare (true,false) = LESS
  | bool_compare (false,true) = GREATER
  | bool_compare _ = EQUAL;
  
(* ------------------------------------------------------------------------- *)
(* Pairs                                                                     *)
(* ------------------------------------------------------------------------- *)

fun op## (f,g) (x,y) = (f x, g y);

fun D x = (x,x);

fun Df f = f ## f;

fun fst (x,_) = x;

fun snd (_,y) = y;

fun pair x y = (x,y);

fun swap (x,y) = (y,x);

fun curry f x y = f (x,y);

fun uncurry f (x,y) = f x y;

fun equal x y = (x = y);

(* ------------------------------------------------------------------------- *)
(* State transformers                                                        *)
(* ------------------------------------------------------------------------- *)

val unit : 'a -> 's -> 'a * 's = pair;

fun bind f (g : 'a -> 's -> 'b * 's) = uncurry g o f;

fun mmap f (m : 's -> 'a * 's) = bind m (unit o f);

fun mjoin (f : 's -> ('s -> 'a * 's) * 's) = bind f I;

fun mwhile c b = let fun f a = if c a then bind (b a) f else unit a in f end;

(* ------------------------------------------------------------------------- *)
(* Lists                                                                     *)
(* ------------------------------------------------------------------------- *)

fun cons x y = x :: y;

fun hd_tl l = (hd l, tl l);

fun append xs ys = xs @ ys;

fun sing a = [a];

fun first f [] = NONE
  | first f (x :: xs) = (case f x of NONE => first f xs | s => s);

fun index p =
  let
    fun idx _ [] = NONE
      | idx n (x :: xs) = if p x then SOME n else idx (n + 1) xs
  in
    idx 0
  end;

fun maps (_ : 'a -> 's -> 'b * 's) [] = unit []
  | maps f (x :: xs) =
  bind (f x) (fn y => bind (maps f xs) (fn ys => unit (y :: ys)));

fun partial_maps (_ : 'a -> 's -> 'b option * 's) [] = unit []
  | partial_maps f (x :: xs) =
  bind (f x)
  (fn yo => bind (partial_maps f xs)
   (fn ys => unit (case yo of NONE => ys | SOME y => y :: ys)));

fun enumerate n = fst o C (maps (fn x => fn m => ((m, x), m + 1))) n;

fun zipwith f =
  let
    fun z l [] [] = l
      | z l (x :: xs) (y :: ys) = z (f x y :: l) xs ys
      | z _ _ _ = raise Error "zipwith: lists different lengths";
  in
    fn xs => fn ys => rev (z [] xs ys)
  end;

fun zip xs ys = zipwith pair xs ys;

fun unzip ab =
  foldl (fn ((x, y), (xs, ys)) => (x :: xs, y :: ys)) ([], []) (rev ab);

fun cartwith f =
  let
    fun aux _ res _ [] = res
      | aux xs_copy res [] (y :: yt) = aux xs_copy res xs_copy yt
      | aux xs_copy res (x :: xt) (ys as y :: _) =
      aux xs_copy (f x y :: res) xt ys
  in
    fn xs => fn ys =>
    let val xs' = rev xs in aux xs' [] xs' (rev ys) end
  end;

fun cart xs ys = cartwith pair xs ys;

local
  fun aux res l 0 = (rev res, l)
    | aux _ [] _ = raise Subscript
    | aux res (h :: t) n = aux (h :: res) t (n - 1);
in
  fun divide l n = aux [] l n;
end;

fun update_nth f n l =
  let
    val (a, b) = divide l n
  in
    case b of [] => raise Subscript
    | h :: t => a @ (f h :: t)
  end;

fun shared_map f =
    let
      fun map _ (a,b) [] = List.revAppend (a,b)
        | map c (a,b) (x :: xs) =
          let
            val y = f x
            val c = y :: c
          in
            map c (if mlibPortable.pointer_eq x y then (a,b) else (c,xs)) xs
          end
    in
      fn l => map [] ([],l) l
    end;

(* ------------------------------------------------------------------------- *)
(* Lists-as-sets                                                             *)
(* ------------------------------------------------------------------------- *)

fun mem x = List.exists (equal x);

fun insert x s = if mem x s then s else x :: s;
fun delete x s = List.filter (not o equal x) s;

(* Removes duplicates *)
fun setify s = foldl (fn (v,x) => if mem v x then x else v :: x) [] s;

fun union s t = foldl (fn (v,x) => if mem v t then x else v::x) t (rev s);
fun intersect s t = foldl (fn (v,x) => if mem v t then v::x else x) [] (rev s);
fun subtract s t = foldl (fn (v,x) => if mem v t then x else v::x) [] (rev s);

fun subset s t = List.all (fn x => mem x t) s;

fun distinct [] = true
  | distinct (x :: rest) = not (mem x rest) andalso distinct rest;

(* ------------------------------------------------------------------------- *)
(* Comparisons.                                                              *)
(* ------------------------------------------------------------------------- *)

type 'a ordering = 'a * 'a -> order;

fun order_to_string LESS = "LESS"
  | order_to_string EQUAL = "EQUAL"
  | order_to_string GREATER = "GREATER";

fun map_order mf f (a,b) = f (mf a, mf b);

fun rev_order f xy =
  case f xy of LESS => GREATER | EQUAL => EQUAL | GREATER => LESS;

fun lex_order f g ((a,c),(b,d)) = case f (a,b) of EQUAL => g (c,d) | x => x;

fun lex_order2 f = lex_order f f;

fun lex_order3 f =
    map_order (fn (a,b,c) => (a,(b,c))) (lex_order f (lex_order2 f));

fun lex_seq_order f g (a,b) = lex_order f g ((a,a),(b,b));

fun lex_list_order f =
  let
    fun lex [] [] = EQUAL
      | lex [] (_ :: _) = LESS
      | lex (_ :: _) [] = GREATER
      | lex (x :: xs) (y :: ys) = case f (x,y) of EQUAL => lex xs ys | r => r
  in
    uncurry lex
  end;

(* ------------------------------------------------------------------------- *)
(* Finding the minimum and maximum element of a list, wrt some order.        *)
(* ------------------------------------------------------------------------- *)

fun min cmp =
  let
    fun min_acc (l,m,r) _ [] = (m, List.revAppend (l,r))
      | min_acc (best as (_,m,_)) l (x :: r) =
      min_acc (case cmp (x,m) of LESS => (l,x,r) | _ => best) (x :: l) r
  in
    fn [] => raise Error "min: empty list"
     | h :: t => min_acc ([],h,t) [h] t
  end;

fun max cmp = min (rev_order cmp);

(* ------------------------------------------------------------------------- *)
(* Merge (for the following merge-sort, but generally useful too).           *)
(* ------------------------------------------------------------------------- *)

fun merge cmp =
  let
    fun mrg acc [] ys = List.revAppend (acc, ys)
      | mrg acc xs [] = List.revAppend (acc, xs)
      | mrg acc (xs as x :: xt) (ys as y :: yt) =
      (case cmp (x,y) of GREATER => mrg (y :: acc) xs yt
       | _ => mrg (x :: acc) xt ys)
  in
    mrg []
  end;

(* ------------------------------------------------------------------------- *)
(* Merge sort.(stable)                                                       *)
(* ------------------------------------------------------------------------- *)

fun sort cmp =
  let
    val m = merge cmp
    fun f [] = []
      | f (xs as [_]) = xs
      | f xs = let val (l,r) = divide xs (length xs div 2) in m (f l) (f r) end
  in
    f
  end;

fun sort_map _ _ [] = []
  | sort_map _ _ (xs as [_]) = xs
  | sort_map f cmp xs =
  let
    fun ncmp ((m,_),(n,_)) = cmp (m,n)
    val nxs = map (fn x => (f x, x)) xs
    val nys = sort ncmp nxs
  in
    map snd nys
  end;

(* ------------------------------------------------------------------------- *)
(* Topological sort                                                          *)
(* ------------------------------------------------------------------------- *)

fun top_sort cmp parents =
    let
      fun f stack (x,(acc,seen)) =
          if Binaryset.member (stack,x) then raise Error "top_sort: cycle"
          else if Binaryset.member (seen,x) then (acc,seen)
          else
            let
              val stack = Binaryset.add (stack,x)
              val (acc,seen) = foldl (f stack) (acc,seen) (parents x)
              val acc = x :: acc
              val seen = Binaryset.add (seen,x)
            in
              (acc,seen)
            end
    in
      rev o fst o foldl (f (Binaryset.empty cmp)) ([], Binaryset.empty cmp)
    end

(* ------------------------------------------------------------------------- *)
(* Integers.                                                                 *)
(* ------------------------------------------------------------------------- *)

val int_to_string = Int.toString;
fun string_to_int s =
  case Int.fromString s of SOME n => n | NONE => raise Error "string_to_int";

fun int_to_bits 0 = []
  | int_to_bits n = (n mod 2 <> 0) :: (int_to_bits (n div 2));

fun bits_to_int [] = 0
  | bits_to_int (h :: t) = (if h then curry op+ 1 else I) (2 * bits_to_int t);

local
  val enc = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

  val (max, rev_enc) =
    foldl (fn (c,(i,m)) => (i + 1, Binarymap.insert (m,c,i)))
    (0, Binarymap.mkDict Char.compare) (String.explode enc);
in
  fun int_to_base64 n =
    if 0 <= n andalso n < max then String.sub (enc,n)
    else raise Error "int_to_base64: out of range";

  fun base64_to_int c =
    case Binarymap.peek (rev_enc, c) of SOME n => n
    | NONE => raise Error "base64_to_int: out of range";
end;

fun interval m 0 = []
  | interval m len = m :: interval (m + 1) (len - 1);

fun divides a b = if a = 0 then b = 0 else b mod (Int.abs a) = 0;

fun even n = divides 2 n;

fun odd n = not (even n);

local
  fun both f g n = f n andalso g n;
  fun next f = let fun nx x = if f x then x else nx (x + 1) in nx end;

  fun looking res 0 _ _ = rev res
    | looking res n f x =
    let
      val p = next f x
      val res' = p :: res
      val f' = both f (not o divides p)
    in
      looking res' (n - 1) f' (p + 1)
    end
in
  fun primes n = looking [] n (K true) 2
end;

local
  fun hcf 0 n = n | hcf 1 _ = 1 | hcf m n = hcf (n mod m) m;
in
  fun gcd m n =
    let
      val m = Int.abs m
      val n = Int.abs n
    in
      if m < n then hcf m n else hcf n m
    end;
end;

(* ------------------------------------------------------------------------- *)
(* Strings                                                                   *)
(* ------------------------------------------------------------------------- *)

local
  fun len l = (length l, l)
  val upper = len (explode "ABCDEFGHIJKLMNOPQRSTUVWXYZ");
  val lower = len (explode "abcdefghijklmnopqrstuvwxyz");
  fun rotate (n,l) c k = List.nth (l, (k+Option.valOf(index(equal c)l)) mod n);
in
  fun rot k c =
    if Char.isLower c then rotate lower c k
    else if Char.isUpper c then rotate upper c k
    else c;
end;

fun nchars x =
  let fun dup _ 0 l = l | dup x n l = dup x (n - 1) (x :: l)
  in fn n => implode (dup x n [])
  end;

fun chomp s =
    let
      val n = size s
    in
      if n = 0 orelse String.sub (s, n - 1) <> #"\n" then s
      else String.substring (s, 0, n - 1)
    end;

local
  fun chop [] = []
    | chop (l as (h :: t)) = if Char.isSpace h then chop t else l;
in
  val unpad = implode o chop o rev o chop o rev o explode;
end;

fun join _ [] = "" | join s (h :: t) = foldl (fn (x,y) => y ^ s ^ x) h t;

local
  fun match [] l = SOME l
    | match _ [] = NONE
    | match (x :: xs) (y :: ys) = if x = y then match xs ys else NONE;

  fun stringify acc [] = acc
    | stringify acc (h :: t) = stringify (implode h :: acc) t;
in
  fun split sep =
    let
      val pat = String.explode sep
      fun div1 prev recent [] = stringify [] (rev recent :: prev)
        | div1 prev recent (l as h :: t) =
        case match pat l of NONE => div1 prev (h :: recent) t
        | SOME rest => div1 (rev recent :: prev) [] rest
    in
      fn s => div1 [] [] (explode s)
    end;
end;

fun variant x vars = if mem x vars then variant (x ^ "'") vars else x;

fun variant_num x vars =
  let
    fun xn n = x ^ int_to_string n
    fun v n = let val x' = xn n in if mem x' vars then v (n + 1) else x' end
  in
    if mem x vars then v 1 else x
  end;

fun dest_prefix p =
  let
    fun check s = assert (String.isPrefix p s) (Error "dest_prefix")
    val size_p = size p
  in
    fn s => (check s; String.extract (s, size_p, NONE))
  end;

fun is_prefix p = can (dest_prefix p);

fun mk_prefix p s = p ^ s;

fun align_table {left,pad} =
  let
    fun pad_col n s =
      let val p = nchars pad (n - size s)
      in if left then s ^ p else p ^ s
      end
    fun pad_cols (l as [] :: _) = map (K "") l
      | pad_cols l =
      let
        val hs = map hd l
        val (n,_) = min (Int.compare o swap) (map size hs)
        val last_left = left andalso length (hd l) = 1
        val hs = if last_left then hs else map (pad_col n) hs
      in
        zipwith (fn x => fn y => x ^ y) hs (pad_cols (map tl l))
      end
  in
    pad_cols
  end;

(* ------------------------------------------------------------------------- *)
(* Reals.                                                                    *)
(* ------------------------------------------------------------------------- *)

val real_to_string = Real.toString;

fun percent_to_string x = int_to_string (Real.round (100.0 * x)) ^ "%";

fun pos r = Real.max (r,0.0);

local val ln2 = Math.ln 2.0 in fun log2 x = Math.ln x / ln2 end;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

(* Generic pretty-printers *)

type 'a pp = ppstream -> 'a -> unit;

val LINE_LENGTH = ref 75;

fun pp_map f pp_a (ppstrm : ppstream) x : unit = pp_a ppstrm (f x);

fun pp_bracket l r pp_a pp a =
  (PP.begin_block pp PP.INCONSISTENT (size l); PP.add_string pp l; pp_a pp a;
   PP.add_string pp r; PP.end_block pp);

fun pp_sequence sep pp_a pp =
  let fun pp_x x = (PP.add_string pp sep; PP.add_break pp (1,0); pp_a pp x)
  in fn [] => () | h :: t => (pp_a pp h; app pp_x t)
  end;

fun pp_binop s pp_a pp_b pp (a,b) =
  (PP.begin_block pp PP.INCONSISTENT 0;
   pp_a pp a;
   PP.add_string pp s;
   PP.add_break pp (1,0);
   pp_b pp b;
   PP.end_block pp);

(* Pretty-printers for common types *)

fun pp_string pp s =
  (PP.begin_block pp PP.INCONSISTENT 0;
   PP.add_string pp s;
   PP.end_block pp);

val pp_unit = pp_map (fn () => "()") pp_string;

val pp_char = pp_map str pp_string;

val pp_bool = pp_map bool_to_string pp_string;

val pp_int = pp_map int_to_string pp_string;

val pp_real = pp_map real_to_string pp_string;

val pp_order = pp_map order_to_string pp_string;

val pp_porder =
  pp_map (fn NONE => "INCOMPARABLE" | SOME x => order_to_string x) pp_string;

fun pp_list pp_a = pp_bracket "[" "]" (pp_sequence "," pp_a);

fun pp_pair pp_a pp_b = pp_bracket "(" ")" (pp_binop "," pp_a pp_b);

fun pp_triple pp_a pp_b pp_c =
  pp_bracket "(" ")"
  (pp_map (fn (a, b, c) => (a, (b, c)))
   (pp_binop "," pp_a (pp_binop "," pp_b pp_c)));

fun to_string pp_a a = PP.pp_to_string (!LINE_LENGTH) pp_a a;

(* ------------------------------------------------------------------------- *)
(* Sums                                                                      *)
(* ------------------------------------------------------------------------- *)

datatype ('a, 'b) sum = INL of 'a | INR of 'b

fun is_inl (INL _) = true | is_inl (INR _) = false;

fun is_inr (INR _) = true | is_inr (INL _) = false;

fun pp_sum pp_a _ pp (INL a) = pp_a pp a
  | pp_sum _ pp_b pp (INR b) = pp_b pp b;

(* ------------------------------------------------------------------------- *)
(* Maplets.                                                                  *)
(* ------------------------------------------------------------------------- *)

datatype ('a, 'b) maplet = op|-> of 'a * 'b;

fun pp_maplet pp_a pp_b =
  pp_map (fn a |-> b => (a, b)) (pp_binop " |->" pp_a pp_b);

(* ------------------------------------------------------------------------- *)
(* Trees.                                                                    *)
(* ------------------------------------------------------------------------- *)

datatype ('a, 'b) tree = BRANCH of 'a * ('a, 'b) tree list | LEAF of 'b;

local
  fun f (LEAF _) = {leaves = 1, branches = 0}
    | f (BRANCH (_, ts)) = foldl g {leaves = 0, branches = 1} ts
  and g (t, {leaves = l, branches = b}) =
    let val {leaves=l', branches=b'} = f t in {leaves=l+l', branches=b+b'} end;
in
  fun tree_size t = f t;
end;

fun tree_foldr f_b f_l (LEAF l) = f_l l
  | tree_foldr f_b f_l (BRANCH (p, s)) = f_b p (map (tree_foldr f_b f_l) s);

fun tree_foldl f_b f_l =
  let
    fun fold state (LEAF l, res) = f_l l state :: res
      | fold state (BRANCH (p, ts), res) = foldl (fold (f_b p state)) res ts
  in
    fn state => fn t => fold state (t, [])
  end;

fun tree_partial_foldl f_b f_l =
  let
    fun fold state (LEAF l, res) =
      (case f_l l state of NONE => res | SOME x => x :: res)
      | fold state (BRANCH (p, ts), res) =
      (case f_b p state of NONE => res | SOME s => foldl (fold s) res ts)
  in
    fn state => fn t => fold state (t, [])
  end;

(* ------------------------------------------------------------------------- *)
(* mlibUseful impure features                                                    *)
(* ------------------------------------------------------------------------- *)

fun op== (x,y) = mlibPortable.pointer_eq x y;

fun memoize f = let val s = Susp.delay f in fn () => Susp.force s end;

local
  val generator = ref 0
in
  fun new_int () = let val n = !generator val () = generator := n + 1 in n end;

  fun new_ints 0 = []
    | new_ints k =
    let val n = !generator val () = generator := n + k in interval n k end;
end;

local
  val gen = Random.newgenseed 1.0;
in
  fun uniform () = Random.random gen;
  fun coin_flip () = Random.range (0,2) gen = 0;
end;

fun with_flag (r,update) f x =
  let
    val old = !r
    val () = r := update old
    val y = f x handle e => (r := old; raise e)
    val () = r := old
  in
    y
  end;

fun cached cmp f =
    let
      val cache = ref (Binarymap.mkDict cmp)
    in
      fn x =>
      case Binarymap.peek (!cache,x) of
        SOME y => y
      | NONE =>
        let
          val y = f x
          val () = cache := Binarymap.insert (!cache,x,y)
        in
          y
        end
    end;

(* ------------------------------------------------------------------------- *)
(* Environment.                                                              *)
(* ------------------------------------------------------------------------- *)

val host = Option.getOpt (OS.Process.getEnv "HOSTNAME", "unknown");

val date = Date.fmt "%H:%M:%S %d/%m/%Y" o Date.fromTimeLocal o Time.now;

val today = Date.fmt "%d/%m/%Y" o Date.fromTimeLocal o Time.now;

local
  fun err x s = TextIO.output (TextIO.stdErr, x ^ ": " ^ s ^ "\n");
in
  val warn = err "WARNING";
  fun die s = (err "\nFATAL ERROR" s; OS.Process.exit OS.Process.failure);
end

fun read_textfile {filename} =
  let
    open TextIO
    val h = openIn filename
    val contents = inputAll h
    val () = closeIn h
  in
    contents
  end;

fun write_textfile {filename,contents} =
  let
    open TextIO
    val h = openOut filename
    val () = output (h,contents)
    val () = closeOut h
  in
    ()
  end;

end
