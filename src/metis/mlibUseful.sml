(* ========================================================================= *)
(* ML UTILITY FUNCTIONS                                                      *)
(* Created by Joe Hurd, April 2001                                           *)
(* ========================================================================= *)

structure mlibUseful :> mlibUseful =
struct

infixr 0 oo ## |->;

(* ------------------------------------------------------------------------- *)
(* Exceptions, profiling and tracing.                                        *)
(* ------------------------------------------------------------------------- *)

exception ERR_EXN of {origin_function : string, message : string};
exception BUG_EXN of {origin_function : string, message : string};

fun ERR f s = ERR_EXN {origin_function = f, message = s};
fun BUG f s = BUG_EXN {origin_function = f, message = s};

fun ERR_to_string (ERR_EXN {origin_function, message}) =
  "\nERR in function " ^ origin_function ^ ":\n" ^ message ^ "\n"
  | ERR_to_string _ = raise BUG "ERR_to_string" "not an ERR_EXN";

fun BUG_to_string (BUG_EXN {origin_function, message}) =
  "\nBUG in function " ^ origin_function ^ ":\n" ^ message ^ "\n"
  | BUG_to_string _ = raise BUG "BUG_to_string" "not a BUG_EXN";

local
  fun p {origin_function, message} = origin_function ^ ": \"" ^ message ^ "\"";
in
  fun report (ERR_EXN m) = "ERR in " ^ p m
    | report (BUG_EXN m) = "BUG in " ^ p m
    | report _ = raise BUG "report" "not an ERR_EXN or BUG_EXN";
end;

fun assert b e = if b then () else raise e;

fun try f a = f a
  handle h as ERR_EXN _ => (print (ERR_to_string h); raise h)
       | b as BUG_EXN _ => (print (BUG_to_string b); raise b)
       | e => (print "\ntry: strange exception raised\n"; raise e);

fun total f x = SOME (f x) handle ERR_EXN _ => NONE;

fun can f = Option.isSome o total f;

fun partial (e as ERR_EXN _) f x = (case f x of SOME y => y | NONE => raise e)
  | partial _ _ _ = raise BUG "partial" "must take a ERR_EXN";

fun timed f a =
  let
    val tmr = Timer.startCPUTimer ()
    val res = f a
    val {usr, sys, ...} = Timer.checkCPUTimer tmr
  in
    (Time.toReal usr + Time.toReal sys, res)
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
fun pair x y = (x,y)     (* Note: val add_fst = pair and add_snd = C pair; *)
fun swap (x,y) = (y,x);
fun curry f x y = f (x,y);
fun uncurry f (x,y) = f x y;
fun equal x y = (x = y);

(* ------------------------------------------------------------------------- *)
(* State transformers.                                                       *)
(* ------------------------------------------------------------------------- *)

val unit : 'a -> 's -> 'a * 's = pair;

fun bind f (g : 'a -> 's -> 'b * 's) = uncurry g o f;

fun mmap f (m : 's -> 'a * 's) = bind m (unit o f);

fun join (f : 's -> ('s -> 'a * 's) * 's) = bind f I;

fun mwhile c b = let fun f a = if c a then bind (b a) f else unit a in f end;

(* ------------------------------------------------------------------------- *)
(* Lists.                                                                    *)
(* ------------------------------------------------------------------------- *)

fun cons x y = x :: y;
fun append xs ys = xs @ ys;
fun wrap a = [a];
fun unwrap [a] = a | unwrap _ = raise ERR "unwrap" "not a singleton";

fun first f [] = NONE
  | first f (x :: xs) = (case f x of NONE => first f xs | s => s);

fun index p =
  let
    fun idx _ [] = NONE
      | idx n (x :: xs) = if p x then SOME n else idx (n + 1) xs
  in
    idx 0
  end;

(* This is the pure version
fun maps (_ : 'a -> 's -> 'b * 's) [] = unit []
  | maps f (x :: xs) =
  bind (f x) (fn y => bind (maps f xs) (fn ys => unit (y :: ys)));
*)

(* This is an optimized version *)
fun maps f =
  let fun g (x, (ys, s)) = let val (y, s) = f x s in (y :: ys, s) end
  in fn l => fn (s : 's) => (rev ## I) (foldl g ([], s) l)
  end;

(* This is the pure version
fun partial_maps (_ : 'a -> 's -> 'b option * 's) [] = unit []
  | partial_maps f (x :: xs) =
  bind (f x)
  (fn yo => bind (partial_maps f xs)
   (fn ys => unit (case yo of NONE => ys | SOME y => y :: ys)));
*)

(* This is an optimized version *)
fun partial_maps f =
  let
    fun g (x, (ys, s)) =
      let val (yo, s) = f x s
      in (case yo of NONE => ys | SOME y => y :: ys, s)
      end
  in
    fn l => fn (s : 's) => (rev ## I) (foldl g ([], s) l)
  end;

fun enumerate n = fst o C (maps (fn x => fn m => ((m, x), m + 1))) n;

fun zipwith f =
  let
    fun z l [] [] = l
      | z l (x :: xs) (y :: ys) = z (f x y :: l) xs ys
      | z _ _ _ = raise ERR "zipwith" "lists different lengths";
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
  fun split l n = aux [] l n;
end;

fun update_nth f n l =
  let
    val (a, b) = split l n
  in
    case b of [] => raise Subscript
    | h :: t => a @ (f h :: t)
  end;

(* ------------------------------------------------------------------------- *)
(* Lists-as-sets.                                                            *)
(* ------------------------------------------------------------------------- *)

fun mem x = List.exists (equal x);

fun insert x s = if mem x s then s else x :: s;
fun delete x s = List.filter (not o equal x) s;

(* Removes duplicates *)
fun setify s = foldl (fn (v, x) => if mem v x then x else v :: x) [] s;

(* For all three set operations: if s has duplicates, so may the result. *)
fun union s t = foldl (fn (v, x) => if mem v x then x else v :: x) s t;
fun intersect s t = foldl (fn (v, x) => if mem v t then v :: x else x) [] s;
fun subtract s t = foldl (fn (v, x) => if mem v t then x else v :: x) [] s;

fun subset s t = List.all (fn x => mem x t) s;

fun distinct [] = true
  | distinct (x :: rest) = not (mem x rest) andalso distinct rest;

(* ------------------------------------------------------------------------- *)
(* Comparisons.                                                              *)
(* ------------------------------------------------------------------------- *)

fun rev_order f xy =
  case f xy of LESS => GREATER | EQUAL => EQUAL | GREATER => LESS;

fun lex_combine f g ((a,c),(b,d)) = case f (a,b) of EQUAL => g (c,d) | x => x;

fun lex_compare f =
  let
    fun lex [] [] = EQUAL
      | lex [] (_ :: _) = LESS
      | lex (_ :: _) [] = GREATER
      | lex (x :: xs) (y :: ys) = case f (x,y) of EQUAL => lex xs ys | r => r
  in
    uncurry lex
  end;

(* ------------------------------------------------------------------------- *)
(* Finding the minimal element of a list, wrt some order.                    *)
(* ------------------------------------------------------------------------- *)

fun min cmp =
  let
    fun min_acc (l,m,r) _ [] = (m, List.revAppend (l,r))
      | min_acc (best as (_,m,_)) l (x :: r) =
      min_acc (case cmp (x,m) of LESS => (l,x,r) | _ => best) (x :: l) r
  in
    fn [] => raise ERR "min" "empty list"
     | h :: t => min_acc ([],h,t) [h] t
  end;

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
(* Merge sort.                                                               *)
(* ------------------------------------------------------------------------- *)

fun sort cmp =
  let
    val m = merge cmp
    fun f [] = []
      | f (xs as [_]) = xs
      | f xs = let val (l,r) = split xs (length xs div 2) in m (f l) (f r) end
  in
    f
  end;

fun sort_map f cmp xs =
  let
    fun ncmp ((m,_),(n,_)) = cmp (m,n)
    val nxs = map (fn x => (f x, x)) xs
    val nys = sort ncmp nxs
  in
    map snd nys
  end;

(* ------------------------------------------------------------------------- *)
(* Integers.                                                                 *)
(* ------------------------------------------------------------------------- *)

val int_to_string = Int.toString;
val string_to_int = Option.valOf o Int.fromString;

fun int_to_bits 0 = []
  | int_to_bits n = (n mod 2 <> 0) :: (int_to_bits (n div 2));

fun bits_to_int [] = 0
  | bits_to_int (h :: t) = (if h then curry op+ 1 else I) (2 * bits_to_int t);

fun interval m 0 = []
  | interval m len = m :: interval (m + 1) (len - 1);

fun divides a b = if a = 0 then b = 0 else b mod (Int.abs a) = 0;

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
(* Strings.                                                                  *)
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
    fun check s = assert (String.isPrefix p s) (ERR "dest_prefix" "")
    val size_p = size p
  in
    fn s => (check s; String.extract (s, size_p, NONE))
  end;

fun is_prefix p = can (dest_prefix p);

fun mk_prefix p s = p ^ s;

(* ------------------------------------------------------------------------- *)
(* Reals.                                                                    *)
(* ------------------------------------------------------------------------- *)

val real_to_string = Real.toString;

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

val pp_string = PP.add_string;

fun pp_unit pp = pp_map (K "()") pp_string pp;

val pp_bool = pp_map bool_to_string pp_string;

val pp_int = pp_map int_to_string pp_string;

val pp_real = pp_map real_to_string pp_string;

val pp_order =
  pp_map (fn LESS => "LESS" | EQUAL => "EQUAL" | GREATER => "GREATER")
  pp_string;

val pp_porder =
  pp_map (fn NONE => "INCOMPARABLE" | SOME LESS => "LESS" |
          SOME EQUAL => "EQUAL" | SOME GREATER => "GREATER") pp_string;

fun pp_list pp_a = pp_bracket "[" "]" (pp_sequence "," pp_a);

fun pp_pair pp_a pp_b = pp_bracket "(" ")" (pp_binop "," pp_a pp_b);

fun pp_triple pp_a pp_b pp_c =
  pp_bracket "(" ")"
  (pp_map (fn (a, b, c) => (a, (b, c)))
   (pp_binop "," pp_a (pp_binop "," pp_b pp_c)));

local
  fun pad1 n s = funpow (n - size s) (fn x => " " ^ x) s;

  fun pad (l as [] :: _) = l
    | pad l =
    let
      val hs = map hd l
      val ts = pad (map tl l)
      val (n,_) = min (Int.compare o swap) (map size hs)
      val hs = map (pad1 n) hs
    in
      zipwith cons hs ts
    end;

  fun pp_row pp sl =
    (pp_bracket "[ " " ]" (pp_sequence "" pp_string) pp sl;
     PP.add_newline pp)
in
  fun pp_table pp tab =
    let
      val tab = pad tab
    in
      (PP.begin_block pp PP.INCONSISTENT 2;
       app (pp_row pp) tab;
       PP.end_block pp)
    end;
end;
  
(* ------------------------------------------------------------------------- *)
(* Sums.                                                                     *)
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
(* mlibUseful imperative features.                                               *)
(* ------------------------------------------------------------------------- *)

fun lazify_thunk f = let val s = Susp.delay f in fn () => Susp.force s end;

local
  val generator = ref 0
in
  fun new_int () = let val n = !generator val () = generator := n + 1 in n end;

  fun new_ints 0 = []
    | new_ints k =
    let val n = !generator val () = generator := n + k in interval n k end;
end;

fun with_flag (r, update) f x =
  let
    val old = !r
    val () = r := update old
    val y = f x handle e => (r := old; raise e)
    val () = r := old
  in
    y
  end;

(* ------------------------------------------------------------------------- *)
(* Information about the environment.                                        *)
(* ------------------------------------------------------------------------- *)

val host = Option.getOpt (OS.Process.getEnv "HOSTNAME", "unknown");

val date = Date.fmt "%H:%M:%S %d/%m/%Y" o Date.fromTimeLocal o Time.now;

val today = Date.fmt "%d/%m/%Y" o Date.fromTimeLocal o Time.now;

(* ------------------------------------------------------------------------- *)
(* Command line arguments.                                                   *)
(* ------------------------------------------------------------------------- *)

exception Optionexit of {message : string option, usage : bool, success : bool};

type Opt = {switches : string list, arguments : string list,
            description : string, processor : string * string list -> unit};

type Allopts = {name : string, head : string, foot : string, opts : Opt list};

val version_string = ref "";

fun version_information () =
  let
    val s = !version_string
  in
    if s = "" then
      raise Optionexit {message = SOME "no version information available",
                        usage = false, success = true}
    else
      (print s;
       raise Optionexit {message = NONE, usage = false, success = true})
  end;

val basic_options : Opt list =
  [{switches = ["--verbosity"], arguments = ["0..10"],
    description = "the degree of verbosity",
    processor = fn (_,l) => trace_level := string_to_int (hd l)},
   {switches = ["--secret"], arguments = [],
    description = "process then hide the next option",
    processor = fn _ => raise Fail "basic_options: --secret"},
   {switches = ["--"], arguments = [],
    description = "no more options",
    processor = fn _ => raise Fail "basic_options: --"},
   {switches = ["-?","-h","--help"], arguments = [],
    description = "display all options and exit",
    processor = fn _ => raise Optionexit
    {message = SOME "displaying all options", usage = true, success = true}},
   {switches = ["-v", "--version"], arguments = [],
    description = "display version information",
    processor = fn _ => version_information ()}];

fun process_options ({name, head, foot, opts} : Allopts) =
  let
    fun exit true = OS.Process.exit OS.Process.success
      | exit false = OS.Process.exit OS.Process.failure
    fun join _ [] = raise Fail "process_options"
      | join s ("" :: t) = "  " ^ join s t
      | join s (h :: t) = foldl (fn (x,y) => y ^ s ^ x) h t
    fun list_opts {switches = n, arguments = r, description = s, ...} =
      (foldl (fn (x,y) => y ^ " " ^ x) (join ", " n) r, s)
    val usage_message =
      let
        val l = map list_opts opts
        val (n,_) = min (rev_order Int.compare) (map (size o fst) l)
        fun f ((x,d),s) =
          let val m = size x in s^"  "^x^nchars #" " (n + 2 - m) ^ d ^ "\n" end
      in
        head ^ foldl f "" l ^ foot
      end
    fun escape {message, usage, success} =
      (case message of NONE => () | SOME m => print (name ^ ": " ^ m ^ "\n");
       if usage then print usage_message else ();
       exit success)

    fun process [] = ([], [])
      | process ("--" :: xs) = ([("--",[])], xs)
      | process ("--secret" :: xs) = (tl ## I) (process xs)
      | process (x :: xs) =
      (case List.find (fn {switches = n, ...} => mem x n) opts of
         NONE =>
           if hd (explode x) <> #"-" then ([], x :: xs)
           else escape {message = SOME ("unknown switch \"" ^ x ^ "\""),
                        usage = true, success = false}
       | SOME {arguments = r, processor = f, ...} =>
         let
           val m = length r
           val () =
             if m <= length xs then ()
             else escape {message = SOME
                          (x ^ " options needs "
                           ^ (if m = 1 then "a following argument"
                              else int_to_string m ^ " following arguments")
                           ^ " (" ^ join " " r ^ ")"),
                          usage = true, success = false}
           val (ys,xs) = split xs m
           val () = f (x,ys)
         in
           (cons (x,ys) ## I) (process xs)
         end)
  in
    fn l =>
    let
      val () = if null l then version_information () else ()
      val (a,b) = process l
      val a = foldl (fn ((x,xs),ys) => x :: xs @ ys) [] (rev a)
    in
      (a,b)
    end
    handle Optionexit x => escape x
  end;

end
