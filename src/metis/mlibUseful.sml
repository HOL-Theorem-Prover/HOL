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

val tracing = ref 0;

val traces : {module : string, alignment : int -> int} list ref = ref [];

local
  val MAX = 10;
  fun query m l =
    let val t = List.find (fn {module, ...} => module = m) (!traces)
    in case t of NONE => MAX | SOME {alignment, ...} => alignment l
    end;
in
  fun visible {module = m, level = l} =
    0 < !tracing andalso (MAX <= !tracing orelse query m l <= !tracing);
end;

local
  val trace_printer = Lib.say;
in
  fun trace {module = m, message = s, level = l} =
    if visible {module = m, level = l} then trace_printer s else ();
end;

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

fun lex_compare f =
  let
    fun lex [] = EQUAL
      | lex (x :: l) = case f x of EQUAL => lex l | y => y
  in
    lex
  end;

(* ------------------------------------------------------------------------- *)
(* Finding the minimal element of a list, wrt some order.                    *)
(* ------------------------------------------------------------------------- *)

fun min cmp =
  let
    fun min_acc (l, x, r) _ [] = (x, List.revAppend (l, r))
      | min_acc (best as (_, x, _)) l (h :: t) =
      min_acc (case cmp (h, x) of LESS => (l, h, t) | _ => best) (h :: l) t
  in
    fn [] => raise ERR "min" "empty list"
     | h :: t => min_acc ([], h, t) [] t
  end;

(* ------------------------------------------------------------------------- *)
(* Merge (for the following merge-sort, but generally useful too).           *)
(* ------------------------------------------------------------------------- *)

fun merge cmp =
  let
    fun mrg acc [] ys = List.revAppend (acc, ys)
      | mrg acc xs [] = List.revAppend (acc, xs)
      | mrg acc (xs as x :: xt) (ys as y :: yt) =
      (case cmp (x, y) of GREATER => mrg (y :: acc) xs yt
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
      | f xs = let val (l, r) = split xs (length xs div 2) in m (f l) (f r) end
  in
    f
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

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

type 'a pp = ppstream -> 'a -> unit;

val LINE_LENGTH = ref 75;

fun unit_pp pp_a a pp () = pp_a pp a;

fun pp_unit_pp pp upp = upp pp ();

fun pp_map f pp_a (ppstrm : ppstream) x : unit = pp_a ppstrm (f x);

fun pp_bracket (l, r) pp_a pp a =
  (PP.begin_block pp PP.INCONSISTENT (size l); PP.add_string pp l; pp_a pp a;
   PP.add_string pp r; PP.end_block pp);

fun pp_sequence sep pp_a =
  let
    fun pp_elt pp x = (PP.add_string pp sep; PP.add_break pp (1, 0); pp_a pp x)
    fun pp_seq pp []       = ()
      | pp_seq pp (h :: t) = (pp_a pp h; app (pp_elt pp) t)
  in
    fn pp => fn l =>
    (PP.begin_block pp PP.INCONSISTENT 0; pp_seq pp l; PP.end_block pp)
  end;

fun pp_unop s pp_a pp a =
  (PP.begin_block pp PP.CONSISTENT 0;
   PP.add_string pp s;
   PP.add_break pp (1, 0);
   pp_a pp a;
   PP.end_block pp);

fun pp_binop s pp_a pp_b pp (a, b) =
  (PP.begin_block pp PP.INCONSISTENT 0;
   pp_a pp a;
   PP.add_string pp s;
   PP.add_break pp (1, 0);
   pp_b pp b;
   PP.end_block pp);

fun pp_nothing pp _ = (PP.begin_block pp PP.CONSISTENT 0; PP.end_block pp);

fun pp_string pp s =
  (PP.begin_block pp PP.CONSISTENT 0; PP.add_string pp s; PP.end_block pp);

fun pp_unit pp = pp_map (K "()") pp_string pp;

val pp_bool = pp_map bool_to_string pp_string;

val pp_int = pp_map int_to_string pp_string;

val pp_real = pp_map real_to_string pp_string;

val pp_order =
  pp_map (fn LESS => "LESS" | EQUAL => "EQUAL" | GREATER => "GREATER")
  pp_string;

fun pp_list pp_a = pp_bracket ("[", "]") (pp_sequence "," pp_a);

fun pp_pair pp_a pp_b = pp_bracket ("(", ")") (pp_binop "," pp_a pp_b);

fun pp_triple pp_a pp_b pp_c =
  pp_bracket ("(", ")")
  (pp_map (fn (a, b, c) => (a, (b, c)))
   (pp_binop "," pp_a (pp_binop "," pp_b pp_c)));

local fun pp_l pp = pp_sequence "," (pp_binop " =" pp_string pp_unit_pp) pp;
in fun pp_record l = pp_bracket ("{", "}") (unit_pp pp_l l);
end;

fun pp_option pp_a pp NONE = pp_string pp "NONE"
  | pp_option pp_a pp (SOME a) = pp_unop "SOME" pp_a pp a;

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

end
