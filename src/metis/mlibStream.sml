(* ========================================================================= *)
(* A POSSIBLY-INFINITE STREAM DATATYPE FOR ML                                *)
(* Created by Joe Hurd, April 2001                                           *)
(* ========================================================================= *)

structure mlibStream :> mlibStream =
struct

open mlibUseful;

infixr 0 oo ##;

(* ------------------------------------------------------------------------- *)
(* The datatype declaration encapsulates all the primitive operations.       *)
(* ------------------------------------------------------------------------- *)

datatype 'a stream = NIL | CONS of 'a * (unit -> 'a stream);

type 'a Sthk = unit -> 'a stream;

(* ------------------------------------------------------------------------- *)
(* mlibUseful functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun cons h t = CONS (h, t);

fun null NIL = true | null (CONS _) = false;

fun hd NIL = raise Empty | hd (CONS (h, _)) = h;

fun tl NIL = raise Empty | tl (CONS (_, t)) = t ();

fun dest s = (hd s, tl s);

fun repeat x = let fun rep () = CONS (x, rep) in rep () end;

fun count n = CONS (n, fn () => count (n + 1));

fun foldl f =
  let
    fun fold b NIL = INL b
      | fold b (CONS (h,t)) = case f (h,b) of INL b => fold b (t ()) | c => c
  in
    fold
  end;

fun foldr b c =
  let fun f NIL = c | f (CONS (x, xs)) = b (x, fn () => f (xs ())) in f end;

fun map f =
  let
    fun m NIL = NIL
      | m (CONS (h, t)) = CONS (f h, fn () => m (t ()))
  in
    m
  end;

fun map_thk f =
  let
    fun mt NIL = NIL
      | mt (CONS (h, t)) = CONS (h, mt' t)
    and mt' t = f (fn () => mt (t ()))
  in
    mt'
  end;

fun partial_map f =
  let
    fun mp NIL = NIL
      | mp (CONS (h, t)) =
      case f h of NONE => mp (t ())
      | SOME h' => CONS (h', fn () => mp (t ()))
  in
    mp
  end;

fun maps f =
  let
    fun mm _ NIL = NIL
      | mm s (CONS (x, xs)) =
      let val (y, s') = f x s
      in CONS (y, fn () => mm s' (xs ()))
      end
  in
    mm
  end;

fun partial_maps f =
  let
    fun mm _ NIL = NIL
      | mm s (CONS (x, xs)) =
      let
        val (yo, s') = f x s
        val t = mm s' o xs
      in
        case yo of NONE => t () | SOME y => CONS (y, t)
      end
  in
    mm
  end;

fun filter f = partial_map (fn x => if f x then SOME x else NONE);

fun flatten NIL = NIL
  | flatten (CONS (NIL, ss)) = flatten (ss ())
  | flatten (CONS (CONS (x, xs), ss)) =
  CONS (x, fn () => flatten (CONS (xs (), ss)));

fun zipwith f =
  let
    fun z NIL _ = NIL
      | z _ NIL = NIL
      | z (CONS (x, xs)) (CONS (y, ys)) =
      CONS (f x y, fn () => z (xs ()) (ys ()))
  in
    z
  end;

fun zip s t = zipwith pair s t;

fun take 0 s = NIL
  | take n NIL = raise Subscript
  | take 1 (CONS (x, _)) = CONS (x, K NIL)
  | take n (CONS (x, xs)) = CONS (x, fn () => take (n - 1) (xs ()));

fun drop n s = funpow n tl s handle Empty => raise Subscript;

local
  fun to_lst res NIL = rev res
    | to_lst res (CONS (x, xs)) = to_lst (x :: res) (xs ());
in
  fun to_list s = to_lst [] s;
end;

fun from_list [] = NIL
  | from_list (x :: xs) = CONS (x, fn () => from_list xs);

fun from_textfile filename =
  let
    open TextIO
    val fh = openIn filename
    fun res () =
      case inputLine fh of "" => (closeIn fh; NIL)
      | s => CONS (s, lazify_thunk res)
  in
    res ()
  end;

end
