(* ========================================================================= *)
(* A POSSIBLY-INFINITE STREAM DATATYPE FOR ML                                *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

structure mlibStream :> mlibStream =
struct

open mlibUseful;

infixr 0 oo ##;

(* ------------------------------------------------------------------------- *)
(* The datatype declaration encapsulates all the primitive operations        *)
(* ------------------------------------------------------------------------- *)

datatype 'a stream = NIL | CONS of 'a * (unit -> 'a stream);

(* ------------------------------------------------------------------------- *)
(* mlibStream constructors                                                       *)
(* ------------------------------------------------------------------------- *)

fun repeat x = let fun rep () = CONS (x, rep) in rep () end;

fun count n = CONS (n, fn () => count (n + 1));

fun powers f x = CONS (x, fn () => powers f (f x));

(* ------------------------------------------------------------------------- *)
(* mlibStream versions of standard list operations: these should all terminate   *)
(* ------------------------------------------------------------------------- *)

fun cons h t = CONS (h,t);

fun null NIL = true | null (CONS _) = false;

fun hd NIL = raise Empty | hd (CONS (h, _)) = h;

fun tl NIL = raise Empty | tl (CONS (_, t)) = t ();

fun hd_tl s = (hd s, tl s);

fun sing s = CONS (s, K NIL);

fun append NIL s = s ()
  | append (CONS (h,t)) s = CONS (h, fn () => append (t ()) s);

fun map f =
  let
    fun m NIL = NIL
      | m (CONS (h, t)) = CONS (f h, fn () => m (t ()))
  in
    m
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

fun zipwith f =
  let
    fun z NIL _ = NIL
      | z _ NIL = NIL
      | z (CONS (x,xs)) (CONS (y,ys)) =
      CONS (f x y, fn () => z (xs ()) (ys ()))
  in
    z
  end;

fun zip s t = zipwith pair s t;

fun take 0 _ = NIL
  | take n NIL = raise Subscript
  | take 1 (CONS (x,_)) = CONS (x, K NIL)
  | take n (CONS (x,xs)) = CONS (x, fn () => take (n - 1) (xs ()));

fun drop n s = funpow n tl s handle Empty => raise Subscript;

(* ------------------------------------------------------------------------- *)
(* mlibStream versions of standard list operations: these might not terminate    *)
(* ------------------------------------------------------------------------- *)

local fun len n NIL = n | len n (CONS (_,t)) = len (n + 1) (t ());
in fun length s = len 0 s;
end;

fun exists pred =
  let fun f NIL = false | f (CONS (h,t)) = pred h orelse f (t ()) in f end;

fun all pred = not o exists (not o pred);

fun filter p NIL = NIL
  | filter p (CONS (x,xs)) =
  if p x then CONS (x, fn () => filter p (xs ())) else filter p (xs ());

fun foldl f =
  let
    fun fold b NIL = b
      | fold b (CONS (h,t)) = fold (f (h,b)) (t ())
  in
    fold
  end;

fun flatten NIL = NIL
  | flatten (CONS (NIL, ss)) = flatten (ss ())
  | flatten (CONS (CONS (x, xs), ss)) =
  CONS (x, fn () => flatten (CONS (xs (), ss)));

fun partial_map f =
  let
    fun mp NIL = NIL
      | mp (CONS (h,t)) =
      case f h of NONE => mp (t ())
      | SOME h' => CONS (h', fn () => mp (t ()))
  in
    mp
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

(* ------------------------------------------------------------------------- *)
(* mlibStream operations                                                         *)
(* ------------------------------------------------------------------------- *)

fun memoize NIL = NIL
  | memoize (CONS (h,t)) = CONS (h, mlibUseful.memoize (fn () => memoize (t ())));

local
  fun to_lst res NIL = rev res
    | to_lst res (CONS (x, xs)) = to_lst (x :: res) (xs ());
in
  fun to_list s = to_lst [] s;
end;

fun from_list [] = NIL
  | from_list (x :: xs) = CONS (x, fn () => from_list xs);

fun to_textfile {filename = f} s =
  let
    open TextIO
    val (h,c) = if f = "-" then (stdOut, K ()) else (openOut f, closeOut)
    fun to_file NIL = ()
      | to_file (CONS (x,y)) = (output (h,x); to_file (y ()))
    val () = to_file s
  in
    c h
  end;

fun from_textfile {filename = f} =
  let
    open TextIO
    val (h,c) = if f = "-" then (stdIn, K ()) else (openIn f, closeIn)
    fun res () = case inputLine h of "" => (c h; NIL) | s => CONS (s,res)
  in
    memoize (res ())
  end;

end
