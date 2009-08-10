(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF TERMS                                *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

(*
app load ["mlibUseful", "mlibTerm"];
*)

(*
*)
structure mlibTermnet :> mlibTermnet =
struct

infixr |-> ::> oo;

open mlibUseful mlibTerm;

structure M = Binarymap; local open Binarymap in end;

(* ------------------------------------------------------------------------- *)
(* Tuning parameters.                                                        *)
(* ------------------------------------------------------------------------- *)

type parameters = {fifo : bool};

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

val flatten = List.concat;

val omap = Option.map;

(* ------------------------------------------------------------------------- *)
(* Variable and function maps                                                *)
(* ------------------------------------------------------------------------- *)

type 'a vmap = (string, 'a) M.dict;
fun empty_vmap () : 'a vmap = M.mkDict String.compare;

type 'a fmap = (string * int, 'a) M.dict;
fun empty_fmap () : 'a fmap = M.mkDict (lex_order String.compare Int.compare);

(* ------------------------------------------------------------------------- *)
(* Dealing with the terms that emerge from termnets.                         *)
(* ------------------------------------------------------------------------- *)

fun fifoize ({fifo, ...} : parameters) l =
  if fifo then sort (fn ((m,_),(n,_)) => Int.compare (m,n)) l else l;

fun finally parm l = map snd (fifoize parm l);

(* ------------------------------------------------------------------------- *)
(* Quotient terms                                                            *)
(* ------------------------------------------------------------------------- *)

datatype qterm = VAR | FN of (string * int) * qterm list;

fun qterm (Var _) = VAR
  | qterm (Fn (f,l)) = FN ((f, length l), map qterm l);

local
  fun qm [] = true
    | qm ((VAR, _) :: rest) = qm rest
    | qm ((FN _, Var _) :: _) = false
    | qm ((FN ((f,n),a), Fn (g,b)) :: rest) =
    f = g andalso n = length b andalso qm (zip a b @ rest);
in
  fun qmatch qtm tm = qm [(qtm,tm)];
end;

local
  fun update sub v qtm =
    (case M.peek (sub,v) of NONE => M.insert (sub,v,qtm)
     | SOME qtm' => if qtm = qtm' then sub else raise Error "matchq: vars");

  fun qn sub [] = sub
    | qn sub ((Var v, qtm) :: rest) = qn (update sub v qtm) rest
    | qn _ ((Fn _, VAR) :: _) = raise Error "matchq: match fn var"
    | qn sub ((Fn (f,a), FN ((g,n),b)) :: rest) =
    if f = g andalso length a = n then qn sub (zip a b @ rest)
    else raise Error "matchq: match fn fn";
in
  fun matchq sub tm qtm = qn sub [(tm,qtm)];
end;

local
  fun qv VAR x = x
    | qv x VAR = x
    | qv (FN (f,a)) (FN (g,b)) =
      let
        val () = assert (f = g) (Error "qunify: incompatible vars")
      in
        FN (f, zipwith qv a b)
      end;

  fun qu sub [] = sub
    | qu sub ((VAR, _) :: rest) = qu sub rest
    | qu sub ((qtm, Var v) :: rest) =
    let val qtm = case M.peek (sub,v) of NONE => qtm | SOME qtm' => qv qtm qtm'
    in qu (M.insert (sub, v, qtm)) rest
    end
    | qu sub ((FN ((f,n),a), Fn (g,b)) :: rest) =
    if f = g andalso n = length b then qu sub (zip a b @ rest)
    else raise Error "unifyq: structurally different";
in
  fun qunify qtm qtm' = total (qv qtm) qtm';
  fun unifyq sub qtm tm = total (qu sub) [(qtm,tm)];
end;

fun qterm' VAR = Var "_" | qterm' (FN ((f,_),l)) = Fn (f, map qterm' l);

val pp_qterm = pp_map qterm' pp_term;

(* ------------------------------------------------------------------------- *)
(* mlibTerm discrimination trees are optimized for match queries.                *)
(* ------------------------------------------------------------------------- *)

datatype 'a net =
  RESULT of 'a list
| SINGLE of qterm * 'a net
| MULTIPLE of 'a net option * 'a net fmap;

datatype 'a termnet = NET of parameters * int * (int * (int * 'a) net) option;

fun empty parm : 'a termnet = NET (parm,0,NONE);

fun size (NET (_,_,NONE)) = 0 | size (NET (_, _, SOME (i,_))) = i;

fun singles tms a = foldr SINGLE a tms;

local
  fun pre NONE = (0,NONE) | pre (SOME (i,n)) = (i, SOME n);
  fun add (RESULT l) [] (RESULT l') = RESULT (l @ l')
    | add a (input1 as tm :: tms) (SINGLE (tm',n)) =
    if tm = tm' then SINGLE (tm, add a tms n)
    else add a input1 (add n [tm'] (MULTIPLE (NONE, empty_fmap ())))
    | add a (VAR::tms) (MULTIPLE (vs,fs)) = MULTIPLE (SOME (oadd a tms vs), fs)
    | add a (FN (f,l) :: tms) (MULTIPLE (vs,fs)) =
    MULTIPLE (vs, M.insert (fs, f, oadd a (l @ tms) (M.peek (fs,f))))
    | add _ _ _ = raise Bug "mlibTermnet.insert: mlibMatch"
  and oadd a tms NONE = singles tms a
    | oadd a tms (SOME n) = add a tms n;
  fun ins a tm (i,n) = SOME (i + 1, oadd (RESULT [a]) [tm] n);
in
  fun insert (tm |-> a) (NET (p,k,n)) =
    NET (p, k + 1, ins (k,a) (qterm tm) (pre n))
    handle Error _ => raise Bug "mlibTermnet.insert: should never fail";
end;

local
  fun mat acc [] = acc
    | mat acc ((RESULT l, []) :: rest) = mat (l @ acc) rest
    | mat acc ((SINGLE (tm',n), tm :: tms) :: rest) =
    mat acc (if qmatch tm' tm then (n,tms) :: rest else rest)
    | mat acc ((MULTIPLE (vs,fs), tm :: tms) :: rest) =
    let
      val rest = case vs of NONE => rest | SOME n => (n,tms) :: rest
      val rest =
        case tm of Var _ => rest
        | Fn (f,l) =>
          (case M.peek (fs, (f, length l)) of NONE => rest
           | SOME n => (n, l @ tms) :: rest)
    in
      mat acc rest
    end
    | mat _ _ = raise Bug "mlibTermnet.match: mlibMatch";
in
  fun match (NET (_,_,NONE)) _ = []
    | match (NET (p, _, SOME (_,n))) tm = finally p (mat [] [(n,[tm])])
    handle Error _ => raise Bug "mlibTermnet.match: should never fail";
end;

fun harvest inc =
  let
    fun chk [] acc = acc
      | chk (([],[],[tm],net) :: rest) acc = chk rest (inc tm net acc)
      | chk ((pl, (f as (_,i), 0) :: fl, sl, n) :: l) acc =
      let val (a,b) = divide sl i
      in chk ((pl, fl, FN (f, rev a) :: b, n) :: l) acc
      end
      | chk ((pl, (f,j)::fl, sl, n) :: l) acc = get (pl,(f,j-1)::fl,sl,n) l acc
      | chk _ _ = raise Bug "mlibTermnet.harvest: mlibMatch 1"
    and get (p :: pl, fl, sl, SINGLE (t,n)) l acc =
      (case qunify p t of NONE => chk l acc
       | SOME t => chk ((pl, fl, t :: sl, n) :: l) acc)
      | get (VAR :: pl, fl, sl, MULTIPLE (vs,fs)) l acc =
      let
        fun fget (f as (_,i), n, x) =
          (funpow i (cons VAR) pl, (f,i) :: fl, sl, n) :: x
        val l = case vs of NONE => l | SOME n => (pl, fl, VAR :: sl, n) :: l
      in
        chk (M.foldr fget l fs) acc
      end
      | get (FN (f as (_,i), a) :: pl, fl, sl, MULTIPLE (_,fs)) l acc =
      (case M.peek (fs,f) of NONE => chk l acc
       | SOME n => chk ((a @ pl, (f,i) :: fl, sl, n) :: l) acc)
      | get _ _ _ = raise Bug "mlibTermnet.harvest: mlibMatch 2"
  in
    fn pat => fn net => fn acc => get ([pat],[],[],net) [] acc
  end;

local
  fun pat sub v = case M.peek (sub,v) of NONE => VAR | SOME qtm => qtm;

  fun inc sub v tms tm net rest = (M.insert (sub,v,tm), net, tms) :: rest;

  fun mat acc [] = acc
    | mat acc ((_, RESULT l, []) :: rest) = mat (l @ acc) rest
    | mat acc ((sub, SINGLE (tm', n), tm :: tms) :: rest) =
    (case unifyq sub tm' tm of NONE => mat acc rest
     | SOME sub => mat acc ((sub,n,tms) :: rest))
    | mat acc ((sub, net as MULTIPLE _, Var v :: tms) :: rest) =
    mat acc (harvest (inc sub v tms) (pat sub v) net rest)
    | mat acc ((sub, MULTIPLE (vs,fs), Fn (f,l) :: tms) :: rest) =
    let
      val rest =
        (case M.peek (fs, (f, length l)) of NONE => rest
         | SOME n => (sub, n, l @ tms) :: rest)
    in
      mat acc (case vs of NONE => rest | SOME n => (sub,n,tms) :: rest)
    end
    | mat _ _ = raise Bug "mlibTermnet.unify: mlibMatch";
in
  fun unify (NET (_,_,NONE)) _ = []
    | unify (NET (p, _, SOME (_,n))) tm =
    finally p (mat [] [(empty_vmap (), n, [tm])])
    handle Error _ => raise Bug "mlibTermnet.unify: should never fail";
end;

local
  fun pat NONE = VAR | pat (SOME qtm) = qtm;

  fun oeq qtm NONE = true | oeq qtm (SOME qtm') = qtm = qtm';

  fun inc sub v seen tms tm net rest =
    if oeq tm seen then (M.insert (sub,v,tm), net, tms) :: rest else rest;

  fun mat acc [] = acc
    | mat acc ((_, RESULT l, []) :: rest) = mat (l @ acc) rest
    | mat acc ((sub, SINGLE (tm', n), tm :: tms) :: rest) =
    (case total (matchq sub tm) tm' of NONE => mat acc rest
     | SOME sub => mat acc ((sub,n,tms) :: rest))
    | mat acc ((sub, net as MULTIPLE _, Var v :: tms) :: rest) =
    let val seen = M.peek (sub,v)
    in mat acc (harvest (inc sub v seen tms) (pat seen) net rest)
    end
    | mat acc ((sub, MULTIPLE (_,fs), Fn (f,l) :: tms) :: rest) =
    mat acc (case M.peek (fs, (f, length l)) of NONE => rest
             | SOME n => (sub, n, l @ tms) :: rest)
    | mat _ _ = raise Bug "mlibTermnet.matched: mlibMatch";
in
  fun matched (NET (_,_,NONE)) _ = []
    | matched (NET (p, _, SOME (_,n))) tm =
    finally p (mat [] [(empty_vmap(),n,[tm])])
    handle Error _ => raise Bug "mlibTermnet.matched: should never fail";
end;

fun filter pred =
  let
    fun filt (RESULT l) =
      (case List.filter (pred o snd) l of [] => NONE
       | l => SOME (length l, RESULT l))
      | filt (SINGLE (tm,n)) = omap (fn (i,n) => (i, SINGLE (tm,n))) (filt n)
      | filt (MULTIPLE (vs,fs)) =
      let
        fun subfilt (x, n, im as (i,m)) =
          case filt n of NONE => im | SOME (j,n) => (i + j, M.insert (m,x,n))
        val (i,vs) =
          case Option.mapPartial filt vs of NONE => (0,NONE)
          | SOME (i,n) => (i, SOME n)
        val (i,fs) = M.foldl subfilt (i, empty_fmap ()) fs
      in
        if i = 0 then NONE else SOME (i, MULTIPLE (vs,fs))
      end
  in
    fn net as NET (_,_,NONE) => net
     | NET (p, k, SOME (_,n)) => NET (p, k, filt n)
  end
  handle Error _ => raise Bug "mlibTermnet.filter: should never fail";

fun from_maplets p l = foldl (uncurry insert) (empty p) l;

local
  fun inc tm (RESULT l) acc = foldl (fn (x,y) => (qterm' tm |-> x) :: y) acc l
    | inc _ _ _ = raise Bug "mlibTermnet.to_maplets: mlibMatch";
  fun fin (tm |-> (n,a)) = (n, tm |-> a);
in
  fun to_maplets (NET (_,_,NONE)) = []
    | to_maplets (NET (p, _, SOME (_,n))) =
    finally p (map fin (harvest inc VAR n []));
end;

fun pp_termnet pp_a = pp_map to_maplets (pp_list (pp_maplet pp_term pp_a));

end
