(* ========================================================================= *)
(* SUBSUMPTION CHECKING                                                      *)
(* Copyright (c) 2002-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

(*
app load ["Intmap", "Intset", "mlibLiteralnet", "mlibMatch"];
*)

(*
*)
structure mlibSubsume :> mlibSubsume =
struct

infix ## |-> ::>;

open mlibUseful mlibTerm mlibMatch;

structure O = Option; local open Option in end;
structure I = Intset; local open Intset in end;
structure M = Intmap; local open Intmap in end;
structure N = mlibLiteralnet; local open mlibLiteralnet in end;
structure S = mlibStream; local open mlibStream in end;

type 'a intmap = 'a M.intmap;
type 'a stream = 'a S.stream;
type 'a lnet   = 'a N.literalnet;

val ofilter       = Option.filter;
type subst        = mlibSubst.subst;
val |<>|          = mlibSubst.|<>|;
val op ::>        = mlibSubst.::>;
val term_subst    = mlibSubst.term_subst;
val formula_subst = mlibSubst.formula_subst;

(* ------------------------------------------------------------------------- *)
(* Chatting                                                                  *)
(* ------------------------------------------------------------------------- *)

val module = "mlibSubsume";
val () = traces := {module = module, alignment = I} :: !traces;
fun chatting l = tracing {module = module, level = l};
fun chat s = (trace s; true)

(* ------------------------------------------------------------------------- *)
(* Helper functions                                                          *)
(* ------------------------------------------------------------------------- *)

local
  fun psym lit =
    let
      val (s,(x,y)) = (I ## dest_eq) (dest_literal lit)
      val () = assert (x <> y) (Error "psym: refl")
    in
      mk_literal (s, mk_eq (y,x))
    end;
in
  fun psymize lits = List.mapPartial (total psym) lits @ lits;
end;

local
  fun sz n [] = n
    | sz n (Fn (":", [t, _]) :: l) = sz n (t :: l)
    | sz n (Fn (_,a) :: l) = sz (n + 1) (a @ l)
    | sz n (Var _ :: l) = sz n l;
in
  val literal_size = sz 0 o sing o dest_atom o literal_atom;
end;

val sort_literals = sort_map literal_size (rev_order Int.compare);

(* Partial evaluation on the first argument *)
fun compatible a =
  let val l = psymize [a]
  in fn b => List.exists (can (unify_literals |<>| b)) l
  end;

(* ------------------------------------------------------------------------- *)
(* The core function for subsumption checking                                *)
(*                                                                           *)
(* Assumes flits has already been extended with symmetries of equality lits. *)
(* ------------------------------------------------------------------------- *)

fun qcheck vlits flits =
  List.all (fn v => List.exists (can (match_literals v)) flits) vlits;

fun subsum flits =
  let
    fun f [] = S.NIL
      | f ((sub,[]) :: rest) = S.CONS (sub, fn () => f rest)
      | f ((sub, v :: vs) :: rest) =
      let
        fun g (l,r) =
          case total (matchl_literals sub) [(v,l)] of NONE => r
          | SOME sub => (sub,vs) :: r
      in
        f (foldl g rest flits)
      end
  in
    fn vlits => if qcheck vlits flits then f [(|<>|,vlits)] else S.NIL
  end;

(* ------------------------------------------------------------------------- *)
(* Basic operations                                                          *)
(* ------------------------------------------------------------------------- *)

datatype 'a subsume = SUBSUME of
  {zero : (subst * 'a) stream,
   one  : (formula * 'a) lnet,
   many : int * (int*int) lnet * (int*int) lnet * (formula list * 'a) intmap};

fun empty () = SUBSUME
  {zero = S.NIL,
   one = N.empty {fifo = false},
   many = (0, N.empty {fifo = false}, N.empty {fifo = false}, M.empty ())};

fun size (SUBSUME {zero, one, many = (_,_,_,m)}) =
  S.length zero + N.size one + M.numItems m;

fun add (lits |-> a) (SUBSUME {zero,one,many}) =
  SUBSUME
  (case sort_literals lits of
     [] => {zero = S.CONS ((|<>|, a), K zero), one = one, many = many}
   | [h] => {zero = zero, one = N.insert (h |-> (h,a)) one, many = many}
   | h :: (t as th :: tt) =>
     let
       val (i,l,r,m) = many
       val k = (i, length lits)
       val l = N.insert (h |-> k) l
       val x = O.getOpt (List.find (not o compatible h) t, th)
       val r = N.insert (x |-> k) r
       val m = M.insert (m, i, (tt @ [h, th], a))
       val many = (i + 1, l, r, m)
     in
       {zero = zero, one = one, many = many}
     end);

fun filter pred (SUBSUME {zero,one,many}) =
  let
    fun f (i, x as (_,a), (s,m)) =
      if pred a then (s, M.insert (m,i,x)) else (I.add (s,i), m)
    val zero = S.filter (pred o snd) zero
    val one = N.filter (pred o snd) one
    val (i,l,r,m) = many
    val (h,m) = M.foldl f (I.empty, M.empty ()) m
    val l = N.filter (not o curry I.member h o fst) l
    val r = N.filter (not o curry I.member h o fst) r
    val many = (i,l,r,m)
  in
    SUBSUME {zero = zero, one = one, many = many}
  end;

(* ------------------------------------------------------------------------- *)
(* subsumes  = all subsuming clauses                                         *)
(* subsumes' = all subsuming clauses that don't contain more literals        *)
(* ------------------------------------------------------------------------- *)

local
  fun real_match net y =
    let
      fun f [] z = z
        | f ((x,a) :: l) z =
        f l (case total (match_literals x) y of NONE => z | SOME s => (s,a)::z)
    in
      f (N.match net y) []
    end;

  fun subone one flits () =
    let
      fun f [] = S.NIL
        | f (h :: t) = S.append (S.from_list (real_match one h)) (fn () => f t)
    in
      f flits
    end;

  fun submany (_,l,r,m) n flits () =
    let
      fun f ((i,k),s) = if n = ~1 orelse k <= n then I.add (s,i) else s
      fun g x (lit,s) = foldl f s (N.match x lit)
      fun h i =
        let val (vlits,a) = M.retrieve (m,i)
        in S.map (fn s => (s,a)) (subsum flits vlits)
        end
      fun j [] = S.NIL | j (i :: is) = S.append (h i) (fn () => j is)
      val lis = foldl (g l) I.empty flits
      val ris = foldl (g r) I.empty flits
    in
      j (I.listItems (I.intersection (lis,ris)))
    end;
in
  fun subsumes (SUBSUME {zero,...}) [] = zero
    | subsumes (SUBSUME {zero,one,many}) flits =
    let val flits = psymize flits
    in S.append (S.append zero (subone one flits)) (submany many ~1 flits)
    end;

  fun subsumes' (SUBSUME {zero,...}) [] = zero
    | subsumes' (SUBSUME {zero,one,many}) flits =
    let
      val max = length flits
      val flits = psymize flits
    in
      S.append (S.append zero (subone one flits))
      (if max = 1 then K S.NIL else submany many max flits)
    end;
end;

(* ------------------------------------------------------------------------- *)
(* Single clause versions                                                    *)
(* ------------------------------------------------------------------------- *)

fun subsumes1 vlits flits =
  let val flits = psymize flits
  in if subset vlits flits then [|<>|] else S.to_list (subsum flits vlits)
  end;

fun subsumes1' vlits flits =
  if length vlits <= length flits then subsumes1 vlits flits else [];

(* ------------------------------------------------------------------------- *)
(* Pretty-printing                                                           *)
(* ------------------------------------------------------------------------- *)

fun pp_subsume pp = pp_map size pp_int pp;

(* Quick testing
quotation := true;
installPP pp_formula;
installPP pp_term;
installPP pp_subst;
installPP pp_thm;
freeze_vars (map parse [`x + y <= 0`, `x = __x()`]);
val s = add_subsumer (AXIOM (map parse [`p(x,3)`, `p(2,y)`])) empty_subsum;
subsumed s (map parse [`p(2,3)`]);
*)

end
