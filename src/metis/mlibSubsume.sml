(* ========================================================================= *)
(* SUBSUMPTION CHECKING                                                      *)
(* Created by Joe Hurd, April 2002                                           *)
(* ========================================================================= *)

(*
app load ["mlibLiteralnet", "mlibMatch"];
*)

(*
*)
structure mlibSubsume :> mlibSubsume =
struct

infix ## |-> ::>;

open mlibUseful mlibTerm mlibMatch;

structure N = mlibLiteralnet; local open mlibLiteralnet in end;

val ofilter       = Option.filter;
type subst        = mlibSubst.subst;
val |<>|          = mlibSubst.|<>|;
val op ::>        = mlibSubst.::>;
val term_subst    = mlibSubst.term_subst;
val formula_subst = mlibSubst.formula_subst;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val () = traces := {module = "mlibSubsume", alignment = K 1} :: !traces;

fun chat l m = trace {module = "mlibSubsume", message = m, level = l};

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

val literal_size = formula_size o literal_atom;

val sort_literals_by_size =
  map snd o sort (fn ((m, _), (n, _)) => Int.compare (n, m)) o
  map (fn vlit => (literal_size vlit, vlit));

fun psym lit =
  let
    val (s, (x,y)) = (I ## dest_eq) (dest_literal lit)
    val () = assert (x <> y) (ERR "psym" "refl")
  in
    mk_literal (s, mk_eq (y,x))
  end;

(* ------------------------------------------------------------------------- *)
(* The core engine for subsumption checking.                                 *)
(* ------------------------------------------------------------------------- *)

type 'a sinfo = {sub : subst, hd : formula, tl : formula list, fin : 'a};

type 'a subs = 'a sinfo N.literalnet;

fun add_lits k a (net : 'a subs) = N.insert (k |-> a) net;

fun subsums flits =
  let
    fun extend sub [] fin (net, res) = (net, (sub, fin) :: res)
      | extend sub (h :: t) fin (net, res) =
      (add_lits (formula_subst sub h) {sub=sub, hd=h, tl=t, fin=fin} net, res)
    fun examine flit ({sub, hd, tl, fin}, s) =
      case total (matchl_literals sub) [(hd, flit)] of NONE => s
      | SOME sub => extend sub tl fin s
    fun narrow1 net (flit, s) =
      (case total psym flit of NONE => I
       | SOME flit => C (foldl (examine flit)) (N.match net flit))
      (foldl (examine flit) s (N.match net flit))
    fun narrow (net, res) =
      if N.size net = 0 then res
      else narrow (foldl (narrow1 net) (N.empty, res) flits)
  in
    fn nr => narrow nr
  end
  handle ERR_EXN _ => raise BUG "subsums" "shouldn't fail";

(* ------------------------------------------------------------------------- *)
(* The user interface.                                                       *)
(* ------------------------------------------------------------------------- *)

type 'a subsume = (subst * (int * 'a)) list * (int * 'a) subs;

val empty : 'a subsume = ([], N.empty);

fun add (lits |-> a) (con, net) =
  let
    val fin = (length lits, a)
  in
    case sort_literals_by_size lits of [] => ((|<>|, fin) :: con, net)
    | h :: t => (con, add_lits h {sub = |<>|, hd = h, tl = t, fin = fin} net)
  end;

local
  fun Filt n = List.filter (fn (_, (m, _)) => m <= n);
  fun Sort l = sort (fn ((_, (m, _)), (_, (n, _))) => Int.compare (m, n)) l;
  fun Strip l = map (fn (a, (_, b)) => (a, b)) l;
in
  fun subsumes  (c, n) l = Strip (Sort (subsums l (n, c)));
  fun subsumes' (c, n) l = Strip (Sort (Filt (length l) (subsums l (n, c))));
end;

fun info (con, net) = int_to_string (length con + N.size net);

fun pp_subsume pp = pp_map info pp_string pp;

local
  fun subsetq s t =
    let
      fun p x =
        mem x t orelse (case total psym x of NONE => false | SOME x => mem x t)
    in
      List.all p s
    end;

  fun single vlits = add (vlits |-> ()) empty;
in
  fun subsumes1  vlits flits =
    if subsetq vlits flits then [|<>|]
    else map fst (subsumes (single vlits) flits);

  fun subsumes1' vlits flits =
    if length vlits <= length flits andalso subsetq vlits flits then [|<>|]
    else (***map fst (subsumes' (single vlits) flits)*)
         raise BUG "mlibSubsume.subsumes1'" "this shouldn't happen at the moment";
end;  

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
