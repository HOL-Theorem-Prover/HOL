(* ========================================================================= *)
(* A TYPE FOR SUBSUMPTION CHECKING                                           *)
(* Created by Joe Hurd, April 2002                                           *)
(* ========================================================================= *)

(*
app load ["mlibThm", "mlibMatch"];
*)

(*
*)
structure mlibSubsum :> mlibSubsum =
struct

infix |-> ::>;

open mlibUseful mlibTerm mlibMatch;

structure D = mlibLiteralDisc; local open mlibLiteralDisc in end;
structure N = mlibLiteralNet; local open mlibLiteralNet in end;

val ofilter       = Option.filter;
type subst        = mlibSubst.subst;
val |<>|          = mlibSubst.|<>|;
val op ::>        = mlibSubst.::>;
val term_subst    = mlibSubst.term_subst;
val formula_subst = mlibSubst.formula_subst;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val () = traces := insert "Subsumption1" (!traces);

val chat = trace "Subsumption1";

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

val frozen_prefix = "FROZEN__";

fun mk_frozen v = Fn (frozen_prefix ^ v, []);

local
  val chk = String.isPrefix frozen_prefix;
  val dest =
    let val l = size frozen_prefix in fn s => String.extract (s, l, NONE) end;
in
  fun dest_frozen (Fn (s, [])) =
    (assert (chk s) (ERR "dest_frozen" "not a frozen var"); dest s)
    | dest_frozen _ = raise ERR "dest_frozen" "bad structure";
end;

val is_frozen = can dest_frozen;

fun freeze_vars fms =
  let
    val vars = FV (list_mk_disj fms)
    val sub = foldl (fn (v, s) => (v |-> mk_frozen v) ::> s) |<>| vars
  in
    map (formula_subst sub) fms
  end;

local
  fun f (v |-> a) = (v |-> (if is_frozen a then Var (dest_frozen a) else a));
in
  val defrost_vars = mlibSubst.from_maplets o map f o mlibSubst.to_maplets;
end;

val lit_size = formula_size o literal_atom;

val sort_literals_by_size =
  map snd o sort (fn (m, _) => fn (n, _) => m <= n) o
  map (fn lit => (lit_size lit, lit));

(* ------------------------------------------------------------------------- *)
(* The core engine for subsumption checking.                                 *)
(* ------------------------------------------------------------------------- *)

type 'a sinfo = {sub : subst, hd : formula, tl : formula list, fin : 'a};

type 'a subs = 'a sinfo D.literal_map;

fun add_lits (i as {hd, ...}) (net : 'a subs) = D.insert (hd |-> i) net;

local
  fun subsum strict lits =
    let
      val accept =
        (if strict then ofilter (non mlibSubst.is_renaming) else SOME) o
        defrost_vars
      val impossible =
        let val lit_net = N.from_maplets (map (fn l => (l |-> ())) lits)
        in List.exists (null o N.matched lit_net)
        end
      fun extend sub lits fin net =
        if impossible lits then net
        else
          case sort_literals_by_size lits of [] => raise BUG "extend" "null"
          | hd :: tl => add_lits {sub = sub, hd = hd, tl = tl, fin = fin} net
      fun examine lit ({sub, hd, tl, fin}, s as (net, res)) =
        case total (matchl_literals sub) [(hd, lit)] of NONE => s
        | SOME sub =>
          if null tl then
            case accept sub of SOME sub => (net, (sub, fin) :: res) | NONE => s
          else (extend sub (map (formula_subst sub) tl) fin net, res)
      fun narrow1 net (lit, s) = foldl (examine lit) s (D.match net lit)
      fun narrow (net, res) =
        if D.size net = 0 then res
        else narrow (foldl (narrow1 net) (D.empty, res) lits)
    in
      narrow
    end;
in
  fun subsumes strict net lits =
    subsum strict (freeze_vars lits) (net, [])
    handle ERR_EXN _ => raise BUG "subsumes" "shouldn't fail";
end;

(* ------------------------------------------------------------------------- *)
(* The user interface.                                                       *)
(* ------------------------------------------------------------------------- *)

type 'a subsum = ('a, 'a subs) sum;

val empty : 'a subsum = INR D.empty;

fun add _ (s as INL _) = s
  | add (fms |-> fin) (INR net) =
  case sort_literals_by_size fms of [] => INL fin
  | h :: t => INR (add_lits {sub = |<>|, hd = h, tl = t, fin = fin} net);

fun subsumed (INL fin) _ = [(|<>|, fin)]
  | subsumed (INR _) [] = []
  | subsumed (INR net) lits = subsumes false net lits;

fun strictly_subsumed _ [] = []
  | strictly_subsumed (INL fin) _ = [(|<>|, fin)]
  | strictly_subsumed (INR net) lits = subsumes true net lits;

fun info ((INL _) : 'a subsum) = "*"
  | info (INR net) = int_to_string (D.size net);

val pp_subsum = pp_map info pp_string;

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