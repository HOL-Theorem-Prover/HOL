(* ========================================================================= *)
(* THE SET OF SUPPORT                                                        *)
(* Created by Joe Hurd, April 2002                                           *)
(* ========================================================================= *)

(*
app load ["mlibHeap", "UNLINK", "mlibThm", "mlibSubsumers1"];
*)

(*
*)
structure mlibSupport :> mlibSupport =
struct

infix |->;

open mlibUseful mlibTerm;

structure H = mlibHeap; local open mlibHeap in end;
structure C = mlibClause; local open mlibClause in end;
structure S = mlibClauseset; local open mlibClauseset in end;

type 'a heap   = 'a H.heap;
type clause    = C.clause;
type id_clause = S.id_clause;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val module = "mlibSupport";
val () = traces := {module = module, alignment = I} :: !traces;
fun chatting l = tracing {module = module, level = l};
fun chat s = (trace s; true)

(* ------------------------------------------------------------------------- *)
(* Parameters.                                                               *)
(* ------------------------------------------------------------------------- *)

type parameters = {size_power : real, literal_power : real};

val defaults = {size_power = 1.0, literal_power = 1.0};

fun update_size_power f (parm : parameters) : parameters =
  let val {size_power = s, literal_power = r} = parm
  in {size_power = f s, literal_power = r}
  end;

fun update_literal_power f (parm : parameters) : parameters =
  let val {size_power = s, literal_power = r} = parm
  in {size_power = s, literal_power = f r}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

(* This clause_size function deliberately ignores type annotations *)
local
  fun sz n []                         = n
    | sz n (Fn (":", [tm, _]) :: tms) = sz n (tm :: tms)
    | sz n (Var _ :: tms)             = sz n tms
    | sz n (Fn (_,l) :: tms)          = sz (n + 1) (l @ tms);
  fun lsz (l,n) = sz n [dest_atom (literal_atom l)];
in
  val clause_size = Real.fromInt o foldl lsz 0 o C.clause_lits;
end;

val clause_lits = Real.fromInt o length o C.clause_lits;

(* ------------------------------------------------------------------------- *)
(* mlibClause weights.                                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun priority n = 1e~12 * Real.fromInt n;
in
  fun clause_weight (parm : parameters) dist icl =
    let
      val {size_power, literal_power, ...} = parm
      val (i,cl) = S.dest_id_clause icl
      val siz = Math.pow (clause_size cl, size_power)
      val lit = Math.pow (clause_lits cl, literal_power)
    in
      siz * lit * (1.0 + dist) + priority i
    end;
end;

(* ------------------------------------------------------------------------- *)
(* The set of support.                                                       *)
(* ------------------------------------------------------------------------- *)

datatype sos = SOS of
  {parm    : parameters,
   clauses : (real * (real * id_clause)) heap};

fun update_clauses c sos =
  let val SOS {parm = p, clauses = _} = sos in SOS {parm = p, clauses = c} end;

val empty_heap : (real * (real * id_clause)) heap =
  H.empty (fn ((m,_),(n,_)) => Real.compare (m,n));

fun empty p = SOS {parm = p, clauses = empty_heap};

fun reset (SOS {parm = p, ...}) = SOS {parm = p, clauses = empty_heap};

fun size (SOS {clauses, ...}) = H.size clauses;

local
  fun add1 d (icl,sos) =
    let
      val SOS {parm, clauses, ...} = sos
      val w = clause_weight parm d icl
      val sos = update_clauses (H.add (w,(d,icl)) clauses) sos
    in
      sos
    end;
in
  fun add dist cls sos = foldl (add1 dist) sos cls;
end;

fun remove sos =
  let
    val SOS {clauses, ...} = sos
  in
    if H.is_empty clauses then NONE else
      let
        val ((_,dcl),cls) = H.remove clauses
        val sos = update_clauses cls sos
      in
        SOME (dcl,sos)
      end
  end;

end
