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
structure M = mlibModel; local open mlibModel in end;
structure C = mlibClause; local open mlibClause in end;

type 'a heap = 'a H.heap;
type clause = C.clause;

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

type parameters =
  {size_power    : real,
   literal_power : real,
   model_power   : real,
   model_checks  : int,
   model_parms   : M.parameters list};

type 'a parmupdate = ('a -> 'a) -> parameters -> parameters;

val defaults =
  {size_power = 1.0,
   literal_power = 1.0,
   model_power = 1.0,
   model_checks = 20,
   model_parms = []};

fun update_size_power f (parm : parameters) : parameters =
  let val {size_power = s, literal_power = r, model_power = m,
           model_checks = c, model_parms = p} = parm
  in {size_power = f s, literal_power = r, model_power = m,
      model_checks = c, model_parms = p}
  end;

fun update_literal_power f (parm : parameters) : parameters =
  let val {size_power = s, literal_power = r, model_power = m,
           model_checks = c, model_parms = p} = parm
  in {size_power = s, literal_power = f r, model_power = m,
      model_checks = c, model_parms = p}
  end;

fun update_model_power f (parm : parameters) : parameters =
  let val {size_power = s, literal_power = r, model_power = m,
           model_checks = c, model_parms = p} = parm
  in {size_power = s, literal_power = r, model_power = f m,
      model_checks = c, model_parms = p}
  end;

fun update_model_checks f (parm : parameters) : parameters =
  let val {size_power = s, literal_power = r, model_power = m,
           model_checks = c, model_parms = p} = parm
  in {size_power = s, literal_power = r, model_power = m,
      model_checks = f c, model_parms = p}
  end;

fun update_model_parms f (parm : parameters) : parameters =
  let val {size_power = s, literal_power = r, model_power = m,
           model_checks = c, model_parms = p} = parm
  in {size_power = s, literal_power = r, model_power = m,
      model_checks = c, model_parms = f p}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun clause_to_formula cl = list_mk_disj (C.literals cl);

fun clause_to_string cl = PP.pp_to_string (!LINE_LENGTH) mlibClause.pp_clause cl;

(* This clause_size function deliberately ignores type annotations *)
local
  fun sz n []                         = n
    | sz n (Fn (":", [tm, _]) :: tms) = sz n (tm :: tms)
    | sz n (Var _ :: tms)             = sz (n + 1) tms
    | sz n (Fn (_,l) :: tms)          = sz (n + 1) (l @ tms);
  fun lsz (l,n) = sz n [dest_atom (literal_atom l)];
in
  val clause_size = Real.fromInt o foldl lsz 0 o C.literals;
end;

val clause_lits = Real.fromInt o length o C.literals;

(* clause_sat calculates the mean satisfiability *)
fun clause_sat _ [] _ = 1.0
  | clause_sat n mods cl =
  let
    val fm = clause_to_formula cl
    fun sat m = Real.fromInt (M.checkn m fm n) / Real.fromInt n
    val sum_sat = foldl (fn (m,x) => sat m + x) 0.0 mods
    val mean_sat = sum_sat / Real.fromInt (length mods)
  in
    mean_sat + 1.0
  end;

(* ------------------------------------------------------------------------- *)
(* mlibClause weights.                                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun priority n = 1e~12 * Real.fromInt n;
in
  fun clause_weight (parm : parameters) models dist cl =
    let
      val {size_power, literal_power, model_power, model_checks, ...} = parm
      val {id, ...} = C.dest_clause cl
      val siz = Math.pow (clause_size cl, size_power)
      val lit = Math.pow (clause_lits cl, literal_power)
      val mods = Math.pow (clause_sat model_checks models cl, model_power)
      val w = siz * lit * mods * (1.0 + dist) + priority id
      val _ = chatting 1 andalso
              chat ("clause_weight: " ^ clause_to_string cl ^ " -> " ^
                    real_to_string w ^ "\n")
    in
      w
    end;
end;

(* ------------------------------------------------------------------------- *)
(* The set of support type                                                   *)
(* ------------------------------------------------------------------------- *)

datatype sos = SOS of
  {parm    : parameters,
   clauses : (real * (real * clause)) heap,
   models  : mlibModel.model list};

fun update_clauses c sos =
  let val SOS {parm = p, clauses = _, models = m} = sos
  in SOS {parm = p, clauses = c, models = m}
  end;

fun update_models m sos =
  let val SOS {parm = p, clauses = c, models = _} = sos
  in SOS {parm = p, clauses = c, models = m}
  end;

(* ------------------------------------------------------------------------- *)
(* Basic operations                                                          *)
(* ------------------------------------------------------------------------- *)

val empty_heap : (real * (real * clause)) heap =
  H.empty (fn ((m,_),(n,_)) => Real.compare (m,n));

fun empty p fms =
  let val models = map (fn mp => M.new mp fms) (#model_parms p)
  in SOS {parm = p, clauses = empty_heap, models = models}
  end;

fun ssize (SOS {clauses, ...}) = H.size clauses;

val pp_sos = pp_map (fn s => "S<" ^ int_to_string (ssize s) ^ ">") pp_string;

(* ------------------------------------------------------------------------- *)
(* Adding new clauses                                                        *)
(* ------------------------------------------------------------------------- *)

local
  fun add1 d (cl,sos) =
    let
      val SOS {parm, clauses, models, ...} = sos
      val w = clause_weight parm models d cl
      val sos = update_clauses (H.add (w,(d,cl)) clauses) sos
    in
      sos
    end;
in
  fun add (dist,cls) sos = foldl (add1 dist) sos cls;
end;

(* ------------------------------------------------------------------------- *)
(* Removing the lightest clause                                              *)
(* ------------------------------------------------------------------------- *)

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

local
  fun f acc sos =
    case remove sos of NONE => rev acc
    | SOME ((_,cl),sos) => f (cl :: acc) sos;
in
  val to_list = f [];
end;

(* ------------------------------------------------------------------------- *)
(* Registering clauses in the models                                         *)
(* ------------------------------------------------------------------------- *)

fun register cls sos =
  let
    val SOS {models, ...} = sos
    val fms = map clause_to_formula cls
    val models = map (M.add fms) models
  in
    update_models models sos
  end;

(* ------------------------------------------------------------------------- *)
(* Rebinding for signature                                                   *)
(* ------------------------------------------------------------------------- *)

val size = ssize;

end
