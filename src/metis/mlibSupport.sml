(* ========================================================================= *)
(* THE SET OF SUPPORT                                                        *)
(* Copyright (c) 2002-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

(*
app load ["mlibHeap", "UNLINK", "mlibThm", "mlibSubsumers1"];
*)

(*
*)
structure mlibSupport :> mlibSupport =
struct

infix |-> ##;

open mlibUseful mlibTerm;

structure I = Intmap; local open Intmap in end;
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
   model_perts   : int,
   model_checks  : int,
   model_parms   : M.parameters list};

type 'a parmupdate = ('a -> 'a) -> parameters -> parameters;

val defaults =
  {size_power = 1.0,
   literal_power = 1.0,
   model_power = 1.0,
   model_perts = 100,
   model_checks = 20,
   model_parms = []};

fun update_size_power f (parm : parameters) : parameters =
  let val {size_power = s, literal_power = r, model_power = m,
           model_perts = p, model_checks = c, model_parms = z} = parm
  in {size_power = f s, literal_power = r, model_power = m,
      model_perts = p, model_checks = c, model_parms = z}
  end;

fun update_literal_power f (parm : parameters) : parameters =
  let val {size_power = s, literal_power = r, model_power = m,
           model_perts = p, model_checks = c, model_parms = z} = parm
  in {size_power = s, literal_power = f r, model_power = m,
      model_perts = p, model_checks = c, model_parms = z}
  end;

fun update_model_power f (parm : parameters) : parameters =
  let val {size_power = s, literal_power = r, model_power = m,
           model_perts = p, model_checks = c, model_parms = z} = parm
  in {size_power = s, literal_power = r, model_power = f m,
      model_perts = p, model_checks = c, model_parms = z}
  end;

fun update_model_perts f (parm : parameters) : parameters =
  let val {size_power = s, literal_power = r, model_power = m,
           model_perts = p, model_checks = c, model_parms = z} = parm
  in {size_power = s, literal_power = r, model_power = m,
      model_perts = f p, model_checks = c, model_parms = z}
  end;

fun update_model_checks f (parm : parameters) : parameters =
  let val {size_power = s, literal_power = r, model_power = m,
           model_perts = p, model_checks = c, model_parms = z} = parm
  in {size_power = s, literal_power = r, model_power = m,
      model_perts = p, model_checks = f c, model_parms = z}
  end;

fun update_model_parms f (parm : parameters) : parameters =
  let val {size_power = s, literal_power = r, model_power = m,
           model_perts = p, model_checks = c, model_parms = z} = parm
  in {size_power = s, literal_power = r, model_power = m,
      model_perts = p, model_checks = c, model_parms = f z}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun clause_to_formula cl = list_mk_disj (C.literals cl);

val clause_id = #id o C.dest_clause;

fun clause_to_string cl = PP.pp_to_string (!LINE_LENGTH) mlibClause.pp_clause cl;

val clause_lits = Real.fromInt o length o C.literals;

(* ------------------------------------------------------------------------- *)
(* Calculate clause_size (ignoring type annotations)                         *)
(* ------------------------------------------------------------------------- *)

local
  fun sz n []                         = n
    | sz n (Fn (":", [tm, _]) :: tms) = sz n (tm :: tms)
    | sz n (Var _ :: tms)             = sz (n + 1) tms
    | sz n (Fn (_,l) :: tms)          = sz (n + 1) (l @ tms);
  fun lsz (l,n) = sz n [dest_atom (literal_atom l)];
in
  val clause_size = Real.fromInt o foldl lsz 0 o C.literals;
end;

(* ------------------------------------------------------------------------- *)
(* Calculate average satisfiability in the models                            *)
(* ------------------------------------------------------------------------- *)

local
  fun small_space _ _ 0 _ = true
    | small_space N n i k =
    let val k = k * N in k <= n andalso small_space N n (i - 1) k end;

  fun sat_clause m n fm =
    if small_space (M.size m) n (length (FV fm)) 1 then M.count m fm
    else (M.checkn m fm n, n);
in
  fun sat_mod_fm m fm n =
    let val (i,k) = sat_clause m n fm
    in Real.fromInt i / Real.fromInt k
    end;
end;

fun sat_mod_fms _ [] _ = raise Bug "sat_mod_fms: no formulas"
  | sat_mod_fms m fms n =
  let val sum = foldl (fn (fm,x) => sat_mod_fm m fm n + x) 0.0 fms
  in sum / Real.fromInt (length fms)
  end;

fun sat_wmod_fm (w,m) fm n = w * (sat_mod_fm m fm n) + (1.0 - w);

fun clause_sat [] _ _ = 0.0
  | clause_sat wmods cl n =
  let
    val fm = clause_to_formula cl
    val sum = foldl (fn (wmod,x) => sat_wmod_fm wmod fm n + x) 0.0 wmods
  in
    sum / Real.fromInt (length wmods)
  end;

(* ------------------------------------------------------------------------- *)
(* mlibClause weights.                                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun priority n = 1e~12 * Real.fromInt n;
in
  fun clause_weight (parm : parameters) clsat dist cl =
    let
      val {size_power, literal_power, model_power, ...} = parm
      val {id, ...} = C.dest_clause cl
      val siz = Math.pow (clause_size cl, size_power)
      val lit = Math.pow (clause_lits cl, literal_power)
      val sat = Math.pow (1.0 + clsat, model_power)
      val w = siz * lit * sat * (1.0 + dist) + priority id
      val _ = chatting 5 andalso
              chat ("clause_weight: " ^ clause_to_string cl ^ " -> " ^
                    real_to_string w ^ "\n")
    in
      w
    end;
end;

(* ------------------------------------------------------------------------- *)
(* The set of support type                                                   *)
(* ------------------------------------------------------------------------- *)

type distance = real;

datatype sos = SOS of
  {parm     : parameters,
   clauses  : (real * (real * clause)) heap,
   distance : real I.intmap,
   models   : (real * mlibModel.model) list};

fun update_clauses c sos =
  let val SOS {parm = p, clauses = _, distance = d, models = m} = sos
  in SOS {parm = p, clauses = c, distance = d, models = m}
  end;

fun update_distance d sos =
  let val SOS {parm = p, clauses = c, distance = _, models = m} = sos
  in SOS {parm = p, clauses = c, distance = d, models = m}
  end;

fun update_models m sos =
  let val SOS {parm = p, clauses = c, distance = d, models = _} = sos
  in SOS {parm = p, clauses = c, distance = d, models = m}
  end;

(* ------------------------------------------------------------------------- *)
(* Basic operations                                                          *)
(* ------------------------------------------------------------------------- *)

val empty_heap : (real * (real * clause)) heap =
  H.empty (fn ((m,_),(n,_)) => Real.compare (m,n));

local
  val TEST_MODEL_SIZES = [10,11];
  fun test_model n = M.new {size = n, fix = M.pure_fix};
  val test_models = map test_model TEST_MODEL_SIZES;
in
  fun is_prob_taut n fm = List.all (fn m => M.checkn m fm n = n) test_models;
end;

local
  fun pert_models [] _ _ mods = []
    | pert_models fms p n mods =
    let val mods = map (M.perturb fms p) mods
    in map (fn m => (sat_mod_fms m fms n, m)) mods
    end;

  fun chatmods wmods =
    chat ("{" ^ join "," (map (percent_to_string o fst) wmods) ^ "}");
in
  fun new_models _ _ _ [] = []
    | new_models fms p n mps =
    let
      val mods = map M.new mps
      val fms = List.filter (not o is_prob_taut n) fms
      val wmods = pert_models fms p n mods
      val _ = chatting 2 andalso chatmods wmods
    in
      wmods
    end;
end;

fun empty parm fms =
  let
    val {model_perts,model_checks,model_parms,...} = parm
    val models = new_models fms model_perts model_checks model_parms
  in
    SOS {parm = parm, clauses = empty_heap, distance = I.empty (),
         models = models}
  end;

fun ssize (SOS {clauses,...}) = H.size clauses;

val pp_sos = pp_map (fn s => "S<" ^ int_to_string (ssize s) ^ ">") pp_string;

(* ------------------------------------------------------------------------- *)
(* Adding new clauses                                                        *)
(* ------------------------------------------------------------------------- *)

fun add1 dist (cl,sos) =
  let
    val SOS {parm,clauses,distance,models,...} = sos
    val {model_checks,...} = parm
    val {id,...} = C.dest_clause cl
    val dist =
      case I.peek (distance, id) of NONE => dist | SOME d => Real.min (dist,d)
    val distance = I.insert (distance,id,dist)
    val sat = clause_sat models cl model_checks
    val weight = clause_weight parm sat dist cl
    val sos = update_clauses (H.add (weight,(dist,cl)) clauses) sos
    val sos = update_distance distance sos
  in
    sos
  end;

fun inc_dist d n = d + log2 (Real.fromInt (1 + n));

fun add (dist,cls) sos =
  let val dist = inc_dist dist (length cls)
  in foldl (add1 dist) sos cls
  end;

fun new parm fms cls = foldl (add1 0.0) (empty parm fms) cls;

(* ------------------------------------------------------------------------- *)
(* Removing the lightest clause                                              *)
(* ------------------------------------------------------------------------- *)

fun remove sos =
  let
    val SOS {clauses,...} = sos
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
(* Rebinding for signature                                                   *)
(* ------------------------------------------------------------------------- *)

val size = ssize;

end
