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
val () = add_trace {module = module, alignment = I}
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
(* Seeding the models from the problem                                       *)
(*                                                                           *)
(* The models are a search heuristic, so their seed only has to be a         *)
(* function of the problem: the same problem must give the same models       *)
(* every time it is attempted.  A fold over its structure does that in       *)
(* one linear pass.                                                          *)
(*                                                                           *)
(* Two kinds of name reach here from counters that run for the life of       *)
(* the process, and neither may decide the seed: mlibThm.FRESH_VARS          *)
(* renames variables to _N, and HOL's CNF names skolem constants             *)
(* %%genvar%%N.  Both are a stem and a number, so symbol names are hashed    *)
(* with any trailing digits dropped, and variables by the order in which     *)
(* they are first met.                                                      *)
(*                                                                          *)
(* Dropping names altogether would be simpler and is wrong: goals that       *)
(* differ only in their constants would then hash alike, so a theory full    *)
(* of similar goals would put every one of them to the same model, and       *)
(* one unlucky model would cost the whole file.  Keeping the stems keeps     *)
(* that apart.                                                              *)
(*                                                                          *)
(* Even so, seeding does not make a call bit-for-bit repeatable: a           *)
(* model's interpretation is md5 of the full symbol names                    *)
(* (mlibModel.randomize), which still carry the counter.  That residual      *)
(* belongs upstream, in the naming, not here.                                *)
(*                                                                           *)
(* Not formula_to_string: that goes through the pretty-printer, which        *)
(* reads the global !infixes and !LINE_LENGTH, and the point here is to      *)
(* have nothing outside the problem decide what the models are.              *)
(* ------------------------------------------------------------------------- *)

local
  (* stays under 2^24, so every intermediate fits a 31-bit Int *)
  val MODULUS = 16777213

  fun mix (h,n) = (h * 37 + n) mod MODULUS

  fun tag ((h,ns),n) = (mix (h,n), ns)

  (* the name with any trailing digits dropped *)
  fun sym ((h,ns),s) =
      let
        fun stem 0 = 0
          | stem i =
            if Char.isDigit (String.sub (s, i - 1)) then stem (i - 1) else i
        val n = stem (String.size s)
        fun go (i,acc) =
            if n <= i then acc
            else go (i + 1, mix (acc, Char.ord (String.sub (s,i))))
      in
        (go (0,h), ns)
      end

  (* the position at which this name was first met *)
  fun name ((h,ns),s) =
      let
        fun index (i, []) = (i, ns @ [s])
          | index (i, t :: ts) = if s = t then (i, ns) else index (i + 1, ts)
        val (i,ns) = index (0, ns)
      in
        (mix (h,i), ns)
      end

  (* terms and formulas share one tag space: 1-2 here, 3-12 below *)
  fun hash_tm (Var v, st) = name (tag (st,1), v)
    | hash_tm (Fn (f,args), st) =
      foldl hash_tm (tag (sym (tag (st,2), f), length args)) args

  fun hash_fm (True, st) = tag (st,3)
    | hash_fm (False, st) = tag (st,4)
    | hash_fm (Atom t, st) = hash_tm (t, tag (st,5))
    | hash_fm (Not p, st) = hash_fm (p, tag (st,6))
    | hash_fm (And (p,q), st) = hash_fm (q, hash_fm (p, tag (st,7)))
    | hash_fm (Or (p,q), st) = hash_fm (q, hash_fm (p, tag (st,8)))
    | hash_fm (Imp (p,q), st) = hash_fm (q, hash_fm (p, tag (st,9)))
    | hash_fm (Iff (p,q), st) = hash_fm (q, hash_fm (p, tag (st,10)))
    | hash_fm (Forall (v,p), st) = hash_fm (p, name (tag (st,11), v))
    | hash_fm (Exists (v,p), st) = hash_fm (p, name (tag (st,12), v))
in
  fun problem_seed fms = fst (foldl hash_fm (0,[]) fms)
  fun slot_seed seed i = mix (seed,i)
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

(* Built per call rather than once per process: `checkn` samples with
   the model's generator, so a pair shared between calls would answer
   according to how many formulas the calls before had put through it.
   Their seeds are fixed rather than taken from the problem, because
   this predicate asks whether a formula holds in an arbitrary model --
   a probe drawn from the problem would lean towards the problem it is
   filtering. *)
local
  val TEST_MODEL_SIZES = [10,11];
  fun test_model n = M.new (M.update_size (K n) M.defaults) n;
in
  fun new_test_models () = map test_model TEST_MODEL_SIZES
end;

fun is_prob_taut tms n fm = List.all (fn m => M.checkn m fm n = n) tms;

local
  fun pert_models [] _ _ mods = []
    | pert_models fms p n mods =
    let val mods = map (M.perturb fms p) mods
    in map (fn m => (sat_mod_fms m fms n, m)) mods
    end;

  fun chatmods wmods =
    chat ("{" ^ join "," (map (percent_to_string o fst) wmods) ^ "}");
in
  fun new_models _ _ _ _ [] = []
    | new_models seed fms p n mps =
    let
      (* one stream per slot, so two models of a problem do not sample
         in lockstep *)
      val _ = chatting 2 andalso
              chat ("seed: " ^ int_to_string seed ^ "\n")
      val mods = map (fn (i,mp) => M.new mp (slot_seed seed i))
                     (enumerate 0 mps)
      val tms = new_test_models ()
      val fms = List.filter (not o is_prob_taut tms n) fms
      val wmods = pert_models fms p n mods
      val _ = chatting 2 andalso chatmods wmods
    in
      wmods
    end;
end;

fun empty parm seed fms =
  let
    val {model_perts,model_checks,model_parms,...} = parm
    val models = new_models seed fms model_perts model_checks model_parms
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

fun new parm seed fms cls = foldl (add1 0.0) (empty parm seed fms) cls;

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
