(* ========================================================================= *)
(* THE METIS COMBINATION OF PROOF PROCEDURES FOR FIRST-ORDER LOGIC           *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

(*
app load
 ["mlibUseful", "Mosml", "mlibTerm", "mlibThm", "mlibCanon",
  "mlibSolver", "mlibMeson", "mlibResolution"];
*)

(*
*)
structure mlibMetis :> mlibMetis =
struct

open mlibUseful mlibTerm mlibThm mlibMeter mlibSolver;

infix |-> ::> @> oo ## ::* ::@;

structure M = mlibMeson; local open mlibMeson in end;
structure R = mlibResolution; local open mlibResolution in end;

(* ------------------------------------------------------------------------- *)
(* Aligning trace levels.                                                    *)
(* ------------------------------------------------------------------------- *)

(* mlibMetis trace levels:
   0: No output
   1: Status information during proof search
   2: More status information
   3: More detailed prover information: slice by slice
   4: High-level proof search information
   5: Log of every inference during proof search
   6: mlibSupport infrastructure such as mlibTermorder *)

val aligned_traces =
  [{module = "mlibTermorder",  alignment = fn n => n + 5},
   {module = "mlibModel",      alignment = fn n => n + 5},
   {module = "mlibRewrite",    alignment = fn n => n + 4},
   {module = "mlibClause",     alignment = fn n => n + 4},
   {module = "mlibSolver",     alignment = I},
   {module = "mlibMeson",      alignment = I},
   {module = "mlibClauseset",  alignment = I},
   {module = "mlibSupport",    alignment = I},
   {module = "mlibResolution", alignment = I}];

val () = trace_level := 1;
val () = traces := aligned_traces;

(* ------------------------------------------------------------------------- *)
(* Helper functions                                                          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Tuning parameters                                                         *)
(* ------------------------------------------------------------------------- *)

datatype prover =
  mlibResolution of R.parameters
| mlibMeson of M.parameters
| Delta of M.parameters;

type prover_parameters = prover * mlibSolver.sos_filter option * mlibSolver.cost_fn;

type parameters = prover_parameters list;

local
  val rl = R.update_clause_parm o mlibClause.update_literal_order o K;
  fun rm ns =
    (R.update_sos_parm o mlibSupport.update_model_parms)
    (fn l => l @ map (fn n => mlibModel.update_size (K n) mlibModel.defaults) ns);
in
  fun R_ordered ns = (rm ns o rl true) R.defaults;
end;

val default_meson : prover_parameters =
  (mlibMeson M.defaults, SOME (only_if_everything all_negative), Time 1.0);

val default_delta : prover_parameters =
  (Delta M.defaults, NONE, Time 0.25);

val default_resolution : prover_parameters =
  (mlibResolution R.defaults, SOME everything, Time 2.0);

val ordered_resolution : prover_parameters =
  (mlibResolution (R_ordered [3,4,5]), NONE, Time 4.0);

val defaults = [default_resolution, default_meson, ordered_resolution];

local
  fun b2s true = "on" | b2s false = "off";
  val i2s = mlibUseful.int_to_string;
  fun io2s NONE = "NONE" | io2s (SOME i) = "SOME " ^ i2s i;
  val r2s = mlibUseful.real_to_string;
  fun mp2s {size, perts = (p,q)} = i2s size ^ "(" ^ i2s p ^ "+" ^ i2s q ^ ")";
  fun mpl2s l = "[" ^ join "," (map (int_to_string o #size) l) ^ "]";

  fun f2s (f : mlibClauseset.filter) =
    "      subsumption ...... " ^ b2s (#subsumption f) ^ "\n" ^
    "      simplification ... " ^ i2s (#simplification f) ^ "\n" ^
    "      splitting ........ " ^ b2s (#splitting f) ^ "\n";

  fun raw_rp2s (parm : R.parameters) =
    let
      val {clause_parm = c, sos_parm = a, set_parm = b} = parm
      val {termorder_parm = t, ...} = c
    in
      "  clause_parm:\n" ^
      "    term_order ......... " ^ b2s (#term_order c) ^ "\n" ^
      "    literal_order ...... " ^ b2s (#literal_order c) ^ "\n" ^
      "    order_stickiness ... " ^ i2s (#order_stickiness c) ^ "\n" ^
      "    termorder_parm:\n" ^
      "      precision ........ " ^ i2s (#precision t) ^ "\n" ^
      "  sos_parm:\n" ^
      "    size_power ......... " ^ r2s (#size_power a) ^ "\n" ^
      "    literal_power ...... " ^ r2s (#literal_power a) ^ "\n" ^
      "    model_power ........ " ^ r2s (#model_power a) ^ "\n" ^
      "    model_perts ........ " ^ i2s (#model_perts a) ^ "\n" ^
      "    model_checks ....... " ^ i2s (#model_checks a) ^ "\n" ^
      "    model_parms ........ " ^ mpl2s (#model_parms a) ^ "\n" ^
      "  set_parm:\n" ^
      "    prefactoring:\n" ^ f2s (#prefactoring b) ^
      "    postfactoring:\n" ^ f2s (#postfactoring b)
    end;

  fun rp2s name (parm : R.parameters) = name ^ ":\n" ^ raw_rp2s parm;

  fun rlp2s name parm = name ^ ":\n" ^ join "  +\n" (map raw_rp2s parm);

  fun mp2s name (parm : M.parameters) =
    name ^ ":\n" ^
    "  ancestor_pruning ..... " ^ b2s (#ancestor_pruning parm) ^ "\n" ^
    "  ancestor_cutting ..... " ^ b2s (#ancestor_cutting parm) ^ "\n" ^
    "  state_simplify ....... " ^ b2s (#state_simplify parm) ^ "\n" ^
    "  cache_cutting ........ " ^ b2s (#cache_cutting parm) ^ "\n" ^
    "  divide_conquer ....... " ^ b2s (#divide_conquer parm) ^ "\n" ^
    "  unit_lemmaizing ...... " ^ b2s (#unit_lemmaizing parm) ^ "\n" ^
    "  sort_literals ........ " ^ i2s (#sort_literals parm) ^ "\n" ^
    "  sort_rules ........... " ^ b2s (#sort_rules parm) ^ "\n";

  fun p2s (mlibResolution r) = rp2s "resolution" r
    | p2s (mlibMeson m) = mp2s "meson" m
    | p2s (Delta d) = mp2s "delta" d;

  fun s2s (s : sos_filter option) =
    "sos: " ^ (case s of NONE => "natural" | SOME {name, ...} => name) ^ "\n";

  fun c2s c = "cost_fn: " ^ PP.pp_to_string (!LINE_LENGTH) pp_cost_fn c ^ "\n";
in
  fun parameters_to_string (parm : parameters) =
    join "\n" (map (fn (p,s,c) => p2s p ^ s2s s ^ c2s c) parm);
end;

(* ------------------------------------------------------------------------- *)
(* The metis combination of solvers.                                         *)
(* ------------------------------------------------------------------------- *)

local
  fun mk_prover (mlibResolution p) = ("r", fn n => R.resolution' (n,p))
    | mk_prover (mlibMeson p) = ("m", fn n => M.meson' (n,p))
    | mk_prover (Delta p) = ("d", fn n => M.delta' (n,p));

  fun apply NONE slv = slv | apply (SOME s) slv = apply_sos_filter s slv;

  fun mk_provers ((t,s,c),(l,v)) =
    let
      val (n,f) = mk_prover t
      val n = variant n v
    in
      ((c, apply s (f n)) :: l, n :: v)
    end
in
  val metis' = combine o rev o fst o foldl mk_provers ([],[]);
end;

val metis = metis' defaults;

(* ------------------------------------------------------------------------- *)
(* A user-friendly interface.                                                *)
(* ------------------------------------------------------------------------- *)

val settings = ref defaults;

val limit : limit ref = ref {time = NONE, infs = NONE};

fun prove goal =
    let
      val {thms,hyps} = clauses goal
      val solv = metis' (!settings)
    in
      refute (initialize solv {limit = !limit, thms = thms, hyps = hyps})
    end;

fun query database =
  initialize M.prolog
  {thms = axiomatize database, hyps = [], limit = unlimited};

end
