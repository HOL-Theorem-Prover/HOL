(* ========================================================================= *)
(* THE METIS COMBINATION OF PROOF PROCEDURES FOR FIRST-ORDER LOGIC           *)
(* Created by Joe Hurd, September 2001                                       *)
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

open mlibUseful mlibTerm mlibThm mlibMeter mlibCanon mlibSolver mlibMeson mlibResolution;

infix |-> ::> @> oo ## ::* ::@;

(* ------------------------------------------------------------------------- *)
(* Aligning trace levels.                                                    *)
(* ------------------------------------------------------------------------- *)

(* mlibMetis trace levels:
   0: No output
   1: Status information during proof search
   2: More detailed prover information: slice by slice
   3: High-level proof search information
   4: Log of every inference during proof search
   5: mlibSupport infrastructure such as mlibTermorder *)

val aligned_traces =
  [{module = "mlibRewrite",    alignment = fn n => n + 3},
   {module = "mlibTermorder",  alignment = fn n => n + 4},
   {module = "mlibSolver",     alignment = I},
   {module = "mlibMeson",      alignment = I},
   {module = "mlibClause",     alignment = fn n => n + 3},
   {module = "mlibClauseset",  alignment = fn 1 => 1 | n => n + 2},
   {module = "mlibResolution", alignment = fn n => if n <= 2 then n else n - 1}];

val () = trace_level := 1;
val () = traces := aligned_traces;

(* ------------------------------------------------------------------------- *)
(* Helper functions                                                          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Tuning parameters                                                         *)
(* ------------------------------------------------------------------------- *)

datatype prover =
  mlibResolution of mlibResolution.parameters
| mlibMeson of mlibMeson.parameters
| Delta of mlibMeson.parameters

type parameters = (mlibSolver.cost_fn * prover) list

val default_resolution = (time_power 1.0, mlibResolution mlibResolution.defaults);
val default_meson = (time_power 2.0, mlibMeson mlibMeson.defaults);
val default_delta = (once_only, Delta mlibMeson.defaults);
val defaults = [default_meson, default_resolution, default_delta];

local
  fun b2s true = "on" | b2s false = "off";
  val i2s = mlibUseful.int_to_string;
  fun io2s NONE = "NONE" | io2s (SOME i) = "SOME " ^ i2s i;
  val r2s = mlibUseful.real_to_string;

  fun rp2s name (parm : mlibResolution.parameters) =
    let
      val {restart = r, clause_parm = c, sos_parm = a, set_parm = b} = parm
      val {termorder_parm = t, ...} = c
    in
      name ^ ":\n" ^
      "  restart .............. " ^ io2s r ^ "\n" ^
      "  clause_parm:\n" ^
      "    literal_order ...... " ^ b2s (#literal_order c) ^ "\n" ^
      "    term_order ......... " ^ b2s (#term_order c) ^ "\n" ^
      "    termorder_parm:\n" ^
      "      stickiness ....... " ^ i2s (#stickiness t) ^ "\n" ^
      "      precision ........ " ^ i2s (#precision t) ^ "\n" ^
      "  sos_parm:\n" ^
      "    size_power ......... " ^ r2s (#size_power a) ^ "\n" ^
      "    literal_power ...... " ^ r2s (#literal_power a) ^ "\n" ^
      "  set_parm:\n" ^
      "    subsumption ........ " ^ i2s (#subsumption b) ^ "\n" ^
      "    simplification ..... " ^ i2s (#simplification b) ^ "\n" ^
      "    splitting .......... " ^ i2s (#splitting b) ^ "\n"
    end;

  fun mp2s name (parm : mlibMeson.parameters) =
    name ^ ":\n" ^
    "  ancestor_pruning ..... " ^ b2s (#ancestor_pruning parm) ^ "\n" ^
    "  ancestor_cutting ..... " ^ b2s (#ancestor_cutting parm) ^ "\n" ^
    "  state_simplify ....... " ^ b2s (#state_simplify parm) ^ "\n" ^
    "  cache_cutting ........ " ^ b2s (#cache_cutting parm) ^ "\n" ^
    "  divide_conquer ....... " ^ b2s (#divide_conquer parm) ^ "\n" ^
    "  unit_lemmaizing ...... " ^ b2s (#unit_lemmaizing parm) ^ "\n";

  fun p2s (mlibResolution r) = rp2s "resolution" r
    | p2s (mlibMeson m) = mp2s "meson" m
    | p2s (Delta d) = mp2s "delta" d;

  fun f2s c = "cost_fn: " ^ PP.pp_to_string (!LINE_LENGTH) pp_cost_fn c ^ "\n";
in
  fun parameters_to_string (parm : parameters) =
    case map (fn (c,p) => p2s p ^ f2s c) parm of [] => ""
    | h :: t => foldl (fn (x,y) => y ^ "\n" ^ x) h t;
end;

(* ------------------------------------------------------------------------- *)
(* The metis combination of solvers.                                         *)
(* ------------------------------------------------------------------------- *)

local
  fun mk_prover (mlibResolution p) = resolution' p
    | mk_prover (mlibMeson p) = meson' p
    | mk_prover (Delta p) = delta' p;
in
  fun metis' p = combine (map (I ## mk_prover) p);
end;

val metis = metis' defaults;

(* ------------------------------------------------------------------------- *)
(* A user-friendly interface.                                                *)
(* ------------------------------------------------------------------------- *)

val settings = ref defaults;

val limit : limit ref = ref {time = NONE, infs = NONE};

local
  fun lift0 f (s,[]) = f s | lift0 _ _ = raise BUG "lift0" ""
  fun lift1 f (s,[x]) = f (s,x) | lift1 _ _ = raise BUG "lift1" ""
  fun lift2 f (s,[x,y]) = f (s,x,y) | lift2 _ _ = raise BUG "lift2" ""

  fun update_resolution _ f ((c,mlibResolution p) :: l) = (c,mlibResolution (f p)) :: l
    | update_resolution p _ _ =
    raise Optionexit
      {success = false, usage = false,
       message = SOME ("create resolution prover " ^
                       "before tweaking parameter " ^ p)};

  fun update_meson _ f ((c, mlibMeson p) :: rest) = (c, mlibMeson (f p)) :: rest
    | update_meson _ f ((c, Delta p) :: rest) = (c, Delta (f p)) :: rest
    | update_meson p _ _ =
    raise Optionexit
      {success = false, usage = false,
       message = SOME ("create meson or delta prover " ^
                       "before tweaking parameter " ^ p)};

  fun update_cost s ((_,p) :: l) =
    let
      val n = string_to_int s
      val c = if n = 0 then once_only else time_power (Real.fromInt n / 10.0)
    in
      (c,p) :: l
    end
    | update_cost _ _ =
    raise Optionexit
      {success = false, usage = false,
       message = SOME "create a prover before specifying cost function"};

  fun tlimit "-" = NONE | tlimit s = SOME (Real.fromInt (string_to_int s));

  val virgin_settings = ref true;

  fun change f =
    (if not (!virgin_settings) then ()
     else (virgin_settings := false; settings := []);
     settings := rev (f (rev (!settings))));
in
  val options =
    [{switches = ["-t","--time"], arguments = ["SECS"],
      description = "time per problem",
      processor = lift1 (fn (_,x) => limit := {time = tlimit x, infs = NONE})},
     {switches = ["-r","--resolution"], arguments = [],
      description = "create resolution prover",
      processor = lift0 (fn _ => change (cons default_resolution))},
     {switches = ["","-rl","--literal-order"], arguments = [],
      description = "toggle ordered resolution",
      processor = lift0
      (fn p =>
       (change
        o update_resolution p
        o mlibResolution.update_clause_parm
        o mlibClause.update_literal_order)
       not)},
     {switches = ["","-rt","--term-order"], arguments = [],
      description = "toggle ordered paramodulation",
      processor = lift0
      (fn p =>
       (change
        o update_resolution p
        o mlibResolution.update_clause_parm
        o mlibClause.update_term_order)
       not)},
     {switches = ["","-ro","--order-stickiness"], arguments = ["0..2"],
      description = "stickiness of ordering constraints",
      processor = lift1
      (fn (p,x) =>
       (change
        o update_resolution p
        o mlibResolution.update_clause_parm
        o mlibClause.update_termorder_parm
        o mlibTermorder.update_stickiness)
       (K (string_to_int x)))},
     {switches = ["","-rp","--order-precision"], arguments = ["0..1"],
      description = "precision of term order constraints",
      processor = lift1
      (fn (p,x) =>
       (change
        o update_resolution p
        o mlibResolution.update_clause_parm
        o mlibClause.update_termorder_parm
        o mlibTermorder.update_precision)
       (K (string_to_int x)))},
     {switches = ["","-rs","--subsumption"], arguments = ["0..2"],
      description = "amount of forward subsumption",
      processor = lift1
      (fn (p,x) =>
       (change
        o update_resolution p
        o mlibResolution.update_set_parm
        o mlibClauseset.update_subsumption)
       (K (string_to_int x)))},
     {switches = ["","-rw","--simplification"], arguments = ["0..2"],
      description = "amount of simplification by rewriting",
      processor = lift1
      (fn (p,x) =>
       (change
        o update_resolution p
        o mlibResolution.update_set_parm
        o mlibClauseset.update_simplification)
       (K (string_to_int x)))},
     {switches = ["","-rx","--splitting"], arguments = ["0..2"],
      description = "amount of clause splitting",
      processor = lift1
      (fn (p,x) =>
       (change
        o update_resolution p
        o mlibResolution.update_set_parm
        o mlibClauseset.update_splitting)
       (K (string_to_int x)))},
     {switches = ["","-rz","--size-power"], arguments = ["N/10"],
      description = "effect of clause size on weight",
      processor = lift1
      (fn (p,x) =>
       (change
        o update_resolution p
        o mlibResolution.update_sos_parm
        o mlibSupport.update_size_power)
       (K (Real.fromInt (string_to_int x) / 10.0)))},
     {switches = ["","-rn","--literal-power"], arguments = ["N/10"],
      description = "effect of #literals on clause weight",
      processor = lift1
      (fn (p,x) =>
       (change
        o update_resolution p
        o mlibResolution.update_sos_parm
        o mlibSupport.update_literal_power)
       (K (Real.fromInt (string_to_int x) / 10.0)))},
     {switches = ["-m","--meson"], arguments = [],
      description = "create model elimination prover",
      processor = lift0 (fn _ => change (cons default_meson))},
     {switches = ["-d","--delta"], arguments = [],
      description = "create delta prover",
      processor = lift0 (fn _ => change (cons default_delta))},
     {switches = ["","-ma","--ancestor-pruning"], arguments = [],
      description = "toggle ancestor pruning",
      processor = lift0
      (fn p =>
       (change
        o update_meson p
        o mlibMeson.update_ancestor_pruning)
       not)},
     {switches = ["","-mb","--ancestor-cutting"], arguments = [],
      description = "toggle ancestor cutting",
      processor = lift0
      (fn p =>
       (change
        o update_meson p
        o mlibMeson.update_ancestor_cutting)
       not)},
     {switches = ["","-ms","--state-simplify"], arguments = [],
      description = "toggle state simplification",
      processor = lift0
      (fn p =>
       (change
        o update_meson p
        o mlibMeson.update_state_simplify)
       not)},
     {switches = ["","-mc","--cache-cutting"], arguments = [],
      description = "toggle cache cutting",
      processor = lift0
      (fn p =>
       (change
        o update_meson p
        o mlibMeson.update_cache_cutting)
       not)},
     {switches = ["","-md","--divide-conquer"], arguments = [],
      description = "toggle divide & conquer searching",
      processor = lift0
      (fn p =>
       (change
        o update_meson p
        o mlibMeson.update_divide_conquer)
       not)},
     {switches = ["","-mu","--unit-lemmaizing"], arguments = [],
      description = "toggle unit lemmaizing",
      processor = lift0
      (fn p =>
       (change
        o update_meson p
        o mlibMeson.update_unit_lemmaizing)
       not)},
     {switches = ["-f","--cost-fn"], arguments = ["N/10"],
      description = "specify cost function as time power",
      processor = lift1 (fn (_,n) => (change o update_cost) n)}];
end;

local
  fun raw a b = (axiomatize a, axiomatize b, I);

  fun syn g =
    ([], eq_axiomatize (Not (generalize g)), set_of_support all_negative);
in
  fun prove g =
    let
      val (thms, hyps, sos) =
        case g of Imp (a, Imp (b, False))
          => if is_cnf a andalso is_cnf b then raw a b else syn g
        | _ => syn g
      val solv = sos (metis' (!settings))
    in
      refute (initialize solv {limit = !limit, thms = thms, hyps = hyps})
    end;
end;

fun query database =
  initialize prolog {thms = axiomatize database, hyps = [], limit = unlimited};

end
