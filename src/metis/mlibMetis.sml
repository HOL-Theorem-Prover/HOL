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
  [{module = "mlibSolver",     alignment = I},
   {module = "mlibMeson",      alignment = I},
   {module = "mlibTermorder",  alignment = fn n => n + 4},
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

type parameters =
  {resolution_parms : mlibResolution.parameters list,
   meson_parms      : mlibMeson.parameters list,
   delta_parms      : mlibMeson.parameters list};

val defaults =
  {resolution_parms = [mlibResolution.defaults],
   meson_parms      = [mlibMeson.defaults],
   delta_parms      = [mlibMeson.defaults]};

type 'a Parmupdate = ('a -> 'a) -> parameters -> parameters;

fun update_resolution_parms f (parm : parameters) : parameters =
  let val {resolution_parms = r, meson_parms = m, delta_parms = d} = parm
  in {resolution_parms = f r, meson_parms = m, delta_parms = d}
  end;

fun update_meson_parms f (parm : parameters) : parameters =
  let val {resolution_parms = r, meson_parms = m, delta_parms = d} = parm
  in {resolution_parms = r, meson_parms = f m, delta_parms = d}
  end;

fun update_delta_parms f (parm : parameters) : parameters =
  let val {resolution_parms = r, meson_parms = m, delta_parms = d} = parm
  in {resolution_parms = r, meson_parms = m, delta_parms = f d}
  end;

local
  fun b2s true = "on" | b2s false = "off";
  fun v2s true = "visible" | v2s false = "invisible";
  val i2s = mlibUseful.int_to_string;
  val l2s = mlibMeter.limit_to_string;
  fun io2s NONE = "NONE" | io2s (SOME i) = "SOME " ^ i2s i;
  val r2s = mlibUseful.real_to_string;

  fun rp2s name (parm : mlibResolution.parameters) =
    let
      val {restart = r, clause_parm = c, sos_parm = a, set_parm = b} = parm
    in
      name ^ ":\n" ^
      "  restart .............. " ^ io2s r ^ "\n" ^
      "  clause_parm:\n" ^
      "    literal_order ...... " ^ b2s (#literal_order c) ^ "\n" ^
      "    term_order ......... " ^ b2s (#term_order c) ^ "\n" ^
      "    termorder_parm:\n" ^
      "      approx ........... " ^ i2s (#approx (#termorder_parm c)) ^ "\n" ^
      "  sos_parm:\n" ^
      "    size_power ......... " ^ r2s (#size_power a) ^ "\n" ^
      "    literal_power ...... " ^ r2s (#literal_power a) ^ "\n" ^
      "  set_parm:\n" ^
      "    subsumption ........ " ^ i2s (#subsumption b) ^ "\n" ^
      "    simplification ..... " ^ i2s (#simplification b) ^ "\n"
    end;

  fun mp2s name (parm : mlibMeson.parameters) =
    name ^ ":\n" ^
    "  ancestor_pruning ..... " ^ b2s (#ancestor_pruning parm) ^ "\n" ^
    "  ancestor_cutting ..... " ^ b2s (#ancestor_cutting parm) ^ "\n" ^
    "  state_simplify ....... " ^ b2s (#state_simplify parm) ^ "\n" ^
    "  cache_cutting ........ " ^ b2s (#cache_cutting parm) ^ "\n" ^
    "  divide_conquer ....... " ^ b2s (#divide_conquer parm) ^ "\n" ^
    "  unit_lemmaizing ...... " ^ b2s (#unit_lemmaizing parm) ^ "\n";
in
  fun parameters_to_string (parm : parameters) =
    let
      val {resolution_parms = r, meson_parms = m, delta_parms = d} = parm
      val m = map (mp2s "meson"     ) m
      val r = map (rp2s "resolution") r
      val d = map (mp2s "delta"     ) d
    in
      case m @ r @ d of [] => ""
      | h :: t => foldl (fn (x,y) => y ^ "\n" ^ x) h t
    end;
end;

(* ------------------------------------------------------------------------- *)
(* The metis combination of solvers.                                         *)
(* ------------------------------------------------------------------------- *)

fun metis' {resolution_parms = r, meson_parms = m, delta_parms = d} =
  combine
  (map (fn p => (time2,     meson'      p)) m @
   map (fn p => (time1,     resolution' p)) r @
   map (fn p => (once_only, delta'      p)) d);

val metis = metis' defaults;

(* ------------------------------------------------------------------------- *)
(* A user-friendly interface.                                                *)
(* ------------------------------------------------------------------------- *)

val settings = ref defaults;

val limit : limit ref = ref {time = NONE, infs = NONE};

local
  fun lift0 f [] = f () | lift0 _ _ = raise BUG "lift0" ""
  fun lift1 f [x] = f x | lift1 _ _ = raise BUG "lift1" ""
  fun lift2 f [x,y] = f (x,y) | lift2 _ _ = raise BUG "lift2" ""

  fun snoc x l = l @ [x];

  fun update_last _ [] =
    raise Optionexit
      {message = SOME "create prover before setting prover options",
       usage = true, success = false}
    | update_last f l = update_nth f (length l - 1) l;

  fun tlimit "-" = NONE | tlimit s = SOME (Real.fromInt (string_to_int s));

  val pure_settings =
    (update_resolution_parms (K []) o
     update_meson_parms      (K []) o
     update_delta_parms      (K [])) defaults;

  val virgin_settings = ref true;

  fun change f =
    (if not (!virgin_settings) then ()
     else (virgin_settings := false; settings := pure_settings);
     settings := f (!settings));
in
  val options =
    [{switches = ["-t","--time"], arguments = ["SECS"],
      description = "time per problem",
      processor = lift1 (fn x => limit := {time = tlimit x, infs = NONE})},
     {switches = ["-r","--resolution"], arguments = [],
      description = "create resolution prover",
      processor = lift0
      (fn () => (change o update_resolution_parms) (snoc mlibResolution.defaults))},
     {switches = ["-m","--meson"], arguments = [],
      description = "create model elimination prover",
      processor = lift0
      (fn () => (change o update_meson_parms) (snoc mlibMeson.defaults))},
     {switches = ["-d","--delta"], arguments = [],
      description = "create delta prover",
      processor = lift0
      (fn () => (change o update_delta_parms) (snoc mlibMeson.defaults))},
     {switches = ["-rl","--resolution-literal-order"], arguments = [],
      description = "toggle ordered resolution",
      processor = lift0
      (fn () =>
       (change
        o update_resolution_parms o update_last
        o mlibResolution.update_clause_parm
        o mlibClause.update_literal_order)
       not)},
     {switches = ["-rt","--resolution-term-order"], arguments = [],
      description = "toggle ordered paramodulation",
      processor = lift0
      (fn () =>
       (change
        o update_resolution_parms o update_last
        o mlibResolution.update_clause_parm
        o mlibClause.update_term_order)
       not)},
     {switches = ["-ro","--resolution-approx"], arguments = ["0..2"],
      description = "stickiness of ordering constraints",
      processor = lift1
      (fn x =>
       (change
        o update_resolution_parms o update_last
        o mlibResolution.update_clause_parm
        o mlibClause.update_termorder_parm
        o mlibTermorder.update_approx)
       (K (string_to_int x)))},
     {switches = ["-rs","--resolution-subsumption"], arguments = ["0..2"],
      description = "amount of forward subsumption",
      processor = lift1
      (fn x =>
       (change
        o update_resolution_parms o update_last
        o mlibResolution.update_set_parm
        o mlibClauseset.update_subsumption)
       (K (string_to_int x)))},
     {switches = ["-rw","--resolution-simplification"], arguments = ["0..2"],
      description = "amount of simplification by rewriting",
      processor = lift1
      (fn x =>
       (change
        o update_resolution_parms o update_last
        o mlibResolution.update_set_parm
        o mlibClauseset.update_simplification)
       (K (string_to_int x)))},
     {switches = ["-rz","--resolution-size-power"], arguments = ["N"],
      description = "effect of clause size on weight",
      processor = lift1
      (fn x =>
       (change
        o update_resolution_parms o update_last
        o mlibResolution.update_sos_parm
        o mlibSupport.update_size_power)
       (K (Real.fromInt (string_to_int x))))},
     {switches = ["-rn","--resolution-literal-power"], arguments = ["N"],
      description = "effect of #literals on clause weight",
      processor = lift1
      (fn x =>
       (change
        o update_resolution_parms o update_last
        o mlibResolution.update_sos_parm
        o mlibSupport.update_literal_power)
       (K (Real.fromInt (string_to_int x))))},
     {switches = ["-ma","--meson-ancestor-pruning"], arguments = [],
      description = "toggle ancestor pruning",
      processor = lift0
      (fn () =>
       (change
        o update_meson_parms o update_last
        o mlibMeson.update_ancestor_pruning)
       not)},
     {switches = ["-mb","--meson-ancestor-cutting"], arguments = [],
      description = "toggle ancestor cutting",
      processor = lift0
      (fn () =>
       (change
        o update_meson_parms o update_last
        o mlibMeson.update_ancestor_cutting)
       not)},
     {switches = ["-ms","--meson-state-simplify"], arguments = [],
      description = "toggle state simplification",
      processor = lift0
      (fn () =>
       (change
        o update_meson_parms o update_last
        o mlibMeson.update_state_simplify)
       not)},
     {switches = ["-mc","--meson-cache-cutting"], arguments = [],
      description = "toggle cache cutting",
      processor = lift0
      (fn () =>
       (change
        o update_meson_parms o update_last
        o mlibMeson.update_cache_cutting)
       not)},
     {switches = ["-md","--meson-divide-conquer"], arguments = [],
      description = "toggle divide & conquer searching",
      processor = lift0
      (fn () =>
       (change
        o update_meson_parms o update_last
        o mlibMeson.update_divide_conquer)
       not)},
     {switches = ["-mu","--meson-unit-lemmaizing"], arguments = [],
      description = "toggle unit lemmaizing",
      processor = lift0
      (fn () =>
       (change
        o update_meson_parms o update_last
        o mlibMeson.update_unit_lemmaizing)
       not)}];
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
