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

open mlibUseful mlibTerm mlibThm mlibMeter mlibCanon mlibSolver mlibOptions;

infix |-> ::> @> oo ## ::* ::@;

structure M = mlibMeson; local open mlibMeson in end;
structure R = mlibResolution; local open mlibResolution in end;

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
   {module = "mlibModel",      alignment = fn n => n + 4},
   {module = "mlibSolver",     alignment = I},
   {module = "mlibMeson",      alignment = I},
   {module = "mlibClause",     alignment = fn n => n + 3},
   {module = "mlibClauseset",  alignment = fn 1 => 1 | n => n + 2},
   {module = "mlibSupport",    alignment = fn n => n + 3},
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
  mlibResolution of R.parameters
| mlibMeson of M.parameters
| Delta of M.parameters;

type parameters = (prover * sos_filter option * cost_fn) list;

val default_model = mlibModel.update_perts (K (100,1)) mlibModel.defaults;

local
  val rl = R.update_clause_parm o mlibClause.update_literal_order o K;
  fun rm ns =
    (R.update_sos_parm o mlibSupport.update_model_parms)
    (fn l => l @ map (fn n => mlibModel.update_size (K n) default_model) ns);
in
  val ord_mlibResolution = mlibResolution o rm [4,5,6] o rl true;
end;

val default_meson = (mlibMeson M.defaults, NONE, time_power 2.0);
val default_resolution = (mlibResolution R.defaults,SOME everything,time_power 1.3);
val default_delta = (Delta M.defaults, NONE, once_only);
val ord_resolution = (ord_mlibResolution R.defaults, NONE, time_power 1.0);
val defaults = [default_meson,default_resolution,default_delta,ord_resolution];

local
  fun b2s true = "on" | b2s false = "off";
  val i2s = mlibUseful.int_to_string;
  fun io2s NONE = "NONE" | io2s (SOME i) = "SOME " ^ i2s i;
  val r2s = mlibUseful.real_to_string;
  fun mp2s {size, perts = (p,q)} = i2s size ^ "(" ^ i2s p ^ "+" ^ i2s q ^ ")";
  fun mpl2s l = PP.pp_to_string (!LINE_LENGTH) (pp_list pp_string) (map mp2s l);

  fun rp2s name (parm : R.parameters) =
    let
      val {clause_parm = c, sos_parm = a, set_parm = b} = parm
      val {termorder_parm = t, ...} = c
    in
      name ^ ":\n" ^
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
      "    model_checks ....... " ^ i2s (#model_checks a) ^ "\n" ^
      "    model_parms ........ " ^ mpl2s (#model_parms a) ^ "\n" ^
      "  set_parm:\n" ^
      "    subsumption ........ " ^ i2s (#subsumption b) ^ "\n" ^
      "    simplification ..... " ^ i2s (#simplification b) ^ "\n" ^
      "    splitting .......... " ^ i2s (#splitting b) ^ "\n"
    end;

  fun mp2s name (parm : M.parameters) =
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

  fun s2s (s : sos_filter option) =
    "sos: " ^ (case s of NONE => "natural" | SOME {name, ...} => name) ^ "\n";

  fun c2s c = "cost_fn: " ^ PP.pp_to_string (!LINE_LENGTH) pp_cost_fn c ^ "\n";
in
  fun parameters_to_string (parm : parameters) =
    case map (fn (p,s,c) => p2s p ^ s2s s ^ c2s c) parm of [] => ""
    | h :: t => foldl (fn (x,y) => y ^ "\n" ^ x) h t;
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

local
  fun lift0 f (s,[]) = f s | lift0 _ _ = raise BUG "lift0" "";
  fun lift1 f (s,[x]) = f (s,x) | lift1 _ _ = raise BUG "lift1" "";
  fun lift2 f (s,[x,y]) = f (s,x,y) | lift2 _ _ = raise BUG "lift2" "";

  fun lift_toggle f = lift0 (fn s => f s not);

  fun lift_nat f = int_option (SOME 0, NONE) (fn (s,i) => f s (K i));

  fun lift_int m f = int_option (SOME 0, SOME m) (fn (s,i) => f s (K i));

  fun lift_sign f = int_option (SOME ~1, SOME 1) (fn (s,i) => f s (K i));

  fun lift_real f = real_option (SOME 0.0, NONE) (fn (s,r) => f s (K r));

  fun update_resolution _ f ((mlibResolution p, s, c) :: l) =
    (mlibResolution (f p), s, c) :: l
    | update_resolution p _ _ =
    raise Optionexit
      {success = false, usage = false,
       message = SOME ("create resolution prover " ^
                       "before tweaking parameter " ^ p)};

  fun update_meson _ f ((mlibMeson p, s, c) :: rest) = (mlibMeson (f p), s, c) :: rest
    | update_meson _ f ((Delta p, s, c) :: rest) = (Delta (f p), s, c) :: rest
    | update_meson p _ _ =
    raise Optionexit
      {success = false, usage = false,
       message = SOME ("create meson or delta prover " ^
                       "before tweaking parameter " ^ p)};

  fun update_sos (_,"P") ((p,_,c) :: l) = ((p, SOME all_positive, c) :: l)
    | update_sos (_,"N") ((p,_,c) :: l) = ((p, SOME all_negative, c) :: l)
    | update_sos (_,"-") ((p,_,c) :: l) = ((p, NONE, c) :: l)
    | update_sos (_,"p") ((p,_,c) :: l) = ((p, SOME one_positive, c) :: l)
    | update_sos (_,"n") ((p,_,c) :: l) = ((p, SOME one_negative, c) :: l)
    | update_sos (_,"1") ((p,_,c) :: l) = ((p, SOME everything, c) :: l)
    | update_sos (_,s) (_ :: _) =
    raise Optionexit
      {success = false, usage = false,
       message = SOME ("unknown set of support: \"" ^ s ^ "\"")}
    | update_sos _ [] =
    raise Optionexit
      {success = false, usage = false,
       message = SOME "create a prover before specifying set of support"};

  fun update_cost (_,r) ((p,s,_) :: l) =
    (p, s, if Real.== (r, 0.0) then once_only else time_power r) :: l
    | update_cost _ [] =
    raise Optionexit
      {success = false, usage = false,
       message = SOME "create a prover before specifying cost function"};

  val virgin_settings = ref true;

  fun change f =
    (if not (!virgin_settings) then ()
     else (virgin_settings := false; settings := []);
     settings := rev (f (rev (!settings))));
in
  val options =
    [{switches = ["-t","--time"], arguments = ["SECS"],
      description = "time per problem",
      processor =
      let
        fun f x = limit := {time = x, infs = NONE}
      in
        fn (_,["-"]) => f NONE
         | x => real_option (SOME 0.0, NONE) (f o SOME o snd) x
      end},
     {switches = ["-r","--resolution"], arguments = [],
      description = "create resolution prover",
      processor = lift0 (fn _ => change (cons default_resolution))},
     {switches = ["","-rt","--term-order"], arguments = [],
      description = "toggle ordered paramodulation",
      processor = lift_toggle
      (fn p =>
       change
       o update_resolution p
       o R.update_clause_parm
       o mlibClause.update_term_order)},
     {switches = ["","-rl","--literal-order"], arguments = [],
      description = "toggle ordered resolution",
      processor = lift_toggle
      (fn p =>
       change
       o update_resolution p
       o R.update_clause_parm
       o mlibClause.update_literal_order)},
     {switches = ["","-ro","--order-stickiness"], arguments = ["0..3"],
      description = "stickiness of term order constraints",
      processor = lift_int 3
      (fn p =>
       change
       o update_resolution p
       o R.update_clause_parm
       o mlibClause.update_order_stickiness)},
     {switches = ["","-rp","--order-precision"], arguments = ["0..3"],
      description = "precision of term order constraints",
      processor = lift_int 3
      (fn p =>
       change
       o update_resolution p
       o R.update_clause_parm
       o mlibClause.update_termorder_parm
       o mlibTermorder.update_precision)},
     {switches = ["","-rs","--subsumption"], arguments = ["0..2"],
      description = "amount of forward subsumption",
      processor = lift_int 2
      (fn p =>
       change
       o update_resolution p
       o R.update_set_parm
       o mlibClauseset.update_subsumption)},
     {switches = ["","-rw","--simplification"], arguments = ["0..2"],
      description = "amount of simplification by rewriting",
      processor = lift_int 2
      (fn p =>
       change
       o update_resolution p
       o R.update_set_parm
       o mlibClauseset.update_simplification)},
     {switches = ["","-rx","--splitting"], arguments = ["0..2"],
      description = "amount of clause splitting",
      processor = lift_int 2
      (fn p =>
       change
       o update_resolution p
       o R.update_set_parm
       o mlibClauseset.update_splitting)},
     {switches = ["","-rz","--size-power"], arguments = ["N"],
      description = "effect of clause size on weight",
      processor = lift_real
      (fn p =>
       change
       o update_resolution p
       o R.update_sos_parm
       o mlibSupport.update_size_power)},
     {switches = ["","-rn","--literal-power"], arguments = ["N"],
      description = "effect of #literals on clause weight",
      processor = lift_real
      (fn p =>
       change
       o update_resolution p
       o R.update_sos_parm
       o mlibSupport.update_literal_power)},
     {switches = ["","-rd","--model-power"], arguments = ["N"],
      description = "effect of model checking on clause weight",
      processor = lift_real
      (fn p =>
       change
       o update_resolution p
       o R.update_sos_parm
       o mlibSupport.update_model_power)},
     {switches = ["","-rm","--add-model"], arguments = ["n"],
      description = "add a finite model with domain {0..n-1}",
      processor = lift_nat
      (fn p =>
       change
       o update_resolution p
       o R.update_sos_parm
       o mlibSupport.update_model_parms
       o (fn n => fn l => l @ [mlibModel.update_size n default_model]))},
     {switches = ["-m","--meson"], arguments = [],
      description = "create model elimination prover",
      processor = lift0 (fn _ => change (cons default_meson))},
     {switches = ["-d","--delta"], arguments = [],
      description = "create delta prover",
      processor = lift0 (fn _ => change (cons default_delta))},
     {switches = ["","-ma","--ancestor-pruning"], arguments = [],
      description = "toggle ancestor pruning",
      processor = lift_toggle
      (fn p =>
       change
       o update_meson p
       o M.update_ancestor_pruning)},
     {switches = ["","-mb","--ancestor-cutting"], arguments = [],
      description = "toggle ancestor cutting",
      processor = lift_toggle
      (fn p =>
       change
       o update_meson p
       o M.update_ancestor_cutting)},
     {switches = ["","-ms","--state-simplify"], arguments = [],
      description = "toggle state simplification",
      processor = lift_toggle
      (fn p =>
       change
       o update_meson p
       o M.update_state_simplify)},
     {switches = ["","-mc","--cache-cutting"], arguments = [],
      description = "toggle cache cutting",
      processor = lift_toggle
      (fn p =>
       change
       o update_meson p
       o M.update_cache_cutting)},
     {switches = ["","-md","--divide-conquer"], arguments = [],
      description = "toggle divide & conquer searching",
      processor = lift_toggle
      (fn p =>
       change
       o update_meson p
       o M.update_divide_conquer)},
     {switches = ["","-mu","--unit-lemmaizing"], arguments = [],
      description = "toggle unit lemmaizing",
      processor = lift_toggle
      (fn p =>
       change
       o update_meson p
       o M.update_unit_lemmaizing)},
     {switches = ["-s","--sos"], arguments = ["{P,N,-,p,n,1}"],
      description = "specify the set of support",
      processor = lift1 (change o update_sos)},
     {switches = ["-c","--cost-fn"], arguments = ["N"],
      description = "specify cost function as time power",
      processor = real_option (SOME 0.0, NONE) (change o update_cost)}];
end;

local
  fun raw a b = (axiomatize a, axiomatize b, I);

  fun syn g =
    ([], eq_axiomatize (Not (generalize g)), apply_sos_filter all_negative);
in
  fun prove g =
    let
      val g = generalize g
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
  initialize M.prolog
  {thms = axiomatize database, hyps = [], limit = unlimited};

end
