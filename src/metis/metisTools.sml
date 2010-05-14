(* ========================================================================= *)
(* A HOL INTERFACE TO THE METIS FIRST-ORDER PROVER.                          *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

(*
app load ["mlibUseful", "mlibMetis", "folTools"];
*)

(*
*)
structure metisTools :> metisTools =
struct

open HolKernel Parse boolLib folTools folMapping;

infix THEN ORELSE THENC;

(* ------------------------------------------------------------------------- *)
(* Chatting and error handling.                                              *)
(* ------------------------------------------------------------------------- *)

(* "Metis" trace levels:
   0: No output
   1: The equivalent of Meson dots
   2: Timing information
   3: More detailed prover information: slice by slice
   4: Log of each step in proof translation
   5: Log of each inference during proof search *)

local
  open mlibUseful;
  val module = "metisTools";
  val aligned_traces =
    [{module = "mlibClause",     alignment = fn n => n + 4},
     {module = "mlibSolver",     alignment = I},
     {module = "mlibMeson",      alignment = I},
     {module = "mlibClauseset",  alignment = I},
     {module = "mlibSupport",    alignment = I},
     {module = "mlibResolution", alignment = I},
     {module = "folMapping",     alignment = fn n => n + 3},
     {module = "folTools",       alignment = I},
     {module = "metisTools",     alignment = I},
     {module = "metisLib",       alignment = I}];
  val () = register_trace ("metis", trace_level, 10);
  val () = trace_level := (if !Globals.interactive then 1 else 0);
  val () = traces := aligned_traces;
in
  fun chatting l = tracing {module = module, level = l};
  fun chat s = (trace s; true)
  val ERR = mk_HOL_ERR module;
  fun BUG f m = Bug (f ^ ": " ^ m);
end;

(* ------------------------------------------------------------------------- *)
(* Making the Metis prover HOL specific.                                     *)
(* ------------------------------------------------------------------------- *)

fun bool_map ":" = SOME "fst"      (* Force types to be ignored in the model *)
  | bool_map "combin.I" = SOME "id"
  | bool_map "pair.FST" = SOME "id"
  | bool_map "pair.," = SOME "fst"
  | bool_map _ = NONE;

fun num_map "num.0" = SOME "0"
  | num_map "num.SUC" = SOME "suc"
  | num_map "prim_rec.PRE" = SOME "pre"
  | num_map "arithmetic.+" = SOME "+"
  | num_map "arithmetic.-" = SOME "-"
  | num_map "arithmetic.*" = SOME "*"
  | num_map "arithmetic.EXP" = SOME "exp"
  | num_map "arithmetic.MOD" = SOME "mod"
  | num_map "arithmetic.<=" = SOME "<="
  | num_map "prim_rec.<" = SOME "<"
  | num_map "arithmetic.>" = SOME ">"
  | num_map "arithmetic.>=" = SOME ">="
  | num_map "divides.divides" = SOME "divides"
  | num_map "arithmetic.ODD" = SOME "odd"
  | num_map "arithmetic.EVEN" = SOME "even"
  | num_map "arithmetic.NUMERAL" = SOME "id"
  | num_map "arithmetic.ALT_ZERO" = SOME "0"
  | num_map "arithmetic.NUMERAL_BIT1" = SOME "BIT1"
  | num_map "arithmetic.NUMERAL_BIT2" = SOME "BIT2"
  | num_map _ = NONE;

fun holify_num fix N =
  let
    val {func,pred} = fix N
    val funk = partial (BUG "holify_num" "missing function alert!") func
    val one = funk ("1",[]) and two = funk ("2",[])
    fun func' ("BIT1",[m]) = SOME (funk ("+", [funk ("*",[two,m]), one]))
      | func' ("BIT2",[m]) = SOME (funk ("+", [funk ("*",[two,m]), two]))
      | func' x = func x
  in
    {func = func', pred = pred}
  end;

fun int_map "integer.int_neg" = SOME "~"
  | int_map "integer.int_add" = SOME "+"
  | int_map "integer.int_sub" = SOME "-"
  | int_map "integer.int_mul" = SOME "*"
  | int_map "integer.int_exp" = SOME "exp"
  | int_map "integer.int_le" = SOME "<="
  | int_map "integer.int_lt" = SOME "<"
  | int_map "integer.int_gt" = SOME ">"
  | int_map "integer.int_ge" = SOME ">="
  | int_map "integer.int_of_num" = SOME "id"
  | int_map _ = NONE;

fun list_map "list.NIL" = SOME "0"
  | list_map "list.CONS" = SOME "suc"
  | list_map "list.TL" = SOME "pre"
  | list_map "list.APPEND" = SOME "+"
  | list_map "list.NULL" = SOME "is_0"
  | list_map "list.LENGTH" = SOME "id"
  | list_map _ = NONE;

fun set_map "pred_set.EMPTY" = SOME "empty"
  | set_map "pred_set.UNIV" = SOME "univ"
  | set_map "pred_set.UNION" = SOME "union"
  | set_map "pred_set.INTER" = SOME "inter"
  | set_map "pred_set.COMPL" = SOME "compl"
  | set_map "pred_set.CARD" = SOME "card"
  | set_map "bool.IN" = SOME "in"
  | set_map "pred_set.SUBSET" = SOME "subset"
  | set_map _ = NONE;

val modulo_basic_fix =
  mlibModel.fix_merge mlibModel.modulo_fix mlibModel.basic_fix;

val hol_fix = mlibModel.fix_mergel
  [mlibModel.pure_fix,
   mlibModel.map_fix bool_map mlibModel.basic_fix,
   mlibModel.map_fix num_map (holify_num modulo_basic_fix),
   mlibModel.map_fix int_map modulo_basic_fix,
   mlibModel.map_fix list_map modulo_basic_fix,
   mlibModel.map_fix set_map mlibModel.set_fix];

local
  val METIS_PROVER = [mlibMetis.ordered_resolution];
  val MODEL_SIZE = 8;
  val MODEL_PERTS = 5;

  fun hol_parm n =
    (mlibModel.update_fix (K hol_fix) o
     mlibModel.update_size (K n)) mlibModel.defaults;

  fun holify_res ms =
    mlibResolution.update_sos_parm
    (mlibSupport.update_model_perts (K MODEL_PERTS) o
     mlibSupport.update_model_parms (K ms));

  fun holify ms (mlibMetis.mlibResolution r, f, c) =
    (mlibMetis.mlibResolution (holify_res ms r), f, c)
    | holify _ x = x;

  fun update_models ms = map (holify ms) METIS_PROVER;
in
  val fo_solver = update_models [hol_parm MODEL_SIZE];
  val ho_solver = update_models [];
end;

(* ------------------------------------------------------------------------- *)
(* Parameters.                                                               *)
(* ------------------------------------------------------------------------- *)

type Fparm = folTools.parameters;
type Mparm = mlibMetis.parameters;
type parameters = {interface : Fparm, solver : Mparm, limit : limit};

val defaults =
  {interface = folTools.defaults,
   limit = mlibMeter.unlimited,
   solver = fo_solver};

fun update_interface f {interface, solver, limit} =
  {interface = f interface, solver = solver, limit = limit};

fun update_solver f {interface, solver, limit} =
  {interface = interface, solver = f solver, limit = limit};

fun update_limit f {interface, solver, limit} =
  {interface = interface, solver = solver, limit = f limit};

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun timed_fn s f a =
  let
    val (t, r) = mlibUseful.timed f a
    val _ = chatting 2 andalso chat
      ("metis: " ^ s ^ " time: " ^ mlibUseful.real_to_string t ^ "\n")
  in
    r
  end;

fun contains s =
  let
    fun g [] _ = true | g _ [] = false | g (a::b) (c::d) = a = c andalso g b d
    val k = explode s
    fun f [] = false | f (l as _ :: ys) = g k l orelse f ys
  in
    f o explode
  end;

fun const_scheme c =
  let val {Thy, Name, ...} = dest_thy_const c
  in prim_mk_const {Name = Name, Thy = Thy}
  end;

fun trap f g x =
  f x
  handle e as HOL_ERR {message, ...} =>
    (if not (contains "proof translation error" message) then raise e else
       (chatting 1 andalso
        chat "metis: proof translation error: trying again with types.\n";
        g x));

(* ------------------------------------------------------------------------- *)
(* Prolog solver.                                                            *)
(* ------------------------------------------------------------------------- *)

local
  val prolog_parm =
    {equality = false,
     boolean = false,
     combinator = false,
     mapping_parm = {higher_order = false, with_types = true}};
in
  fun PROLOG_SOLVE ths =
    let
      val _ = (chatting 1 andalso chat "prolog: "; chatting 2 andalso chat "\n")
      val (cs,ths) = FOL_NORM ths
      val lmap = build_map (prolog_parm,cs,ths)
    in
      FOL_SOLVE mlibMeson.prolog lmap mlibMeter.unlimited
    end;
end;

(* ------------------------------------------------------------------------- *)
(* Metis solver.                                                             *)
(* ------------------------------------------------------------------------- *)

fun GEN_METIS_SOLVE parm ths =
  let
    val {interface, solver, limit, ...} : parameters = parm
    val _ = (chatting 1 andalso chat "metis solver: ";
             chatting 2 andalso chat "\n")
    val (cs,ths) = FOL_NORM ths
    val lmap = build_map (interface,cs,ths)
  in
    FOL_SOLVE (mlibMetis.metis' solver) lmap limit
  end;

(* ------------------------------------------------------------------------- *)
(* Tactic interface to the metis prover.                                     *)
(* ------------------------------------------------------------------------- *)

fun X_METIS_TAC ttac ths goal =
  (chatting 1 andalso chat "metis: "; chatting 2 andalso chat "\n";
   FOL_NORM_TTAC ttac ths goal);

fun GEN_METIS_TTAC parm (cs,ths) =
  let
    val {interface, solver, limit, ...} : parameters = parm
    val lmap = timed_fn "logic map build" build_map (interface,cs,ths)
  in
    FOL_TACTIC (mlibMetis.metis' solver) lmap limit
  end;

val GEN_METIS_TAC = X_METIS_TAC o GEN_METIS_TTAC;

(* ------------------------------------------------------------------------- *)
(* All the following use this limit.                                         *)
(* ------------------------------------------------------------------------- *)

val limit : limit ref = ref (#limit defaults);

(* ------------------------------------------------------------------------- *)
(* Canned parameters for common situations.                                  *)
(* ------------------------------------------------------------------------- *)

fun inc_limit p = update_limit (K (!limit)) p;
fun set_limit f p t g = f (inc_limit p) t g;

(* First-order *)

val fo_parm =
  update_interface
  (update_mapping_parm (K {higher_order = false, with_types = false}))
  (update_solver (K fo_solver) defaults);

val fot_parm =
  update_interface (update_mapping_parm (update_with_types (K true))) fo_parm;

val FOT_METIS_TTAC = set_limit GEN_METIS_TTAC fot_parm;

fun FO_METIS_TTAC ths =
  trap (set_limit GEN_METIS_TTAC fo_parm ths) (FOT_METIS_TTAC ths);

(* Higher-order *)

val ho_parm =
  update_interface
  (update_mapping_parm (K {higher_order = true, with_types = false}))
  (update_solver (K ho_solver) defaults);

val hot_parm =
  update_interface (update_mapping_parm (update_with_types (K true))) ho_parm;

val HOT_METIS_TTAC = set_limit GEN_METIS_TTAC hot_parm;

fun HO_METIS_TTAC ths =
  trap (set_limit GEN_METIS_TTAC ho_parm ths) (HOT_METIS_TTAC ths);

(* Higher-order with rules for combinator reductions and booleans *)

val full_parm =
  (update_interface (update_combinator (K true) o update_boolean (K true)))
  hot_parm;

val FULL_METIS_TTAC = set_limit GEN_METIS_TTAC full_parm;

(* ------------------------------------------------------------------------- *)
(* Canned tactics.                                                           *)
(* ------------------------------------------------------------------------- *)

val FO_METIS_TAC   = X_METIS_TAC FO_METIS_TTAC;
val FOT_METIS_TAC  = X_METIS_TAC FOT_METIS_TTAC;
val HO_METIS_TAC   = X_METIS_TAC HO_METIS_TTAC;
val HOT_METIS_TAC  = X_METIS_TAC HOT_METIS_TTAC;
val FULL_METIS_TAC = X_METIS_TAC FULL_METIS_TTAC;

(* ------------------------------------------------------------------------- *)
(* Simple user interface to the metis prover.                                *)
(* ------------------------------------------------------------------------- *)

fun prover ttac ths goal = Tactical.default_prover (goal, ttac ths);

val FO_METIS_PROVE   = prover FO_METIS_TAC;
val FOT_METIS_PROVE  = prover FOT_METIS_TAC;
val HO_METIS_PROVE   = prover HO_METIS_TAC;
val HOT_METIS_PROVE  = prover HOT_METIS_TAC;
val FULL_METIS_PROVE = prover FULL_METIS_TAC;

(* ------------------------------------------------------------------------- *)
(* Uses heuristics to apply one of FO_, HO_ or FULL_.                        *)
(* ------------------------------------------------------------------------- *)

datatype class = First | Higher | Full;

fun class_str First = "first-order"
  | class_str Higher = "higher-order"
  | class_str Full = "higher-order + combinators";

fun class_tac First = FO_METIS_TTAC
  | class_tac Higher = HO_METIS_TTAC
  | class_tac Full = FULL_METIS_TTAC;

local
  fun mk_set ts = Binaryset.addList (Binaryset.empty compare, ts);
  fun member x s = Binaryset.member (s,x);

  val empty : (term, bool * int) Binarymap.dict = Binarymap.mkDict compare;
  fun update ts x n = Binarymap.insert (ts,x,n);
  fun lookup ts x = Binarymap.peek (ts,x);

  fun bump Full _ = Full
    | bump Higher Full = Full
    | bump Higher _ = Higher
    | bump First cl = cl;

  fun ord _ [] state = state
    | ord top (tm :: tms) (c,g,l,t,v) =
    let
      val (f,xs) = strip_comb tm
      val f = if is_const f then const_scheme f else f
      val n = length xs
      val tn = (top,n)
      val tms = xs @ tms
    in
      ord false tms
      (if member f v then
         ((if n <> 0 orelse top then bump Higher c else c), g, l, t, v)
       else if member f t then
         (case lookup l f of NONE => (c, g, update l f tn, t, v)
          | SOME tn' => ((if tn = tn' then c else bump Higher c), g, l, t, v))
       else
         (case lookup g f of NONE => (c, update g f tn, l, t, v)
          | SOME tn' => ((if tn = tn' then c else bump Higher c), g, l, t, v)))
    end;

  fun order_lit [] state = state
    | order_lit (lit :: lits) (state as (c,g,l,t,v)) =
    let
      val atom = case total dest_neg lit of NONE => lit | SOME lit => lit
    in
      order_lit lits (ord true [atom] state)
    end;

  fun order_cl (cl,gs,_,_,_) [] = (cl,gs)
    | order_cl state (fm :: fms) =
    order_cl (order_lit (strip_disj fm) state) fms;

  fun order (cl,_) [] = cl
    | order (cl,cs) (fm :: fms) =
    let
      val (ts,fm) = strip_exists fm
      val (vs,fm) = strip_forall fm
      val cls = strip_conj fm
    in
      order (order_cl (cl, cs, empty, mk_set ts, mk_set vs) cls) fms
    end;
in
  fun classify fms = order (First,empty) fms
    handle HOL_ERR _ => raise BUG "metisTools.classify" "shouldn't fail";
end;

fun METIS_TTAC (cs,ths) =
  let
    val class = timed_fn "problem classification" classify (map concl ths)
    val _ = chatting 2 andalso
            chat ("metis: a " ^ class_str class ^ " problem.\n")
  in
    class_tac class (cs,ths)
  end;

val METIS_TAC = X_METIS_TAC METIS_TTAC;

(*
val METIS_TAC = fn ths => fn goal =>
    let
      val met = Count.mk_meter ()
      val _ = chat "\nMETIS_TAC: new\n"
      val res = METIS_TAC ths goal
      val {prims,...} = Count.read met
      val _ = chat ("METIS_TAC: " ^ Int.toString prims ^ "\n")
    in
      res
    end;
*)

val METIS_PROVE = prover METIS_TAC;

end
