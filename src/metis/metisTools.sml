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
    [{module = "mlibSolver",     alignment = fn 1 => 1 | n => n + 1},
     {module = "mlibMeson",      alignment = fn 1 => 1 | n => n + 1},
     {module = "mlibClause",     alignment = fn n => n + 4},
     {module = "mlibResolution", alignment = fn n => if n <= 3 then n else n+1},
     {module = "folMapping",     alignment = fn n => n + 3},
     {module = "folTools",       alignment = fn 1 => 2 | n => n + 2},
     {module = "metisTools",     alignment = I},
     {module = "metisLib",       alignment = I}];
  val () = register_trace ("metis", trace_level, 10);
  val () = trace_level := (if !Globals.interactive then 1 else 0);
  val () = traces := aligned_traces;
in
  fun chatting l = tracing {module = module, level = l};
  fun chat s = (trace s; true)
  val ERR = mk_HOL_ERR module;
  val BUG = BUG;
end;

(* ------------------------------------------------------------------------- *)
(* Parameters.                                                               *)
(* ------------------------------------------------------------------------- *)

type Fparm      = folTools.parameters;
type Mparm      = mlibMetis.parameters;
type parameters = {interface : Fparm, solver : Mparm, limit : limit};

val defaults =
  {interface = folTools.defaults,
   solver    = mlibMetis.defaults,
   limit     = mlibMeter.unlimited};

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
    {equality   = false,
     boolean    = false,
     combinator = false,
     mapping    = {higher_order = false, with_types = true}};
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
  (update_mapping (K {higher_order = false, with_types = false})) defaults;

val fot_parm =
  update_interface (update_mapping (update_with_types (K true))) fo_parm;

val FOT_METIS_TTAC = set_limit GEN_METIS_TTAC fot_parm;

fun FO_METIS_TTAC ths =
  trap (set_limit GEN_METIS_TTAC fo_parm ths) (FOT_METIS_TTAC ths);

(* Higher-order *)

val ho_parm =
  update_interface
  (update_mapping (K {higher_order = true, with_types = false})) defaults;

val hot_parm =
  update_interface (update_mapping (update_with_types (K true))) ho_parm;

val HOT_METIS_TTAC = set_limit GEN_METIS_TTAC hot_parm;

fun HO_METIS_TTAC ths =
  trap (set_limit GEN_METIS_TTAC ho_parm ths) (HOT_METIS_TTAC ths);

(* Higher-order with rules for combinator reductions *)

val full_parm = update_interface (update_combinator (K true)) hot_parm;

val FULL_METIS_TTAC =
  set_limit GEN_METIS_TTAC full_parm (*** o map normalForms.EXT_RULE***);

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

fun FO_METIS_PROVE   ths goal = prove (goal, FO_METIS_TAC   ths);
fun FOT_METIS_PROVE  ths goal = prove (goal, FOT_METIS_TAC  ths);
fun HO_METIS_PROVE   ths goal = prove (goal, HO_METIS_TAC   ths);
fun HOT_METIS_PROVE  ths goal = prove (goal, HOT_METIS_TAC  ths);
fun FULL_METIS_PROVE ths goal = prove (goal, FULL_METIS_TAC ths);

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
    handle HOL_ERR _ =>
      raise mlibUseful.BUG "metisTools.classify" "shouldn't fail";
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

fun METIS_PROVE ths goal = prove (goal, METIS_TAC ths);

end
