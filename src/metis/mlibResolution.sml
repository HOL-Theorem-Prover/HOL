(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* Created by Joe Hurd, November 2001                                        *)
(* ========================================================================= *)

(*
app load
 ["mlibUseful", "Mosml", "mlibTerm", "mlibThm", "mlibCanon", "mlibTheap",
  "mlibStream", "mlibSolver", "mlibMeter", "mlibUnits", "mlibResolvers"];
*)

(*
*)
structure mlibResolution :> mlibResolution =
struct

open mlibUseful mlibTerm mlibThm mlibCanon mlibMeter mlibSolver mlibResolvers mlibTheap;

infix |-> ::> @> oo ## ::* ::@;

structure S = mlibStream; local open mlibStream in end;
structure U = mlibUnits; local open mlibUnits in end;

type 'a subsume = 'a mlibSubsume.subsume;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val () = traces := {module = "mlibResolution", alignment = K 1} :: !traces;

fun chat l m = trace {module = "mlibResolution", message = m, level = l};

(* ------------------------------------------------------------------------- *)
(* Tuning parameters.                                                        *)
(* ------------------------------------------------------------------------- *)

type parameters =
  {subsumption_checking : int,          (* in the range 0..3 *)
   positive_refinement  : bool,
   theap_parm           : mlibTheap.parameters}

val defaults =
  {subsumption_checking = 1,
   positive_refinement  = true,
   theap_parm           = mlibTheap.defaults};

(* ------------------------------------------------------------------------- *)
(* Clause stores.                                                            *)
(* ------------------------------------------------------------------------- *)

type store = thm subsume * resolvers;

val empty_store : store = (mlibSubsume.empty, empty_resolvers);

fun store_add th (s, r) =
  (mlibSubsume.add (clause th |-> th) s, add_resolver th r);

fun store_resolvants ((_, r) : store) = find_resolvants r;

fun store_subsumed ((s, _) : store) = mlibSubsume.subsumed s o clause;

fun store_info (s, r) = "(" ^ mlibSubsume.info s ^ "," ^ resolvers_info r ^ ")";

(* ------------------------------------------------------------------------- *)
(* Positive refinement.                                                      *)
(* ------------------------------------------------------------------------- *)

local
  val pos_th = List.all positive o clause;

  fun check true = K true
    | check false = fn ({mate, ...} : resolvant) => pos_th mate;
in
  fun positive_check false = K (K true)
    | positive_check true = check o pos_th;
end;

(* ------------------------------------------------------------------------- *)
(* Full resolution procedure.                                                *)
(* ------------------------------------------------------------------------- *)

exception Contradiction of thm;

fun unit_strengthen units th =
  (case first (U.subsumes units) (clause th) of SOME th => th
   | NONE => U.demod units th);

fun subsumption_check store th =
  case store_subsumed store th of [] => SOME th | _ :: _ => NONE;

fun theap_strengthen theap th =
  (case mlibSubsume.strictly_subsumed (theap_subsumers theap) (clause th) of []
     => th
   | (_, th) :: _ => th);

fun resolve (parm : parameters) =
  let
    fun feedback k r =
      int_to_string k ^ (if k = r then "" else "/" ^ int_to_string r)

    fun L n = n <= #subsumption_checking parm
    val pos_filt = Option.filter o positive_check (#positive_refinement parm)

    fun ftest b f = if b then Option.mapPartial (subsumption_check f) else I
    fun stest b s = if b then subsumption_check s else SOME
    fun wpass b w = if b then theap_strengthen w else I
    fun upass u = unit_strengthen u

    fun next_candidate u f s w =
      case theap_remove w of NONE => NONE
      | SOME (th, w) =>
        (case (ftest (L 1) f o stest (L 1) s o wpass (L 2) w o upass u) th of
           NONE => next_candidate u f s w
         | SOME th => SOME (th, w))

    fun retention_test u f s th =
      List.mapPartial
      (Option.mapPartial (ftest (L 3) f o stest (L 3) s o upass u o #res) o
       pos_filt th)

    fun check_add th =
      if is_contradiction th then raise Contradiction th else U.add th
  in
    fn record => fn (facts, used, unused) => fn units =>
    (case next_candidate units facts used unused of NONE => NONE
     | SOME (th, unused) =>
       let
         val units = check_add th units
         val used = store_add th used
         val th = FRESH_VARS th
         val resolvants =
           store_resolvants facts th @ store_resolvants used th
         val () = record (length resolvants)
         val units = foldl (uncurry check_add) units (map #res resolvants)
         val keep = retention_test units facts used th resolvants
         val () = chat 2 (feedback (length keep) (length resolvants))
         val unused = theap_addl keep unused
       in
         SOME ((facts, used, unused), units)
       end)
       handle ERR_EXN _ => raise BUG "resolve" "shouldn't fail"
  end;

fun raw_resolution parm =
  mk_solver_node
  {name = "resolution",
   solver_con =
   fn {slice, units, thms, hyps} =>
   let
     val resolve' = resolve parm
     fun run wrap state =
       if not (check_meter (!slice)) then S.CONS (NONE, wrap state)
       else
         (chat 1 "+";
          case resolve' (record_infs (!slice)) state (!units) of NONE => S.NIL
          | SOME (state, units') => (units := units'; run wrap state))
     fun wrapper g (a as (_, _, w)) () =
       (chat 2 (theap_info w); run (wrapper g) a)
       handle Contradiction th => contradiction_solver th g
     val facts = foldl (fn (t, l) => store_add t l) empty_store thms
     val used = empty_store
     val unused = theap_addl hyps (new_theap (#theap_parm parm))
     val () = chat 2
       ("resolution--initializing--#thms=" ^ int_to_string (length thms) ^
        "--#hyps=" ^ int_to_string (length hyps) ^
        "--facts=" ^ store_info facts ^
        "--unused=" ^ theap_info unused ^ ".\n")
   in
     fn goals => wrapper goals (facts, used, unused) ()
   end};

fun resolution' parm =
  (if #positive_refinement parm then set_of_support everything else I)
  (raw_resolution parm);

val resolution = resolution' defaults;

(* quick testing
load "UNLINK";
open UNLINK;
val time = Mosml.time;
quotation := true;
installPP pp_term;
installPP pp_formula;
installPP mlibSubst.pp_subst;
installPP pp_thm;

(* Testing the resolution prover *)

val limit : limit ref = ref {infs = NONE, time = SOME 30.0};
fun resolution_prove g =
  try (time refute)
  (initialize (set_of_support all_negative resolution)
   {limit = !limit, thms = [], hyps = axiomatize (Not (generalize g))});

axiomatize (Not (generalize True));
resolution_prove True;

val prop13 = parse_formula (get nonequality "PROP_13");
axiomatize (Not (generalize prop13));
resolution_prove prop13;

val p33 = parse_formula (get nonequality "P33");
axiomatize (Not (generalize p33));
resolution_prove p33;

val p59 = parse_formula (get nonequality "P59");
val ths = axiomatize (Not (generalize p59));
resolution_prove p59;

val p39 = parse_formula (get nonequality "P39");
clausal (Not (generalize p39));
axiomatize (Not (generalize p39));
resolution_prove p39;

val num14 = parse_formula (get tptp "NUM014-1");
resolution_prove num14;

val p55 = parse_formula (get nonequality "P55");
resolution_prove p55;

val p26 = parse_formula (get nonequality "P26");
clausal (Not (generalize p26));
resolution_prove p26;

val los = parse_formula (get nonequality "LOS");
resolution_prove los;

val reduced_num284 = parse_formula
  `fibonacci 0 (s 0) /\ fibonacci (s 0) (s 0) /\
   (!x y z x' y' z'.
      ~sum x (s (s 0)) z \/ ~sum y (s 0) z \/
      ~fibonacci x x' \/ ~fibonacci y y' \/ ~sum x' y' z' \/
      fibonacci z z') /\ (!x. sum x 0 x) /\
   (!x y z. ~sum x y z \/ sum x (s y) (s z)) /\
   (!x. ~fibonacci (s (s (s (s (s (s (s (s 0)))))))) x) ==> F`;
resolution_prove reduced_num284;

val p29 = parse_formula (get nonequality "P29");
clausal (Not (generalize p29));
resolution_prove p29;

val num1 = parse_formula (get tptp "NUM001-1");
resolution_prove num1;

val gilmore9 = parse_formula (get nonequality "GILMORE_9");
axiomatize (Not (generalize gilmore9));
resolution_prove gilmore9;

val model_completeness = parse_formula (get nonequality "MODEL_COMPLETENESS");
resolution_prove model_completeness;
*)

end
