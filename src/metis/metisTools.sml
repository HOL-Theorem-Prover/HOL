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
   1: The equivalent of the Meson: dots
   2: Timing information
   3: More detailed prover information: slice by slice
   4: Log of each step in proof translation
   5: Log of each inference during proof search *)

local
  open mlibUseful;
  val aligned_traces =
    [{module = "mlibSolver",     alignment = fn 1 => 1 | n => n + 1},
     {module = "mlibMeson",      alignment = fn 1 => 1 | n => n + 1},
     {module = "mlibClause",     alignment = fn n => n + 4},
     {module = "mlibResolution", alignment = fn 1 => 1 | n => n + 1},
     {module = "folMapping",  alignment = fn n => n + 3},
     {module = "folTools",    alignment = fn 1 => 2 | n => n + 2},
     {module = "metisTools",  alignment = I},
     {module = "metisLib",    alignment = I}];
in
  val () = register_trace ("metis", tracing, 10);
  val () = tracing := (if !Globals.interactive then 1 else 0);
  val () = traces := aligned_traces;
  fun chat l m = trace {module = "metisTools", message = m, level = l};
  val ERR = mk_HOL_ERR "metisTools";
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

fun update_parm_interface f {interface, solver, limit} =
  {interface = f interface, solver = solver, limit = limit};

fun update_parm_solver f {interface, solver, limit} =
  {interface = interface, solver = f solver, limit = limit};

fun update_parm_limit f {interface, solver, limit} =
  {interface = interface, solver = solver, limit = f limit};

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun contains s =
  let
    fun g [] _ = true | g _ [] = false | g (a::b) (c::d) = a = c andalso g b d
    val k = explode s
    fun f [] = false | f (l as _ :: ys) = g k l orelse f ys
  in
    f o explode
  end;

fun trap f g x =
  f x
  handle e as HOL_ERR {message, ...} =>
    (if not (contains "proof translation error" message) then raise e else
       (chat 1 "metis: proof translation error: trying again with types.\n";
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
      val () = (chat 1 "prolog: "; chat 2 "\n")
      val lmap = build_map (prolog_parm, map FOL_NORM_RULE ths)
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
    val () = (chat 1 "metis solver: "; chat 2 "\n")
    val lmap = build_map (interface, map FOL_NORM_RULE ths)
  in
    FOL_SOLVE (mlibMetis.metis' solver) lmap limit
  end;

(* ------------------------------------------------------------------------- *)
(* Tactic interface to the metis prover.                                     *)
(* ------------------------------------------------------------------------- *)

fun X_METIS_TAC ttac ths goal =
  (chat 1 "metis: "; chat 2 "\n"; FOL_NORM_TTAC ttac ths goal);

fun GEN_METIS_TTAC parm =
  let
    val {interface, solver, limit, ...} : parameters = parm
    fun ttac ths =
      let val lmap = build_map (interface, ths)
      in FOL_TACTIC (mlibMetis.metis' solver) lmap limit
      end
  in
    ttac
  end;

val GEN_METIS_TAC = X_METIS_TAC o GEN_METIS_TTAC;

(* ------------------------------------------------------------------------- *)
(* All the following use this limit.                                         *)
(* ------------------------------------------------------------------------- *)

val limit : limit ref = ref (#limit defaults);

(* ------------------------------------------------------------------------- *)
(* Canned parameters for common situations.                                  *)
(* ------------------------------------------------------------------------- *)

fun inc_limit p = update_parm_limit (K (!limit)) p;
fun set_limit f p t g = f (inc_limit p) t g;

(* First-order *)

val fo_parm =
  update_parm_interface
  (update_parm_mapping (K {higher_order = false, with_types = false}))
  defaults;

val fot_parm =
  update_parm_interface
  (update_parm_mapping (update_parm_with_types (K true))) fo_parm;

val FOT_METIS_TTAC = set_limit GEN_METIS_TTAC fot_parm;

fun FO_METIS_TTAC ths =
  trap (set_limit GEN_METIS_TTAC fo_parm ths) (FOT_METIS_TTAC ths);

(* Higher-order *)

val ho_parm =
  update_parm_interface
  (update_parm_mapping (K {higher_order = true, with_types = false}))
  defaults;

val hot_parm =
  update_parm_interface
  (update_parm_mapping (update_parm_with_types (K true))) ho_parm;

val HOT_METIS_TTAC = set_limit GEN_METIS_TTAC hot_parm;

fun HO_METIS_TTAC ths =
  trap (set_limit GEN_METIS_TTAC ho_parm ths) (HOT_METIS_TTAC ths);

(* Higher-order with rules for combinator reductions *)

val full_parm =
  update_parm_interface (update_parm_combinator (K true)) hot_parm;

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
  fun update s v t =
    (v |-> t) :: List.filter (fn {redex, ...} => redex <> v) s;

  fun bump Full _ = Full
    | bump Higher Full = Full
    | bump Higher _ = Higher
    | bump First cl = cl;

  fun ord cc [] = cc
    | ord (cl, cs) ((s, tm) :: tms) =
    let
      val (f, xs) = strip_comb tm
      val f = subst s f
      val n = length xs
      val tms = map (fn x => (s, x)) xs @ tms
    in
      case List.find (fn (x,_) => x = f) cs of
        NONE => ord (cl, (f, n) :: cs) tms
      | SOME (_, ~1) => ord ((if n = 0 then cl else bump Higher cl), cs) tms
      | SOME (_, n') => ord ((if n = n' then cl else bump Higher cl), cs) tms
    end;

  fun order (cl, _) [] = cl
    | order (cl, cs) ((s, tm) :: tms) =
    if is_exists tm then
      let
        val (v, b) = dest_exists tm
        val g = genvar (type_of v)
      in
        order (cl, cs) ((update s v g, b) :: tms)
      end
    else if is_conj tm then
      let val (a, b) = dest_conj tm
      in order (cl, cs) ((s, a) :: (s, b) :: tms)
      end
    else if is_forall tm then
      let
        val (v, b) = dest_forall tm
        val g = genvar (type_of v)
      in
        order (cl, (g, ~1) :: cs) ((update s v g, b) :: tms)
      end
    else if is_disj tm then
      let val (a, b) = dest_disj tm
      in order (cl, cs) ((s, a) :: (s, b) :: tms)
      end
    else if is_neg tm then
      let val a = dest_neg tm
      in order (cl, cs) ((s, a) :: tms)
      end
    else
      let val cl = if mem (subst s tm, ~1) cs then bump Higher cl else cl
      in order (ord (cl, cs) [(s, tm)]) tms
      end;
in
  fun classify fms =
    order (First, []) (map (fn tm => ([], tm)) fms)
    handle HOL_ERR _ => raise mlibUseful.BUG "metisTools.classify" "shouldn't fail";
end;

fun METIS_TTAC ths =
  let
    val class = classify (map concl ths)
    val () = chat 2 ("metis: a " ^ class_str class ^ " problem.\n")
  in
    class_tac class ths
  end;

val METIS_TAC = X_METIS_TAC METIS_TTAC;

fun METIS_PROVE ths goal = prove (goal, METIS_TAC ths);

(* Quick testing
installPP mlibTerm.pp_subst;
installPP folMapping.pp_term;
installPP folMapping.pp_formula;
installPP folMapping.pp_thm;
show_assums := true;
folMapping.show_types := false;

load "combinTheory";
open combinTheory;

total_limit := Prover1.unlimited;
recent_fol_axioms := SOME [];
!recent_fol_axioms;

val p = mlibUseful.try (METIS_PROVE []) ``?x. x``;

val th =
  MK_COMB (REFL ``$! : ('a->bool)->bool``, ETA_CONV ``\x. (P:'a->bool) x``);
val p = try (METIS_PROVE [th, K_THM]) ``?x. $! x``;

val p = mlibUseful.try (METIS_PROVE [S_DEF, K_DEF]) ``?f. !x. f x = x``;

val p = mlibUseful.try (METIS_PROVE [S_THM, K_THM]) ``?f. !x. f x = x``;

val p = mlibUseful.try (METIS_PROVE [S_THM, K_THM, EQ_EXT]) ``S K S = S K K``;

val p = try (METIS_PROVE [S_THM, K_THM, I_THM]) ``?f. !x. f x = x z``;

val i = METIS_SOLVE [] (([``x:bool``], []), [``x:bool``]);

val i = METIS_SOLVE [th, K_THM] (([``x:'a->bool``], []), [``$! (x:'a->bool)``]);

val i = METIS_SOLVE [S_DEF, K_DEF]
  (([``f:'a->'a``], []), [``f x = (x:'a)``, ``f y = (y:'a)``]);

val i = METIS_SOLVE [S_THM, K_THM]
  (([``f:'a->'a``], []), [``f x = (x:'a)``, ``f y = (y:'a)``]);

val i = try (METIS_SOLVE [S_THM, K_THM, I_THM])
  (([``f:('a->'b)->'b``], []),
   [``f x = (x:'a->'b) z``, ``f y = (y:'a->'b) z``]);

stop;

app load ["pred_setTheory", "arithmeticTheory"];
open pred_setTheory combinTheory arithmeticTheory numTheory listTheory;

val iff_def = new_definition ("<=>", ``$<=> (a : bool) b = (a = b)``);
add_infix ("<=>", 99, HOLgrammars.RIGHT);
Parse.hide "W";
Parse.hide "K";
Parse.hide "S";
Parse.hide "transitive";

total_limit := Prover1.unlimited;

g `p <=> p`;
try e (PURE_REWRITE_TAC [iff_def]);
try e PURE_METIS_TAC;
drop ();

g `((p <=> q) <=> r) <=> (p <=> (q <=> r))`;
try e (PURE_REWRITE_TAC [iff_def]);
try e PURE_METIS_TAC;
drop ();

g `(?x. P(x)) /\ (?x. G(x)) ==>
   ((!x. P(x) ==> H(x)) /\ (!x. G(x) ==> J(x)) <=>
    (!x y. P(x) /\ G(y) ==> H(x) /\ J(y)))`;
try e (PURE_REWRITE_TAC [iff_def]);
try e PURE_METIS_TAC;
drop ();

g `(!M p. sentence(p) ==> holds(M,p) \/ holds(M,not(p))) /\
   (!M p. ~(holds(M,p) /\ holds(M,not(p)))) ==>
   ((!p.
       sentence(p) ==>
       (!M. models(M,S) ==> holds(M,p)) \/
       (!M. models(M,S) ==> holds(M,not(p)))) <=>
    (!M M'.
       models(M,S) /\ models(M',S) ==>
       (!p. sentence(p) ==> (holds(M,p) <=> holds(M',p)))))`;
try e (PURE_REWRITE_TAC [iff_def]);
try e PURE_METIS_TAC;
drop ();

g `{0} SUBSET {0}`;
try e (METIS_TAC [SUBSET_REFL]);
drop ();

g `{0} SUBSET {SUC x; 0}`;
try e (METIS_TAC [SUBSET_REFL, SUBSET_INSERT, IN_SING, NOT_SUC]);
drop ();

g `lives(agatha()) /\ lives(butler()) /\ lives(charles()) /\
   (killed(agatha(),agatha()) \/ killed(butler(),agatha()) \/
    killed(charles(),agatha())) /\
   (!x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\
   (!x. hates(agatha(),x) ==> ~hates(charles(),x)) /\
   (hates(agatha(),agatha()) /\ hates(agatha(),charles())) /\
   (!x. lives(x) /\ ~richer(x,agatha()) ==> hates(butler(),x)) /\
   (!x. hates(agatha(),x) ==> hates(butler(),x)) /\
   (!x. ~hates(x,agatha()) \/ ~hates(x,butler()) \/ ~hates(x,charles()))
   ==>
   killed(agatha(),agatha()) /\ ~killed(butler(),agatha()) /\
   ~killed(charles(),agatha())`;
e PURE_METIS_TAC;
drop ();

g `!x. ?y. !z.
     ((!u. ?v. F'(y, u, v) /\ G(y, u) /\ ~H(y, x)) ==>
      (!u. ?v. F'(x, u, v) /\ G(z, u) /\ ~H(x, z)) ==>
      (!u. ?v. F'(x, u, v) /\ G(y, u) /\ ~H(x, y))) /\
     ((!u. ?v. F'(x, u, v) /\ G(y, u) /\ ~H(x, y)) ==>
      ~(!u. ?v. F'(x, u, v) /\ G(z, u) /\ ~H(x, z)) ==>
      (!u. ?v. F'(y, u, v) /\ G(y, u) /\ ~H(y, x)) /\
      (!u. ?v. F'(z, u, v) /\ G(y, u) /\ ~H(z, y)))`;
e PURE_METIS_TAC;
drop ();

val parse = Term;

fun prove tm =
  (case
     total (try Tactical.prove)
     (tm, PURE_REWRITE_TAC [iff_def] THEN PURE_METIS_TAC) of SOME _
     => "SUCCESSFULLY PROVED:"
   | NONE => "FAILED TO PROVE", tm);

total_limit := {time = SOME 60.0, infs = NONE};

use "../../../sml/metis/data/sample.sml";
use "../../../sml/metis/data/num.sml";

g `P (a,b,c,d,e,f,g,h,i,j) ==>
   ?a' b' c' d' e' f' g' h' i' j'.
   P (a',b',c',d',e',f',g',h',i',j')`;
time e PURE_METIS_TAC;

g `P (a,b,c,d,e,f,g,h,i,j,k) ==>
   ?a' b' c' d' e' f' g' h' i' j' k'.
   P (a',b',c',d',e',f',g',h',i',j',k')`;
time e PURE_METIS_TAC;

g `P (a,b,c,d,e,f,g,h,i,j,k,l) ==>
   ?a' b' c' d' e' f' g' h' i' j' k' l'.
   P (a',b',c',d',e',f',g',h',i',j',k',l')`;
time e PURE_METIS_TAC;

g `P (a,b,c,d,e,f,g,h,i,j,k,l,m) ==>
   ?a' b' c' d' e' f' g' h' i' j' k' l' m'.
   P (a',b',c',d',e',f',g',h',i',j',k',l',m')`;
time e PURE_METIS_TAC;

g `P (a,b,c,d,e,f,g,h,i,j,k,l,m,n) ==>
   ?a' b' c' d' e' f' g' h' i' j' k' l' m' n'.
   P (a',b',c',d',e',f',g',h',i',j',k',l',m',n')`;
time e PURE_METIS_TAC;
(*
Meson search level: ..
runtime: 26.160s,    gctime: 2.930s,     systime: 0.030s.
*)

g `P (a,b,c,d,e,f,g,h,i,j,k,l,m,n,p,q,r,s,t,u,v,w,x,y,z) ==>
   ?a' b' c' d' e' f' g' h' i' j' k' l' m' n' p' q' r' s' t' u' v' w' x' y' z'.
   P (a',b',c',d',e',f',g',h',i',j',k',l',m',n',p',q',r',s',t',u',v',w',x',y',z')`;
time e PURE_METIS_TAC;
*)

end