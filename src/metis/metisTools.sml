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

val parm =
  update_parm_solver
  (mlibMetis.update_parm_delta (K false) o mlibMetis.update_parm_resolution (K false))
  defaults;

val ho_parm =
  update_parm_interface
  (update_parm_mapping
   (update_parm_higher_order (K true) o update_parm_with_types (K true)))
  defaults;

val full_parm =
  update_parm_interface (update_parm_combinator (K true)) ho_parm;

(* ------------------------------------------------------------------------- *)
(* Interface to the metis solver.                                            *)
(* ------------------------------------------------------------------------- *)

fun GEN_METIS_SOLVE parm {thms, hyps} =
  let
    val {interface, solver, limit, ...} : parameters = parm
  in
    FOL_SOLVE (mlibMetis.metis' solver)
    {parm = interface, thms = thms, hyps = hyps, lim = limit}
  end;

(* ------------------------------------------------------------------------- *)
(* Tactic interface to the metis prover.                                     *)
(* ------------------------------------------------------------------------- *)

fun GEN_METIS_TAC parm ths goal =
  let val {interface, solver, limit, ...} : parameters = parm
  in FOL_TAC (mlibMetis.metis' solver, interface, limit) ths goal
  end;

(* ------------------------------------------------------------------------- *)
(* All the following use this limit.                                         *)
(* ------------------------------------------------------------------------- *)

val limit : limit ref = ref (#limit defaults);

(* ------------------------------------------------------------------------- *)
(* Canned parameters for common situations.                                  *)
(* ------------------------------------------------------------------------- *)

fun set_limit f p x y = f (update_parm_limit (K (!limit)) p) x y;

val METIS_TAC      = set_limit GEN_METIS_TAC parm;
val HO_METIS_TAC   = set_limit GEN_METIS_TAC ho_parm;
val FULL_METIS_TAC = set_limit GEN_METIS_TAC full_parm;

(* ------------------------------------------------------------------------- *)
(* Simple user interface to the metis prover.                                *)
(* ------------------------------------------------------------------------- *)

fun METIS_PROVE      ths goal = prove (goal, METIS_TAC      ths);
fun HO_METIS_PROVE   ths goal = prove (goal, HO_METIS_TAC   ths);
fun FULL_METIS_PROVE ths goal = prove (goal, FULL_METIS_TAC ths);

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