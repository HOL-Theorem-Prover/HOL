(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* Created by Joe Hurd, November 2001                                        *)
(* ========================================================================= *)

(*
app load
 ["Moscow", "mlibUseful", "mlibTerm", "mlibThm", "mlibCanon", "mlibSupport",
  "mlibStream", "mlibSolver", "mlibMeter", "mlibUnits", "mlibClauseset1"];
*)

(*
*)
structure mlibResolution :> mlibResolution =
struct

open mlibUseful mlibTerm mlibMatch mlibMeter mlibSolver mlibClause;

infix |-> ::> @> oo ## ::* ::@;

structure O = Option; local open Option in end;
structure S = mlibStream; local open mlibStream in end;
structure U = mlibUnits; local open mlibUnits in end;
structure A = mlibSupport; local open mlibSupport in end;
structure B = mlibClauseset1; local open mlibClauseset1 in end;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val () = traces := {module = "mlibResolution", alignment = I} :: !traces;

fun chat l m = trace {module = "mlibResolution", message = m, level = l};

(* ------------------------------------------------------------------------- *)
(* Parameters.                                                               *)
(* ------------------------------------------------------------------------- *)

type parameters =
  {restart     : int option,
   clause_parm : mlibClause.parameters,
   sos_parm    : mlibSupport.parameters};

val defaults : parameters =
  {restart     = NONE,
   clause_parm = mlibClause.defaults,
   sos_parm    = mlibSupport.defaults};

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun state_info (sos, used) =
  "(" ^ int_to_string (A.size sos) ^ "," ^ int_to_string (B.size used) ^ ")";

fun add_unit units cl =
  case total clause_thm cl of NONE => ()
  | SOME th => if mlibThm.is_unit th then units := U.add th (!units) else ();

(* ------------------------------------------------------------------------- *)
(* Resolution procedure.                                                     *)
(* ------------------------------------------------------------------------- *)

local
  fun comment (n,x) = (if n = 0 then () else chat 1 (int_to_string n ^ "x"); x);
  fun select units used =
    let
      fun remove n sos =
        case A.remove sos of NONE => (n, NONE)
        | SOME (cl, sos) => check n sos (demodulate units (B.simplify used cl))
      and check n sos cl =
        if B.subsumed used cl then remove (n + 1) sos
        else (n, SOME (cl, (sos, used)))
    in
      remove 0
    end;
in
  fun select_clause units (sos, used) = comment (select units used sos);
end;

fun resolve record units_ref (sos, used) cl =
  let
    val () = chat 3 ("\ngiven clause:\n" ^ clause_to_string cl ^ "\n")
    val () = add_unit units_ref cl
    val used = B.add cl used
    val units = !units_ref
    val cl = FRESH_VARS cl
    val cls = B.deduce used units cl
    val () = app (add_unit units_ref) cls
    val infs = length cls
    val () = chat 3 (foldl (fn (h,t) => t ^ clause_to_string h ^ "\n")
                     "\nnew clauses:\n" cls)
    val () = (record infs; chat 1 (int_to_string infs ^ "+"))
    val sos = A.addl cls sos
  in
    (sos, used)
  end;

fun resolution_stream (parm : parameters) slice_ref units_ref initials =
  let
    fun thk func state () = (chat 2 (state_info state); func state)
    fun reset N =
      let
        fun f 0 state = S.CONS (NONE, thk (reset (2 * N)) state)
          | f n state = g (n - 1) (select_clause (!units_ref) state)
        and g _ NONE = S.NIL
          | g n (SOME (cl, state)) =
          if not (null (clause_lits cl)) then h n (cl, state)
          else S.CONS (SOME cl, thk (h n o pair cl) state)
        and h n (cl, state) =
          let
            val state = resolve (record_infs (!slice_ref)) units_ref state cl
          in
            if check_meter (!slice_ref) then f n state
            else S.CONS (NONE, thk (f n) state)
          end
      in
        fn (sos, used) =>
        let
          val () = chat 1 ("|" ^ (if N < 0 then "*" else int_to_string N) ^ "|")
          val used = B.reset used
          val initials = B.initialize used (!units_ref) initials
          val () = chat 3
            ("\nresolution': initials =\n" ^
             PP.pp_to_string 60 (pp_list pp_clause) initials ^ "\n")
          val sos = A.addl initials (A.reset sos)
        in
          f N (sos, used)
        end
      end

    val {sos_parm, restart, ...} = parm
    val initial_state = (A.new sos_parm, B.empty)
  in
    thk (reset (case restart of SOME n => n | NONE => ~1)) initial_state ()
  end;

fun lift_f cl = [clause_thm cl];

fun lift_g g cl =
  let
    val gs = map (pair g) (interval 0 (length g))
    val ths = map (clause_thm o C dest_coherents cl o wrap) gs
  in
    case List.find mlibThm.is_contradiction ths of NONE => ths
    | SOME th => map (fn l => mlibThm.CONTR l th) g
  end;

fun resolution' (parm : parameters) =
  mk_solver_node
  {name = "resolution",
   solver_con =
   fn {slice = slice_ref, units = units_ref, thms, hyps} =>
   let
     val {clause_parm, ...} = parm
     fun stream f i =
       S.map (O.map f) (resolution_stream parm slice_ref units_ref i)
     val initials = map (NEQ_SIMP o mk_clause clause_parm) (thms @ hyps)
     val () = app (add_unit units_ref) initials
     val initials = map (demodulate (!units_ref)) initials
     val () = chat 2
      ("resolution--initializing--#initials=" ^
       int_to_string (length initials) ^ ".\n")
   in
     fn [False] => stream lift_f initials
      | g =>
        let val c = map negate g
        in stream (lift_g c) (mk_coherent clause_parm c :: initials)
        end
   end};

val resolution = resolution' defaults;

(* quick testing
load "UNLINK";
open mlibCanon UNLINK;
val time = Moscow.time;
quotation := true;

installPP pp_term;
installPP pp_formula;
installPP mlibSubst.pp_subst;
installPP mlibThm.pp_thm;
fun initialize x y = try (fn (a,b) => mlibSolver.initialize a b) (x,y);
fun refute x = try (time mlibSolver.refute) x;

(* Testing the resolution prover *)

val limit : limit ref = ref {infs = NONE, time = NONE};
fun resolution_prove g = (fn x => refute o initialize x)
  (resolution'
   {restart     = NONE,
    clause_parm = {literal_order = true,
                   term_order = true,
                   tracking = false},
    sos_parm    = {size_bias = 100}})
  {limit = !limit, thms = [],
   hyps = eq_axiomatize' (Not (generalize g))};

val attack = map (fn {name, goal} => (print ("\n\n" ^ name ^ "\n"); let val th = resolution_prove (parse_formula goal) val () = print ("\n" ^ mlibThm.proof_to_string (mlibThm.proof (Option.valOf th))) in th end));

(*
*)
val avoided = ["P34", "P38", "GILMORE_9"];
fun avoid set =
  List.filter (fn ({name, ...} : 'a problem) => not (mem name avoided)) set;
try attack (avoid equality);
attack (avoid nonequality);

val judita3 = parse_formula (get equality "JUDITA_3");
eq_axiomatize' (Not (generalize judita3));
resolution_prove judita3;

val p49' = parse_formula
  `p a /\ p b /\ ~(a = b) /\ ~p c /\ (!x. x = d \/ x = e) ==> F`;
eq_axiomatize' (Not (generalize p49'));
resolution_prove p49';

val p49 = parse_formula (get equality "P49");
eq_axiomatize' (Not (generalize p49));
resolution_prove p49;

val agatha = parse_formula (get equality "AGATHA");
val Imp (h, And (c1, And (c2, c3))) = agatha;
val agatha1 = Imp (h, c1);
val agatha2 = Imp (h, c2);
val agatha3 = Imp (h, c3);
resolution_prove agatha1;
resolution_prove agatha2;
resolution_prove agatha3;
resolution_prove agatha;

val p51 = parse_formula (get equality "P51");
resolution_prove p51;

stop;

axiomatize (Not (generalize True));
resolution_prove True;

val p_or_not_p = parse_formula (get nonequality "P_or_not_P");
axiomatize (Not (generalize p_or_not_p));
resolution_prove p_or_not_p;

val prop13 = parse_formula (get nonequality "PROP_13");
(*axiomatize (Not (generalize prop13));*)
resolution_prove prop13;

val p33 = parse_formula (get nonequality "P33");
(*axiomatize (Not (generalize p33));*)
resolution_prove p33;

val p59 = parse_formula (get nonequality "P59");
(*axiomatize (Not (generalize p59));*)
resolution_prove p59;

val p39 = parse_formula (get nonequality "P39");
(*clausal (Not (generalize p39));*)
(*axiomatize (Not (generalize p39));*)
resolution_prove p39;

val num14 = parse_formula (get tptp "NUM014-1");
resolution_prove num14;

val p55 = parse_formula (get nonequality "P55");
resolution_prove p55;

val p26 = parse_formula (get nonequality "P26");
(*clausal (Not (generalize p26));*)
resolution_prove p26;

val los = parse_formula (get nonequality "LOS");
resolution_prove los;

val lcl107 = parse_formula (get tptp "LCL107-1");
resolution_prove lcl107;

val steamroller = parse_formula (get nonequality "STEAM_ROLLER");
resolution_prove steamroller;

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
(*clausal (Not (generalize p29));*)
resolution_prove p29;

val num1 = parse_formula (get tptp "NUM001-1");
resolution_prove num1;

val gilmore9 = parse_formula (get nonequality "GILMORE_9");
(*axiomatize (Not (generalize gilmore9));*)
resolution_prove gilmore9;

val model_completeness = parse_formula (get nonequality "MODEL_COMPLETENESS");
resolution_prove model_completeness;
*)

end
