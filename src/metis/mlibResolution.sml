(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* Created by Joe Hurd, November 2001                                        *)
(* ========================================================================= *)

(*
app load
 ["Moscow", "mlibUseful", "mlibTerm", "mlibThm", "mlibCanon", "mlibSupport",
  "mlibStream", "mlibSolver", "mlibMeter", "mlibUnits", "mlibClauseset"];
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
structure B = mlibClauseset; local open mlibClauseset in end;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val module = "mlibResolution";
val () = traces := {module = module, alignment = I} :: !traces;
fun chatting l = tracing {module = module, level = l};
fun chat s = (trace s; true)

(* ------------------------------------------------------------------------- *)
(* Parameters.                                                               *)
(* ------------------------------------------------------------------------- *)

type parameters =
  {restart     : int option,
   clause_parm : mlibClause.parameters,
   sos_parm    : mlibSupport.parameters,
   set_parm    : mlibClauseset.parameters};

val defaults : parameters =
  {restart     = NONE,
   clause_parm = mlibClause.defaults,
   sos_parm    = mlibSupport.defaults,
   set_parm    = mlibClauseset.defaults};

type 'a Parmupdate = ('a -> 'a) -> parameters -> parameters;

fun update_restart f (parm : parameters) : parameters =
  let val {restart = r, clause_parm = c, sos_parm = a, set_parm = b} = parm
  in {restart = f r, clause_parm = c, sos_parm = a, set_parm = b}
  end;

fun update_clause_parm f (parm : parameters) : parameters =
  let val {restart = r, clause_parm = c, sos_parm = a, set_parm = b} = parm
  in {restart = r, clause_parm = f c, sos_parm = a, set_parm = b}
  end;

fun update_sos_parm f (parm : parameters) : parameters =
  let val {restart = r, clause_parm = c, sos_parm = a, set_parm = b} = parm
  in {restart = r, clause_parm = c, sos_parm = f a, set_parm = b}
  end;

fun update_set_parm f (parm : parameters) : parameters =
  let val {restart = r, clause_parm = c, sos_parm = a, set_parm = b} = parm
  in {restart = r, clause_parm = c, sos_parm = a, set_parm = f b}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun state_info (sos,used) =
  "(" ^ int_to_string (A.size sos) ^ "," ^ int_to_string (B.size used) ^ ")";

fun ofilt _ NONE = NONE | ofilt p (s as SOME x) = if p x then s else NONE;

(* ------------------------------------------------------------------------- *)
(* An ugly way to get hold of the current state.                             *)
(* ------------------------------------------------------------------------- *)

val current_state = ref (mlibClauseset.empty (mlibClause.defaults,mlibClauseset.defaults));

(* ------------------------------------------------------------------------- *)
(* The resolution procedure as a solver_node.                                *)
(* ------------------------------------------------------------------------- *)

local
  fun comment (n,x) =
    (0 < n andalso chatting 2 andalso chat ("x" ^ int_to_string n); x);
  fun select units used =
    let
      fun remove n sos =
        case A.remove sos of NONE => (n,NONE)
        | SOME (dcl,sos) => check n sos dcl
      and check n sos (d,cl) =
        case ofilt (not o B.subsumed used) (B.strengthen used units cl) of
          NONE => remove (n + 1) sos
        | SOME cl => (n, SOME ((d,cl),(sos,used)))
    in
      remove 0
    end;
in
  fun select_clause units (sos,used) = comment (select units used sos);
end;

fun resolve record units_ref (sos,used) (d,cl) =
  let
    val _ = chatting 4 andalso
            chat ("\ngiven clause:\n" ^ B.id_clause_to_string cl ^ "\n")
    val (cls,used) = B.add used (!units_ref) cl
    val _ = chatting 2 andalso chat ("-" ^ int_to_string (length cls))
    val (cls,used,units) = B.initialize (cls,used,!units_ref)
    val () = units_ref := units
    val infs = length cls
    val _ = chatting 4 andalso
            chat ("\nnew clauses:\n" ^ B.id_clauses_to_string cls ^ "\n")
    val _ = (record infs; chatting 1 andalso chat ("+" ^ int_to_string infs))
    val sos = A.add (d + log2 (Real.fromInt (1 + infs))) cls sos
  in
    (sos,used)
  end;

fun resolution_stream (parm : parameters) slice_ref units_ref inits =
  let
    fun thk func state () =
      (chatting 3 andalso chat (state_info state); func state)
    fun reset N =
      let
        fun f 0 state = S.CONS (NONE, thk (reset (2 * N)) state)
          | f n state = g (n - 1) (select_clause (!units_ref) state)
        and g _ NONE = S.NIL
          | g n (SOME (dcl,state)) =
          case B.empty_id_clause (snd dcl) of NONE => h n (dcl,state)
          | SOME ecl => S.CONS (SOME ecl, thk (h n o pair dcl) state)
        and h n (dcl,state) =
          let
            val state = resolve (record_infs (!slice_ref)) units_ref state dcl
            val () = current_state := snd state
          in
            if check_meter (!slice_ref) then f n state
            else S.CONS (NONE, thk (f n) state)
          end
      in
        fn (sos,used) =>
        let
          val _ = chatting 1 andalso chat
            ("|" ^ (if N < 0 then "*" else int_to_string N) ^ "|")
          val (initials,used) =
            let
              val (rewrs,used) = B.reset used
              val (init_ids,used,units) = B.initialize (inits,used,!units_ref)
              val () = units_ref := units
            in
              (rewrs @ init_ids, used)
            end
          val sos = A.add 0.0 initials (A.reset sos)
          val _ = chatting 4 andalso chat
            ("\nresolution: initials =\n"^B.id_clauses_to_string initials^"\n")
        in
          f N (sos,used)
        end
      end

    val {clause_parm, sos_parm, set_parm, restart, ...} = parm
    val initial_state = (A.empty sos_parm, B.empty (clause_parm,set_parm))
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
     val _ = chatting 3 andalso chat
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

end
