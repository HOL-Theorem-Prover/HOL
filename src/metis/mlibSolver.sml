(* ========================================================================= *)
(* PACKAGING UP SOLVERS TO ALLOW THEM TO COOPERATE UNIFORMLY                 *)
(* Created by Joe Hurd, March 2002                                           *)
(* ========================================================================= *)

(*
app load ["mlibUseful", "Mosml", "mlibThm", "mlibCanon", "mlibMatch", "mlibMeter", "mlibUnits"];
*)

(*
*)
structure mlibSolver :> mlibSolver =
struct

open mlibUseful mlibTerm mlibMatch mlibThm mlibMeter;

infix |-> ::> @> oo ##;

structure S = mlibStream; local open mlibStream in end;
structure U = mlibUnits; local open mlibUnits in end;

type 'a stream = 'a S.stream;
type units     = U.units;

val |<>|   = mlibSubst.|<>|;
val op ::> = mlibSubst.::>;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val module = "mlibSolver";
val () = traces := {module = module, alignment = I} :: !traces;
fun chatting l = tracing {module = module, level = l};
fun chat s = (trace s; true)

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun drop_after f =
  S.foldr (fn (x, xs) => S.CONS (x, if f x then K S.NIL else xs)) S.NIL;

fun time_to_string t =
  let val dp = if t < 10.0 then 1 else 0
  in Real.fmt (StringCvt.FIX (SOME dp)) t
  end;

fun infs_to_string i =
  if i < 10000 then int_to_string i
  else if i < 10000000 then int_to_string (i div 1000) ^ "K"
  else int_to_string (i div 1000000) ^ "M";

fun option_case n _ NONE = n
  | option_case _ s (SOME _) = s;

(* ------------------------------------------------------------------------- *)
(* The type of a generic solver.                                             *)
(* ------------------------------------------------------------------------- *)

type solver = formula list -> thm list option stream;

local
  fun contr th [False] = [th]
    | contr th gs = map (C CONTR th) gs;
in
  fun contradiction_solver th =
    (assert (is_contradiction th) (ERR "contradiction_solver" "thm not |- F");
     fn gs => S.CONS (SOME (contr th gs), K S.NIL));
end;

(* ------------------------------------------------------------------------- *)
(* Filters to cut off searching or drop subsumed solutions.                  *)
(* ------------------------------------------------------------------------- *)

local
  fun concl [] = False
    | concl [lit] = lit
    | concl _ = raise BUG "concl" "not a literal";
in
  fun solved_filter solver goals =
    let
      fun solves goals' = can (matchl_literals |<>|) (zip goals' goals)
      fun final NONE = false
        | final (SOME ths) = solves (map (concl o clause) ths)
    in
      drop_after final (solver goals)
    end;
end;

local
  fun munge s n = "MUNGED__" ^ int_to_string n ^ "__" ^ s;
  fun munge_lit (n, Atom (Fn (p, a))) = Atom (Fn (munge p n, a))
    | munge_lit (n, Not (Atom (Fn (p, a)))) = Not (Atom (Fn (munge p n, a)))
    | munge_lit _ = raise BUG "munge_lit" "bad literal";
  fun distinctivize fms = map munge_lit (enumerate 0 fms);    
  fun advance NONE s = (SOME NONE, s)
    | advance (SOME ths) s =
    let
      val fms = distinctivize (List.mapPartial (total dest_unit) ths)
    in
      if non S.null (mlibSubsume.subsumes s fms) then (NONE, s)
      else (SOME (SOME ths), mlibSubsume.add (fms |-> ()) s)
    end
    handle ERR_EXN _ => raise BUG "advance" "shouldn't fail";
in
  fun subsumed_filter s g = S.partial_maps advance (mlibSubsume.empty ()) (s g);
end;

(* ------------------------------------------------------------------------- *)
(* User-friendly interface to generic solvers                                *)
(* ------------------------------------------------------------------------- *)

fun raw_solve s = S.partial_map I o (subsumed_filter (solved_filter s));

local
  fun tk 0 _ = [] | tk n t = stk n (t ())
  and stk _ S.NIL = [] | stk n (S.CONS (h, t)) = h :: tk (n - 1) t;
in
  fun solve s n q = tk n (fn () => raw_solve s q);
end;

fun find s = total unwrap o (solve s 1);

fun refute s = Option.map unwrap (find s [False]);

(* ------------------------------------------------------------------------- *)
(* mlibSolver nodes must construct themselves from the following form.           *)
(* ------------------------------------------------------------------------- *)

type form =
  {slice : meter ref,                   (* A meter to stop after each slice *)
   units : units ref,                   (* mlibSolvers share a unit cache *)
   thms  : thm list,                    (* Context, assumed consistent *)
   hyps  : thm list};                   (* Hypothesis, no assumptions *)

(* ------------------------------------------------------------------------- *)
(* mlibSolver nodes also incorporate a name.                                     *)
(* ------------------------------------------------------------------------- *)

type node_data = {name : string, solver_con : form -> solver};

datatype solver_node = mlibSolver_node of node_data;

val mk_solver_node = mlibSolver_node;

val pp_solver_node = pp_map (fn mlibSolver_node {name, ...} => name) pp_string;

(* ------------------------------------------------------------------------- *)
(* At each step we schedule a time slice to the least cost solver node.      *)
(* ------------------------------------------------------------------------- *)

val SLICE : limit ref = ref {time = SOME (1.0 / 3.0), infs = NONE};

type cost_fn = string * (mlibMeter.meter_reading -> real);

val once_only : cost_fn =
  ("once only",
   fn {infs, ...} => if infs = 0 then 0.0 else ~1.0);

fun time_power n : cost_fn =
  ("time power " ^ Real.toString n,
   fn {time, ...} => Real.abs (Math.pow (time, n)));

fun infs_power n : cost_fn =
  ("infs power " ^ Real.toString n,
   fn {infs, ...} => Real.abs (Math.pow (Real.fromInt infs, n)));

val pp_cost_fn = pp_map fst pp_string;

(* ------------------------------------------------------------------------- *)
(* This allows us to hierarchically arrange solver nodes.                    *)
(* ------------------------------------------------------------------------- *)

local
  fun name (mlibSolver_node {name, ...}) = name;
  fun seq f [] = ""
    | seq f (h :: t) = foldl (fn (n, s) => s ^ "," ^ f n) (f h) t;
in
  fun combine_names csolvers = "[" ^ seq (name o snd) csolvers ^ "]";
end;

datatype subnode = Subnode of
  {name   : string,
   used   : meter_reading,
   cost   : cost_fn,
   solns  : (unit -> thm list option stream) option};

fun init_subnode (cost, (name, solver : solver)) goal =
  Subnode
  {name = name,
   used = zero_reading,
   cost = cost,
   solns = SOME (fn () => solver goal)};

local
  fun order ((r,_),(s,_)) = Real.compare (r,s);
  fun munge_node (n, Subnode {solns, cost = (_,f), used, ...}) =
    case solns of NONE => NONE | SOME _ =>
      let val c = f used in if c < 0.0 then NONE else SOME (c,n) end;
in
  fun choose_subnode l =
    case List.mapPartial munge_node (enumerate 0 l) of [] => NONE
    | l => SOME (snd (fst (min order l)))
end;

fun subnode_info (Subnode {name, used = {time,infs}, solns, ...}) =
  name ^ (* "(" ^ *) time_to_string time ^ (* ^ "," ^ infs_to_string infs *)
  (* ")" ^ *) (case solns of NONE => "*" | SOME _ => "");

local
  fun seq f [] = ""
    | seq f (h :: t) = foldl (fn (n, s) => s ^ "--" ^ f n) (f h) t;
in
  fun status_info subnodes units =
    "[" ^ seq subnode_info subnodes ^ "]--u=" ^ U.info units ^ "--";
end;

fun schedule check read stat =
  let
    fun sched nodes =
      (chatting 2 andalso chat (stat nodes);
       if not (check ()) then
         (chatting 1 andalso chat "?\n"; S.CONS (NONE, fn () => sched nodes))
       else
         case choose_subnode nodes of
           NONE => (chatting 1 andalso chat "!\n"; S.NIL)
         | SOME n =>
           let
             val Subnode {name, used, solns, cost} = List.nth (nodes, n)
             val _ = chatting 1 andalso chat name
             val seq = (Option.valOf solns) ()
             val r = read ()
             val _ = chatting 2 andalso
                     chat ("--t=" ^ time_to_string (#time r) ^ "\n")
             val used = add_readings used r
             val (res, solns) =
               case seq of S.NIL => (NONE, NONE) | S.CONS (a, r) => (a, SOME r)
             val node =
               Subnode {name = name, used = used, cost = cost, solns = solns}
             val nodes = update_nth (K node) n nodes
             val _ =
               Option.isSome res andalso
               (chatting 2 andalso chat (stat nodes);
                chatting 1 andalso chat "#\n")
           in
             S.CONS (res, fn () => sched nodes)
           end)
  in
    sched
  end;

fun combine_solvers n csolvers {slice, units, thms, hyps} =
  let
    val _ = chatting 2 andalso chat
      (n ^ "--initializing--#thms=" ^ int_to_string (length thms)
       ^ "--#hyps=" ^ int_to_string (length hyps) ^ ".\n")
    val meter = ref (new_meter expired)
    fun f (mlibSolver_node {name, solver_con}) =
      (name, solver_con {slice=meter, units=units, thms=thms, hyps=hyps})
    val cnodes = map (I ## f) csolvers
    fun check () =
      check_meter (!slice) andalso (meter := sub_meter (!slice) (!SLICE); true)
    fun read () = read_meter (!meter)
    fun stat s = status_info s (!units)
  in
    fn goal => schedule check read stat (map (C init_subnode goal) cnodes)
  end;

fun combine csolvers =
  let val n = combine_names csolvers
  in mlibSolver_node {name = n, solver_con = combine_solvers n csolvers}
  end;

(* ------------------------------------------------------------------------- *)
(* Overriding the 'natural' set of support from the problem.                 *)
(* ------------------------------------------------------------------------- *)

type sos_filter = {name : string, filter : thm -> bool};

fun apply_sos_filter {name = sos, filter} (mlibSolver_node {name, solver_con}) =
  let
    fun solver_con' {slice, units, thms, hyps} =
      let
        val _ = chatting 2 andalso chat
          (name ^ "--initializing--#thms=" ^ int_to_string (length thms) ^
           "--#hyps=" ^ int_to_string (length hyps) ^
           "--apply sos (" ^ sos ^ ").\n")
        val (hyps', thms') = List.partition filter (thms @ hyps)
      in
        solver_con {slice = slice, units = units, thms = thms', hyps = hyps'}
      end
  in
    mlibSolver_node {name = name, solver_con = solver_con'}
  end;

val everything : sos_filter = {name = "everything", filter = K true};

val one_negative : sos_filter =
  {name = "one negative",
   filter = (fn x => null x orelse List.exists negative x) o clause};

val one_positive : sos_filter =
  {name = "one positive",
   filter = (fn x => null x orelse List.exists positive x) o clause};

val all_negative : sos_filter =
  {name = "all negative", filter = List.all negative o clause};

val all_positive : sos_filter =
  {name = "all positive", filter = List.all positive o clause};

(* ------------------------------------------------------------------------- *)
(* Initializing a solver node makes it ready for action.                     *)
(* ------------------------------------------------------------------------- *)

type init_data = {limit : limit, thms : thm list, hyps : thm list}

fun initialize (mlibSolver_node {solver_con, ...}) {limit, thms, hyps} =
  case List.find is_contradiction (thms @ hyps) of SOME th
    => contradiction_solver th
  | NONE =>
    let
      val meter = ref (new_meter expired)
      val units = ref U.empty
      val solver =
        solver_con {slice = meter, units = units, thms = thms, hyps = hyps}
    in
      fn g =>
      let val () = meter := new_meter limit
      in drop_after (fn _ => not (check_meter (!meter))) (solver g)
      end
    end;

end
