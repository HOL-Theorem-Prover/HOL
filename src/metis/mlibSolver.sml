(* ========================================================================= *)
(* PACKAGING UP SOLVERS TO ALLOW THEM TO COOPERATE UNIFORMLY                 *)
(* Created by Joe Hurd, March 2002                                           *)
(* ========================================================================= *)

(*
app load
 ["mlibUseful", "Mosml", "mlibTerm", "mlibThm", "mlibCanon", "mlibMatch", "mlibMeter", "mlibUnits",
  "mlibSolver"];
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

val () = traces := {module = "mlibSolver", alignment = K 1} :: !traces;

fun chat l m = trace {module = "mlibSolver", message = m, level = l};

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun drop_after f =
  S.foldr (fn (x, xs) => S.CONS (x, if f x then K S.NIL else xs)) S.NIL;

fun time_to_string t =
  let val dp = if t < 10.0 then 2 else if t < 1000.0 then 1 else 0
  in Real.fmt (StringCvt.FIX (SOME dp)) t
  end;

fun infs_to_string i =
  if i < 10000 then int_to_string i
  else if i < 10000000 then int_to_string (i div 1000) ^ "K"
  else int_to_string (i div 1000000) ^ "M";

val name_to_string = str o hd o explode;

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
      if non null (mlibSubsume.subsumes s fms) then (NONE, s)
      else (SOME (SOME ths), mlibSubsume.add (fms |-> ()) s)
    end
    handle ERR_EXN _ => raise BUG "advance" "shouldn't fail";
in
  fun subsumed_filter s g = S.partial_maps advance mlibSubsume.empty (s g);
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
(* Solver nodes must construct themselves from the following form.           *)
(* ------------------------------------------------------------------------- *)

type form =
  {slice : meter ref,                   (* A meter to stop after each slice *)
   units : units ref,                   (* Solvers share a unit cache *)
   thms  : thm list,                    (* Context, assumed consistent *)
   hyps  : thm list};                   (* Hypothesis, no assumptions *)

(* ------------------------------------------------------------------------- *)
(* Solver nodes also incorporate a name.                                     *)
(* ------------------------------------------------------------------------- *)

type node_data = {name : string, solver_con : form -> solver};

datatype solver_node =
  Solver_node of {name : string, initial : string, solver_con : form -> solver};

fun mk_solver_node {name, solver_con} =
  Solver_node
  {name = name, initial = (str o hd o explode) name, solver_con = solver_con};

val pp_solver_node = pp_map (fn Solver_node {name, ...} => name) pp_string;

(* ------------------------------------------------------------------------- *)
(* At each step we schedule a time slice to the least cost solver node.      *)
(* ------------------------------------------------------------------------- *)

val SLICE : limit ref = ref {time = SOME (1.0 / 3.0), infs = NONE};

type cost_fn = mlibMeter.meter_reading -> real;

local
  fun sq x : real = x * x;
in
  val once_only : cost_fn = fn {infs, ...} => if infs = 0 then 0.0 else 1.0e30;
  val time1     : cost_fn = fn {time, ...} => time;
  val time2     : cost_fn = fn {time, ...} => sq time;
  val infs1     : cost_fn = fn {infs, ...} => Real.fromInt infs;
  val infs2     : cost_fn = fn {infs, ...} => sq (Real.fromInt infs);
end;

(* ------------------------------------------------------------------------- *)
(* This allows us to hierarchically arrange solver nodes.                    *)
(* ------------------------------------------------------------------------- *)

local
  fun name (Solver_node {name, ...}) = name;
  fun initial (Solver_node {initial, ...}) = initial;
  fun seq f [] = ""
    | seq f (h :: t) = foldl (fn (n, s) => s ^ "," ^ f n) (f h) t;
in
  fun combine_names csolvers = "[" ^ seq (name o snd) csolvers ^ "]";
  fun combine_initials csolvers = "[" ^ seq (initial o snd) csolvers ^ "]";
end;

datatype subnode = Subnode of
  {name   : string,
   used   : meter_reading,
   cost   : meter_reading -> real,
   solns  : (unit -> thm list option stream) option};

fun init_subnode (cost, (name, solver : solver)) goal =
  Subnode
  {name = name,
   used = zero_reading,
   cost = cost,
   solns = SOME (fn () => solver goal)};

fun least_cost [] = K NONE
  | least_cost _ =
  (SOME o snd o fst o min (fn ((r, _), (s, _)) => Real.compare (r, s)) o
   map (fn (n, Subnode {used, cost, ...}) => (cost used, n)))

val choose_subnode =
  W least_cost o
  List.filter (fn (_, Subnode {solns, ...}) => Option.isSome solns) o
  enumerate 0;

fun subnode_info (Subnode {name, used = {time, infs}, solns, ...}) =
  name_to_string name ^ "(" ^ time_to_string time ^ "," ^
  infs_to_string infs ^ ")" ^ (case solns of NONE => "*" | SOME _ => "");

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
      (chat 2 (stat nodes);
       if not (check ()) then
         (chat 1 "?\n"; S.CONS (NONE, fn () => sched nodes))
       else
         case choose_subnode nodes of NONE => (chat 1 "!\n"; S.NIL)
         | SOME n =>
           let
             val Subnode {name, used, solns, cost} = List.nth (nodes, n)
             val () = chat 1 name
             val seq = (Option.valOf solns) ()
             val r = read ()
             val () = chat 2 ("--t=" ^ time_to_string (#time r) ^ "\n")
             val used = add_readings used r
             val (res, solns) =
               case seq of S.NIL => (NONE, NONE) | S.CONS (a, r) => (a, SOME r)
             val node =
               Subnode {name = name, used = used, cost = cost, solns = solns}
             val nodes = update_nth (K node) n nodes
             val () =
               case res of NONE => ()
               | SOME _ => (chat 2 (stat nodes); chat 1 "#\n")
           in
             S.CONS (res, fn () => sched nodes)
           end)
  in
    sched
  end;

fun combine_solvers (n, i) csolvers {slice, units, thms, hyps} =
  let
    val () = chat 2
      (n ^ "--initializing--#thms=" ^ int_to_string (length thms) ^
       "--#hyps=" ^ int_to_string (length hyps) ^ ".\n")
    val meter = ref (new_meter expired)
    fun f (Solver_node {initial, solver_con, ...}) =
      (initial,
       solver_con {slice = meter, units = units, thms = thms, hyps = hyps})
    val cnodes = map (I ## f) csolvers
    fun check () =
      check_meter (!slice) andalso (meter := sub_meter (!slice) (!SLICE); true)
    fun read () = read_meter (!meter)
    fun stat s = status_info s (!units)
  in
    fn goal => schedule check read stat (map (C init_subnode goal) cnodes)
  end;

fun combine csolvers =
  let
    val n = combine_names csolvers
    val i = combine_initials csolvers
  in
    Solver_node
    {name = n, initial = i, solver_con = combine_solvers (n, i) csolvers}
  end;

(* ------------------------------------------------------------------------- *)
(* Overriding the 'natural' set of support from the problem.                 *)
(* ------------------------------------------------------------------------- *)

fun sos_solver_con filt name solver_con {slice, units, thms, hyps} =
  let
    val () = chat 2
      (name ^ "--initializing--#thms=" ^ int_to_string (length thms) ^
       "--#hyps=" ^ int_to_string (length hyps) ^ ".\n")
    val (hyps', thms') = List.partition filt (thms @ hyps)
  in
    solver_con {slice = slice, units = units, thms = thms', hyps = hyps'}
  end;

fun set_of_support filt (Solver_node {name, initial, solver_con}) =
  let val name' = "!" ^ name
  in
    Solver_node
    {name = name', initial = initial,
     solver_con = sos_solver_con filt name' solver_con}
  end;

val everything : thm -> bool = K true;

val one_negative = (fn x => null x orelse List.exists negative x) o clause;

val one_positive = (fn x => null x orelse List.exists positive x) o clause;

val all_negative = List.all negative o clause;

val all_positive = List.all positive o clause;

val nothing : thm -> bool = K false;

(* ------------------------------------------------------------------------- *)
(* Initializing a solver node makes it ready for action.                     *)
(* ------------------------------------------------------------------------- *)

type init_data = {limit : limit, thms : thm list, hyps : thm list}

fun initialize (Solver_node {solver_con, ...}) {limit, thms, hyps} =
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
