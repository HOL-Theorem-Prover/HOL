(* ========================================================================= *)
(* PACKAGING UP SOLVERS TO ALLOW THEM TO COOPERATE UNIFORMLY                 *)
(* Copyright (c) 2002-2004 Joe Hurd.                                         *)
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

fun drop_after p =
    let
      fun f S.NIL = S.NIL
        | f (S.CONS (x,xs)) = S.CONS (x, if p x then K S.NIL else g xs)
      and g xs () = f (xs ())
    in
      f
    end;

fun time_to_string t =
  let val dp = if t < 9.95 then 1 else 0
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
    (assert (is_contradiction th) (Error "contradiction_solver: thm not |- F");
     fn gs => S.CONS (SOME (contr th gs), K S.NIL));
end;

(* ------------------------------------------------------------------------- *)
(* Filters to cut off searching or drop subsumed solutions.                  *)
(* ------------------------------------------------------------------------- *)

local
  fun concl [] = False
    | concl [lit] = lit
    | concl _ = raise Bug "concl: not a literal";
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
    | munge_lit _ = raise Bug "munge_lit: bad literal";
  fun distinctivize fms = map munge_lit (enumerate 0 fms);
  fun advance NONE s = (SOME NONE, s)
    | advance (SOME ths) s =
    let
      val fms = distinctivize (List.mapPartial (total dest_unit) ths)
    in
      if non S.null (mlibSubsume.subsumes s fms) then (NONE, s)
      else (SOME (SOME ths), mlibSubsume.add (fms |-> ()) s)
    end
    handle Error _ => raise Bug "advance: shouldn't fail";
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

fun find s q = case solve s 1 q of [x] => SOME x | _ => NONE;

fun refute s = Option.map hd (find s [False]);

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

val SLICE : real ref = ref (1.0 / 3.0);

datatype cost_fn = Time of real | Infs of real;

fun calc_cost (Time x) ({time,...} : meter_reading) = time / x
  | calc_cost (Infs x) {infs,...} = Real.fromInt infs / x;

val pp_cost_fn =
  pp_map (fn Time x => "time coeff " ^ real_to_string x
           | Infs x => "infs coeff " ^ real_to_string x) pp_string;

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
  {name  : string,
   used  : meter_reading,
   cost  : cost_fn,
   solns : (unit -> thm list option stream) option};

fun init_subnode (cost, (name, solver : solver)) goal =
  Subnode
  {name = name,
   used = zero_reading,
   cost = cost,
   solns = SOME (fn () => solver goal)};

local
  fun order ((r,_),(s,_)) = Real.compare (r,s);
  fun munge_node (n, Subnode {solns, cost, used, ...}) =
    if Option.isSome solns then SOME (calc_cost cost used, n) else NONE;
in
  fun choose_subnode l =
    case List.mapPartial munge_node (enumerate 0 l) of [] => NONE
    | l => SOME (snd (fst (min order l)))
end;

fun used_to_string {time,infs} =
  "(" ^ real_to_string time ^ "," ^ int_to_string infs ^ ")";

fun subnode_info verbose (Subnode {name, used, solns, ...}) =
  name ^ (if verbose then used_to_string used else time_to_string (#time used))
  ^ (case solns of NONE => "*" | SOME _ => "");

local
  fun seq f [] = ""
    | seq f (h :: t) = foldl (fn (n, s) => s ^ "--" ^ f n) (f h) t;
in
  fun status_info verbose subnodes units =
    "[" ^ seq (subnode_info verbose) subnodes ^ "]--u=" ^ U.info units ^ "--";
end;

fun schedule check slice read stat =
  let
    fun sched nodes =
      (chatting 3 andalso chat (stat false nodes);
       if not (check ()) then
         (chatting 1 andalso chat "?\n"; S.CONS (NONE, fn () => sched nodes))
       else
         case choose_subnode nodes of
           NONE => (chatting 1 andalso chat "!\n"; S.NIL)
         | SOME n =>
           let
             val Subnode {name, used, solns, cost} = List.nth (nodes,n)
             val _ = chatting 1 andalso chat name
             val () = slice cost
             val seq = (Option.valOf solns) ()
             val r = read ()
             val _ = chatting 3 andalso
                     chat ("--t=" ^ time_to_string (#time r) ^ "\n")
             val used = add_readings used r
             val (res, solns) =
               case seq of S.NIL => (NONE, NONE) | S.CONS (a, r) => (a, SOME r)
             val node =
               Subnode {name = name, used = used, cost = cost, solns = solns}
             val nodes = update_nth (K node) n nodes
           in
             if not (Option.isSome res) then sched nodes else
               (chatting 3 andalso chat (stat true nodes);
                chatting 1 andalso chat "#\n";
                S.CONS (res, fn () => sched nodes))
           end)
  in
    sched
  end;

fun combine_solvers n csolvers {slice, units, thms, hyps} =
  let
    val _ = chatting 3 andalso chat
      (n ^ "--initializing--#thms=" ^ int_to_string (length thms)
       ^ "--#hyps=" ^ int_to_string (length hyps) ^ ".\n")
    val meter = ref (new_meter expired)
    fun f (mlibSolver_node {name, solver_con}) =
      (name, solver_con {slice=meter, units=units, thms=thms, hyps=hyps})
    val cnodes = map (I ## f) csolvers
    fun check () = check_meter (!slice)
    fun slce cost =
      meter := sub_meter (!slice)
      (case cost of Time x => {time = SOME (!SLICE * x), infs = NONE}
       | Infs x => {time = NONE, infs = SOME (Real.round (!SLICE * x))})
    fun read () = read_meter (!meter)
    fun stat v s = status_info v s (!units)
  in
    fn goal => schedule check slce read stat (map (C init_subnode goal) cnodes)
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
        val _ = chatting 3 andalso chat
          (name ^ "--initializing--#thms=" ^ int_to_string (length thms) ^
           "--#hyps=" ^ int_to_string (length hyps) ^
           "--apply sos (" ^ sos ^ ").\n")
        val (hyps',thms') =
          if String.isPrefix "?" sos andalso not (null thms) then (hyps,thms)
          else List.partition filter (hyps @ thms)
      in
        solver_con {slice = slice, units = units, thms = thms', hyps = hyps'}
      end
  in
    mlibSolver_node {name = name, solver_con = solver_con'}
  end;

fun only_if_everything {name, filter} : sos_filter =
  {name = "?" ^ name, filter = filter};

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
