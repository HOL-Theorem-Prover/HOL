(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
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

open mlibUseful mlibTerm mlibMeter mlibSolver;

infix |-> ::> @> oo ## ::* ::@;

structure I = Intset; local open Intset in end;
structure S = mlibStream; local open mlibStream in end;

type clause = mlibClause.clause;
type distance = mlibSupport.distance;

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
  {clause_parm : mlibClause.parameters,
   set_parm    : mlibClauseset.parameters,
   sos_parm    : mlibSupport.parameters};

val defaults : parameters =
  {clause_parm = mlibClause.defaults,
   set_parm    = mlibClauseset.defaults,
   sos_parm    = mlibSupport.defaults};

type 'a parmupdate = ('a -> 'a) -> parameters -> parameters;

fun update_clause_parm f (parm : parameters) : parameters =
  let val {clause_parm = c, sos_parm = a, set_parm = b} = parm
  in {clause_parm = f c, sos_parm = a, set_parm = b}
  end;

fun update_set_parm f (parm : parameters) : parameters =
  let val {clause_parm = c, sos_parm = a, set_parm = b} = parm
  in {clause_parm = c, sos_parm = a, set_parm = f b}
  end;

fun update_sos_parm f (parm : parameters) : parameters =
  let val {clause_parm = c, sos_parm = a, set_parm = b} = parm
  in {clause_parm = c, sos_parm = f a, set_parm = b}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions                                                          *)
(* ------------------------------------------------------------------------- *)

fun ofilt _ NONE = NONE | ofilt p (s as SOME x) = if p x then s else NONE;

local fun ins (c,i) = Intmap.insert (i, #id (mlibClause.dest_clause c), c);
in fun insert cls init = foldl ins init cls;
end;

val thm_to_formula = list_mk_disj o mlibThm.clause;

val clause_id = #id o mlibClause.dest_clause;

fun clause_to_string cl =
  PP.pp_to_string (!LINE_LENGTH) mlibClause.pp_clause cl;

fun clauses_to_string cls =
  PP.pp_to_string (!LINE_LENGTH) (pp_list mlibClause.pp_clause) cls;

(* ------------------------------------------------------------------------- *)
(* mlibResolution                                                                *)
(* ------------------------------------------------------------------------- *)

datatype resolution = RES of {set : mlibClauseset.clauseset, sos : mlibSupport.sos};

fun update_set b res =
  let val RES {set = _, sos = a} = res
  in RES {set = b, sos = a}
  end;

fun update_sos a res =
  let val RES {set = b, sos = _} = res
  in RES {set = b, sos = a}
  end;

fun dest (RES r) = r;

fun size (RES {set,sos,...}) =
  {used = mlibClauseset.size set, waiting = mlibSupport.size sos,
   rewrites = mlibClause.size (mlibClauseset.rewrites set)};

fun units (RES {set,...}) = mlibClauseset.units set;

fun new_units units (res as RES {set,...}) =
  update_set (mlibClauseset.new_units units set) res;

fun mk_axioms thms hyps =
  let
    val thms = map thm_to_formula thms
    and hyps = map thm_to_formula hyps
  in
    if null thms then hyps else thms @ map Not hyps
  end;

fun mk_thms_hyps (clause_parm : mlibClause.parameters) thms hyps =
  let
    val thms = map (mlibClause.mk_clause clause_parm) thms
    and hyps = map (mlibClause.mk_clause clause_parm) hyps
  in
    if #literal_order clause_parm then ([], hyps @ thms) else
      let val (noneqs,eqs) = List.partition (null o mlibClause.largest_eqs) thms
      in (noneqs, hyps @ eqs)
      end
  end;

fun new (parm : parameters, units, thms, hyps) =
  let
    val {clause_parm,sos_parm,set_parm,...} = parm
    val axioms = mk_axioms thms hyps
    val (thms,hyps) = mk_thms_hyps clause_parm thms hyps
    val set = mlibClauseset.empty (clause_parm,set_parm)
    val set = mlibClauseset.new_units units set
    val (thms,set) = mlibClauseset.factor thms set
    val set = foldl (fn (c,s) => mlibClauseset.add c s) set thms
    val (hyps,set) = mlibClauseset.factor hyps set
    val sos = mlibSupport.new sos_parm axioms hyps
  in
    RES {set = set, sos = sos}
  end;

local
  fun beef_up set = mlibClauseset.strengthen set o mlibClauseset.simplify set;

  fun get_clause set sos n =
    case mlibSupport.remove sos of NONE => (n,NONE)
    | SOME (dcl,sos) => check set sos n dcl
  and check set sos n (d,cl) =
    case ofilt (not o mlibClauseset.subsumed set) (beef_up set cl) of
      NONE => get_clause set sos (n + 1)
    | SOME cl => (n, SOME ((d,cl),sos));
in
  fun select res =
    let
      val RES {set,sos,...} = res
      val (n,dcl_sos) = get_clause set sos 0
      val _ = 0 < n andalso chatting 2 andalso chat ("x" ^ int_to_string n)
    in
      case dcl_sos of NONE => NONE
      | SOME ((d,cl),sos) =>
      let
        val res = update_sos sos res
        val {order_stickiness, ...} = #parm (mlibClause.dest_clause cl)
        val cl = if order_stickiness <= 2 then mlibClause.drop_order cl else cl
        val set = mlibClauseset.add cl set
        val res = update_set set res
      in
        SOME ((d,cl),res)
      end
    end;
end;

fun deduce cl res =
  let
    val _ = chatting 4 andalso
            chat ("\ngiven clause:\n" ^ clause_to_string cl ^ "\n")
    val RES {set,...} = res
    val cl = mlibClause.FRESH_VARS cl
    val cls = mlibClauseset.deduce set cl
  in
    cls
  end;

fun factor cls res =
  let
    val RES {set,...} = res
    val (cls,set) = mlibClauseset.factor cls set
    val res = update_set set res
    val _ = chatting 4 andalso
            chat ("\nnew clauses:\n" ^ clauses_to_string cls ^ "\n")
  in
    (cls,res)
  end;

fun add (dist,cls) res =
  let
    val RES {sos,...} = res
    val sos = mlibSupport.add (dist,cls) sos
    val res = update_sos sos res
  in
    res
  end;

fun advance res =
  case select res of NONE => NONE
  | SOME ((d,cl),res) =>
    let
      val cls = deduce cl res
      val (cls,res) = factor cls res
      val res = add (d,cls) res
    in
      SOME res
    end;

fun resolution_to_string res =
  let
    val {used = u, waiting = w, rewrites = r} = size res
  in
    "(" ^ int_to_string u ^ "<-" ^ int_to_string w
    ^ (if r = 0 then "" else "=" ^ int_to_string r) ^ ")"
  end;

val pp_resolution = pp_map resolution_to_string pp_string;

(* ------------------------------------------------------------------------- *)
(* The resolution procedure as a solver_node                                 *)
(* ------------------------------------------------------------------------- *)

fun resolution_stream slice_ref units_ref =
  let
    fun stat func res () =
      (chatting 3 andalso chat (resolution_to_string res); func res)

    fun sq f x =
      let
        val _ = chatting 1 andalso chat "["
        val y = f x
        val _ = chatting 1 andalso chat "]"
      in
        y
      end

    fun shove res = new_units (!units_ref) res

    fun swipe res = units_ref := units res

    fun record infs = record_infs (!slice_ref) infs

    fun f res =
      case select res of NONE => (swipe res; S.NIL)
      | SOME dcl_res => g dcl_res
    and g (dcl as (_,cl), res) =
      if not (mlibClause.is_empty cl) then h dcl res
      else (swipe res; S.CONS (SOME cl, stat (h dcl o shove) res))
    and h (d,cl) res =
      let
        val cls = deduce cl res
        val (cls,res) = factor cls res
        val () = record (length cls + #rewrites (size res))
        val res = add (d,cls) res
      in
        if check_meter (!slice_ref) then f res
        else (swipe res; S.CONS (NONE, stat (f o shove) res))
      end;
  in
    fn (parm,thms,hyps) => stat f (sq new (parm,!units_ref,thms,hyps)) ()
  end;

fun resolution' (name, parm : parameters) =
  mk_solver_node
  {name = name,
   solver_con =
   fn {slice = slice_ref, units = units_ref, thms, hyps} =>
   let
     val _ = chatting 3 andalso chat
       (name ^ "--initializing--#thms=" ^ int_to_string (length thms) ^
        "--#hyps=" ^ int_to_string (length hyps) ^ ".\n")
     val solution_stream =
       S.map (Option.map (sing o #thm o mlibClause.dest_clause)) o
       resolution_stream slice_ref units_ref
   in
     fn [False] => solution_stream (parm,thms,hyps) | _ => S.NIL
   end};

val resolution = resolution' ("resolution",defaults);

end
