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

open mlibUseful mlibTerm mlibMeter mlibSolver;

infix |-> ::> @> oo ## ::* ::@;

structure S = mlibStream; local open mlibStream in end;

type clause = mlibClause.clause;

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

fun clause_to_string cl =
  PP.pp_to_string (!LINE_LENGTH) mlibClause.pp_clause cl;

fun clauses_to_string cls =
  PP.pp_to_string (!LINE_LENGTH) (pp_list mlibClause.pp_clause) cls;

(* ------------------------------------------------------------------------- *)
(* mlibResolution                                                                *)
(* ------------------------------------------------------------------------- *)

type components = {set : mlibClauseset.clauseset, sos : mlibSupport.sos};

datatype resolution = RES of components;

fun update_set b res =
  let val RES {set = _, sos = a} = res
  in RES {set = b, sos = a}
  end;

fun update_sos a res =
  let val RES {set = b, sos = _} = res
  in RES {set = b, sos = a}
  end;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val mk_res = RES;

fun dest_res (RES r) = r;

fun new (parm : parameters) cls =
  let
    val {clause_parm,sos_parm,set_parm,...} = parm
    val set = mlibClauseset.empty (clause_parm,set_parm)
    val (cls,set) = mlibClauseset.initialize cls set
    val set = foldl (fn (c,s) => mlibClauseset.add c s) set cls
    val sos = mlibSupport.empty sos_parm
  in
    RES {set = set, sos = sos}
  end;

fun size (RES {set,sos,...}) =
  {used = mlibClauseset.size set, waiting = mlibSupport.size sos,
   rewrites = mlibClause.size (mlibClauseset.rewrites set)};

fun add_init dist cls res =
  let
    val _ = chatting 2 andalso chat ("-" ^ int_to_string (length cls))
    val RES {set,sos,...} = res
    val (cls,set) = mlibClauseset.initialize cls set
    val _ = chatting 4 andalso
            chat ("\nnew clauses:\n" ^ clauses_to_string cls ^ "\n")
    val infs = length cls
    val _ = chatting 1 andalso chat ("+" ^ int_to_string (length cls))
    val sos = mlibSupport.add (dist infs, cls) sos
    val res = update_set set res
    val res = update_sos sos res
  in
    res
  end;

val add = add_init (K 0.0);

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
      val _ = chatting 2 andalso 0 < n andalso chat ("x" ^ int_to_string n)
    in
      case dcl_sos of NONE => NONE
      | SOME (dcl,sos) => SOME (dcl, update_sos sos res)
    end
end;

fun deduce0 record ((d,cl),res) =
  let
    fun dist infs = (record infs; d + log2 (Real.fromInt (1 + infs)))
    val _ = chatting 4 andalso
            chat ("\ngiven clause:\n" ^ clause_to_string cl ^ "\n")
    val RES {set,...} = res
    val {order_stickiness, ...} = #parm (mlibClause.dest_clause cl)
    val cl = if order_stickiness <= 2 then mlibClause.drop_order cl else cl
    val set = mlibClauseset.add cl set
    val res = update_set set res
    val cl = mlibClause.FRESH_VARS cl
    val cls = mlibClauseset.deduce set cl
  in
    add_init dist cls res
  end;

val deduce = deduce0 (K ());

fun advance res =
  case select res of NONE => NONE
  | SOME dcl_res => SOME (deduce dcl_res);

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
        val _ = chatting 2 andalso chat "["
        val y = f x
        val _ = chatting 2 andalso chat "]"
      in
        y
      end

    fun shove res =
      let
        val {set,sos} = dest_res res
        val set = mlibClauseset.new_units (!units_ref) set
      in
        mk_res {set = set, sos = sos}
      end

    fun swipe res = units_ref := mlibClauseset.units (#set (dest_res res))

    fun record infs = record_infs (!slice_ref) infs

    fun f res =
      case select res of NONE => (swipe res; S.NIL)
      | SOME dcl_res => g dcl_res
    and g (dcl as (_,cl), res) =
      if not (mlibClause.is_empty cl) then h dcl res
      else (swipe res; S.CONS (SOME cl, stat (h dcl o shove) res))
    and h dcl res =
      let
        val res = deduce0 record (dcl,res)
      in
        if check_meter (!slice_ref) then f res
        else (swipe res; S.CONS (NONE, stat (f o shove) res))
      end;
  in
    fn (parm,thms,hyps) => stat f (sq (add hyps) (shove (new parm thms))) ()
  end;

fun mk_thms_hyps cl_parm thms hyps =
  let
    val thms = map (mlibClause.mk_clause cl_parm) thms
    and hyps = map (mlibClause.mk_clause cl_parm) hyps
  in
    if #literal_order cl_parm then ([], hyps @ thms) else
      let val (noneqs,eqs) = List.partition (null o mlibClause.largest_eqs) thms
      in (noneqs, hyps @ eqs)
      end
  end;

fun resolution' (name, parm : parameters) =
  mk_solver_node
  {name = name,
   solver_con =
   fn {slice = slice_ref, units = units_ref, thms, hyps} =>
   let
     val solution_stream =
       S.map (Option.map (wrap o #thm o mlibClause.dest_clause)) o
       resolution_stream slice_ref units_ref
     val (thms,hyps) = mk_thms_hyps (#clause_parm parm) thms hyps
     val _ = chatting 3 andalso chat
       (name ^ "--initializing--#thms=" ^ int_to_string (length thms) ^
        "--#hyps=" ^ int_to_string (length hyps) ^ ".\n")
   in
     fn [False] => solution_stream (parm,thms,hyps)
      | _ => S.NIL
   end};

val resolution = resolution' ("resolution",defaults);

end
