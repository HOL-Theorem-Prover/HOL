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
  {restart     : int option,
   clause_parm : mlibClause.parameters,
   set_parm    : mlibClauseset.parameters,
   sos_parm    : mlibSupport.parameters};

val defaults : parameters =
  {restart     = NONE,
   clause_parm = mlibClause.defaults,
   set_parm    = mlibClauseset.defaults,
   sos_parm    = mlibSupport.defaults};

type 'a parmupdate = ('a -> 'a) -> parameters -> parameters;

fun update_restart f (parm : parameters) : parameters =
  let val {restart = r, clause_parm = c, sos_parm = a, set_parm = b} = parm
  in {restart = f r, clause_parm = c, sos_parm = a, set_parm = b}
  end;

fun update_clause_parm f (parm : parameters) : parameters =
  let val {restart = r, clause_parm = c, sos_parm = a, set_parm = b} = parm
  in {restart = r, clause_parm = f c, sos_parm = a, set_parm = b}
  end;

fun update_set_parm f (parm : parameters) : parameters =
  let val {restart = r, clause_parm = c, sos_parm = a, set_parm = b} = parm
  in {restart = r, clause_parm = c, sos_parm = a, set_parm = f b}
  end;

fun update_sos_parm f (parm : parameters) : parameters =
  let val {restart = r, clause_parm = c, sos_parm = a, set_parm = b} = parm
  in {restart = r, clause_parm = c, sos_parm = f a, set_parm = b}
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

datatype resolution = RES of
  {parm : parameters,
   init : mlibClause.clause Intmap.intmap,
   iter : int,
   max  : int option,
   set  : mlibClauseset.clauseset,
   sos  : mlibSupport.sos};

fun update_init i res =
  let val RES {parm = z, init = _, iter = n, max = m, set = b, sos = a} = res
  in RES {parm = z, init = i, iter = n, max = m, set = b, sos = a}
  end;

fun update_iter n res =
  let val RES {parm = z, init = i, iter = _, max = m, set = b, sos = a} = res
  in RES {parm = z, init = i, iter = n, max = m, set = b, sos = a}
  end;

fun update_max m res =
  let val RES {parm = z, init = i, iter = n, max = _, set = b, sos = a} = res
  in RES {parm = z, init = i, iter = n, max = m, set = b, sos = a}
  end;

fun update_set b res =
  let val RES {parm = z, init = i, iter = n, max = m, set = _, sos = a} = res
  in RES {parm = z, init = i, iter = n, max = m, set = b, sos = a}
  end;

fun update_sos a res =
  let val RES {parm = z, init = i, iter = n, max = m, set = b, sos = _} = res
  in RES {parm = z, init = i, iter = n, max = m, set = b, sos = a}
  end;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

type components = {iter : int, set : mlibClauseset.clauseset, sos : mlibSupport.sos};

fun new parm =
  let
    val {restart,clause_parm,sos_parm,set_parm,...} = parm
    val set = mlibClauseset.empty (clause_parm,set_parm)
    val sos = mlibSupport.empty sos_parm
  in
    RES {parm = parm, init = Intmap.empty (), iter = 0,
         max = restart, set = set, sos = sos}
  end;

fun dest (RES {iter,set,sos,...}) = {iter = iter, set = set, sos = sos};

fun overlay {iter,set,sos} res =
  let
    val res = update_iter iter res
    val res = update_set set res
    val res = update_sos sos res
  in
    res
  end;

fun size (RES {set,sos,...}) =
  {used = mlibClauseset.size set, waiting = mlibSupport.size sos,
   rewrites = mlibClause.size (mlibClauseset.rewrites set)};

fun weight res =
  let
    val RES {iter,...} = res
    val {used,waiting,...} = size res
  in 
    iter + used + waiting
  end;

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

fun add cls res =
  let
    val RES {init,...} = res
    val res = update_init (insert cls init) res
  in
    add_init (K 0.0) cls res
  end;

fun check res =
  let val RES {max,...} = res
  in case max of NONE => true | SOME bound => weight res <= bound
  end;

fun calibrate f res =
  let
    val RES {max,...} = res
  in
    case max of NONE => res
    | SOME m => update_max (SOME (f (Int.max (m, weight res)))) res
  end;

fun restart (res as RES {iter = 0, ...}) = res
  | restart res =
  let
    val RES {parm,init,set,sos,...} = res
    val res = update_iter 0 res
    val res = update_set (mlibClauseset.clear set) res
    val res = update_sos (mlibSupport.reset sos) res
    val init = insert (mlibClause.eqns (mlibClauseset.rewrites set)) init
    val cls = map snd (Intmap.listItems init)
  in
    add_init (K 0.0) cls res
  end;

fun recalibrate res =
  if check res then res else restart (calibrate (fn n => 2 * n) res);

local
  fun beef_up set = mlibClauseset.strengthen set o mlibClauseset.simplify set;

  fun max_to_string max =
    "|" ^ (case max of NONE => "*" | SOME m => int_to_string m) ^ "|";

  fun inc_iter res =
    let
      val RES {iter,max,...} = res
      val _ = chatting 1 andalso iter = 0 andalso chat (max_to_string max)
    in
      update_iter (iter + 1) res
    end;

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
      val res = inc_iter res
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
    val set = mlibClauseset.add cl set
    val res = update_set set res
    val cl = mlibClause.FRESH_VARS cl
    val cls = mlibClauseset.deduce set cl
  in
    add_init dist cls res
  end;

val deduce = deduce0 (K ());

fun advance res =
  case select (recalibrate res) of NONE => NONE
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

    fun shove res =
      let
        val {iter,set,sos} = dest res
        val set = mlibClauseset.new_units (!units_ref) set
      in
        overlay {iter = iter, set = set, sos = sos} res
      end

    fun swipe res = units_ref := mlibClauseset.units (#set (dest res))

    fun record infs = record_infs (!slice_ref) infs

    fun f res =
      case select (recalibrate res) of NONE => (swipe res; S.NIL)
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
    fn (parm,initials) => stat (f o add initials o shove) (new parm) ()
  end;

fun resolution' (parm : parameters) =
  mk_solver_node
  {name = "resolution",
   solver_con =
   fn {slice = slice_ref, units = units_ref, thms, hyps} =>
   let
     val initials = map (mlibClause.mk_clause (#clause_parm parm)) (thms @ hyps)
     val _ = chatting 3 andalso chat
      ("resolution--initializing--#initials=" ^
       int_to_string (length initials) ^ ".\n")
     val lift = S.map (Option.map (fn cl => [#thm (mlibClause.dest_clause cl)]))
   in
     fn [False] => lift (resolution_stream slice_ref units_ref (parm,initials))
      | _ => S.NIL
   end};

val resolution = resolution' defaults;

end
