(* ========================================================================= *)
(* THE MESON PROOF PROCEDURE                                                 *)
(* Created by Joe Hurd, November 2001                                        *)
(* Partly ported from the CAML-Light code accompanying John Harrison's book  *)
(* ========================================================================= *)

(*
app load
 ["mlibUseful", "mlibStream", "Mosml", "mlibTerm", "mlibThm", "mlibCanon", "mlibMatch",
  "mlibSolver", "mlibMeter", "mlibUnits"];
*)

(*
*)
structure mlibMeson :> mlibMeson =
struct

open mlibUseful mlibTerm mlibMatch mlibThm mlibCanon mlibMeter mlibSolver;

infix |-> ::> @> oo ##;

structure S = mlibStream; local open mlibStream in end;
structure N = mlibLiteralnet; local open mlibLiteralnet in end;
structure U = mlibUnits; local open mlibUnits in end;

val |<>|          = mlibSubst.|<>|;
val op ::>        = mlibSubst.::>;
val formula_subst = mlibSubst.formula_subst;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val module = "mlibMeson";
val () = traces := {module = module, alignment = I} :: !traces;
fun chatting l = tracing {module = module, level = l};
fun chat s = (trace s; true)

(* ------------------------------------------------------------------------- *)
(* Tuning parameters.                                                        *)
(* ------------------------------------------------------------------------- *)

type parameters =
  {ancestor_pruning : bool,
   ancestor_cutting : bool,
   state_simplify   : bool,
   cache_cutting    : bool,
   divide_conquer   : bool,
   unit_lemmaizing  : bool};

val defaults = 
  {ancestor_pruning = true,
   ancestor_cutting = true,
   state_simplify   = true,
   cache_cutting    = false,
   divide_conquer   = false,
   unit_lemmaizing  = true};

type 'a Parmupdate = ('a -> 'a) -> parameters -> parameters

fun update_ancestor_pruning f (parm : parameters) : parameters =
  let
    val {ancestor_pruning = a, ancestor_cutting = b, state_simplify = s,
         cache_cutting = c, divide_conquer = d, unit_lemmaizing = u} = parm
  in
    {ancestor_pruning = f a, ancestor_cutting = b, state_simplify = s,
     cache_cutting = c, divide_conquer = d, unit_lemmaizing = u}
  end;

fun update_ancestor_cutting f (parm : parameters) : parameters =
  let
    val {ancestor_pruning = a, ancestor_cutting = b, state_simplify = s,
         cache_cutting = c, divide_conquer = d, unit_lemmaizing = u} = parm
  in
    {ancestor_pruning = a, ancestor_cutting = f b, state_simplify = s,
     cache_cutting = c, divide_conquer = d, unit_lemmaizing = u}
  end;

fun update_state_simplify f (parm : parameters) : parameters =
  let
    val {ancestor_pruning = a, ancestor_cutting = b, state_simplify = s,
         cache_cutting = c, divide_conquer = d, unit_lemmaizing = u} = parm
  in
    {ancestor_pruning = a, ancestor_cutting = b, state_simplify = f s,
     cache_cutting = c, divide_conquer = d, unit_lemmaizing = u}
  end;

fun update_cache_cutting f (parm : parameters) : parameters =
  let
    val {ancestor_pruning = a, ancestor_cutting = b, state_simplify = s,
         cache_cutting = c, divide_conquer = d, unit_lemmaizing = u} = parm
  in
    {ancestor_pruning = a, ancestor_cutting = b, state_simplify = s,
     cache_cutting = f c, divide_conquer = d, unit_lemmaizing = u}
  end;

fun update_divide_conquer f (parm : parameters) : parameters =
  let
    val {ancestor_pruning = a, ancestor_cutting = b, state_simplify = s,
         cache_cutting = c, divide_conquer = d, unit_lemmaizing = u} = parm
  in
    {ancestor_pruning = a, ancestor_cutting = b, state_simplify = s,
     cache_cutting = c, divide_conquer = f d, unit_lemmaizing = u}
  end;

fun update_unit_lemmaizing f (parm : parameters) : parameters =
  let
    val {ancestor_pruning = a, ancestor_cutting = b, state_simplify = s,
         cache_cutting = c, divide_conquer = d, unit_lemmaizing = u} = parm
  in
    {ancestor_pruning = a, ancestor_cutting = b, state_simplify = s,
     cache_cutting = c, divide_conquer = d, unit_lemmaizing = f u}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun halves n = let val n1 = n div 2 in (n1, n - n1) end;

fun splittable [] = false
  | splittable [_] = false
  | splittable _ = true;

local
  val prefix = "_m";
in
  val mk_mvar      = mk_prefix prefix o int_to_string;
  fun mk_mvars n i = map (Var o mk_mvar) (interval n i);
  val dest_mvar    = string_to_int o dest_prefix prefix;
end;

datatype 'a choice = CHOICE of unit -> 'a * 'a choice;

fun dest_choice (CHOICE c) = c;

val no_choice = (fn () => raise ERR "no_choice" "always fails");

fun binary_choice f g =
  (fn () =>
   let val (a, c) = f () in (a, CHOICE (binary_choice (dest_choice c) g)) end
   handle ERR_EXN _ => g ());

fun first_choice [] = no_choice
  | first_choice [f] = f
  | first_choice (f :: fs) = binary_choice f (first_choice fs);

fun choice_stream f =
  let val (a, CHOICE c) = f () in S.CONS (a, fn () => choice_stream c) end
  handle ERR_EXN _ => S.NIL;

fun swivel m n l =
  let
    val (l1, l') = split l m
    val (l2, l3) = split l' n
  in
    l2 @ l1 @ l3
  end;

fun thm_proves th False = is_contradiction th
  | thm_proves th goal =
  case clause th of [lit] => lit = goal | [] => true | _ => false;

fun filter_meter meter =
  S.filter (fn a => Option.isSome a orelse not (check_meter (!meter)));

(* ------------------------------------------------------------------------- *)
(* Compiling the rule set used by meson.                                     *)
(* ------------------------------------------------------------------------- *)

type rule = {asms : formula list, c : formula, thm : thm, asmn : int};

datatype rules = Rules of rule N.literalnet;

fun dest_rules (Rules r) = r;
val empty_rules = Rules (N.empty ());
val num_all_rules = N.size o dest_rules;
val num_initial_rules = #f o N.size_profile o dest_rules;
fun num_rules r = num_all_rules r - num_initial_rules r;
fun rules_unify r = N.unify (dest_rules r);

local fun dest ({asms, c, ...} : rule) = (asms,c);
in val pp_rule = pp_map dest (pp_binop " ==>" (pp_list pp_formula) pp_formula);
end;

fun rule_to_string r = PP.pp_to_string (!LINE_LENGTH) pp_rule r;

val pp_rules =
  pp_map (map (fn _ |-> x => x) o N.to_maplets o dest_rules)
  (pp_list pp_rule);

fun add_contrapositives chosen sos th (Rules ruls) =
  let
    val th = FRESH_VARS th
    val lits = clause th
    val lits' = map negate lits
    fun g l = (List.filter (not o equal (negate l)) lits', l)
    val base = map g (chosen lits)
    val contrs = if sos then (lits', False) :: base else base
    fun f (a,c) = c |-> {asms = a, c = c, thm = th, asmn = length a}
  in
    Rules (foldl (fn (h,t) => N.insert (f h) t) ruls contrs)
  end;

fun thms_to_rules chosen thms hyps =
  let val f = uncurry o add_contrapositives chosen
  in foldl (f true) (foldl (f false) empty_rules thms) hyps
  end;

val meson_rules = thms_to_rules I;

val prolog_rules = thms_to_rules (wrap o hd);

(* ------------------------------------------------------------------------- *)
(* Creating the delta goals.                                                 *)
(* ------------------------------------------------------------------------- *)

val thms_to_delta_goals =
  List.concat o
  map (fn (f,n) => [Atom (Fn (f,new_vars n)), Not (Atom (Fn (f,new_vars n)))]) o
  foldl (uncurry union) [] o
  map relations o
  List.concat o
  map clause;

(* ------------------------------------------------------------------------- *)
(* The state passed around by meson.                                         *)
(* ------------------------------------------------------------------------- *)

type state = {env : subst, depth : int, proof : thm list, offset : int};

fun update_env f ({env, depth, proof, offset} : state) =
  {env = f env, depth = depth, proof = proof, offset = offset};

fun update_depth f ({env, depth, proof, offset} : state) =
  {env = env, depth = f depth, proof = proof, offset = offset};

fun update_proof f ({env, depth, proof, offset} : state) =
  {env = env, depth = depth, proof = f proof, offset = offset};

fun update_offset f ({env, depth, proof, offset} : state) =
  {env = env, depth = depth, proof = proof, offset = f offset};

(* ------------------------------------------------------------------------- *)
(* Ancestor pruning.                                                         *)
(* ------------------------------------------------------------------------- *)

fun ancestor_prune false _ _ = K false
  | ancestor_prune true env g =
  let
    val g' = formula_subst env g
    fun check a' = a' = g'
  in
    List.exists (check o formula_subst env)
  end;

(* ------------------------------------------------------------------------- *)
(* Ancestor cutting.                                                         *)
(* ------------------------------------------------------------------------- *)

fun ancestor_cut false _ _ = K false
  | ancestor_cut true env g =
  let
    val g' = negate (formula_subst env g)
    fun check a' = a' = g'
  in
    List.exists (check o formula_subst env)
  end;

(* ------------------------------------------------------------------------- *)
(* Cache cutting.                                                            *)
(* ------------------------------------------------------------------------- *)

fun cache_cont c ({offset, ...} : state) =
  let
    fun f v = case total dest_mvar v of NONE => true | SOME n => n < offset
    val listify = mlibSubst.foldr (fn m as v |-> _ => if f v then cons m else I) []
    val mem = ref []
    fun purify (s as {env, depth = n, ...} : state) =
      let
        val l = listify env
        fun p (n', l') = n <= n' andalso l = l'
      in
        if List.exists p (!mem) then raise ERR "cache_cut" "repetition"
        else (mem := (n, l) :: (!mem); update_env (K (mlibSubst.from_maplets l)) s)
      end
  in
    c o purify
  end;

fun cache_cut false = I
  | cache_cut true =
  fn f => fn a => fn g => fn c => fn s => f a g (cache_cont c s) s;

(* ------------------------------------------------------------------------- *)
(* Unit clause shortcut.                                                     *)
(* ------------------------------------------------------------------------- *)

fun grab_unit units (s as {proof = th :: _, ...} : state) =
  (units := U.add th (!units); s)
  | grab_unit _ {proof = [], ...} = raise BUG "grab_unit" "no thms";

fun use_unit units g c (s as {env, ...}) =
  let val prove = partial (ERR "use_unit" "NONE") (U.prove (!units))
  in c (update_proof (cons (unwrap (prove [formula_subst env g]))) s)
  end;

fun unit_cut false _ = I
  | unit_cut true units =
  fn f => fn a => fn g => fn c => fn s =>
  use_unit units g c s handle ERR_EXN _ => f a g (c o grab_unit units) s;

(* ------------------------------------------------------------------------- *)
(* The core of meson: ancestor unification or Prolog-style extension.        *)
(* ------------------------------------------------------------------------- *)

fun freshen_rule ({thm, asms, c, ...} : rule) i =
  let
    val fvs = FVL [] (c :: asms)
    val fvn = length fvs
    val mvs = mk_mvars i fvn
    val sub = mlibSubst.from_maplets (zipwith (curry op|->) fvs mvs)
  in
    ((INST sub thm, map (formula_subst sub) asms, formula_subst sub c), i + fvn)
  end;

fun reward r = update_depth (fn n => n + r);

fun spend m f c (s as {depth = n, ...} : state) =
  let
    val low = n - m
    val () = assert (0 <= low) (ERR "meson" "impossible divide and conquer")
    fun check (s' as {depth = n', ...} : state) =
      if n' <= low then s' else raise ERR "meson" "divide and conquer"
  in
    f (c o check) s
  end;

local
  fun unify env (th, asms, c) g = (th, asms, unify_literals env c g)

  fun match env (th, asms, c) g =
    let val sub = match_literals c g
    in (INST sub th, map (formula_subst sub) asms, env)
    end;
in
  fun next_state false env r g = unify env r g
    | next_state true env r g = match env r g handle ERR_EXN _ => unify env r g;
end;

local
  fun mp _ th [] p = FACTOR th :: p
    | mp env th (g :: gs) (th1 :: p) =
    mp env (RESOLVE (formula_subst env g) (INST env th1) th) gs p
    | mp _ _ (_ :: _) [] = raise BUG "modus_ponens" "fresh out of thms"
in
  fun modus_ponens th gs (state as {env, ...}) =
    update_proof (mp env (INST env th) (rev gs)) state;
end;

fun swivelp m n = update_proof (swivel m n);

fun meson_expand {parm : parameters, rules, cut, meter, saturated} =
  let
    fun expand ancestors g cont (state as {env, ...}) =
      (chatting 4 andalso
       chat ("meson: "^formula_to_string (formula_subst env g)^".\n");
       if not (check_meter (!meter)) then
         (NONE, CHOICE (fn () => expand ancestors g cont state))
       else if ancestor_prune (#ancestor_pruning parm) env g ancestors then
         raise ERR "meson" "ancestor pruning"
       else if ancestor_cut (#ancestor_cutting parm) env g ancestors then
         (record_infs (!meter) 1; cont (update_proof (cons (ASSUME g)) state))
       else
         let
           fun reduction a () =
             let
               val state = update_env (K(unify_literals env g (negate a))) state
               val state = update_proof (cons (ASSUME g)) state
             in
               (record_infs (!meter) 1; cont state)
             end
           val expansion = expand_rule ancestors g cont state
         in
           first_choice
           (map reduction ancestors @
            map expansion (rules_unify rules (formula_subst env g))) ()
         end)
    and expand_rule ancestors g cont {env, depth, proof, offset} r () =
      let
        val depth = depth - #asmn r
        val () =
          if 0 <= depth then ()
          else (saturated := false; raise ERR "meson" "too deep")
        val (r', offset) = freshen_rule r offset
        val (th, asms, env) = next_state (#state_simplify parm) env r' g
        val () = record_infs (!meter) 1
        val _ = chatting 5 andalso chat ("meson rule: "^rule_to_string r^"\n")
      in
        expands (g :: ancestors) asms (cont o modus_ponens th asms)
        {env = env, depth = depth, proof = proof, offset = offset}
      end
    and expands ancestors g c (s as {depth = n, ...}) =
      if #divide_conquer parm andalso splittable g then
        let
          val (l1, l2) = halves (length g)
          val (g1, g2) = split g l1
          val (f1, f2) = Df (expands ancestors) (g1, g2)
          val (n1, n2) = halves n
          val s = update_depth (K n1) s
        in
          binary_choice
          (fn () => f1 (f2 c o reward n2) s)
          (fn () => f2 (spend (n1 + 1) f1 (c o swivelp l1 l2) o reward n2) s) ()
        end
      else foldl (uncurry (cut expand ancestors)) c (rev g) s
  in
    cut expand []
  end;

(* ------------------------------------------------------------------------- *)
(* Full meson procedure.                                                     *)
(* ------------------------------------------------------------------------- *)

fun meson_finally g ({env, proof, ...} : state) =
  let
    val () = assert (length proof = length g) (BUG "meson" "bad final state")
    val g' = map (formula_subst env) g
    val proof' = map (INST env) (rev proof)
    val _ = chatting 3 andalso chat
      (foldl (fn (h,t)=>t^"  "^thm_to_string h^"\n") "meson_finally:\n" proof')
    val () =
      assert (List.all (uncurry thm_proves) (zip proof' g'))
      (BUG "meson" "did not prove goal list")
  in
    (SOME (FRESH_VARSL proof'), CHOICE no_choice)
  end;

fun raw_meson system goals depth =
  choice_stream
  (fn () =>
   foldl (uncurry (meson_expand system)) (meson_finally goals) (rev goals)
   {env = |<>|, depth = depth, proof = [], offset = 0});

(* ------------------------------------------------------------------------- *)
(* Raw solvers.                                                              *)
(* ------------------------------------------------------------------------- *)

type 'a system =
  {parm : parameters, rules : rules, meter : meter ref, saturated : bool ref,
   cut :
     (formula list -> formula -> (state -> 'a) -> state -> 'a) ->
      formula list -> formula -> (state -> 'a) -> state -> 'a};

fun mk_system parm units meter rules : 'a system =
  let
    val {cache_cutting = caching, unit_lemmaizing = lemmaizing, ...} = parm
  in
    {parm      = parm,
     rules     = rules,
     meter     = meter,
     saturated = ref false,
     cut       = unit_cut lemmaizing units o cache_cut caching}
  end;

fun meson' parm =
  mk_solver_node
  {name = "meson",
   solver_con =
   fn {slice, units, thms, hyps} =>
   let
     val ruls = meson_rules thms hyps
     val _ = chatting 2 andalso chat
       ("meson--initializing--#thms=" ^ int_to_string (length thms) ^
        "--#hyps=" ^ int_to_string (length hyps) ^
        "--#rules=" ^ int_to_string (num_rules ruls) ^
        "--#initial_rules=" ^ int_to_string (num_initial_rules ruls) ^ ".\n")
     val system as {saturated = b, ...} = mk_system parm units slice ruls
     fun d n = if !b then S.NIL else (b := true; S.CONS (n, fn () => d (n + 1)))
     fun f q d =
       (chatting 1 andalso chat ("-" ^ int_to_string d);
        raw_meson system q d)
     fun unit_check goals NONE = U.prove (!units) goals | unit_check _ s = s
   in
     fn goals =>
     filter_meter slice
     (S.map (unit_check goals) (S.flatten (S.map (f goals) (d 0))))
   end};

val meson = meson' defaults;

fun delta' parm =
  mk_solver_node
  {name = "delta",
   solver_con =
   fn {slice, units, thms, hyps} =>
   let
     val ruls = meson_rules thms hyps
     val dgoals = thms_to_delta_goals hyps
     val _ = chatting 2 andalso chat
       ("delta--initializing--#thms=" ^ int_to_string (length thms) ^
        "--#hyps=" ^ int_to_string (length hyps) ^
        "--#rules=" ^ int_to_string (num_rules ruls) ^
        "--#delta_goals=" ^ int_to_string (length dgoals) ^ ".\n")
     val system as {saturated = b, ...} = mk_system parm units slice ruls
     val delta_goals = S.from_list dgoals
     fun d n = if !b then S.NIL else (b := true; S.CONS (n, fn () => d (n + 1)))
     fun f d g =
       (chatting 1 andalso chat "+";
        S.map (K NONE) (raw_meson system [g] d))
     fun g d =
       (chatting 1 andalso chat (int_to_string d);
        S.flatten (S.map (f d) delta_goals))
     fun h () = S.flatten (S.map g (d 0))
     fun unit_check goals NONE = U.prove (!units) goals | unit_check _ s = s
   in
     case delta_goals of S.NIL => K S.NIL
     | _ => fn goals => filter_meter slice (S.map (unit_check goals) (h ()))
   end};

val delta = delta' defaults;

val prolog_depth = case Int.maxInt of NONE => 1000000 | SOME i => i;

fun prolog' parm =
  mk_solver_node
  {name = "prolog",
   solver_con =
   fn {slice, units, thms, hyps} =>
   let
     val system = mk_system parm units slice (prolog_rules thms hyps)
     fun comment S.NIL = "!\n"
       | comment (S.CONS (NONE, _)) = "-"
       | comment (S.CONS (SOME _, _)) = "$\n"
     fun f t () = let val x = t () in chatting 1 andalso chat (comment x); x end
   in
     fn goals => S.map_thk f (fn () => raw_meson system goals prolog_depth) ()
   end};

val prolog = prolog' defaults;

end
