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
structure D = mlibLiteralDisc; local open mlibLiteralDisc in end;
structure U = mlibUnits; local open mlibUnits in end;

val |<>|          = mlibSubst.|<>|;
val op ::>        = mlibSubst.::>;
val formula_subst = mlibSubst.formula_subst;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val () = traces := insert "mlibMeson" (!traces);

val chat = trace "mlibMeson";

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
   cache_cutting    = true,
   divide_conquer   = true,
   unit_lemmaizing  = true};

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun protect r f x =
  let
    val v = !r
    val y = f x handle e as ERR_EXN _ => (r := v; raise e)
    val () = r := v
  in
    y
  end;

fun until p =
  let
    open mlibStream
    fun u NIL = NIL
      | u (CONS (x, xs)) = CONS (x, if p x then K NIL else fn () => u (xs ()))
  in
    u
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

datatype rules = Rules of (thm * (formula list * formula)) D.literal_map;

fun dest_rules (Rules r) = r;
val empty_rules = Rules D.empty;
val num_all_rules = D.size o dest_rules;
val num_initial_rules = #f o D.size_profile o dest_rules;
fun num_rules r = num_all_rules r - num_initial_rules r;
val rules_unify = D.unify o dest_rules;

val pp_rules =
  pp_map dest_rules
  (D.pp_literal_map
   (pp_map snd (pp_binop "==>" (pp_list pp_formula) pp_formula)));

fun add_contrapositives chosen sos th (Rules ruls) =
  let
    val lits = clause th
    val lits' = map negate lits
    val base = map (fn l => (subtract lits' [negate l], l)) (chosen lits)
    val contrs = if sos then (lits', False) :: base else base
    fun f (c as (_, t)) = t |-> (th, c)
  in
    Rules (foldl (fn (h, t) => D.insert (f h) t) ruls contrs)
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
  map (fn (f, n) => [Atom (f, new_vars n), Not (Atom (f, new_vars n))]) o
  foldl (uncurry union) [] o
  map relations o
  List.concat o
  map clause;

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

fun cache_cont c =
  let
    val memory = ref []
  in
    fn s as (env, n, _) =>
    if List.exists (fn (env', n', _) => pointer_eq env env' andalso n <= n')
       (!memory) then raise ERR "cache_cut" "repetition"
    else (memory := s :: !memory; c s)
  end;

fun cache_cut false = I
  | cache_cut true = fn f => fn a => fn g => fn c => f a g (cache_cont c);

(* ------------------------------------------------------------------------- *)
(* Unit clause shortcut.                                                     *)
(* ------------------------------------------------------------------------- *)

fun grab_unit units (s as (_, _, th :: _)) =
  (units := U.add th (!units); s)
  | grab_unit _ (_, _, []) = raise BUG "grab_unit" "no thms";

fun use_unit units g c (env, n, p) =
  let val prove = partial (ERR "use_unit" "NONE") (U.prove (!units))
  in c (env, n, unwrap (prove [formula_subst env g]) :: p)
  end;

fun unit_cut false _ = I
  | unit_cut true units =
  fn f => fn a => fn g => fn c => fn s =>
  use_unit units g c s handle ERR_EXN _ => f a g (c o grab_unit units) s;

(* ------------------------------------------------------------------------- *)
(* The core of meson: ancestor unification or Prolog-style extension.        *)
(* ------------------------------------------------------------------------- *)

type state = subst * int * thm list;

fun state1 f ((env, n, p) : state) : state = (f env, n,   p);
fun state2 f ((env, n, p) : state) : state = (env,   f n, p);
fun state3 f ((env, n, p) : state) : state = (env,   n,   f p);

fun rule_renamer (th, (asm, c)) =
  let
    val fvs = FV (list_mk_conj (c :: asm))
    val vvs = new_vars (length fvs)
    val sub = mlibSubst.from_maplets (zipwith (curry op|->) fvs vvs)
  in
    (INST sub th, (map (formula_subst sub) asm, formula_subst sub c))
  end;

fun reward r = state2 (fn n => n + r);

fun check_used m f cont (c as (_, n, _)) =
  let
    val low = n - m
    fun check (c' as (_, n', _)) =
      if n' <= low then c' else raise ERR "meson" "repeated solution"
  in
    f (cont o check) c
  end;

fun next_state false env (th, (asms, c)) g = (th, asms, unify_literals env c g)
  | next_state true env (r as (th, (asms, c))) g =
  (case total (match_literals c) g of NONE => next_state false env r g
   | SOME sub => (INST sub th, map (formula_subst sub) asms, env));

local
  fun mp _ th [] p = FACTOR th :: p
    | mp env th (g :: gs) (th1 :: p) =
    mp env (RESOLVE (formula_subst env g) (INST env th1) th) gs p
    | mp _ _ (_ :: _) [] = raise BUG "modus_ponens" "fresh out of thms"
in
  fun modus_ponens th gs (env, n, p) = (env, n, mp env (INST env th) (rev gs) p)
end;

fun meson_expand {parm : parameters, rules, cut, meter, saturated} =
  let
    fun expand ancestors g cont (env, n, p) =
      if not (check_meter (!meter)) then
        (NONE, CHOICE (fn () => expand ancestors g cont (env, n, p)))
      else if ancestor_prune (#ancestor_pruning parm) env g ancestors then
        raise ERR "meson" "ancestor pruning"
      else if ancestor_cut (#ancestor_cutting parm) env g ancestors then
        (record_infs (!meter) 1; cont (env, n, ASSUME g :: p))
      else
        let
        (*val () = print ("meson: " ^ formula_to_string g ^ ".\n")*)
          fun reduction a () =
            let val env' = unify_literals env g (negate a)
            in (record_infs (!meter) 1; cont (env', n, ASSUME g :: p))
            end
          val expansion = expand_rule ancestors g cont (env, n, p)
        in
          first_choice
          (map reduction ancestors @
           map expansion (rules_unify rules (formula_subst env g))) ()
        end
    and expand_rule ancestors g cont (env, n, p) r () =
      let
        val n = n - length (fst (snd r))
        val () =
          if 0 <= n then ()
          else (saturated := false; raise ERR "meson" "too deep")
        val (th, asms, env) =
          next_state (#state_simplify parm) env (rule_renamer r) g
        val () = record_infs (!meter) 1
      in
        expands (g :: ancestors) asms (cont o modus_ponens th asms)
        (env, n, p)
      end
    and expands ancestors goals cont (env, n, p) =
      if #divide_conquer parm andalso 2 <= length goals then
        let
          val l = length goals
          val l2 = l div 2
          val (g1, g2) = split goals l2
          val n1 = n div 2
          val n2 = n - n1
        in
          binary_choice
          (fn () =>
           expands ancestors g1
           (expands ancestors g2 cont o reward n2) (env, n1, p))
          (fn () =>
           expands ancestors g2
           (check_used (n1 + 1) (expands ancestors g1)
            (cont o state3 (swivel l2 (l - l2))) o reward n2) (env, n1, p)) ()
        end
      else
        foldl (uncurry (cut expand ancestors)) cont (rev goals)
        (env, n, p)
  in
    cut expand []
  end;

(* ------------------------------------------------------------------------- *)
(* Full meson procedure.                                                     *)
(* ------------------------------------------------------------------------- *)

fun meson_finally goals (env, _, ths) =
  let
    val () = assert (length ths = length goals) (BUG "meson" "bad final state")
    val goals' = map (formula_subst env) goals
    val ths' = map (INST env) (rev ths)
  (*val () = (print "meson_finally: "; printVal (goals', ths'); print ".\n")*)
    val () =
      assert (List.all (uncurry thm_proves) (zip ths' goals'))
      (BUG "meson" "did not prove goal list")
  in
    (SOME ths', CHOICE no_choice)
  end;

fun raw_meson system goals depth =
  choice_stream
  (fn () =>
   foldl (uncurry (meson_expand system)) (meson_finally goals) (rev goals)
   (|<>|, depth, []));

(* ------------------------------------------------------------------------- *)
(* Raw solvers.                                                              *)
(* ------------------------------------------------------------------------- *)

type 'a system =
  {parm : parameters, rules : rules, meter : meter ref, saturated : bool ref,
   cut :
     (formula list -> formula -> (state -> 'a) -> state -> 'a) ->
      formula list -> formula -> (state -> 'a) -> state -> 'a};

fun mk_system parm units meter rules : 'a system =
  {parm      = parm,
   rules     = rules,
   meter     = meter,
   saturated = ref false,
   cut       =
   cache_cut (#cache_cutting parm) o unit_cut (#unit_lemmaizing parm) units};

fun meson' parm =
  mk_solver_node
  {name = "meson",
   solver_con =
   fn {slice, units, thms, hyps} =>
   let
     val ruls = meson_rules thms hyps
     val () = chat
       ("meson--initializing--#thms=" ^ int_to_string (length thms) ^
        "--#hyps=" ^ int_to_string (length hyps) ^
        "--#rules=" ^ int_to_string (num_rules ruls) ^
        "--#initial_rules=" ^ int_to_string (num_initial_rules ruls) ^ ".\n")
     val system as {saturated = b, ...} = mk_system parm units slice ruls
     fun d n = if !b then S.NIL else (b := true; S.CONS (n, fn () => d (n + 1)))
     fun f q d = (chat ("-" ^ int_to_string d); raw_meson system q d)
   in
     fn goals => filter_meter slice (S.flatten (S.map (f goals) (d 0)))
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
     val () = chat
       ("delta--initializing--#thms=" ^ int_to_string (length thms) ^
        "--#hyps=" ^ int_to_string (length hyps) ^
        "--#rules=" ^ int_to_string (num_rules ruls) ^
        "--#delta_goals=" ^ int_to_string (length dgoals) ^ ".\n")
     val system as {saturated = b, ...} = mk_system parm units slice ruls
     val delta_goals = S.from_list dgoals
     fun d n = if !b then S.NIL else (b := true; S.CONS (n, fn () => d (n + 1)))
     fun f d g = (chat "+"; S.map (K NONE) (raw_meson system [g] d))
     fun g d = (chat (int_to_string d); S.flatten (S.map (f d) delta_goals))
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
   let val system = mk_system parm units slice (prolog_rules thms hyps)
   in fn goals => raw_meson system goals prolog_depth
   end};

val prolog = prolog' defaults;

(* quick testing
load "UNLINK";
open UNLINK;
val time = Mosml.time;
quotation := true;
installPP pp_term;
installPP pp_formula;
installPP mlibSubst.pp_subst;
installPP pp_rules;
installPP pp_thm;

val limit : limit ref = ref {infs = NONE, time = SOME 30.0};
fun prolog_solve d q =
  try
  (solve
   (initialize prolog {limit = !limit, thms = d, hyps = []})) q;
fun meson_prove g =
  try (time refute)
  (initialize (set_of_support all_negative meson)
   {limit = !limit, thms = [], hyps = axiomatize (Not (generalize g))});

(* Testing the prolog solver *)

val database = (axiomatize o parse_formula)
  `subset nil nil /\
   (!v x y. subset x y ==> subset (v :: x) (v :: y)) /\
   (!v x y. subset x y ==> subset x        (v :: y))`;

try (prolog_solve database) [parse_formula `subset x (0 :: 1 :: 2 :: nil)`];
(* takes ages
try (prolog_solve database) [parse_formula `subset (0 :: 1 :: 2 :: nil) x`];
*)

val database = (axiomatize o parse_formula)
  `p 0 3 /\
   (!x. p x 4) /\
   (!x. p x 3 ==> p (s (s (s x))) 3) /\
   (!x. p (s x) 3 ==> p x 3)`;

try (prolog_solve database) [parse_formula `p (s 0) 3`];

(* Testing the meson prover *)

meson_prove True;

val p59 = parse_formula (get nonequality "P59");
val ths = axiomatize (Not (generalize p59));
val rules = meson_rules [] ths;
rules_unify rules (parse_formula `~P 0`);
meson_prove p59;

val p39 = parse_formula (get nonequality "P39");
clausal (Not (generalize p39));
axiomatize (Not (generalize p39));
meson_prove p39;

val num14 = parse_formula (get tptp "NUM014-1");
meson_prove num14;

val p55 = parse_formula (get nonequality "P55");
meson_prove p55;

val p26 = parse_formula (get nonequality "P26");
clausal (Not (generalize p26));
meson_prove p26;

val los = parse_formula (get nonequality "LOS");
meson_prove los;

val reduced_num284 = parse_formula
  `fibonacci 0 (s 0) /\ fibonacci (s 0) (s 0) /\
   (!x y z x' y' z'.
      ~sum x (s (s 0)) z \/ ~sum y (s 0) z \/
      ~fibonacci x x' \/ ~fibonacci y y' \/ ~sum x' y' z' \/
      fibonacci z z') /\ (!x. sum x 0 x) /\
   (!x y z. ~sum x y z \/ sum x (s y) (s z)) /\
   (!x. ~fibonacci (s (s (s (s (s (s (s (s 0)))))))) x) ==> F`;
meson_prove reduced_num284;

val p29 = parse_formula (get nonequality "P29");
clausal (Not (generalize p29));
meson_prove p29;

val num1 = parse_formula (get tptp "NUM001-1");
meson_prove num1;

val model_completeness = parse_formula (get nonequality "MODEL_COMPLETENESS");
meson_prove model_completeness;
*)

end
