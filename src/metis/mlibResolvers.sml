(* ========================================================================= *)
(* A TYPE TO FIND RESOLVANT CLAUSES                                          *)
(* Created by Joe Hurd, April 2002                                           *)
(* ========================================================================= *)

(*
app load ["mlibThm", "mlibMatch"];
*)

(*
*)
structure mlibResolvers :> mlibResolvers =
struct

infix |-> ::>;

open mlibUseful mlibTerm mlibMatch mlibThm mlibCanon;

structure N = mlibLiteralNet; local open mlibLiteralNet in end;

val |<>|          = mlibSubst.|<>|;
val op ::>        = mlibSubst.::>;
val formula_subst = mlibSubst.formula_subst;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val () = traces := insert "mlibResolvers" (!traces);

val chat = trace "mlibResolvers";

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun trich l n =
  case split l n of (_, []) => raise ERR "trich" "no exact"
  | (l, h :: t) => (l, h, t);

(* ------------------------------------------------------------------------- *)
(* The type definition with some simple operations.                          *)
(* ------------------------------------------------------------------------- *)

type resolvers = (int * thm) N.literal_map;

type resolvant = {mate : thm, sub : subst, res : thm};

val empty_resolvers : resolvers = N.empty;

fun add_resolver th =
  let fun add_lit ((n, lit), net) = N.insert (lit |-> (n, th)) net
  in fn net => foldl add_lit net (enumerate 0 (clause th))
  end;

fun resolvers_info (net : resolvers) = int_to_string (N.size net);

val pp_resolvers = pp_map resolvers_info pp_string;

val dest_resolvers : resolvers -> thm list = 
  map snd o List.filter (equal 0 o fst) o N.to_list;

(* ------------------------------------------------------------------------- *)
(* A reference implementation for debugging.                                 *)
(* ------------------------------------------------------------------------- *)

fun canonize lits =
  let
    val nvars = enumerate 0 (FV (list_mk_conj lits))
    val ms = map (fn (n, v) => v |-> Var ("__" ^ (int_to_string n))) nvars
  in
    map (formula_subst (mlibSubst.from_maplets ms)) lits
  end;

local
  fun subs acc [] = acc
    | subs acc ((prev, []) :: others) = subs (prev :: acc) others
    | subs acc ((prev, h :: t) :: others) =
    subs acc ((h :: prev, t) :: (prev, t) :: others);
in
  fun all_nonempty_subsets l = tl (subs [] [([], l)]);
end;

fun pairs [] = raise ERR "pairs" "empty"
  | pairs [h] = []
  | pairs (h :: (t as h' :: _)) = (h, h') :: pairs t;

fun sanity_resolve_on th th' s s' =
  let
    val sub = unifyl_literals |<>| (pairs (s @ s'))
    val lit = formula_subst sub (hd s)
    val res = FACTOR (RESOLVE lit (INST sub th) (INST sub th'))
  in
    {mate = th', sub = sub, res = res}
  end;

fun sanity_resolve th th' =
  List.mapPartial I
  (cartwith (total o sanity_resolve_on th th')
   (all_nonempty_subsets (clause th))
   (all_nonempty_subsets (map negate (clause th'))));

fun sanity_resolvants net th =
  List.concat (map (sanity_resolve th) (dest_resolvers net));

fun sanity_check net th (res : resolvant list) =
  let
    val () = chat "X"
    val f = PP.pp_to_string (!LINE_LENGTH) (pp_list (pp_map AXIOM pp_thm))
    val fast = map (canonize o clause o #res) res
    val slow = map (canonize o clause o #res) (sanity_resolvants net th)
    val () =
      if subset fast slow then ()
      else
        (print ("\nsanity_check: extra clauses:\nnet = " ^
                f (map clause (dest_resolvers net)) ^ "\nth = " ^
                thm_to_string th ^ "\nfast = " ^ f fast ^ "\nslow = " ^ f slow ^
                "\nextra = " ^ f (subtract fast slow) ^
                "\nmissing = " ^ f (subtract slow fast) ^ "\n");
         raise BUG "find_resolvants" "extra clauses!")
    val () =
      if subset slow fast then ()
      else
        (print ("\nsanity_check: missing clauses:\nnet = " ^
                f (map clause (dest_resolvers net)) ^ "\nth = " ^
                thm_to_string th ^ "\nfast = " ^ f fast ^ "\nslow = " ^ f slow ^
                "\nmissing = " ^ f (subtract slow fast) ^
                "\nextra = " ^ f (subtract fast slow) ^ "\n");
         raise BUG "find_resolvants" "missing clauses")
(*
    val () =
      (print ("\nsanity_check: ok:\nnet = " ^
              f (map clause (dest_resolvers net)) ^ "\nth = " ^
              thm_to_string th ^ "\nres = " ^ f fast ^ "\n"))
*)
  in
    ()
  end;

(* ------------------------------------------------------------------------- *)
(* The core engine for combined factor/resolution steps.                     *)
(* ------------------------------------------------------------------------- *)

fun resolve_on s r th th' =
  SOME (FACTOR (RESOLVE r (INST s th) (INST s th')));

fun resolve acc [] = acc
  | resolve acc ((avoid, sub, res, []) :: others) =
  resolve
  (if mem res (map (formula_subst sub) avoid) then acc
   else (res, sub) :: acc) others
  | resolve acc ((avoid, sub, res, x :: xs) :: others) =
  let
    fun f c = resolve acc (c ((x :: avoid, sub, res, xs) :: others))
  in
    case total (unify_literals sub res) x of NONE => f I
    | SOME sub'
      => f (cons (avoid, mlibSubst.refine sub sub', formula_subst sub' res, xs))
  end;

fun resolve_from (n, th) (n', th') =
  let
    val (prev, lit, succ) = trich (clause th) n
    val (prev', lit', succ') = trich (map negate (clause th')) n'
    val sub = unify_literals |<>| lit lit'
    val res = formula_subst sub lit
    fun f (r, s) = Option.map (pair s) (resolve_on s r th th')
  in
    List.mapPartial f (resolve [] [(prev @ prev', sub, res, succ @ succ')])
  end;

fun resolvants net th =
  let
    fun g (_, mate) ((sub, res), l) = {mate = mate, sub = sub, res = res} :: l
    fun r m (u, acc) =
      case total (resolve_from (m, th)) u of NONE => acc
      | SOME l => foldl (g u) acc l
    fun f ((m, lit), acc) = foldl (r m) acc (N.unify net (negate lit))
    val res = foldl f [] (enumerate 0 (clause th))
  (*val () = sanity_check net th res*)
  in
    res
  end

fun find_resolvants net th =
  List.filter (non tautologous o clause o #res) (resolvants net th)
  handle ERR_EXN _ => raise BUG "find_resolvants" "should never fail";

(* Quick testing
quotation := true;
installPP pp_formula;
installPP pp_term;
installPP pp_subst;
installPP pp_thm;
val th = AXIOM (map parse [`p(3, x, v)`, `q(x)`, `p(3, x, z)`]);
val th' = AXIOM (map parse [`~p(3, f(y), w)`, `~q(y)`, `~p(3, f(y), 4)`]);
try (resolve_from (0, th)) (0, th');
try (resolve_from (2, th)) (0, th');
try (resolve_from (0, th)) (2, th');
try (resolve_from (2, th)) (2, th');
val r = add_resolver th' empty_resolvers;
map #res (find_resolvants r th);
*)

end