(* ========================================================================= *)
(* PROCESSING SETS OF CLAUSES AT A TIME                                      *)
(* Created by Joe Hurd, October 2002                                         *)
(* ========================================================================= *)

(*
app load ["mlibClause", "mlibUnits"];
*)

(*
*)
structure mlibClauseset1 :> mlibClauseset1 =
struct

infix |-> ::> ##;

open mlibUseful mlibTerm mlibMatch mlibClause;

structure T = mlibTermnet; local open mlibTermnet in end;
structure N = mlibLiteralnet; local open mlibLiteralnet in end;
structure S = mlibSubsume; local open mlibSubsume in end;
structure U = mlibUnits; local open mlibUnits in end;

type 'a termnet    = 'a T.termnet;
type 'a literalnet = 'a N.literalnet;
type 'a subsume    = 'a S.subsume;

val |<>|          = mlibSubst.|<>|;
val op ::>        = mlibSubst.::>;
val formula_subst = mlibSubst.formula_subst;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val () = traces := {module = "mlibClauseset1", alignment = K 1} :: !traces;

fun chat l m = trace {module = "mlibClauseset1", message = m, level = l};

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun ofilt _ NONE = NONE | ofilt p (s as SOME x) = if p x then s else NONE;

fun ueq cl =
  case total clause_thm cl of NONE => NONE
  | SOME th => if mlibThm.is_unit_eq th then SOME th else NONE;

fun psym lit =
  let
    val (s, (x,y)) = (I ## dest_eq) (dest_literal lit)
    val () = assert (x <> y) (ERR "psym" "refl")
  in
    mk_literal (s, mk_eq (y,x))
  end;

(* ------------------------------------------------------------------------- *)
(* Symmetric versions of literals.                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun f ((c,i) |-> l) =
    let
      val l = psym l
      val c = SYM (c,i)
    in
      case index (equal l) (clause_lits c) of SOME i => (c,i) |-> l
      | NONE => raise BUG "a_sym" "couldn't find sym"
    end;
in
  val sym_lits = List.mapPartial (total f);
end;

(* ------------------------------------------------------------------------- *)
(* Using unit theorems to strengthen clauses.                                *)
(* ------------------------------------------------------------------------- *)

fun strengthen units cl =
  let
    val cl = NEQ_SIMP cl
  in
    if mlibCanon.tautologous (clause_lits cl) then NONE
    else SOME (demodulate units cl)
  end;

(* ------------------------------------------------------------------------- *)
(* Clause sets.                                                              *)
(* ------------------------------------------------------------------------- *)

datatype clauseset = SET of
  {size       : int,
   rewrites   : thm list,
   subsumers  : clause subsume,
   literals   : (clause * int) literalnet,
   equalities : (clause * int * bool) termnet,
   subterms   : (clause * int * int list) termnet};

fun update_size n set =
  let val SET {size = _, rewrites = w, subsumers = s,
               literals = r, equalities = e, subterms = p} = set
  in SET {size = n, rewrites = w, subsumers = s, literals = r,
          equalities = e, subterms = p}
  end;

fun update_rewrites w set =
  let val SET {size = n, rewrites = _, subsumers = s,
               literals = r, equalities = e, subterms = p} = set
  in SET {size = n, rewrites = w, subsumers = s, literals = r,
          equalities = e, subterms = p}
  end;

fun update_subsumers s set =
  let val SET {size = n, rewrites = w, subsumers = _,
               literals = r, equalities = e, subterms = p} = set
  in SET {size = n, rewrites = w, subsumers = s, literals = r,
          equalities = e, subterms = p}
  end;

fun update_literals r set =
  let val SET {size = n, rewrites = w, subsumers = s,
               literals = _, equalities = e, subterms = p} = set
  in SET {size = n, rewrites = w, subsumers = s, literals = r,
          equalities = e, subterms = p}
  end;

fun update_equalities e set =
  let val SET {size = n, rewrites = w, subsumers = s,
               literals = r, equalities = _, subterms = p} = set
  in SET {size = n, rewrites = w, subsumers = s, literals = r,
          equalities = e, subterms = p}
  end;

fun update_subterms p set =
  let val SET {size = n, rewrites = w, subsumers = s,
               literals = r, equalities = e, subterms = _} = set
  in SET {size = n, rewrites = w, subsumers = s, literals = r,
          equalities = e, subterms = p}
  end;

val empty =
  SET {size = 0, rewrites = [], subsumers = S.empty,
       literals = N.empty, equalities = T.empty, subterms = T.empty};

fun reset (SET {rewrites = w, ...}) =
  SET {size = 0, rewrites = w, subsumers = S.empty,
       literals = N.empty, equalities = T.empty, subterms = T.empty};

fun size (SET {size, ...}) = size;

fun add cl set =
  let
    fun f ((x |-> l), net) = N.insert (l |-> x) net
    fun g ((x |-> t), net) = T.insert (t |-> x) net
    val SET {size = n, rewrites = w, subsumers = s,
             literals = r, equalities = e, subterms = p, ...} = set
    val set = update_size (n + 1) set
    val set = case ueq cl of SOME t => update_rewrites (t::w) set | NONE => set
    val set = update_subsumers (S.add (clause_lits cl |-> cl) s) set
    val lits = active_lits cl
    val set = update_literals (foldl f r (lits @ sym_lits lits)) set
    val set = update_equalities (foldl g e (active_eqs cl)) set
    val set = update_subterms (foldl g p (active_tms cl)) set
  in
    set
  end;

fun addl cls set = foldl (uncurry add) set cls;

fun simplify set cl =
  let val SET {rewrites = w, ...} = set in REWRITE w cl end;

fun subsumed set cl =
  let
    val SET {subsumers, ...} = set
    fun f (sub, c) =
      (case total (INST sub) c of NONE => false | SOME d => subsumes d cl)
  in
    List.exists f (S.subsumes' subsumers (clause_lits cl))
  end;

local
  fun fac set units =
    let
      val f =
        ofilt (not o subsumed set) o strengthen units o simplify set o NEQ_SIMP
      fun g (cl, acc) = case f cl of NONE => acc | SOME cl => cl :: acc
    in
      fn (cl, acc) =>
      (case f cl of NONE => acc | SOME cl => foldl g (cl :: acc) (FACTOR cl))
    end;
in
  fun factor set units cl acc = fac set units (cl, acc);
  fun initialize set units cls = foldl (fac set units) [] cls;
end;

fun deduce set units =
  let
    fun ins cl acc = factor set units cl acc

    fun resolv ci (dj, acc) =
      case total (RESOLVE ci) dj of NONE => acc | SOME l => ins l acc

    fun resolvants r (ci |-> l, acc) =
      foldl (resolv ci) acc (N.unify r (negate l))

    fun paramod cib djp acc =
      case total (PARAMODULATE cib) djp of NONE => acc | SOME l => ins l acc

    fun paramods_from p (cib |-> t, acc) =
      foldl (uncurry (paramod cib)) acc (T.unify p t)

    fun paramods_into e (cip |-> t, acc) =
      foldl (uncurry (C paramod cip)) acc (T.unify e t)
  in
    fn cl =>
    let
      val SET {literals = r, equalities = e, subterms = p, ...} = set
      val res = foldl (resolvants r) [] (active_lits cl)
      val res = foldl (paramods_from p) res (active_eqs cl)
      val res = foldl (paramods_into e) res (active_tms cl)
    in
      res
    end
    handle ERR_EXN _ => raise BUG "deduce" "shouldn't fail"
  end;

val pp_clauseset = pp_bracket ("C<", ">") (pp_map size pp_int);

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
val r = add_literal th' empty_literals;
map #res (find_resolvants r th);
*)

end