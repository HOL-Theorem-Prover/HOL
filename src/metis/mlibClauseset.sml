(* ========================================================================= *)
(* PROCESSING SETS OF CLAUSES AT A TIME                                      *)
(* Created by Joe Hurd, October 2002                                         *)
(* ========================================================================= *)

(*
app load ["mlibClause", "mlibUnits"];
*)

(*
*)
structure mlibClauseset :> mlibClauseset =
struct

infix |-> ::> ##;

open mlibUseful mlibTerm mlibMatch mlibClause;

structure T = mlibTermnet; local open mlibTermnet in end;
structure N = mlibLiteralnet; local open mlibLiteralnet in end;
structure R = mlibRewrite; local open mlibRewrite in end;
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

val module = "mlibClauseset";
val () = traces := {module = module, alignment = I} :: !traces;
fun chatting l = tracing {module = module, level = l};
fun chat s = (trace s; true)

(* ------------------------------------------------------------------------- *)
(* Parameters                                                                *)
(* ------------------------------------------------------------------------- *)

type parameters =
  {subsumption    : int,
   simplification : int};

val defaults =
  {subsumption    = 2,
   simplification = 2};

fun update_subsumption f (parm : parameters) : parameters =
  let val {subsumption = s, simplification = r} = parm
  in {subsumption = f s, simplification = r}
  end;

fun update_simplification f (parm : parameters) : parameters =
  let val {subsumption = s, simplification = r} = parm
  in {subsumption = s, simplification = f r}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun ofilt _ NONE = NONE | ofilt p (s as SOME x) = if p x then s else NONE;

fun psym lit =
  let
    val (s,(x,y)) = (I ## dest_eq) (dest_literal lit)
    val () = assert (x <> y) (ERR "psym" "refl")
  in
    mk_literal (s, mk_eq (y,x))
  end;

fun add_unit c u = case total clause_thm c of NONE => u | SOME t => U.add t u;

fun add_subsum (icl as (_,cl)) = S.add (clause_lits cl |-> icl);

fun lift_thm (cparm,_) (i,th) = (i, mk_clause cparm th);

fun dest_rewr cl =
  let
    val () = assert (#term_order (clause_parm cl)) (ERR "dest_rewr" "no rewrs")
    val th = clause_thm cl
    val (x,y) = mlibThm.dest_unit_eq th
    val () = assert (x <> y) (ERR "dest_rewr" "refl")
  in
    th
  end;

val is_rewr = can dest_rewr;

fun empty_rewrs ({termorder_parm = p, ...} : mlibClause.parameters) =
  R.empty (mlibTermorder.compare (mlibTermorder.empty p));

fun add_rewr (i,cl) rw = R.add (i, dest_rewr cl) rw;

fun literals_to_string l =
  PP.pp_to_string (!LINE_LENGTH)
  (N.pp_literalnet (pp_pair pp_int (pp_pair pp_clause pp_int))) l;

(* ------------------------------------------------------------------------- *)
(* id_clauses                                                                *)
(* ------------------------------------------------------------------------- *)

type id_clause = int * clause;

fun dest_id_clause x : id_clause = x;

fun empty_id_clause icl =
  let val (_,cl) = dest_id_clause icl
  in if empty_clause cl then SOME cl else NONE
  end;

val pp_id_clause = pp_pair pp_int pp_clause;

fun id_clause_to_string cl = PP.pp_to_string (!LINE_LENGTH) pp_id_clause cl;

fun id_clauses_to_string cls =
  PP.pp_to_string (!LINE_LENGTH) (pp_list pp_id_clause) cls;

(* ------------------------------------------------------------------------- *)
(* mlibClause sets.                                                              *)
(* ------------------------------------------------------------------------- *)

datatype clauseset = SET of
  {parm       : mlibClause.parameters * parameters,
   profile    : {age : int, size : int},
   rewrites   : R.rewrs,
   clauses    : (int * clause) list,
   subsumers  : (int * clause) subsume,
   literals   : (int * (clause * int)) literalnet,
   equalities : (int * (clause * int * bool)) termnet,
   subterms   : (int * (clause * int * int list)) termnet};

fun profile (SET {profile = p, ...}) = p;
fun subsumers (SET {subsumers = s, ...}) = s;
fun size set = #size (profile set);
fun rewrites (SET {rewrites, ...}) = rewrites;

fun clauses (SET {clauses = c, ...}) =
  List.mapPartial (total clause_thm o snd) c;

fun update_profile n set =
  let
    val SET {parm = z, profile = _, rewrites = w, clauses = c, subsumers = s,
             literals = r, equalities = e, subterms = p} = set
  in
    SET {parm = z, profile = n, rewrites = w, clauses = c, subsumers = s,
         literals = r, equalities = e, subterms = p}
  end;

fun update_rewrites w set =
  let
    val SET {parm = z, profile = n, rewrites = _, clauses = c, subsumers = s,
             literals = r, equalities = e, subterms = p} = set
  in
    SET {parm = z, profile = n, rewrites = w, clauses = c, subsumers = s,
         literals = r, equalities = e, subterms = p}
  end;

fun update_clauses c set =
  let
    val SET {parm = z, profile = n, rewrites = w, clauses = _, subsumers = s,
             literals = r, equalities = e, subterms = p} = set
  in
    SET {parm = z, profile = n, rewrites = w, clauses = c, subsumers = s,
         literals = r, equalities = e, subterms = p}
  end;

fun update_subsumers s set =
  let
    val SET {parm = z, profile = n, rewrites = w, clauses = c, subsumers = _,
             literals = r, equalities = e, subterms = p} = set
  in
    SET {parm = z, profile = n, rewrites = w, clauses = c, subsumers = s,
         literals = r, equalities = e, subterms = p}
  end;

fun update_literals r set =
  let
    val SET {parm = z, profile = n, rewrites = w, clauses = c, subsumers = s,
             literals = _, equalities = e, subterms = p} = set
  in
    SET {parm = z, profile = n, rewrites = w, clauses = c, subsumers = s,
         literals = r, equalities = e, subterms = p}
  end;

fun update_equalities e set =
  let
    val SET {parm = z, profile = n, rewrites = w, clauses = c, subsumers = s,
             literals = r, equalities = _, subterms = p} = set
  in
    SET {parm = z, profile = n, rewrites = w, clauses = c, subsumers = s,
         literals = r, equalities = e, subterms = p}
  end;

fun update_subterms p set =
  let
    val SET {parm = z, profile = n, rewrites = w, clauses = c, subsumers = s,
             literals = r, equalities = e, subterms = _} = set
  in
    SET {parm = z, profile = n, rewrites = w, clauses = c, subsumers = s,
         literals = r, equalities = e, subterms = p}
  end;

(* ------------------------------------------------------------------------- *)
(* Basic operations                                                          *)
(* ------------------------------------------------------------------------- *)

fun empty (cparm,parm) =
  SET {parm = (cparm,parm), profile = {age = 0, size = 0},
       rewrites = empty_rewrs cparm, clauses = [],
       subsumers = S.empty (), literals = N.empty (),
       equalities = T.empty (), subterms = T.empty ()};

fun reset (SET {parm = z, profile = {age = a,...}, rewrites = w, ...}) =
  (map (lift_thm z) (R.eqns w),
   SET {parm = z, profile = {age = a, size = 0}, rewrites = w,
        clauses = [], subsumers = S.empty (), literals = N.empty (),
        equalities = T.empty (), subterms = T.empty ()});
    
(* ------------------------------------------------------------------------- *)
(* Simplify clauses                                                          *)
(* ------------------------------------------------------------------------- *)

fun simp set = let val SET {rewrites = w, ...} = set in REWRITE w end;

fun simplify set (icl as (i,_)) =
  let val SET {parm = z, rewrites = w, ...} = set
  in case R.peek w i of SOME th => lift_thm z (i,th) | NONE => (i, simp set icl)
  end;

(* ------------------------------------------------------------------------- *)
(* Strengthening clauses                                                     *)
(* ------------------------------------------------------------------------- *)

fun beef_up units cl =
  let
    val cl = NEQ_SIMP cl
    val () = assert (not (mlibCanon.tautologous (clause_lits cl)))
             (ERR "strengthen" "taut")
    val cl = demodulate units cl
  in
    cl
  end;

fun strengthen set units =
  total (fn (i,cl) => (i, beef_up units cl)) o simplify set;

(* ------------------------------------------------------------------------- *)
(* Forward subsumption checking                                              *)
(* ------------------------------------------------------------------------- *)

fun subsum subs cl =
  let
    fun f (sub,(_,c)) =
      (case total (INST sub) c of NONE => false | SOME d => subsumes d cl)
  in
    mlibStream.exists f (S.subsumes' subs (clause_lits cl))
  end;

fun subsumed set (_,cl) = subsum (subsumers set) cl;

(* ------------------------------------------------------------------------- *)
(* Creating id_clauses                                                       *)
(* ------------------------------------------------------------------------- *)

local
  fun add icl set NONE = (icl,set)
    | add (i,cl) set (SOME th) =
    let
      val SET {rewrites = w, ...} = set
      val cl = mk_clause (clause_parm cl) th
      val icl = (i,cl)
      val set = update_rewrites (add_rewr icl w) set
      val _ = chatting 2 andalso
              chat ("\nrewrite set now:\n" ^ R.rewrs_to_string w ^ "\n")
    in
      (icl,set)
    end;
in
  fun stamp_id cl set =
    let
      val SET {profile = {age = a, size = s}, ...} = set
      val set = update_profile {age = a + 1, size = s} set
    in
      add (a,cl) set (total dest_rewr cl)
    end;
end;

(* ------------------------------------------------------------------------- *)
(* Extract clauses that can be simplified                                    *)
(* ------------------------------------------------------------------------- *)

local
  fun reduce rw (icl as (i,cl)) =
    let val cl' = REWRITE rw icl
    in if clause_lits cl = clause_lits cl' then NONE else SOME (i,cl')
    end;

  fun purge ns set =
    let
      fun pred (n,_) = not (mem n ns)
      val SET {profile = {age = a, size = b}, clauses = c, subsumers = s,
               literals = r, equalities = e, subterms = p, ...} = set
      val c = List.filter pred c
      val set = update_clauses c set
      val set = update_profile {age = a, size = length c} set
      val set = update_subsumers (S.filter pred s) set
      val set = update_literals (N.filter pred r) set
      val set = update_equalities (T.filter pred e) set
      val set = update_subterms (T.filter pred p) set
    in
      set
    end;
in
  fun reducibles set units =
    let
      val SET {rewrites = w, clauses = c, ...} = set
      val w = R.reduce w
      val set = update_rewrites w set
      val icls = List.mapPartial (reduce w) c
      val set = purge (map fst icls) set
      val icls = List.mapPartial (strengthen set units) icls
    in
      (icls,set)
    end
end;

(* ------------------------------------------------------------------------- *)
(* Initialize clauses                                                        *)
(* ------------------------------------------------------------------------- *)

local
  fun simpl s = simp s o pair ~1;

  fun utility cl =
    case length (clause_lits cl) of 0 => ~1
    | 1 => if is_rewr cl then 0 else 1
    | n => n;

  val utilitywise = Int.compare;

  fun ins (parm : parameters) cl (icls,set,units,subs) =
    let
      val (icl as (_,cl), set) = stamp_id cl set
      val subs = if #subsumption parm = 0 then subs else add_subsum icl subs
    in
      (icl :: icls, set, add_unit cl units, subs)
    end;

  fun quality (parm : parameters) n (_,s,u,x) =
    let
      val rw = if n <= #simplification parm then simpl s else I
      val sb = if n <= #subsumption parm then ofilt (not o subsum x) else I
    in
      sb o total (beef_up u) o rw
    end;

  fun fac parm (cl,acc) =
    case quality parm 2 acc cl of NONE => acc | SOME cl => ins parm cl acc;

  fun factor parm (cl,acc) =
    case quality parm 1 acc cl of NONE => acc
    | SOME cl => foldl (fac parm) (ins parm cl acc) (FACTOR cl);
in
  fun initialize (cls,set,units) =
    let
      val SET {parm = (_,z), subsumers = subs, ...} = set
      val cls = sort_map utility utilitywise cls
      val (icls,set,units,_) = foldl (factor z) ([],set,units,subs) cls
      val (icls',set) =
        if List.exists (is_rewr o snd) icls then reducibles set units
        else ([],set)
    in
      (icls @ icls', set, units)
    end
    handle ERR_EXN _ => raise BUG "mlibClauseset.initialize" "shouldn't fail";
end;

(* ------------------------------------------------------------------------- *)
(* Add a clause into the set and derive consequences                         *)
(* ------------------------------------------------------------------------- *)

fun incorporate (icl as (i,cl)) set =
  let
    val SET {profile = {age = a, size = n}, clauses = c, subsumers = s,
             literals = r, equalities = e, subterms = p, ...} = set
    fun f (x |-> l, net) = N.insert (l |-> (i,x)) net
    fun g (x |-> t, net) = T.insert (t |-> (i,x)) net
    val set = update_profile {age = a, size = n + 1} set
    val set = update_clauses (icl :: c) set
    val set = update_subsumers (add_subsum icl s) set
    val set = update_literals (foldl f r (active_lits cl)) set
    val set = update_equalities (foldl g e (active_eqs cl)) set
    val set = update_subterms (foldl g p (active_tms cl)) set
    val SET {profile = {age = a, size = n}, clauses = c, subsumers = s,
             literals = r, equalities = e, subterms = p, ...} = set
    val _ = chatting 4 andalso
            chat ("\nactive_lits cl:\n" ^
                  (PP.pp_to_string (!LINE_LENGTH)
                   (pp_list (pp_maplet (pp_pair pp_clause pp_int) pp_formula))
                   (active_lits cl)) ^ "\n")
    val _ = chatting 3 andalso
            chat ("\nliteral set now:\n" ^ literals_to_string r ^ "\n")
  in
    set
  end;

fun deduce set =
  let
    fun resolv ci ((_,dj),acc) =
      case total (RESOLVE ci) dj of NONE => acc | SOME l => l :: acc

    fun resolvants r (ci |-> l, acc) =
      foldl (resolv ci) acc (N.unify r (negate l))

    fun paramod cib djp acc =
      case total (PARAMODULATE cib) djp of NONE => acc | SOME l => l :: acc

    fun paramods_from p (cib |-> t, acc) =
      foldl (uncurry (paramod cib o snd)) acc (T.unify p t)

    fun paramods_into e (cip |-> t, acc) =
      foldl (uncurry (C paramod cip o snd)) acc (T.unify e t)
  in
    fn cl =>
    let
      val SET {literals = r, equalities = e, subterms = p, ...} = set
      val res = foldl (resolvants r) [] (active_lits cl)
      val res = foldl (paramods_from p) res (active_eqs cl)
      val res = foldl (paramods_into e) res (active_tms cl)
    in
      rev res
    end
    handle ERR_EXN _ => raise BUG "deduce" "shouldn't fail"
  end;

fun add set units icl =
  let
    val set = incorporate icl set
    val cls = deduce set (FRESH_VARS (snd icl))
  in
    (cls,set)
  end;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing                                                           *)
(* ------------------------------------------------------------------------- *)

val pp_clauseset = pp_bracket "C<" ">" (pp_map size pp_int);

(* Quick testing
quotation := true;
installPP pp_formula;
installPP pp_term;
installPP pp_subst;
installPP pp_thm;
val th = AXIOM (map parse [`p(3,x,v)`, `q(x)`, `p(3,x,z)`]);
val th' = AXIOM (map parse [`~p(3,f(y),w)`, `~q(y)`, `~p(3,f(y),4)`]);
try (resolve_from (0,th)) (0,th');
try (resolve_from (2,th)) (0,th');
try (resolve_from (0,th)) (2,th');
try (resolve_from (2,th)) (2,th');
val r = add_literal th' empty_literals;
map #res (find_resolvants r th);
*)

end
