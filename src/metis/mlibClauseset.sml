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
   simplification : int,
   splitting      : int};

val defaults =
  {subsumption    = 2,
   simplification = 2,
   splitting      = 0};

fun update_subsumption f (parm : parameters) : parameters =
  let val {subsumption = s, simplification = r, splitting = v} = parm
  in {subsumption = f s, simplification = r, splitting = v}
  end;

fun update_simplification f (parm : parameters) : parameters =
  let val {subsumption = s, simplification = r, splitting = v} = parm
  in {subsumption = s, simplification = f r, splitting = v}
  end;

fun update_splitting f (parm : parameters) : parameters =
  let val {subsumption = s, simplification = r, splitting = v} = parm
  in {subsumption = s, simplification = r, splitting = f v}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun ofilt _ NONE = NONE | ofilt p (s as SOME x) = if p x then s else NONE;

fun olist NONE = [] | olist (SOME x) = [x];

fun psym lit =
  let
    val (s,(x,y)) = (I ## dest_eq) (dest_literal lit)
    val () = assert (x <> y) (ERR "psym" "refl")
  in
    mk_literal (s, mk_eq (y,x))
  end;

fun add_unit cl units =
  let val {thm, ...} = dest_clause cl in U.add thm units end;

fun add_subsum cl = S.add (literals cl |-> cl);

fun clause_to_string cl = PP.pp_to_string (!LINE_LENGTH) mlibClause.pp_clause cl;

fun rewrs_to_string r = PP.pp_to_string (!LINE_LENGTH) mlibClause.pp_rewrs r;

fun literals_to_string l =
  PP.pp_to_string (!LINE_LENGTH)
  (N.pp_literalnet (pp_pair pp_clause pp_int)) l;

(* ------------------------------------------------------------------------- *)
(* mlibClause sets                                                               *)
(* ------------------------------------------------------------------------- *)

datatype clauseset = SET of
  {parm       : mlibClause.parameters * parameters,
   size       : int,
   units      : U.units,
   rewrites   : rewrs,
   clauses    : clause list,
   subsumers  : clause subsume,
   literals   : (clause * int) literalnet,
   equalities : (clause * int * bool) termnet,
   subterms   : (clause * int * int list) termnet};

fun update_size n set =
  let
    val SET {parm = z, size = _, units = u, rewrites = r, clauses = c,
             subsumers = s, literals = l, equalities = e, subterms = p} = set
  in
    SET {parm = z, size = n, units = u, rewrites = r, clauses = c,
         subsumers = s, literals = l, equalities = e, subterms = p}
  end;

fun update_units u set =
  let
    val SET {parm = z, size = n, units = _, rewrites = r, clauses = c,
             subsumers = s, literals = l, equalities = e, subterms = p} = set
  in
    SET {parm = z, size = n, units = u, rewrites = r, clauses = c,
         subsumers = s, literals = l, equalities = e, subterms = p}
  end;

fun update_rewrites r set =
  let
    val SET {parm = z, size = n, units = u, rewrites = _, clauses = c,
             subsumers = s, literals = l, equalities = e, subterms = p} = set
  in
    SET {parm = z, size = n, units = u, rewrites = r, clauses = c,
         subsumers = s, literals = l, equalities = e, subterms = p}
  end;

fun update_clauses c set =
  let
    val SET {parm = z, size = n, units = u, rewrites = r, clauses = _,
             subsumers = s, literals = l, equalities = e, subterms = p} = set
  in
    SET {parm = z, size = n, units = u, rewrites = r, clauses = c,
         subsumers = s, literals = l, equalities = e, subterms = p}
  end;

fun update_subsumers s set =
  let
    val SET {parm = z, size = n, units = u, rewrites = r, clauses = c,
             subsumers = _, literals = l, equalities = e, subterms = p} = set
  in
    SET {parm = z, size = n, units = u, rewrites = r, clauses = c,
         subsumers = s, literals = l, equalities = e, subterms = p}
  end;

fun update_literals l set =
  let
    val SET {parm = z, size = n, units = u, rewrites = r, clauses = c,
             subsumers = s, literals = _, equalities = e, subterms = p} = set
  in
    SET {parm = z, size = n, units = u, rewrites = r, clauses = c,
         subsumers = s, literals = l, equalities = e, subterms = p}
  end;

fun update_equalities e set =
  let
    val SET {parm = z, size = n, units = u, rewrites = r, clauses = c,
             subsumers = s, literals = l, equalities = _, subterms = p} = set
  in
    SET {parm = z, size = n, units = u, rewrites = r, clauses = c,
         subsumers = s, literals = l, equalities = e, subterms = p}
  end;

fun update_subterms p set =
  let
    val SET {parm = z, size = n, units = u, rewrites = r, clauses = c,
             subsumers = s, literals = l, equalities = e, subterms = _} = set
  in
    SET {parm = z, size = n, units = u, rewrites = r, clauses = c,
         subsumers = s, literals = l, equalities = e, subterms = p}
  end;

(* ------------------------------------------------------------------------- *)
(* Basic operations                                                          *)
(* ------------------------------------------------------------------------- *)

fun empty (cparm,parm) =
  SET {parm = (cparm,parm), size = 0, units = U.empty,
       rewrites = mlibClause.empty cparm, clauses = [], subsumers = S.empty (),
       literals = N.empty (), equalities = T.empty (), subterms = T.empty ()};

fun clear (SET {parm = z, units = u, rewrites = r, ...}) =
  SET {parm = z, size = 0, units = u, rewrites = r, clauses = [],
       subsumers = S.empty (), literals = N.empty (),
       equalities = T.empty (), subterms = T.empty ()};
    
fun size (SET {size, ...}) = size;

fun units (SET {units, ...}) = units;

fun rewrites (SET {rewrites, ...}) = rewrites;

fun clauses (SET {clauses, ...}) = clauses;

fun new_units u set = update_units u set;

(* ------------------------------------------------------------------------- *)
(* Simplify and strengthen clauses                                           *)
(* ------------------------------------------------------------------------- *)

fun simplify set = let val SET {rewrites = r, ...} = set in REWRITE r end;

local
  fun taut c = assert (not (mlibCanon.tautologous (literals c))) (ERR "taut" "");
  fun beef_up (SET {units, ...}) cl =
    let
      val () = taut cl
      val cl = NEQ_VARS cl
      val () = taut cl
      val cl = DEMODULATE units cl
    in
      cl
    end;
in
  fun strengthen set = total (beef_up set);
end;

(* ------------------------------------------------------------------------- *)
(* mlibClause splitting                                                          *)
(* ------------------------------------------------------------------------- *)

local
  fun new_pred () =
    case new_var () of Var v => Atom (Fn (v, []))
    | Fn _ => raise BUG "new_pred" "new_var didn't return a var";

  fun AX cl lits = mk_clause (#parm (dest_clause cl)) (mlibThm.AXIOM lits);

  fun new l = Binaryset.addList (Binaryset.empty String.compare, l);
  fun disjoint s t = Binaryset.isEmpty (Binaryset.intersection (s,t));
  fun union s t = Binaryset.union (s,t);

  fun add_lits lits shar = foldl (fn ((_,x),l) => x :: l) lits shar;
  fun add_vars vars shar = foldl (fn ((v,_),s) => union v s) vars shar;

  fun dfs acc lits vars vlits =
    case List.partition (disjoint vars o fst) vlits of
      (_,[]) => components (rev lits :: acc) vlits
    | (disj,shar) => dfs acc (add_lits lits shar) (add_vars vars shar) disj
  and components acc [] = acc
    | components acc ((vs,lit) :: rest) = dfs acc [lit] vs rest;

  fun spl _ _ [] = raise BUG "split" "empty"
    | spl cl acc [c] = rev (AX cl c :: acc)
    | spl cl acc (c1 :: c2 :: cs) =
    let val p = new_pred ()
    in spl cl (AX cl (c1 @ [p]) :: acc) ((Not p :: c2) :: cs)
    end;

  fun split_clause cl comps =
    let
      val _ = chatting 1 andalso chat "%"
      val cls = spl cl [] comps
      val _ = chatting 2 andalso chat
        ("\nsplit: components of clause " ^ clause_to_string cl ^ ":\n"
         ^ PP.pp_to_string (!LINE_LENGTH) (pp_list pp_clause) cls ^ "\n")
    in
      cls
    end;
in
  fun split cl =
    let
      val lits = map (fn lit => (FV lit, lit)) (literals cl)
      val (glits,vlits) = List.partition (null o fst) lits
      val glits = map snd glits
      val vlits = map (new ## I) vlits
    in
      case components [] vlits of [] => [cl]
      | [_] => [cl]
      | l => split_clause cl (rev (if null glits then l else glits :: l))
    end
end;

(* ------------------------------------------------------------------------- *)
(* Forward subsumption checking                                              *)
(* ------------------------------------------------------------------------- *)

fun subsum subs cl =
  let
    fun f (sub,c) =
      case total (INST sub) c of NONE => false | SOME d => subsumes d cl
  in
    mlibStream.exists f (S.subsumes' subs (literals cl))
  end;

fun subsumed (SET {subsumers, ...}) = subsum subsumers;

(* ------------------------------------------------------------------------- *)
(* Add a clause into the set                                                 *)
(* ------------------------------------------------------------------------- *)

fun add cl set =
  let
    val SET {size = n, clauses = c, subsumers = s, literals = l,
             equalities = e, subterms = p, ...} = set
    fun f (x |-> l, net) = N.insert (l |-> x) net
    fun g (x |-> t, net) = T.insert (t |-> x) net
    val set = update_size (n + 1) set
    val set = update_clauses (cl :: c) set
    val set = update_subsumers (add_subsum cl s) set
    val set = update_literals (foldl f l (largest_lits cl)) set
    val set = update_equalities (foldl g e (largest_eqs cl)) set
    val set = update_subterms (foldl g p (largest_tms cl)) set
    val SET {size = n, clauses = c, subsumers = s, literals = l,
             equalities = e, subterms = p, ...} = set
    val _ = chatting 4 andalso
            chat ("\nlargest_lits cl:\n" ^
                  (PP.pp_to_string (!LINE_LENGTH)
                   (pp_list (pp_maplet (pp_pair pp_clause pp_int) pp_formula))
                   (largest_lits cl)) ^ "\n")
    val _ = chatting 3 andalso
            chat ("\nliteral set now:\n" ^ literals_to_string l ^ "\n")
  in
    set
  end;

(* ------------------------------------------------------------------------- *)
(* Derive consequences of a clause                                           *)
(* ------------------------------------------------------------------------- *)

fun deduce set =
  let
    fun resolv ci (dj,acc) =
      case total (RESOLVE ci) dj of NONE => acc | SOME l => l :: acc

    fun resolvants r (ci |-> l, acc) =
      foldl (resolv ci) acc (N.unify r (negate l))

    fun paramod cib djp acc =
      case total (PARAMODULATE cib) djp of NONE => acc | SOME l => l :: acc

    fun paramods_from p (cib |-> t, acc) =
      foldl (uncurry (paramod cib)) acc (T.unify p t)

    fun paramods_into e (cip |-> t, acc) =
      foldl (uncurry (C paramod cip)) acc (T.unify e t)
  in
    fn cl =>
    let
      val SET {literals = r, equalities = e, subterms = p, ...} = set
      val res = []
      val res = foldl (resolvants r) res (largest_lits cl)
      val res = foldl (paramods_from p) res (largest_eqs cl)
      val res = foldl (paramods_into e) res (largest_tms cl)
    in
      rev res
    end
    handle ERR_EXN _ => raise BUG "deduce" "shouldn't fail"
  end;

(* ------------------------------------------------------------------------- *)
(* Extract clauses that can be simplified                                    *)
(* ------------------------------------------------------------------------- *)

local
  fun reduce rw cl =
    let val cl' = REWRITE rw cl
    in if literals cl = literals cl' then NONE else SOME cl'
    end;

  fun purge [] set = set
    | purge ns set =
    let
      fun pred cl = let val {id, ...} = dest_clause cl in not (mem id ns) end
      val SET {clauses = c, subsumers = s, literals = l,
               equalities = e, subterms = p, ...} = set
      val c = List.filter pred c
      val set = update_clauses c set
      val set = update_size (length c) set
      val set = update_subsumers (S.filter pred s) set
      val set = update_literals (N.filter (pred o fst) l) set
      val set = update_equalities (T.filter (pred o #1) e) set
      val set = update_subterms (T.filter (pred o #1) p) set
    in
      set
    end;
in
  fun reducibles set =
    let
      val SET {rewrites = r, clauses = c, ...} = set
      val r = mlibClause.reduce r
      val set = update_rewrites r set
      val cls = List.mapPartial (reduce r) c
      val set = purge (map (#id o dest_clause) cls) set
      val cls = List.mapPartial (strengthen set) cls
    in
      (cls,set)
    end
end;

(* ------------------------------------------------------------------------- *)
(* Initialize derived clauses                                                *)
(* ------------------------------------------------------------------------- *)

local
  fun utility cl =
    case length (literals cl) of 0 => ~1
    | 1 => if is_rewr cl then 0 else 1
    | n => n;

  val utilitywise = Int.compare;

  fun ins (parm : parameters) cl (cls,set,subs) =
    let
      val SET {units = u, rewrites = r, ...} = set
      val is_rw = is_rewr cl
      val (cl,r) = if is_rw then mlibClause.add cl r else (cl,r)
      val _ = chatting 2 andalso is_rw andalso
              chat ("\nrewrite set now:\n" ^ rewrs_to_string r ^ "\n")
      val set = update_units (add_unit cl u) set
      val set = update_rewrites r set
      val subs = if #subsumption parm = 0 then subs else add_subsum cl subs
    in
      (cl :: cls, set, subs)
    end;

  fun quality (parm : parameters) n (_,s,x) =
    let
      val rw = if n <= #simplification parm then simplify s else I
      val sb = if n <= #subsumption parm then ofilt (not o subsum x) else I
      val sp = if n <= #splitting parm then List.concat o map split else I
    in
      sp o olist o sb o strengthen s o rw
    end;

  fun fac parm (cl,acc) =
    foldl (fn (cl,acc) => ins parm cl acc) acc (quality parm 2 acc cl);
      
  fun factor parm (cl,acc) =
    foldl (fn (cl,acc) => foldl (fac parm) (ins parm cl acc) (FACTOR cl)) acc
    (quality parm 1 acc cl);
          
  fun init acc set [] = (rev acc, set)
    | init acc set cls =
    let
      val SET {parm = (_,z), subsumers = subs, ...} = set
      val cls = sort_map utility utilitywise cls
      val (cls,set,_) = foldl (factor z) ([],set,subs) cls
      val (cls',set) =
        if List.exists is_rewr cls then reducibles set else ([],set)
      val (cls1,cls2) = List.partition (fn c => length (literals c) <= 1) cls'
    in
      init (cls1 @ cls @ acc) set cls2
    end;
in
  fun initialize cls set = init [] set cls
    handle ERR_EXN _ => raise BUG "mlibClauseset.initialize" "shouldn't fail";
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
