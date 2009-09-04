(* ========================================================================= *)
(* PROCESSING SETS OF CLAUSES AT A TIME                                      *)
(* Copyright (c) 2002-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

(*
app load ["mlibClause", "mlibUnits"];
*)

(*
*)
structure mlibClauseset :> mlibClauseset =
struct

infix |-> ::> ##;

open mlibUseful mlibTerm mlibClause;

structure T = mlibTermnet; local open mlibTermnet in end;
structure N = mlibLiteralnet; local open mlibLiteralnet in end;
structure S = mlibSubsume; local open mlibSubsume in end;
structure U = mlibUnits; local open mlibUnits in end;

type 'a termnet    = 'a T.termnet;
type 'a literalnet = 'a N.literalnet;
type 'a subsume    = 'a S.subsume;

val |<>|          = mlibSubst.|<>|;
val op ::>        = mlibSubst.::>;
val term_subst    = mlibSubst.term_subst;
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

type filter = {subsumption : bool, simplification : int, splitting : bool}
type parameters = {prefactoring : filter, postfactoring : filter}

val defaults =
  {prefactoring = {subsumption = true, simplification = 2, splitting = false},
   postfactoring = {subsumption = true, simplification = 2, splitting = false}};

fun update_subsumption f (parm : filter) : filter =
  let val {subsumption = s, simplification = r, splitting = v} = parm
  in {subsumption = f s, simplification = r, splitting = v}
  end;

fun update_simplification f (parm : filter) : filter =
  let val {subsumption = s, simplification = r, splitting = v} = parm
  in {subsumption = s, simplification = f r, splitting = v}
  end;

fun update_splitting f (parm : filter) : filter =
  let val {subsumption = s, simplification = r, splitting = v} = parm
  in {subsumption = s, simplification = r, splitting = f v}
  end;

fun update_prefactoring f (parm : parameters) : parameters =
  let val {prefactoring = a, postfactoring = b} = parm
  in {prefactoring = f a, postfactoring = b}
  end;

fun update_postfactoring f (parm : parameters) : parameters =
  let val {prefactoring = a, postfactoring = b} = parm
  in {prefactoring = a, postfactoring = f b}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun ofilt _ NONE = NONE | ofilt p (s as SOME x) = if p x then s else NONE;

fun olist NONE = [] | olist (SOME x) = [x];

val intset_to_string = to_string (pp_map Intset.listItems (pp_list pp_int));

fun psym lit =
  let
    val (s,(x,y)) = (I ## dest_eq) (dest_literal lit)
    val () = assert (x <> y) (Error "psym: refl")
  in
    mk_literal (s, mk_eq (y,x))
  end;

fun add_unit cl units =
  let val {thm, ...} = dest_clause cl in U.add thm units end;

fun add_subsum cl = S.add (literals cl |-> cl);

fun clause_subterm c n p = literal_subterm p (List.nth (literals c, n));

val clause_to_string = to_string mlibClause.pp_clause;

val rewrs_to_string = to_string mlibClause.pp_rewrs;

val literals_to_string = to_string (N.pp_literalnet (pp_pair pp_clause pp_int));

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
       literals = N.empty {fifo = false}, equalities = T.empty {fifo = false},
       subterms = T.empty {fifo = false}};

fun parm (SET {parm, ...}) = parm;

fun ssize (SET {size, ...}) = size;

fun units (SET {units, ...}) = units;

fun rewrites (SET {rewrites, ...}) = rewrites;

fun clauses (SET {clauses, ...}) = clauses;

fun new_units u set = update_units u set;

(* ------------------------------------------------------------------------- *)
(* Simplify and strengthen clauses                                           *)
(* ------------------------------------------------------------------------- *)

fun qsimplify set = let val SET {rewrites = r, ...} = set in QREWRITE r end;

fun simplify set = let val SET {rewrites = r, ...} = set in REWRITE r end;

local
  fun taut c = assert (not (mlibCanon.tautologous (literals c))) (Error "taut");
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
    | Fn _ => raise Bug "new_pred: new_var didn't return a var";

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

  fun spl _ _ [] = raise Bug "split: empty"
    | spl cl acc [c] = rev (AX cl c :: acc)
    | spl cl acc (c1 :: c2 :: cs) =
    let val p = new_pred ()
    in spl cl (AX cl (c1 @ [p]) :: acc) ((Not p :: c2) :: cs)
    end;

  fun split_clause cl comps =
    let
      val _ = chatting 2 andalso chat "%"
      val cls = spl cl [] comps
      val _ = chatting 5 andalso chat
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

fun add_rewr cl set =
  if not (is_rewr cl) then (cl,set) else
    let
      val SET {rewrites = r, ...} = set
      val cl = mlibClause.drop_order cl
      val r = mlibClause.add cl r
      val _ = chatting 5 andalso
              chat ("\nrewrite set now:\n" ^ rewrs_to_string r ^ "\n")
      val set = update_rewrites r set
    in
      (cl,set)
    end;

fun add cl set =
  let
    val SET {size = n, units = u, clauses = c, subsumers = s, literals = l,
             equalities = e, subterms = p, ...} = set
    fun f (x |-> l, net) = N.insert (l |-> x) net
    fun g (x |-> t, net) = T.insert (t |-> x) net
    val set = update_size (n + 1) set
    val (cl,set) = add_rewr cl set
    val set = update_units (add_unit cl u) set
    val set = update_clauses (cl :: c) set
    val set = update_subsumers (add_subsum cl s) set
    val set = update_literals (foldl f l (largest_lits cl)) set
    val set = update_equalities (foldl g e (largest_eqs cl)) set
    val set = update_subterms (foldl g p (largest_tms cl)) set
    val SET {size = n, units = u, clauses = c, subsumers = s, literals = l,
             equalities = e, subterms = p, ...} = set
    val _ = chatting 7 andalso
            chat ("\nlargest_lits cl:\n" ^
                  (PP.pp_to_string (!LINE_LENGTH)
                   (pp_list (pp_maplet (pp_pair pp_clause pp_int) pp_formula))
                   (largest_lits cl)) ^ "\n")
    val _ = chatting 6 andalso
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
      val SET {literals = l, equalities = e, subterms = p, ...} = set
      val res = []
      val res = foldl (resolvants l) res (largest_lits cl)
      val res = foldl (paramods_from p) res (largest_eqs cl)
      val res = foldl (paramods_into e) res (largest_tms cl)
    in
      rev res
    end
    handle Error _ => raise Bug "deduce: shouldn't fail"
  end;

(* ------------------------------------------------------------------------- *)
(* Extract clauses that can be simplified                                    *)
(* ------------------------------------------------------------------------- *)

local
  fun clause_mem cl s =
    let val {id, ...} = dest_clause cl in Intset.member (s,id) end;

  fun clause_reducibles set =
    let
      val SET {rewrites = r, clauses = c, ...} = set
      fun pred x = let val y = REWRITE r x in literals x <> literals y end
      val d = List.filter pred c
    in
      Intset.addList (Intset.empty, map (#id o dest_clause) d)
    end;

  fun valid_rw l ro ord tm =
    let
      val sub = mlibMatch.match l tm
    in
      case ro of NONE => () | SOME r =>
        assert (mlibTermorder.compare ord (tm, term_subst sub r) = SOME GREATER)
        (Error "rewr_reducibles: order violation")
    end;

  fun consider_rw l ro ((c,n,p),s) =
    let
      val {id, order, ...} = dest_clause c
    in
      if Intset.member (s,id) then s
      else if not (can (valid_rw l ro order) (clause_subterm c n p)) then s
      else Intset.add (s,id)
    end;

  fun rewr_reducibles set changed_redexes =
    let
      val SET {rewrites = r, clauses = c, subterms = p, ...} = set

      fun pk i =
        case peek r i of SOME x => x
        | NONE => raise Bug "rewr_reducibles: vanishing rewrite"

      fun red l ro s = foldl (consider_rw l ro) s (T.matched p l)

      fun reds (i,s) =
        case pk i of
          ((l,r),mlibRewrite.LtoR) => red l NONE s
        | ((l,r),mlibRewrite.RtoL) => red r NONE s
        | ((l,r),mlibRewrite.Both) => red l (SOME r) (red r (SOME l) s)

      fun unchanged i th =
        case peek r i of NONE => false
        | SOME (l_r,_) => l_r = mlibThm.dest_unit_eq th

      fun mk_init_id (cl,(s,s')) =
        case total dest_rewr cl of NONE => (s,s')
        | SOME (i,th) =>
          (Intset.add (s,i), if unchanged i th then Intset.add (s',i) else s')

      val (s_init,s_id) = foldl mk_init_id (Intset.empty,Intset.empty) c

      fun quick i = snd (pk i) <> mlibRewrite.Both

      val changed_redexes = op@ (List.partition quick changed_redexes)
    in
      Intset.difference (foldl reds s_init changed_redexes, s_id)
    end;

  fun reducibles set l =
    if not (chatting 4) then
      if ssize set <= length l then clause_reducibles set
      else rewr_reducibles set l
    else
      let
        val SET {clauses = c, rewrites = r, ...} = set
        fun pk i =
          case List.find (fn cl => #id (dest_clause cl) = i) c of SOME cl => cl
          | NONE => raise Bug "reducibles: not a clause"
        fun i_to_string f =
          to_string (pp_list pp_clause) o map (f o pk) o Intset.listItems
        val _ = chat "finding rewritable clauses in the clause set\n"
        val clause_i = clause_reducibles set
        val rewr_i = rewr_reducibles set l
        val () =
          if Intset.equal (clause_i,rewr_i) then () else
            (print ("clause_reducibles = " ^ intset_to_string clause_i ^ "\n" ^
                    i_to_string I clause_i ^ " -->\n" ^
                    i_to_string (REWRITE r) clause_i ^ "\n" ^
                    "rewr_reducibles = " ^ intset_to_string rewr_i ^ "\n" ^
                    i_to_string I rewr_i ^ " -->\n" ^
                    i_to_string (REWRITE r) rewr_i ^ "\n");
             raise Bug "purge_reducibles: rewr <> clause")
      in
        rewr_i
      end;

  fun purge ns set =
    let
      fun pred cl = not (clause_mem cl ns)
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
  fun purge_reducibles (set as SET {rewrites = r, ...}) =
    if reduced r then ([],set) else
      let
        val _ = chatting 2 andalso chat "="
        val _ = chatting 4 andalso chat "\ninter-reducing the clause set\n"
        val (r,l) = mlibClause.reduce r
        val set = update_rewrites r set
        val i = reducibles set l
        val _ = chatting 2 andalso chat (int_to_string (Intset.numItems i))
      in
        if Intset.numItems i = 0 then ([],set) else
          let
            val SET {clauses = c, ...} = set
            val cls = List.filter (fn cl => clause_mem cl i) c
            val cls = map (REWRITE r) cls
            val set = purge i set
          in
            (cls,set)
          end
      end
      handle Error _ => raise Bug "purge_reducibles: shouldn't fail";
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

  fun is_subsumption (parm : parameters) =
    #subsumption (#prefactoring parm) orelse #subsumption (#postfactoring parm);

  fun ins (parm : parameters) cl (cls,set,subs) =
    let
      val (cl,set) = add_rewr cl set
      val set = update_units (add_unit cl (units set)) set
      val subs = if is_subsumption parm then add_subsum cl subs else subs
    in
      (cl :: cls, set, subs)
    end;

  fun quality (parm : parameters) post (_,s,x) =
    let
      val {subsumption, simplification, splitting} =
        if post then #postfactoring parm else #prefactoring parm
      val rw =
        case simplification of 0 => I | 1 => qsimplify s | _ => simplify s
      val sb = if subsumption then ofilt (not o subsum x) else I
      val sp = if splitting then List.concat o map split else I
    in
      sp o olist o sb o strengthen s o rw
    end;

  fun fac1 parm (cl,acc) =
    foldl (fn (cl,acc) => ins parm cl acc) acc (quality parm true acc cl);

  fun facl parm (cl,acc) =
    foldl (fn (cl,acc) => foldl (fac1 parm) (ins parm cl acc) (FACTOR cl)) acc
    (quality parm false acc cl);

  fun factor' acc set [] = (rev acc, set)
    | factor' acc set cls =
    let
      val SET {parm = (_,z), subsumers = subs, ...} = set
      val cls = sort_map utility utilitywise cls
      val (cls,set,_) = foldl (facl z) ([],set,subs) cls
      val (cls',set) = purge_reducibles set
    in
      factor' (cls @ acc) set cls'
    end;
in
  fun factor cls set =
    let
      val _ = chatting 2 andalso chat ("-" ^ int_to_string (length cls))
      val res as (cls,_) = factor' [] set cls
      val _ = chatting 1 andalso chat ("+" ^ int_to_string (length cls))
    in
      res
    end
    handle Error _ => raise Bug "mlibClauseset.initialize: shouldn't fail";
end;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing                                                           *)
(* ------------------------------------------------------------------------- *)

val pp_clauseset = pp_bracket "C<" ">" (pp_map ssize pp_int);

(* ------------------------------------------------------------------------- *)
(* Rebinding for signature                                                   *)
(* ------------------------------------------------------------------------- *)

val size = ssize;

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
