(* ========================================================================= *)
(* CLAUSE = ID + THEOREM + CONSTRAINTS                                       *)
(* Copyright (c) 2002-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

(*
app load ["Moscow", "mlibTerm", "mlibSubst", "mlibThm", "mlibUnits", "mlibTermorder"];
*)

(*
*)
structure mlibClause :> mlibClause =
struct

infix ## |->;

open mlibUseful mlibTerm mlibMatch;

structure S = Binaryset; local open Binaryset in end;
structure T = mlibTermorder; local open mlibTermorder in end;

type subst     = mlibSubst.subst;
type thm       = mlibThm.thm;
type units     = mlibUnits.units;
type termorder = T.termorder;

val |<>|          = mlibSubst.|<>|;
val term_subst    = mlibSubst.term_subst;
val formula_subst = mlibSubst.formula_subst;

(* ------------------------------------------------------------------------- *)
(* Chatting                                                                  *)
(* ------------------------------------------------------------------------- *)

val module = "mlibClause";
val () = traces := {module = module, alignment = I} :: !traces;
fun chatting l = tracing {module = module, level = l};
fun chat s = (trace s; true)

(* ------------------------------------------------------------------------- *)
(* Parameters                                                                *)
(* ------------------------------------------------------------------------- *)

type parameters =
  {term_order       : bool,
   literal_order    : bool,
   order_stickiness : int,
   termorder_parm   : mlibTermorder.parameters};

type 'a parmupdate = ('a -> 'a) -> parameters -> parameters;

val defaults =
  {term_order       = true,
   literal_order    = false,
   order_stickiness = 0,
   termorder_parm   = T.defaults};

fun update_term_order f (parm : parameters) : parameters =
  let
    val {term_order = t, literal_order = l,
         order_stickiness = s, termorder_parm = x} = parm
  in
    {term_order = f t, literal_order = l,
     order_stickiness = s, termorder_parm = x}
  end;

fun update_literal_order f (parm : parameters) : parameters =
  let
    val {term_order = t, literal_order = l,
         order_stickiness = s, termorder_parm = x} = parm
  in
    {term_order = t, literal_order = f l,
     order_stickiness = s, termorder_parm = x}
  end;

fun update_order_stickiness f (parm : parameters) : parameters =
  let
    val {term_order = t, literal_order = l,
         order_stickiness = s, termorder_parm = x} = parm
  in
    {term_order = t, literal_order = l,
     order_stickiness = f s, termorder_parm = x}
  end;

fun update_termorder_parm f (parm : parameters) : parameters =
  let
    val {term_order = t, literal_order = l,
         order_stickiness = s, termorder_parm = x} = parm
  in
    {term_order = t, literal_order = l,
     order_stickiness = s, termorder_parm = f x}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions                                                          *)
(* ------------------------------------------------------------------------- *)

fun ocons (SOME x) l = x :: l | ocons NONE l = l;

val new_id = new_int;

fun dest_refl lit =
  let
    val (x,y) = dest_eq lit
    val () = assert (x = y) (Error "dest_refl")
  in
    x
  end;

val is_refl = can dest_refl;

fun dest_peq lit = (I ## dest_eq) (dest_literal lit);
fun mk_peq (s,xy) = mk_literal (s, mk_eq xy);

fun psym lit =
  let
    val (s,(x,y)) = dest_peq lit
    val () = assert (x <> y) (Error "psym: refl")
  in
    mk_peq (s,(y,x))
  end;

(* ------------------------------------------------------------------------- *)
(* Objects are either predicates or sides of (dis)equations                  *)
(* ------------------------------------------------------------------------- *)

datatype obj = Pred of term | Eq of term;

fun obj_subst sub (Pred tm) = Pred (term_subst sub tm)
  | obj_subst sub (Eq tm) = Eq (term_subst sub tm);

fun dest_pred a = [Pred (dest_atom a)];

fun dest_eq_refl (x,y) = if x = y then [Eq x] else [Eq x, Eq y];

fun object_map f g l =
  let val a = literal_atom l
  in case total dest_eq a of NONE => f a | SOME x_y => g x_y
  end;

local val break = object_map dest_pred dest_eq_refl;
in val objects = foldl (fn (h,t) => break h @ t) [];
end;

(* ------------------------------------------------------------------------- *)
(* mlibTerm and literal ordering                                                 *)
(* ------------------------------------------------------------------------- *)

fun tm_order (parm : parameters) lrs c =
  let val c' = T.add_leqs lrs c
  in if #order_stickiness parm <= 0 then c else c'
  end;

fun term_order (parm : parameters) l r c =
  if l = r then raise Error "term_order: refl"
  else if #term_order parm then tm_order parm [(r,l)] c
  else c;

local
  fun f (Eq x) (Eq y) = SOME (x,y)
    | f (Eq x) (Pred y) = NONE
    | f (Pred x) (Eq y) = raise Error "obj_order: Pred > Eq"
    | f (Pred x) (Pred y) = SOME (x,y);
in
  fun obj_order {literal_order = false, ...} _ _ c = c
    | obj_order p xs ys c = tm_order p (List.mapPartial I (cartwith f ys xs)) c;
end;

fun lit_order {literal_order = false, ...} _ _ c = c
  | lit_order p l ls c =
  let val xs = object_map dest_pred dest_eq_refl l
  in obj_order p xs (objects ls) c
  end;

(* ------------------------------------------------------------------------- *)
(* Generic constraint interface                                              *)
(* ------------------------------------------------------------------------- *)

fun no_constraints ({termorder_parm = p, ...} : parameters) = T.empty p;

fun constraint_vars to = T.vars to;

fun constraint_subst sub to = T.subst sub to;

fun merge_constraints sub to1 to2 =
  (T.merge (T.subst sub to1) (T.subst sub to2), sub);

fun constraint_consistent (p : parameters) to =
  case T.consistent to of
    SOME to => if #order_stickiness p <= 1 then no_constraints p else to
  | NONE =>
    (chatting 1 andalso
     chat ("merge_orderings: resulting termorder is inconsistent:\n" ^
           PP.pp_to_string (!LINE_LENGTH) T.pp_termorder to);
     raise Error "consistent: inconsistent orderings");

fun constraint_subsumes sub to1 to2 =
  case total (T.subst sub) to1 of NONE => false
  | SOME to1 => T.subsumes to1 to2;

fun pp_constraints pp to = T.pp_termorder pp to;

(* ------------------------------------------------------------------------- *)
(* mlibClauses                                                                   *)
(* ------------------------------------------------------------------------- *)

type bits = {parm : parameters, id : int, thm : thm, order : termorder};

datatype clause = CL of parameters * int * thm * termorder * derivation
and derivation =
  Axiom
| mlibResolution of clause * clause
| Paramodulation of clause * clause
| Factor of clause;

fun mk_clause p th = CL (p, new_id (), th, no_constraints p, Axiom);

fun dest_clause (CL (p,i,th,to,_)) = {parm = p, id = i, thm = th, order = to};

fun derivation (CL (_,_,_,_,d)) = d;

val literals = mlibThm.clause o #thm o dest_clause;

fun free_vars cl =
  FVL (constraint_vars (#order (dest_clause cl))) (literals cl);

val is_empty = null o literals;

fun dest_rewr cl =
  let
    val {parm, thm, id, ...} = dest_clause cl
    val () = assert (#term_order parm) (Error "dest_rewr: no rewrs")
    val (x,y) = mlibThm.dest_unit_eq thm
    val () = assert (x <> y) (Error "dest_rewr: refl")
  in
    (id,thm)
  end;

val is_rewr = can dest_rewr;

fun rebrand parm (CL (p,i,th,_,d)) = CL (parm, i, th, no_constraints parm, d);

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val show_id = ref false;

val show_constraint = ref false;

local
  val pp_it = pp_pair pp_int mlibThm.pp_thm;
  val pp_tc = pp_pair mlibThm.pp_thm pp_constraints;
  val pp_itc = pp_triple pp_int mlibThm.pp_thm pp_constraints;
  fun f false false = pp_map (fn CL (_,_,th,_,_) => th) mlibThm.pp_thm
    | f true false = pp_map (fn CL (_,i,th,_,_) => (i,th)) pp_it
    | f false true = pp_map (fn CL (_,_,th,c,_) => (th,c)) pp_tc
    | f true true = pp_map (fn CL (_,i,th,c,_) => (i,th,c)) pp_itc;
in
  fun pp_clause pp cl = f (!show_id) (!show_constraint) pp cl;
end;

(* ------------------------------------------------------------------------- *)
(* Using ordering constraints to cut down the set of possible inferences     *)
(* ------------------------------------------------------------------------- *)

local
  fun fail _ = raise Error "gen_largest_lits: fail";

  fun gen_largest_lits f g (CL (p,i,th,c,d)) =
    let
      val lits = mlibThm.clause th
      val objs = objects lits
      fun collect (n,l) =
        let val xs = object_map f g l
        in (CL (p, i, th, obj_order p xs objs c, d), n) |-> l
        end
    in
      List.mapPartial (total collect) (enumerate 0 lits)
    end;
in
  val largest_noneq_lits = gen_largest_lits dest_pred fail;
  val largest_refl_lits = gen_largest_lits fail dest_eq_refl;
  val largest_lits = gen_largest_lits dest_pred dest_eq_refl;
end;

local
  fun gen_largest_eqs dest (CL (p,i,th,c,d)) =
    let
      val lits = mlibThm.clause th
      val objs = objects lits
      fun f ((n,l),acc) =
        case total dest l of
          NONE => acc
        | SOME (x,y) =>
          let
            fun g b z = (CL (p,i,th,obj_order p [Eq z] objs c,d), n, b) |-> z
          in
            if x = y then acc
            else ocons (total (g false) y) (ocons (total (g true) x) acc)
          end
    in
      foldl f [] (enumerate 0 lits)
    end;
in
  val largest_eqs = gen_largest_eqs dest_eq;
  val largest_peqs = gen_largest_eqs (snd o dest_peq);
end;

local
  fun harvest (c,i) =
    let
      fun f ((_ |-> Var _), acc) = acc
        | f ((_ |-> (Fn (":", [Var _, _]))), acc) = acc
        | f ((p |-> (t as Fn _)), acc) = ((c,i,p) |-> t) :: acc
    in
      C (foldl f)
    end;
in
  fun largest_tms (CL (p,i,th,c,d)) =
    let
      val lits = mlibThm.clause th
      val objs = objects lits
      fun ok x = total (obj_order p x objs) c
      fun collect ((n,l),acc) =
        let
          fun inc c = harvest (CL (p,i,th,c,d), n)
          fun f a =
            (case ok (dest_pred a) of NONE => acc
             | SOME c => inc c (literal_subterms a) acc)
          fun g (x,y) =
            if x = y then acc else
              let
                val acc =
                  case ok [Eq y] of NONE => acc
                  | SOME c => inc c (subterms [1] y) acc
                val acc =
                  case ok [Eq x] of NONE => acc
                  | SOME c => inc c (subterms [0] x) acc
              in
                acc
              end
        in
          object_map f g l
        end
    in
      foldl collect [] (enumerate 0 lits)
    end;
end;

fun drop_order (cl as CL (p,i,th,c,d)) =
  if T.null c then cl else CL (p, i, th, no_constraints p, d);

(* ------------------------------------------------------------------------- *)
(* Subsumption                                                               *)
(* ------------------------------------------------------------------------- *)

fun subsumes (cl as CL (_,_,th,c,_)) (cl' as CL (_,_,th',c',_)) =
  let val subs = mlibSubsume.subsumes1' (mlibThm.clause th) (mlibThm.clause th')
  in List.exists (fn sub => constraint_subsumes sub c c') subs
  end;

(* ------------------------------------------------------------------------- *)
(* mlibClause rewriting                                                          *)
(* ------------------------------------------------------------------------- *)

datatype rewrs = REWR of parameters * mlibRewrite.rewrs;

fun empty (parm as {termorder_parm = p, ...}) =
  REWR (parm, mlibRewrite.empty (mlibTermorder.compare (mlibTermorder.empty p)));

fun size (REWR (_,r)) = mlibRewrite.size r;

fun peek (REWR (p,r)) i =
  case mlibRewrite.peek r i of NONE => NONE
  | SOME (th,ort) => SOME (mlibThm.dest_unit_eq th, ort);

fun add cl rewrs =
  let
    val (i,th) = dest_rewr cl
    val REWR (parm,rw) = rewrs
  in
    REWR (parm, mlibRewrite.add (i,th) rw)
  end;

fun reduce (REWR (p,r)) =
  let val (r,l) = mlibRewrite.reduce' r in (REWR (p,r), l) end;

fun reduced (REWR (_,r)) = mlibRewrite.reduced r;

val pp_rewrs = pp_map (fn REWR (_,r) => r) mlibRewrite.pp_rewrs;

(* ------------------------------------------------------------------------- *)
(* Simplifying rules: these preserve the clause id                           *)
(* ------------------------------------------------------------------------- *)

fun INST sub (cl as CL (p,i,th,c,d)) =
  if mlibSubst.null sub then cl
  else CL (p, i, mlibThm.INST sub th, constraint_subst sub c, d);

fun FRESH_VARS cl =
  let
    val fvs = free_vars cl
    val gvs = new_vars (length fvs)
    val sub = mlibSubst.from_maplets (zipwith (curry op|->) fvs gvs)
  in
    INST sub cl
  end;

local
  fun match_occurs cl l r =
    let
      val v =
        case l of Var v => v
        | Fn (":", [Var v, _]) => v
        | _ => raise Error "match_occurs: not a variable"
      val () = assert (not (mem v (FVT r))) (Error "match_occurs")
      val sub = match l r
    in
      INST sub cl
    end;

  fun dest_neq cl lit =
    let
      val (l,r) = dest_eq (dest_neg lit)
      val () = assert (l <> r) (Error "dest_neq: reflexive")
    in
      case total (match_occurs cl l) r of SOME cl => cl
      | NONE => match_occurs cl r l
    end;

  fun neq_simp1 cl = first (total (dest_neq cl)) (literals cl);

  fun neq_simp cl = case neq_simp1 cl of NONE => cl | SOME cl => neq_simp cl;

  fun eq_factor (CL (p,i,th,c,d)) = CL (p, i, mlibThm.EQ_FACTOR th, c, d);
in
  fun NEQ_VARS cl =
    (case neq_simp1 cl of NONE => cl | SOME cl => eq_factor (neq_simp cl))
    handle Error _ => raise Bug "NEQ_VARS: shouldn't fail";
end;

fun DEMODULATE units (cl as CL (p,i,th,c,d)) =
  let
    val lits = mlibThm.clause th
    val th = mlibUnits.demod units th
  in
    if mlibThm.clause th = lits then cl else CL (p,i,th,c,d)
  end;

local
  fun mk_ord true c = T.compare c | mk_ord false _ = K NONE;

  fun rewr r ord th = mlibThm.EQ_FACTOR (mlibRewrite.rewrite r ord th)

  fun rewrite0 ord r (CL (p,i,th,c,d)) =
    case mlibRewrite.peek r i of SOME (th,_) => CL (p,i,th,c,d)
    | NONE => CL (p, i, rewr r (mk_ord ord c) (i,th), c, d);

  fun GEN_REWRITE _ (REWR ({term_order = false, ...}, _)) cl = cl
    | GEN_REWRITE ord (REWR (_,rw)) cl = rewrite0 ord rw cl;
in
  fun REWRITE rws cl =
    if not (chatting 1) then GEN_REWRITE true rws cl else
      let
        val res = GEN_REWRITE true rws cl
        val _ = literals cl <> literals res andalso chat
          ("\nREWRITE: " ^ PP.pp_to_string 60 pp_clause cl ^
           "\nto get: " ^ PP.pp_to_string 60 pp_clause res ^ "\n")
      in
        res
      end
      handle Error _ => raise Bug "mlibClause.REWRITE: shouldn't fail";

  fun QREWRITE rws cl =
    if not (chatting 1) then GEN_REWRITE false rws cl else
      let
        val res = GEN_REWRITE false rws cl
        val _ = literals cl <> literals res andalso chat
          ("\nQREWRITE: " ^ PP.pp_to_string 60 pp_clause cl ^
           "\nto get: " ^ PP.pp_to_string 60 pp_clause res ^ "\n")
      in
        res
      end
      handle Error _ => raise Bug "mlibClause.QREWRITE: shouldn't fail";
end;

(* ------------------------------------------------------------------------- *)
(* Ordered resolution and paramodulation: these generate new clause ids      *)
(* ------------------------------------------------------------------------- *)

(*
Factoring.

This implementation tries hard to keep the number of generated clauses
to a minimum, because performing simplification and subsumption
testing on each new clause is the bottleneck of the prover.

For each largest literal l in the input clause, we iterate through the
set of all substitutions s that unify l with at least one other
literal. Next apply the substitution s to the clause, and mark all the
literals that are now equal to l with a X, and the others with a -,
eg.

X - - X - - - X -

This is the 'hit list' for the new clause generated by (l,s). If we
ever see the same hit list for another new clause C generated by an
alternative (l',s'), then we can safely discard C immediately (since
(i) the substitution s' must be equal to s, and (ii) the ordering
constraints generated by setting l' to be a largest literal will be
identical to those generated by l).

With equality the situation becomes slightly more complicated. Now we
have two kinds of hits: one as before (called an Id hit); and one for
when we get a hit by applying symmetry to the (dis)equality literal
(called a Sym hit). So now we get a list like:

Sym - - Id - - - Sym -

But this gives the same new clause as the hit list

Id - - Sym - - - Id -

so we always normalize the hit list by flipping Ids and Syms (if
necessary) to make the first hit an Id.

Unfortunately, this quotient function loses too much information
because of ordering constraints. A (dis)equality literal M = N becomes
a largest literal because one of M or N is a largest object in the
clause. If M was the largest, then keep the first hit an Id. If N was
the largest, then make the first hit a Sym. If in the previous step we
had to flip all the hits to make the first hit an Id, then flip this
first hit too.
*)

local
  datatype hit = Id | Sym | Miss;
  fun hit_compare (Id,Id) = EQUAL | hit_compare (Id,_) = LESS
    | hit_compare (_,Id) = GREATER | hit_compare (Sym,Sym) = EQUAL
    | hit_compare (Sym,_) = LESS | hit_compare (_,Sym) = GREATER
    | hit_compare (Miss,Miss) = EQUAL;
  fun hit _ [] _ = Miss | hit a (h :: t) x = if h = x then a else hit Sym t x;
  fun first_hit true = Id | first_hit false = Sym;
  fun flip_hit Id = Sym | flip_hit Sym = Id | flip_hit Miss = Miss;
  fun norm_hits _ [] = raise Bug "norm_hits"
    | norm_hits lr (Miss :: rest) = norm_hits lr rest
    | norm_hits lr (Id :: rest) = first_hit lr :: rest
    | norm_hits lr (Sym :: rest) = map flip_hit (first_hit lr :: rest);
  fun calc_hits lr targs lits = norm_hits lr (map (hit Id targs) lits);

  val empty = (S.empty (lex_list_order hit_compare), []);
  fun is_new h (s,_) = not (S.member (s,h));
  fun insert (h,c) (s,l) = (S.add (s,h), ocons c l);
  fun finish (_,l) = l;

  fun assimilate s l l' =
    let
      val s' = unify_literals s l l'
      val () = assert (formula_subst s l <> formula_subst s l')
                      (Error "assimilate: already included")
    in
      s'
    end;

  fun FAC x lits sub cl =
    let
      val CL (p,_,th,c,_) = INST sub cl
      val th = mlibThm.EQ_FACTOR th
      val c = obj_order p [obj_subst sub x] (objects lits) c
      val c = constraint_consistent p c
    in
      CL (p, new_id (), th, c, Factor cl)
    end;

  fun final cl sub lr x targs =
    let
      fun f acc =
        let
          val lits = map (formula_subst sub) (literals cl)
          val () = assert (List.all (not o is_refl) lits) (Error "final: refl")
          val hits = calc_hits lr (map (formula_subst sub) targs) lits
          val () = assert (is_new hits acc) (Error "final: already seen")
        in
          (hits, total (FAC x lits sub) cl)
        end
    in
      fn acc =>
      if mlibSubst.null sub then acc
      else case total f acc of SOME x => insert x acc | NONE => acc
    end;

  fun factor ((cl,n) |-> lit) =
    let
      val x = object_map (Pred o dest_atom) (fn _ => raise Bug "factor") lit
      fun f [] acc = acc
        | f ((s,[]) :: paths) acc = f paths (final cl s true x [lit] acc)
        | f ((s, l :: ls) :: paths) acc =
        let
          val paths = (s,ls) :: paths
          val paths =
            case total (assimilate s l) lit of NONE => paths
            | SOME s' => (s',ls) :: paths
        in
          f paths acc
        end
    in
      f [(|<>|, List.drop (literals cl, n + 1))]
    end;

  fun factor_eq ((cl,n,b) |-> x) =
    let
      val x = Eq x
      val lit = List.nth (literals cl, n)
      val lit' = psym lit
      fun f [] acc = acc
        | f ((s,[]) :: paths) acc = f paths (final cl s b x [lit,lit'] acc)
        | f ((s, l :: ls) :: paths) acc =
        let
          val paths = (s,ls) :: paths
          val paths =
            case total (assimilate s l) lit of NONE => paths
            | SOME s' => (s',ls) :: paths
          val paths =
            case total (assimilate s l) lit' of NONE => paths
            | SOME s' => (s',ls) :: paths
        in
          f paths acc
        end
    in
      f [(|<>|, List.drop (literals cl, n + 1))]
    end;

  fun FACTOR' cl =
    let
      fun fac acc = foldl (uncurry factor) acc (largest_noneq_lits cl)
      fun fac_eq acc = foldl (uncurry factor_eq) acc (largest_peqs cl)
    in
      finish (fac (fac_eq empty))
    end
    handle Error _ => raise Bug "mlibClause.FACTOR: shouldn't fail";
in
  fun FACTOR cl =
    if not (chatting 1) then FACTOR' cl else
      let
        val res = FACTOR' cl
        val _ = not (null res) andalso chat
          ("\nFACTOR: " ^ PP.pp_to_string 60 pp_clause cl ^
           "\nto get: " ^ PP.pp_to_string 60 (pp_list pp_clause) res ^ "\n")
      in
        res
      end;
end;

local
  fun RESOLVE' (cl1 as CL (p,_,th1,c1,_), n1) (cl2 as CL (_,_,th2,c2,_), n2) =
    let
      val lit1 = List.nth (mlibThm.clause th1, n1)
      val lit2 = List.nth (mlibThm.clause th2, n2)
      val env = unify_literals |<>| lit1 (negate lit2)
      val (c,env) = merge_constraints env c1 c2
      val lit = mlibSubst.formula_subst env lit1
      val th1 = mlibThm.INST env th1
      val th2 = mlibThm.INST env th2
      val th = mlibThm.EQ_FACTOR (mlibThm.RESOLVE lit th1 th2)
      val c = lit_order p lit (mlibThm.clause th) c
      val c = constraint_consistent p c
    in
      CL (p, new_id (), th, c, mlibResolution (cl1,cl2))
    end;
in
  fun RESOLVE arg1 arg2 =
    if not (chatting 1) then RESOLVE' arg1 arg2 else
      let
        fun p res = chat
          ("\nRESOLVE:\n" ^
           PP.pp_to_string 70 (pp_pair pp_clause pp_int) arg1 ^ "\n" ^ 
           PP.pp_to_string 70 (pp_pair pp_clause pp_int) arg2 ^ "\n" ^
           PP.pp_to_string 70 (pp_sum pp_clause pp_string) res ^ "\n")
        val res =
          RESOLVE' arg1 arg2
          handle e as Error _ => (p (INR (report e)); raise e)
      in
        (p (INL res); res)
      end;
end;

local
  fun pick (0 :: _) (x,_) = x
    | pick (1 :: _) (_,y) = y
    | pick _ _ = raise Bug "into_obj: bad path";

  fun into_obj p = object_map (Pred o dest_atom) (Eq o pick p);

  fun PARAMODULATE' (cl1,n1,lr1) (cl2,n2,p2) =
    let
      val CL (p,_,th1,c1,_) = cl1
      val CL (_,_,th2,c2,_) = cl2
      val lit1 = List.nth (mlibThm.clause th1, n1)
      val lit2 = List.nth (mlibThm.clause th2, n2)
      val (l1,r1) = (if lr1 then I else swap) (dest_eq lit1)
      val t2 = literal_subterm p2 lit2
      val env = unify |<>| l1 t2
      val (c,env) = merge_constraints env c1 c2
      val (l1,r1) = Df (mlibSubst.term_subst env) (l1,r1)
      val c = term_order p l1 r1 c
      val (lit1,lit2) = Df (mlibSubst.formula_subst env) (lit1,lit2)
      val (th1,th2) = Df (mlibThm.INST env) (th1,th2)
      val c = obj_order p [Eq l1] (objects (mlibThm.clause th1)) c
      val c = obj_order p [into_obj p2 lit2] (objects (mlibThm.clause th2)) c
      val c = constraint_consistent p c
      val th =
        let val eq_th = mlibThm.EQUALITY lit2 p2 r1 lr1 th2
        in mlibThm.EQ_FACTOR (mlibThm.RESOLVE lit1 th1 eq_th)
        end
        handle Error _ => raise Bug "PARAMODULATE (rule): shouldn't fail"
    in
      CL (p, new_id (), th, c, Paramodulation (cl1,cl2))
    end;
in
  fun PARAMODULATE arg1 arg2 =
    if not (chatting 1) then PARAMODULATE' arg1 arg2 else
      let
        fun p res = chat
          ("\nPARAMODULATE:\n" ^
           PP.pp_to_string 70 (pp_triple pp_clause pp_int pp_bool) arg1 ^ "\n"^ 
           PP.pp_to_string 70 (pp_triple pp_clause pp_int (pp_list pp_int))arg2^
           "\n" ^ PP.pp_to_string 70 (pp_sum pp_clause pp_string) res ^ "\n")
        val res =
          PARAMODULATE' arg1 arg2
          handle e as Error _ => (p (INR (report e)); raise e)
      in
        (p (INL res); res)
      end;
end;

end
