(* ========================================================================= *)
(* CLAUSE = THEOREM + CONSTRAINTS                                            *)
(* Created by Joe Hurd, September 2002                                       *)
(* ========================================================================= *)

(*
app load ["Moscow", "mlibTerm", "mlibSubst", "mlibThm", "mlibUnits", "mlibTermorder"];
*)

(*
*)
structure mlibClause :> mlibClause =
struct

infix ## |->;

open mlibUseful mlibTerm mlibMatch mlibThm;

structure S = Binaryset; local open Binaryset in end;
structure T = mlibTermorder; local open mlibTermorder in end;

type subst     = mlibSubst.subst;
type units     = mlibUnits.units;
type termorder = T.termorder;

val |<>|          = mlibSubst.|<>|;
val term_subst    = mlibSubst.term_subst;
val formula_subst = mlibSubst.formula_subst;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val module = "mlibClause";
val () = traces := {module = module, alignment = I} :: !traces;
fun chatting l = tracing {module = module, level = l};
fun chat s = (trace s; true)

(* ------------------------------------------------------------------------- *)
(* Parameters.                                                               *)
(* ------------------------------------------------------------------------- *)

type parameters =
  {literal_order  : bool,
   term_order     : bool,
   termorder_parm : mlibTermorder.parameters};

type 'a Parmupdate = ('a -> 'a) -> parameters -> parameters;

val defaults =
  {literal_order  = true,
   term_order     = true,
   termorder_parm = T.defaults};

fun update_literal_order f (parm : parameters) : parameters =
  let val {literal_order = l, term_order = t, termorder_parm = x} = parm
  in {literal_order = f l, term_order = t, termorder_parm = x}
  end;

fun update_term_order f (parm : parameters) : parameters =
  let val {literal_order = l, term_order = t, termorder_parm = x} = parm
  in {literal_order = l, term_order = f t, termorder_parm = x}
  end;

fun update_termorder_parm f (parm : parameters) : parameters =
  let val {literal_order = l, term_order = t, termorder_parm = x} = parm
  in {literal_order = l, term_order = t, termorder_parm = f x}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun ocons (SOME x) l = x :: l | ocons NONE l = l;

fun dest_refl lit =
  let
    val (x,y) = dest_eq lit
    val () = assert (x = y) (ERR "dest_refl" "")
  in
    x
  end;

val is_refl = can dest_refl;

fun psym lit =
  let
    val (s,(x,y)) = (I ## dest_eq) (dest_literal lit)
    val () = assert (x <> y) (ERR "psym" "refl")
  in
    mk_literal (s, mk_eq (y,x))
  end;

fun object_map f g l =
  let val a = literal_atom l
  in case total dest_eq a of NONE => f a | SOME xy => g xy
  end;

local val break = object_map (fn x => [dest_atom x]) (fn (x,y) => [x,y]);
in val objects = foldl (fn (h,t) => break h @ t) [];
end;

(* ------------------------------------------------------------------------- *)
(* Coherence constraints.                                                    *)
(* ------------------------------------------------------------------------- *)

type coherent = formula list * term list;

fun new_coherent g = (g, map Var (FVL [] g));

fun coherent_vars vs c = FVL vs (List.concat (map (map Atom o snd) c));

fun coherent_subst sub c = map (I ## map (mlibSubst.term_subst sub)) c;

local
  fun mcoherents c (a as (g,ts), (d,r)) =
     case List.find (equal g o fst) c of NONE => (a :: d, r)
     | SOME (_,ts') => (d, zip ts' ts @ r);
in
  fun merge_coherents sub c1 c2 =
    let
      val (c,sync) = foldl (mcoherents c2) (c2,[]) c1
      val sub = unifyl sub sync
    in
      (coherent_subst sub c, sub)
    end;
end;

fun coherent_consistent c = c;

local
  fun csubsumes c ((g,ts),sub) =
    case List.find (equal g o fst) c of NONE => raise ERR "csubsumes" ""
    | SOME (_,ts') => matchl sub (zip ts ts');
in
  fun coherent_subsumes sub c1 c2 = foldl (csubsumes c2) sub c1;
end;

(* ------------------------------------------------------------------------- *)
(* Ordering constraints.                                                     *)
(* ------------------------------------------------------------------------- *)

fun no_ordering ({termorder_parm = p, ...} : parameters) = T.empty p;

fun ordering_vars to = T.vars to;

fun ordering_subst sub to = T.subst sub to;

fun merge_orderings sub to1 to2 = T.subst sub (T.merge to1 to2);

fun ordering_consistent to =
  case T.consistent to of SOME to => to
  | NONE =>
    (chatting 1 andalso
     chat ("merge_orderings: resulting termorder is inconsistent:\n" ^
           PP.pp_to_string (!LINE_LENGTH) T.pp_termorder to);
     raise ERR "consistent" "inconsistent orderings");

fun ordering_subsumes sub to1 to2 =
  case total (ordering_subst sub) to1 of NONE => false
  | SOME to1 => T.subsumes to1 to2;

(* ------------------------------------------------------------------------- *)
(* Generic constraints.                                                      *)
(* ------------------------------------------------------------------------- *)

type constraints = {coherents : coherent list, ordering : termorder};

fun update_coherents c (con : constraints) =
  let val {coherents = _, ordering = t} = con
  in {coherents = c, ordering = t}
  end;

fun update_ordering t (con : constraints) =
  let val {coherents = c, ordering = _} = con
  in {coherents = c, ordering = t}
  end;

fun no_constraints p : constraints = {coherents = [], ordering = no_ordering p};

fun new_coherent_constraints p g : constraints =
  update_coherents [new_coherent g] (no_constraints p);

fun constraint_vars (con : constraints) =
  let
    val {coherents = c, ordering = t} = con
  in
    coherent_vars (ordering_vars t) c
  end;

fun constraint_subst sub con =
  let
    val {coherents = c, ordering = t} = con
    val c = coherent_subst sub c
    val t = ordering_subst sub t
  in
    {coherents = c, ordering = t}
  end;

fun merge_constraints sub con1 con2 =
  let
    val {coherents = c1, ordering = t1} = con1
    val {coherents = c2, ordering = t2} = con2
    val (c,sub) = merge_coherents sub c1 c2
    val t = merge_orderings sub t1 t2
  in
    ({coherents = c, ordering = t}, sub)
  end;

fun constraint_consistent con =
  let
    val {coherents = c, ordering = t} = con
    val c = coherent_consistent c
    val t = ordering_consistent t
  in
    {coherents = c, ordering = t}
  end;

fun constraint_subsumes sub con1 con2 =
  let
    val {coherents = c1, ordering = t1} = con1
    val {coherents = c2, ordering = t2} = con2
  in
    case total (coherent_subsumes sub c1) c2 of NONE => false
    | SOME sub => ordering_subsumes sub t1 t2
  end;

val pp_constraints =
  pp_map (fn {coherents = c, ordering = t} => (c,t))
  (pp_pair
   (pp_list (pp_pair (pp_list pp_formula) (pp_list pp_term))) T.pp_termorder);

(* ------------------------------------------------------------------------- *)
(* Making use of the term ordering.                                          *)
(* ------------------------------------------------------------------------- *)

fun tm_order lrs c = update_ordering (T.add_leqs lrs (#ordering c)) c;

fun term_order (parm : parameters) l r c =
  if l = r then raise ERR "term_order" "refl"
  else if #term_order parm then tm_order [(r,l)] c
  else c;

fun obj_order (parm : parameters) xs ys c =
  if #literal_order parm then tm_order (cart ys xs) c else c;

fun lit_order {literal_order = false, ...} _ _ c = c
  | lit_order (p as {literal_order = true, ...}) l ls c =
  let
    fun f (x,y) = if x = y then x else raise BUG "lit_order" "no eqs"
    val x = object_map dest_atom f l
  in
    obj_order p [x] (objects ls) c
  end;

(* ------------------------------------------------------------------------- *)
(* mlibClauses.                                                                  *)
(* ------------------------------------------------------------------------- *)

datatype clause = CL of parameters * thm * constraints;

fun mk_clause p th = CL (p, th, no_constraints p);

fun clause_parm (CL (p,_,_)) = p;

local val err = ERR "clause_thm" "clause has coherence constraints";
in fun clause_thm (CL (_,th,c)) = (assert (null (#coherents c)) err; th);
end;

fun clause_lits (CL (_,th,_)) = clause th;

fun empty_clause cl = null (clause_lits cl);

fun clause_constraints (CL (_,_,c)) = c;

fun free_vars (CL (_,th,c)) = FVL (constraint_vars c) (clause th);

fun active_lits (CL (p,th,c)) =
  let
    val lits = clause th
    val objs = objects lits
    fun f pos (x,y) =
      if x = y then [x]
      else if pos then raise ERR "active_lits" "no positive eqs"
      else [x,y]
    fun collect (n,l) =
      let val xs = object_map (wrap o dest_atom) (f (positive l)) l
      in (CL (p, th, obj_order p xs objs c), n) |-> l
      end
  in
    List.mapPartial (total collect) (enumerate 0 lits)
  end;

fun gen_active_eqs dest (CL (p,th,c)) =
  let
    val lits = clause th
    val objs = objects lits
    fun f ((n,l),acc) =
      case total dest l of NONE => acc
      | SOME (x,y) =>
        let
          fun g b x = (CL (p, th, obj_order p [x] objs c), n, b) |-> x
        in
          if x = y then acc
          else ocons (total (g false) y) (ocons (total (g true) x) acc)
        end
  in
    foldl f [] (enumerate 0 lits)
  end;

val active_eqs = gen_active_eqs dest_eq;

local fun dest l = dest_eq l handle ERR_EXN _ => dest_eq (negate l);
in val active_peqs = gen_active_eqs dest;
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
  fun active_tms (CL (p,th,c)) =
    let
      val lits = clause th
      val objs = objects lits
      fun ok x = total (obj_order p [x] objs) c
      fun collect ((n,l),acc) =
        let
          fun inc c = harvest (CL (p,th,c), n)
          fun f a =
            (case ok (dest_atom a) of NONE => acc
             | SOME c => inc c (literal_subterms a) acc)
          fun g (x,y) =
            (case ok x of NONE => I | SOME c => inc c (subterms [0] x))
            (case ok y of NONE => acc | SOME c => inc c (subterms [1] y) acc)
        in
          object_map f g l
        end
    in
      foldl collect [] (enumerate 0 lits)
    end;
end;

fun subsumes (cl as CL (p,th,c)) (cl' as CL (p',th',c')) =
  let val subs = mlibSubsume.subsumes1' (clause th) (clause th')
  in List.exists (fn sub => constraint_subsumes sub c c') subs
  end;

fun demodulate units (cl as CL (p,th,c)) =
  let
    val lits = clause th
    val th =
      case first (mlibUnits.prove units o wrap) lits of SOME [t] => t
      | _ => mlibUnits.demod units th
  in
    if clause th = lits then cl else CL (p,th,c)
  end;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val show_constraints = ref false;

val pp_clause =
  pp_map
  (fn CL (_,th,c) => if !show_constraints then INR (th,c) else INL th)
  (pp_sum pp_thm (pp_pair pp_thm pp_constraints));

fun clause_to_string' len = PP.pp_to_string len pp_clause;

fun clause_to_string cl = clause_to_string' (!LINE_LENGTH) cl;

(* ------------------------------------------------------------------------- *)
(* mlibClauses with coherence constraints.                                       *)
(* ------------------------------------------------------------------------- *)

fun mk_coherent p g = CL (p, AXIOM g, new_coherent_constraints p g);

fun list_coherents (CL (_,_,c)) = map fst (#coherents c);

local
  fun dest cis th =
    case List.find (equal (dest_axiom th) o fst) cis of SOME s => s
    | NONE => raise ERR "dest" "";

  fun filt cis =
    let fun f (c,_) = List.all (not o equal c o fst) cis
    in fn c => update_coherents (List.filter f (#coherents c)) c
    end;
in
  fun dest_coherents cis =
    let
      fun f (th,l) =
        case total (dest cis) th of NONE => g th l
        | SOME (lits,i) => (true, mlibThm.ASSUME (List.nth (lits,i)))
      and g th l =
        if List.exists fst l then (true, h (inference th) (map snd l))
        else (false,th)
      and h (Inst' (sub,_)) [th] = mlibThm.INST sub th
        | h (Factor' _) [th] = mlibThm.FACTOR th
        | h (Resolve' (lit,_,_)) [th1,th2] = mlibThm.RESOLVE lit th1 th2
        | h (Equality' (lit,p,t,lr,_)) [th] = mlibThm.EQUALITY lit p t lr th
        | h _ _ = raise BUG "dest_coherents" "weird inference"
    in
      fn CL (p,th,c) => CL (p, snd (thm_map f th), filt cis c)
    end;
end;

(* ------------------------------------------------------------------------- *)
(* Rules of inference.                                                       *)
(* ------------------------------------------------------------------------- *)

fun INST sub (cl as CL (p,th,c)) =
  if mlibSubst.null sub then cl
  else CL (p, mlibThm.INST sub th, constraint_subst sub c);

fun FRESH_VARS cl =
  let
    val fvs = free_vars cl
    val gvs = new_vars (length fvs)
    val sub = mlibSubst.from_maplets (zipwith (curry op|->) fvs gvs)
  in
    INST sub cl
  end;

fun SYM (CL (p,th,c), i) = CL (p, mlibThm.SYM (List.nth (clause th, i)) th, c);

local
  fun match_occurs cl l r =
    let
      val v =
        case l of Var v => v
        | Fn (":", [Var v, _]) => v
        | _ => raise ERR "match_occurs" "not a variable"
      val () = assert (not (mem v (FVT r))) (ERR "match_occurs" "")
      val sub = match l r
    in
      INST sub cl
    end;

  fun dest_neq cl lit =
    let
      val (l,r) = dest_eq (dest_neg lit)
      val () = assert (l <> r) (ERR "dest_neq" "reflexive")
    in
      case total (match_occurs cl l) r of SOME cl => cl
      | NONE => match_occurs cl r l
    end;

  fun neq_simp1 cl = first (total (dest_neq cl)) (clause_lits cl);

  fun neq_simp cl = case neq_simp1 cl of NONE => cl | SOME cl => neq_simp cl;

  fun eq_factor (CL (p,th,c)) = CL (p, mlibThm.EQ_FACTOR th, c);
in
  fun NEQ_SIMP cl =
    (case neq_simp1 cl of NONE => cl | SOME cl => eq_factor (neq_simp cl))
    handle ERR_EXN _ => raise BUG "NEQ_SIMP" "shouldn't fail";
end;

local
  val empty = (S.empty (lex_compare bool_compare), []);
  fun is_new h (s,_) = not (S.member (s,h));
  fun insert (h,c) (s,l) = (S.add (s,h), c :: l);
  fun finish (_,l) = l;

  fun assimilate s l l' =
    let
      val s' = unify_literals s l l'
      val () = assert (formula_subst s l <> formula_subst s l')
                      (ERR "assimilate" "already included")
    in
      s'
    end;

  fun final cl sub lr x targs =
    let
      fun fin acc =
        let
          val lits = map (formula_subst sub) (clause_lits cl)
          val () = assert (List.all (not o is_refl) lits) (ERR "factor" "refl")
          val hits = lr :: map (C mem (map (formula_subst sub) targs)) lits
          val () = assert (is_new hits acc) (ERR "factor" "already seen")
          val CL (p,th,c) = INST sub cl
          val th = mlibThm.EQ_FACTOR th
          val c = obj_order p [term_subst sub x] (objects lits) c
        in
          (hits, CL (p,th,c))
        end
    in
      fn acc =>
      if mlibSubst.null sub then acc
      else case total fin acc of SOME x => insert x acc | NONE => acc
    end;

  fun factor ((cl,n) |-> lit) =
    let
      val x = object_map dest_atom fst lit
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
      f [(|<>|, List.drop (clause_lits cl, n + 1))]
    end;

  fun factor_eq ((cl,n,b) |-> x) =
    let
      val lit = List.nth (clause_lits cl, n)
      val lit' = psym lit
      fun f [] acc = acc
        | f ((s,[]) :: paths) acc = f paths (final cl s b x [lit, lit'] acc)
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
      f [(|<>|, List.drop (clause_lits cl, n + 1))]
    end;

  fun FACTOR' cl =
    let
      fun fac acc = foldl (uncurry factor) acc (active_lits cl)
      fun fac_eq acc = foldl (uncurry factor_eq) acc (active_peqs cl)
    in
      finish (fac (fac_eq empty))
    end
    handle ERR_EXN _ => raise BUG "mlibClause.FACTOR" "shouldn't fail";
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
  fun RESOLVE' (CL (p,th1,c1), n1) (CL (p',th2,c2), n2) =
    let
      val lit1 = List.nth (clause th1, n1)
      val lit2 = List.nth (clause th2, n2)
      val env = unify_literals |<>| lit1 (negate lit2)
      val (c,env) = merge_constraints env c1 c2
      val lit = mlibSubst.formula_subst env lit1
      val th1 = mlibThm.INST env th1
      val th2 = mlibThm.INST env th2
      val th = mlibThm.EQ_FACTOR (mlibThm.RESOLVE lit th1 th2)
      val c = lit_order p lit (clause th) c
      val c = constraint_consistent c
    in
      CL (p,th,c)
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
          handle e as ERR_EXN _ => (p (INR (report e)); raise e)
      in
        (p (INL res); res)
      end;
end;

local
  fun pick (0 :: _) (x,_) = x
    | pick (1 :: _) (_,y) = y
    | pick _ _ = raise BUG "into_obj" "bad path";

  fun into_obj p = object_map dest_atom (pick p);

  fun PARAMODULATE' (CL (p,th1,c1), n1, lr1) (CL (p',th2,c2), n2, p2) =
    let
      val lit1 = List.nth (clause th1, n1)
      val lit2 = List.nth (clause th2, n2)
      val (l1,r1) = (if lr1 then I else swap) (dest_eq lit1)
      val t2 = literal_subterm p2 lit2
      val env = unify |<>| l1 t2
      val (c,env) = merge_constraints env c1 c2
      val (l1,r1) = Df (mlibSubst.term_subst env) (l1,r1)
      val c = term_order p l1 r1 c
      val (lit1,lit2) = Df (mlibSubst.formula_subst env) (lit1,lit2)
      val (th1,th2) = Df (mlibThm.INST env) (th1,th2)
      val c = obj_order p [l1] (objects (clause th1)) c
      val c = obj_order p [into_obj p2 lit2] (objects (clause th2)) c
      val c = constraint_consistent c
      val th =
        let val eq_th = mlibThm.EQUALITY lit2 p2 r1 lr1 th2
        in mlibThm.EQ_FACTOR (mlibThm.RESOLVE lit1 th1 eq_th)
        end
        handle ERR_EXN _ => raise BUG "PARAMODULATE (rule)" "shouldn't fail"
    in
      CL (p,th,c)
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
          handle e as ERR_EXN _ => (p (INR (report e)); raise e)
      in
        (p (INL res); res)
      end;
end;

local
  fun rewr r ord th = mlibThm.EQ_FACTOR (mlibThm.rewrite r ord th)

  fun rewrite0 r i (CL (p,th,c)) =
    CL (p, rewr r (T.compare (#ordering c)) (i,th), c);

  fun REWRITE' r (i,cl) =
    (case clause_parm cl of {term_order = false, ...} => cl
     | {term_order = true, ...} => rewrite0 r i cl)
    handle ERR_EXN _ => raise BUG "mlibClause.REWRITE" "shouldn't fail";
in
  fun REWRITE rws icl =
    if not (chatting 1) then REWRITE' rws icl else
      let
        val (_,cl) = icl
        val res = REWRITE' rws icl
        val _ = clause_lits cl <> clause_lits res andalso chat
          ("\nREWRITE: " ^ PP.pp_to_string 60 pp_clause cl ^
           "\nto get: " ^ PP.pp_to_string 60 pp_clause res ^ "\n")
      in
        res
      end;
end;

end
