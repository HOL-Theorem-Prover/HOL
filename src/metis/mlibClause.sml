(* ========================================================================= *)
(* CLAUSE = THEOREM + CONSTRAINTS                                            *)
(* Created by Joe Hurd, September 2002                                       *)
(* ========================================================================= *)

(*
app load ["mlibTerm", "mlibSubst", "mlibThm", "mlibUnits"];
*)

(*
*)
structure mlibClause :> mlibClause =
struct

infix ## |->;

open mlibUseful mlibTerm mlibMatch mlibThm;

type subst = mlibSubst.subst;
type units = mlibUnits.units;

val |<>|          = mlibSubst.|<>|;
val term_subst    = mlibSubst.term_subst;
val formula_subst = mlibSubst.formula_subst;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val () = traces := {module = "mlibClause", alignment = K 1} :: !traces;

fun chat l m = trace {module = "mlibClause", message = m, level = l};

fun chatting l = visible {module = "mlibClause", level = l};

(* ------------------------------------------------------------------------- *)
(* Parameters.                                                               *)
(* ------------------------------------------------------------------------- *)

type parameters = {literal_order : bool, term_order : bool, tracking : bool};

val defaults =
  {literal_order = true,
   term_order    = true,
   tracking      = false};

fun check_parm (p : parameters) p' = assert (p = p') (BUG "check_parm" "");

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun ocons (SOME x) l = x :: l | ocons NONE l = l;

fun oinsert (SOME x) l = insert x l | oinsert NONE l = l;

fun psym lit =
  let
    val (s, (x,y)) = (I ## dest_eq) (dest_literal lit)
    val () = assert (x <> y) (ERR "psym" "refl")
  in
    mk_literal (s, mk_eq (y,x))
  end;

fun object_map f g l =
  let val a = literal_atom l
  in case total dest_eq a of NONE => f a | SOME xy => g xy
  end;

local val break = object_map (fn x => [dest_atom x]) (fn (x, y) => [x, y]);
in val objects = foldl (fn (h,t) => break h @ t) [];
end;

(* ------------------------------------------------------------------------- *)
(* Coherence constraints.                                                    *)
(* ------------------------------------------------------------------------- *)

type coherent = formula list * term list;

fun new_coherent g = (g, map Var (FVL [] g));

fun coherent_vars c = FVL [] (List.concat (map (map Atom o snd) c));

fun coherent_subst sub c = map (I ## map (mlibSubst.term_subst sub)) c;

local
  fun mcoherents c (a as (g, ts), (d, r)) =
     case List.find (equal g o fst) c of NONE => (a :: d, r)
     | SOME (_, ts') => (d, zip ts' ts @ r);
in
  fun merge_coherents sub c1 c2 =
    let
      val (c, sync) = foldl (mcoherents c2) (c2, []) c1
      val sub = unifyl sub sync
    in
      (coherent_subst sub c, sub)
    end;
end;

local
  fun csubsumes c ((g, ts), sub) =
    case List.find (equal g o fst) c of NONE => raise ERR "csubsumes" ""
    | SOME (_, ts') => matchl sub (zip ts ts');
in
  fun coherence_subsumes sub c1 c2 = foldl (csubsumes c2) sub c1;
end;

(* ------------------------------------------------------------------------- *)
(* Ordering constraints.                                                     *)
(* ------------------------------------------------------------------------- *)

fun tm_order false l r c =
  (assert (kb_comp (l,r) <> SOME LESS) (ERR "tm_order" "violates ordering"); c)
  | tm_order true _ _ _ = raise BUG "tm_order" "tracking not implemented";

fun term_order (p : parameters) l r c =
  if l = r then raise ERR "term_order" "refl"
  else
    (case p of {term_order = false, ...} => c
     | {term_order = true, tracking, ...} => tm_order tracking l r c);

fun obj_order ({literal_order = false, ...} : parameters) _ _ c = c
  | obj_order {literal_order = true, tracking, ...} x ys c =
  foldl (fn (y, c) => tm_order tracking x y c) c ys;

fun lit_order {literal_order = false, ...} _ _ c = c
  | lit_order (p as {literal_order = true, ...}) l ls c =
  let
    fun f (x,y) = if x = y then x else raise BUG "lit_order" "no eqs"
    val x = object_map dest_atom f l
  in
    obj_order p x (objects ls) c
  end;

(* ------------------------------------------------------------------------- *)
(* Generic constraints.                                                      *)
(* ------------------------------------------------------------------------- *)

type constraints = {coherents : coherent list};

fun update_coherents c (_ : constraints) = {coherents = c};

val no_constraints : constraints = {coherents = []};

fun new_coherent_constraints g : constraints = {coherents = [new_coherent g]};

fun constraint_vars (c : constraints) = coherent_vars (#coherents c);

fun constraint_subst sub con =
  let
    val {coherents = c} = con
    val c = coherent_subst sub c
  in
    {coherents = c}
  end;

fun merge_constraints sub con1 con2 =
  let
    val {coherents = c1} = con1
    val {coherents = c2} = con2
    val (c, sub) = merge_coherents sub c1 c2
  in
    ({coherents = c}, sub)
  end;

fun constraint_subsumes sub con1 con2 =
  let
    val {coherents = c1} = con1
    val {coherents = c2} = con2
  in
    case total (coherence_subsumes sub c1) c2 of NONE => false
    | SOME _ => true
  end;

val pp_constraints =
  pp_map (fn {coherents} => coherents)
  (pp_list (pp_pair (pp_list pp_formula) (pp_list pp_term)));

(* ------------------------------------------------------------------------- *)
(* Clauses.                                                                  *)
(* ------------------------------------------------------------------------- *)

datatype clause = CL of parameters * thm * constraints;

fun mk_clause p th = CL (p, th, no_constraints);

fun clause_parm (CL (p, _, _)) = p;

local val err = ERR "clause_thm" "clause has coherence constraints";
in fun clause_thm (CL (_, th, c)) = (assert (null (#coherents c)) err; th);
end;

fun clause_lits (CL (_, th, _)) = clause th;

fun free_vars (CL (_, th, c)) = FVL (constraint_vars c) (clause th);

fun active_lits (CL (p, th, c)) =
  let
    val lits = clause th
    val objs = objects lits
    fun f (x,y) = if x = y then x else raise ERR "active_lits" "no eqs"
    fun collect (n,l) =
      let val x = object_map dest_atom f l
      in (CL (p, th, obj_order p x objs c), n) |-> l
      end
  in
    List.mapPartial (total collect) (enumerate 0 lits)
  end;
  
fun gen_active_eqs dest (CL (p, th, c)) =
  let
    val lits = clause th
    val objs = objects lits
    fun f ((n, l), acc) =
      case total dest l of NONE => acc
      | SOME (x, y) =>
        let
          fun g b x = (CL (p, th, obj_order p x objs c), n, b) |-> x
        in
          if x = y then acc
          else ocons (total (g false) y) (ocons (total (g true) x) acc)
        end
  in
    foldl f [] (enumerate 0 lits)
  end;

val active_eqs = gen_active_eqs dest_eq;

local
  fun dest l = dest_eq l handle ERR_EXN _ => dest_eq (negate l);

  fun num ((_, n) |-> _) = n;

  fun sign ((_, _, b) |-> _) = b;

  fun disorient ((c, n, _) |-> _) = (c, n) |-> List.nth (clause_lits c, n);

  val partitionq = Df (map disorient) o List.partition sign;

  fun mergeq acc [] ys = ys @ acc
    | mergeq acc xs [] = xs @ acc
    | mergeq acc (xs as xh :: xt) (ys as yh :: yt) =
    if xh = yh then mergeq (xh :: acc) xt yt
    else if num xh < num yh then mergeq (yh :: acc) xs yt
    else mergeq (xh :: acc) xt ys;
in
  val active_eqlits = uncurry (mergeq []) o partitionq o gen_active_eqs dest;
end;

local
  fun harvest (c, i) =
    let
      fun f ((_ |-> Var _), acc) = acc
        | f ((_ |-> (Fn (":", [Var _, _]))), acc) = acc
        | f ((p |-> (t as Fn _)), acc) = ((c, i, p) |-> t) :: acc
    in
      C (foldl f)
    end;
in
  fun active_tms (CL (p, th, c)) =
    let
      val lits = clause th
      val objs = objects lits
      fun ok x = total (obj_order p x objs) c
      fun collect ((n, l), acc) =
        let
          fun inc c = harvest (CL (p, th, c), n)
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

fun subsumes (cl as CL (p, th, c)) (cl' as CL (p', th', c')) =
  let
    val () = check_parm p p'
    val subs = mlibSubsume.subsumes1' (clause th) (clause th')
  in
    List.exists (fn sub => constraint_subsumes sub c c') subs
  end;

fun demodulate units (CL (p, th, c)) =
  let
    val th =
      case first (mlibUnits.subsumes units) (clause th) of SOME th => th
      | NONE => mlibUnits.demod units th
  in
    CL (p, th, c)
  end;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val show_constraints = ref false;

val pp_clause =
  pp_map
  (fn CL (_, th, c) => if !show_constraints then INR (th, c) else INL th)
  (pp_sum pp_thm (pp_pair pp_thm pp_constraints));

fun clause_to_string' len = PP.pp_to_string len pp_clause;

fun clause_to_string cl = clause_to_string' (!LINE_LENGTH) cl;

(* ------------------------------------------------------------------------- *)
(* Clauses with coherence constraints.                                       *)
(* ------------------------------------------------------------------------- *)

fun mk_coherent p g = CL (p, AXIOM g, new_coherent_constraints g);

fun list_coherents (CL (_, _, c)) = map fst (#coherents c);

local
  fun dest cis th =
    case List.find (equal (dest_axiom th) o fst) cis of SOME s => s
    | NONE => raise ERR "dest" "";

  fun filt cis =
    let fun f (c, _) = List.all (not o equal c o fst) cis
    in fn c => update_coherents (List.filter f (#coherents c)) c
    end;
in
  fun dest_coherents cis =
    let
      fun f (th, l) =
        case total (dest cis) th of NONE => g th l
        | SOME (lits, i) => (true, mlibThm.ASSUME (List.nth (lits, i)))
      and g th l =
        if List.exists fst l then (true, h (inference th) (map snd l))
        else (false, th)
      and h (Inst' (sub, _)) [th] = mlibThm.INST sub th
        | h (Factor' _) [th] = mlibThm.FACTOR th
        | h (Resolve' (lit, _, _)) [th1, th2] = mlibThm.RESOLVE lit th1 th2
        | h (Equality' (lit, p, t, lr, _)) [th] = mlibThm.EQUALITY lit p t lr th
        | h _ _ = raise BUG "dest_coherents" "weird inference"
    in
      fn CL (p, th, c) => CL (p, snd (thm_map f th), filt cis c)
    end;
end;

(* ------------------------------------------------------------------------- *)
(* Rules of inference.                                                       *)
(* ------------------------------------------------------------------------- *)

fun INST sub (cl as CL (p, th, c)) =
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

fun SYM (CL (p, th, c), i) =
  CL (p, mlibThm.SYM (List.nth (clause th, i)) th, c);

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
      val (l, r) = dest_eq (dest_neg lit)
      val () = assert (l <> r) (ERR "dest_neq" "reflexive")
    in
      case total (match_occurs cl l) r of SOME cl => cl
      | NONE => match_occurs cl r l
    end;

  fun neq_simp1 cl = first (total (dest_neq cl)) (clause_lits cl);

  fun neq_simp cl = case neq_simp1 cl of NONE => cl | SOME cl => neq_simp cl;

  fun eq_factor (CL (p, th, c)) = CL (p, mlibThm.EQ_FACTOR th, c);
in
  fun NEQ_SIMP cl =
    (case neq_simp1 cl of NONE => cl | SOME cl => eq_factor (neq_simp cl))
    handle ERR_EXN _ => raise BUG "NEQ_SIMP" "shouldn't fail";
end;

local
  fun final cl lit sub acc =
    if mlibSubst.null sub then acc
    else
      case total (INST sub) cl of NONE => acc
      | SOME (CL (p, th, c)) =>
        let
          val th = mlibThm.EQ_FACTOR th
          val objs = objects (clause th)
          val inc = oinsert o total (fn x => CL (p, th, obj_order p x objs c))
          fun f a = inc (dest_atom a) acc
          fun g (x,y) = if x = y then inc x acc else inc x (inc y acc)
        in
          object_map f g (formula_subst sub lit)
        end;

  fun merge s l l' =
    let
      val s' = unify_literals s l l'
      val () = assert (formula_subst s l <> formula_subst s l')
                      (ERR "fac" "already included")
    in
      s'
    end;

  fun fac1 cl lit =
    let
      val lit' = total psym lit
      fun f [] res = res
        | f ((s, []) :: paths) res = f paths (final cl lit s res)
        | f ((s, l :: ls) :: paths) res =
        let
          val paths = (s, ls) :: paths
          val paths =
            case total (merge s l) lit of NONE => paths
            | SOME s' => (s', ls) :: paths
          val paths =
            case Option.mapPartial (total (merge s l)) lit' of NONE => paths
            | SOME s' => (s', ls) :: paths
        in
          f paths res
        end
    in
      fn lits => f [(|<>|, lits)]
    end;

  fun factor cl (_ |-> lit, res) = fac1 cl lit (clause_lits cl) res;

  fun FACTOR' cl =
    foldl (factor cl) [] (active_lits cl @ active_eqlits cl)
    handle ERR_EXN _ => raise BUG "mlibClause.FACTOR" "shouldn't fail";
in
  fun FACTOR arg1 =
    if not (chatting 2) then FACTOR' arg1 else
      let
        val res = FACTOR' arg1
        val () = chat 2
          ("\nFACTOR: " ^ PP.pp_to_string 60 pp_clause arg1 ^
           "\nto get: " ^ PP.pp_to_string 60 (pp_list pp_clause) res ^ "\n")
      in
        res
      end;
end;

local
  fun RESOLVE' (CL (p, th1, c1), n1) (CL (p', th2, c2), n2) =
    let
      val () = check_parm p p'
      val lit1 = List.nth (clause th1, n1)
      val lit2 = List.nth (clause th2, n2)
      val env = unify_literals |<>| lit1 (negate lit2)
      val (c, env) = merge_constraints env c1 c2
      val lit = mlibSubst.formula_subst env lit1
      val th1 = mlibThm.INST env th1
      val th2 = mlibThm.INST env th2
      val th = mlibThm.EQ_FACTOR (mlibThm.RESOLVE lit th1 th2)
      val c = lit_order p lit (clause th) c
    in
      CL (p, th, c)
    end;
in
  fun RESOLVE arg1 arg2 =
    if not (chatting 2) then RESOLVE' arg1 arg2 else
      let
        fun p res = chat 2
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
  fun pick (0 :: _) (x, _) = x
    | pick (1 :: _) (_, y) = y
    | pick _ _ = raise BUG "into_obj" "bad path";

  fun into_obj p = object_map dest_atom (pick p);

  fun PARAMODULATE' (CL (p, th1, c1), n1, lr1) (CL (p', th2, c2), n2, p2) =
    let
      val () = check_parm p p'
      val lit1 = List.nth (clause th1, n1)
      val lit2 = List.nth (clause th2, n2)
      val (l1, r1) = (if lr1 then I else swap) (dest_eq lit1)
      val t2 = literal_subterm p2 lit2
      val env = unify |<>| l1 t2
      val (c, env) = merge_constraints env c1 c2
      val (l1, r1) = Df (mlibSubst.term_subst env) (l1, r1)
      val c = term_order p l1 r1 c
      val (lit1, lit2) = Df (mlibSubst.formula_subst env) (lit1, lit2)
      val (th1, th2) = Df (mlibThm.INST env) (th1, th2)
      val c = obj_order p l1 (objects (clause th1)) c
      val c = obj_order p (into_obj p2 lit2) (objects (clause th2)) c
      val th =
        let val eq_th = mlibThm.EQUALITY lit2 p2 r1 lr1 th2
        in mlibThm.EQ_FACTOR (mlibThm.RESOLVE lit1 th1 eq_th)
        end
        handle ERR_EXN _ => raise BUG "PARAMODULATE (rule)" "shouldn't fail"
    in
      CL (p, th, c)
    end;
in
  fun PARAMODULATE arg1 arg2 =
    if not (chatting 2) then PARAMODULATE' arg1 arg2 else
      let
        fun p res = chat 2
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
  fun rewr r = mlibThm.EQ_FACTOR o mlibThm.ORD_REWRITE kb_comp r;
  fun rewrite0 r (CL (p, th, c)) = CL (p, rewr r th, c);

  fun REWRITE' r cl =
    (case clause_parm cl of {term_order = false, ...} => cl
     | {term_order = true, tracking = false, ...} => rewrite0 r cl
     | {term_order = true, tracking = true, ...}
       => raise BUG "mlibClause.REWRITE" "tracking not implemented")
    handle ERR_EXN _ => raise BUG "mlibClause.REWRITE" "shouldn't fail";
in
  fun REWRITE arg1 arg2 =
    if not (chatting 2) then REWRITE' arg1 arg2 else
      let
        val res = REWRITE' arg1 arg2
        val () = if arg2 = res then () else chat 2
          ("\nREWRITE: " ^ PP.pp_to_string 60 pp_clause arg2 ^
           "\nto get: " ^ PP.pp_to_string 60 pp_clause res ^ "\n")
      in
        res
      end;
end;

end
