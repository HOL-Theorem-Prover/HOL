(* ========================================================================= *)
(* CLAUSE = ID + THEOREM + CONSTRAINTS                                       *)
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
  {literal_order  : bool,
   term_order     : bool,
   termorder_parm : mlibTermorder.parameters};

type 'a parmupdate = ('a -> 'a) -> parameters -> parameters;

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
(* Helper functions                                                          *)
(* ------------------------------------------------------------------------- *)

fun ocons (SOME x) l = x :: l | ocons NONE l = l;

val new_id = new_int;

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
(* mlibTerm and literal ordering                                                 *)
(* ------------------------------------------------------------------------- *)

fun tm_order lrs c = T.add_leqs lrs c;

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
(* Generic constraint interface                                              *)
(* ------------------------------------------------------------------------- *)

fun no_constraints ({termorder_parm = p, ...} : parameters) = T.empty p;

fun constraint_vars to = T.vars to;

fun constraint_subst sub to = T.subst sub to;

fun merge_constraints sub to1 to2 =
  (T.merge (T.subst sub to1) (T.subst sub to2), sub);

fun constraint_consistent to =
  case T.consistent to of SOME to => to
  | NONE =>
    (chatting 1 andalso
     chat ("merge_orderings: resulting termorder is inconsistent:\n" ^
           PP.pp_to_string (!LINE_LENGTH) T.pp_termorder to);
     raise ERR "consistent" "inconsistent orderings");

fun constraint_subsumes sub to1 to2 =
  case total (T.subst sub) to1 of NONE => false
  | SOME to1 => T.subsumes to1 to2;

fun pp_constraints pp to = T.pp_termorder pp to;

(* ------------------------------------------------------------------------- *)
(* mlibClauses                                                                   *)
(* ------------------------------------------------------------------------- *)

type bits = {parm : parameters, id : int, thm : thm, order : termorder};

datatype clause = CL of parameters * int * thm * termorder;

fun mk_clause p th = CL (p, new_id (), th, no_constraints p);

fun dest_clause (CL (p, i, th, to)) = {parm = p, id = i, thm = th, order = to};

val literals = mlibThm.clause o #thm o dest_clause;

fun free_vars cl =
  FVL (constraint_vars (#order (dest_clause cl))) (literals cl);

val is_empty = null o literals;

fun dest_rewr cl =
  let
    val {parm, thm, ...} = dest_clause cl
    val () = assert (#term_order parm) (ERR "dest_rewr" "no rewrs")
    val (x,y) = mlibThm.dest_unit_eq thm
    val () = assert (x <> y) (ERR "dest_rewr" "refl")
  in
    thm
  end;

val is_rewr = can dest_rewr;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val show_id = ref false;

val show_constraint = ref false;

local
  val pp_it = pp_pair pp_int mlibThm.pp_thm;
  val pp_tc = pp_pair mlibThm.pp_thm pp_constraints;
  val pp_itc = pp_triple pp_int mlibThm.pp_thm pp_constraints;
  fun f false false = pp_map (fn CL (_,_,th,_) => th) mlibThm.pp_thm
    | f true false = pp_map (fn CL (_,i,th,_) => (i,th)) pp_it
    | f false true = pp_map (fn CL (_,_,th,c) => (th,c)) pp_tc
    | f true true = pp_map (fn CL (_,i,th,c) => (i,th,c)) pp_itc;
in
  fun pp_clause pp cl = f (!show_id) (!show_constraint) pp cl;
end;

(* ------------------------------------------------------------------------- *)
(* Using ordering constraints to cut down the set of possible inferences     *)
(* ------------------------------------------------------------------------- *)

fun largest_lits (CL (p,i,th,c)) =
  let
    val lits = mlibThm.clause th
    val objs = objects lits
    fun f pos (x,y) =
      if x = y then [x]
      else if pos then raise ERR "largest_lits" "no positive eqs"
      else [x,y]
    fun collect (n,l) =
      let val xs = object_map (wrap o dest_atom) (f (positive l)) l
      in (CL (p, i, th, obj_order p xs objs c), n) |-> l
      end
  in
    List.mapPartial (total collect) (enumerate 0 lits)
  end;

fun gen_largest_eqs dest (CL (p,i,th,c)) =
  let
    val lits = mlibThm.clause th
    val objs = objects lits
    fun f ((n,l),acc) =
      case total dest l of NONE => acc
      | SOME (x,y) =>
        let
          fun g b z = (CL (p, i, th, obj_order p [z] objs c), n, b) |-> z
        in
          if x = y then acc
          else ocons (total (g false) y) (ocons (total (g true) x) acc)
        end
  in
    foldl f [] (enumerate 0 lits)
  end;

val largest_eqs = gen_largest_eqs dest_eq;

local fun dest l = dest_eq l handle ERR_EXN _ => dest_eq (negate l);
in val largest_peqs = gen_largest_eqs dest;
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
  fun largest_tms (CL (p,i,th,c)) =
    let
      val lits = mlibThm.clause th
      val objs = objects lits
      fun ok x = total (obj_order p [x] objs) c
      fun collect ((n,l),acc) =
        let
          fun inc c = harvest (CL (p,i,th,c), n)
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

(* ------------------------------------------------------------------------- *)
(* Subsumption                                                               *)
(* ------------------------------------------------------------------------- *)

fun subsumes (cl as CL (_,_,th,c)) (cl' as CL (_,_,th',c')) =
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

fun add cl rewrs =
  let
    val th = dest_rewr cl
    val REWR (parm,rw) = rewrs
    val CL (p,i,th,_) = cl
  in
    (CL (p, i, th, no_constraints p), REWR (parm, mlibRewrite.add (i,th) rw))
  end;

fun reduce (REWR (p,r)) = REWR (p, mlibRewrite.reduce r);

fun eqns (REWR (p,r)) =
  map (fn (i,th) => CL (p, i, th, no_constraints p)) (mlibRewrite.eqns r);

val pp_rewrs = pp_map (fn REWR (_,r) => r) mlibRewrite.pp_rewrs;

(* ------------------------------------------------------------------------- *)
(* Simplifying rules: these preserve the clause id                           *)
(* ------------------------------------------------------------------------- *)

fun INST sub (cl as CL (p,i,th,c)) =
  if mlibSubst.null sub then cl
  else CL (p, i, mlibThm.INST sub th, constraint_subst sub c);

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

  fun neq_simp1 cl = first (total (dest_neq cl)) (literals cl);

  fun neq_simp cl = case neq_simp1 cl of NONE => cl | SOME cl => neq_simp cl;

  fun eq_factor (CL (p,i,th,c)) = CL (p, i, mlibThm.EQ_FACTOR th, c);
in
  fun NEQ_VARS cl =
    (case neq_simp1 cl of NONE => cl | SOME cl => eq_factor (neq_simp cl))
    handle ERR_EXN _ => raise BUG "NEQ_VARS" "shouldn't fail";
end;

fun DEMODULATE units (cl as CL (p,i,th,c)) =
  let
    val lits = mlibThm.clause th
    val th =
      case first (mlibUnits.prove units o wrap) lits of SOME [t] => t
      | _ => mlibUnits.demod units th
  in
    if mlibThm.clause th = lits then cl else CL (p,i,th,c)
  end;

local
  fun rewr r ord th = mlibThm.EQ_FACTOR (mlibRewrite.rewrite r ord th)

  fun rewrite0 r (CL (p,i,th,c)) =
    case mlibRewrite.peek r i of SOME th => CL (p,i,th,c)
    | NONE => CL (p, i, rewr r (T.compare c) (i,th), c);

  fun REWRITE' (REWR ({term_order = false, ...}, _)) cl = cl
    | REWRITE' (REWR (_,rw)) cl = rewrite0 rw cl;
in
  fun REWRITE rws cl =
    (if not (chatting 1) then REWRITE' rws cl else
       let
         val res = REWRITE' rws cl
         val _ = literals cl <> literals res andalso chat
           ("\nREWRITE: " ^ PP.pp_to_string 60 pp_clause cl ^
            "\nto get: " ^ PP.pp_to_string 60 pp_clause res ^ "\n")
       in
         res
       end)
    handle ERR_EXN _ => raise BUG "mlibClause.REWRITE" "shouldn't fail";
end;

(* ------------------------------------------------------------------------- *)
(* Ordered resolution and paramodulation: these generate new clause ids      *)
(* ------------------------------------------------------------------------- *)

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
          val lits = map (formula_subst sub) (literals cl)
          val () = assert (List.all (not o is_refl) lits) (ERR "factor" "refl")
          val hits = lr :: map (C mem (map (formula_subst sub) targs)) lits
          val () = assert (is_new hits acc) (ERR "factor" "already seen")
          val CL (p,_,th,c) = INST sub cl
          val th = mlibThm.EQ_FACTOR th
          val c = obj_order p [term_subst sub x] (objects lits) c
        in
          (hits, CL (p, new_id (), th, c))
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
      f [(|<>|, List.drop (literals cl, n + 1))]
    end;

  fun factor_eq ((cl,n,b) |-> x) =
    let
      val lit = List.nth (literals cl, n)
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
      f [(|<>|, List.drop (literals cl, n + 1))]
    end;

  fun FACTOR' cl =
    let
      fun fac acc = foldl (uncurry factor) acc (largest_lits cl)
      fun fac_eq acc = foldl (uncurry factor_eq) acc (largest_peqs cl)
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
  fun RESOLVE' (CL (p,_,th1,c1), n1) (CL (p',_,th2,c2), n2) =
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
      val c = constraint_consistent c
    in
      CL (p, new_id (), th, c)
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

  fun PARAMODULATE' (CL (p,_,th1,c1), n1, lr1) (CL (p',_,th2,c2), n2, p2) =
    let
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
      val c = obj_order p [l1] (objects (mlibThm.clause th1)) c
      val c = obj_order p [into_obj p2 lit2] (objects (mlibThm.clause th2)) c
      val c = constraint_consistent c
      val th =
        let val eq_th = mlibThm.EQUALITY lit2 p2 r1 lr1 th2
        in mlibThm.EQ_FACTOR (mlibThm.RESOLVE lit1 th1 eq_th)
        end
        handle ERR_EXN _ => raise BUG "PARAMODULATE (rule)" "shouldn't fail"
    in
      CL (p, new_id (), th, c)
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

end
