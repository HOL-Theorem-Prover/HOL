(* ========================================================================= *)
(* INTERFACE TO THE LCF-STYLE LOGICAL KERNEL, PLUS SOME DERIVED RULES        *)
(* Created by Joe Hurd, September 2001                                       *)
(* ========================================================================= *)

(*
app load ["mlibUseful", "mlibTerm", "mlibKernel", "mlibMatch"];
*)

(*
*)
structure mlibThm :> mlibThm =
struct

open mlibUseful mlibTerm mlibKernel mlibMatch;

infixr |-> ::> oo ##;

structure T = mlibTermnet; local open mlibTermnet in end;

type subst        = mlibSubst.subst;
val |<>|          = mlibSubst.|<>|;
val op ::>        = mlibSubst.::>;
val term_subst    = mlibSubst.term_subst;
val formula_subst = mlibSubst.formula_subst;
val pp_subst      = mlibSubst.pp_subst;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val () = traces := {module = "mlibThm", alignment = K 1} :: !traces;

fun chat l m = trace {module = "mlibThm", message = m, level = l};

(* ------------------------------------------------------------------------- *)
(* Annotated primitive inferences.                                           *)
(* ------------------------------------------------------------------------- *)

datatype inference' =
  Axiom'    of formula list
| Refl'     of term
| Assume'   of formula
| Inst'     of subst * thm
| Factor'   of thm
| Resolve'  of formula * thm * thm
| Equality' of formula * int list * term * bool * thm

fun primitive_inference (Axiom'    cl              ) = AXIOM cl
  | primitive_inference (Refl'     tm              ) = REFL tm
  | primitive_inference (Assume'   l               ) = ASSUME l
  | primitive_inference (Inst'     (s, th)         ) = INST s th
  | primitive_inference (Factor'   th              ) = FACTOR th
  | primitive_inference (Resolve'  (l, th1, th2)   ) = RESOLVE l th1 th2
  | primitive_inference (Equality' (l, p, t, s, th)) = EQUALITY l p t s th;

val clause = fst o dest_thm;

fun dest_axiom th =
  case dest_thm th of (lits, (Axiom, [])) => lits
  | _ => raise ERR "dest_axiom" "";

val is_axiom = can dest_axiom;
  
(* ------------------------------------------------------------------------- *)
(* Pretty-printing of theorems                                               *)
(* ------------------------------------------------------------------------- *)

fun pp_thm pp th =
  (PP.begin_block pp PP.INCONSISTENT 3;
   PP.add_string pp "|- ";
   pp_formula pp (list_mk_disj (clause th));
   PP.end_block pp);

local
  fun inf_to_string Axiom    = "Axiom"
    | inf_to_string Refl     = "Refl"
    | inf_to_string Assume   = "Assume"
    | inf_to_string Inst     = "Inst"
    | inf_to_string Factor   = "Factor"
    | inf_to_string Resolve  = "Resolve"
    | inf_to_string Equality = "Equality";
in
  val pp_inference = pp_map inf_to_string pp_string;
end;

local
  fun pp_inf (Axiom'    a) = (Axiom,   C (pp_list pp_formula)                 a)
    | pp_inf (Refl'     a) = (Refl,    C pp_term                              a)
    | pp_inf (Assume'   a) = (Assume,  C pp_formula                           a)
    | pp_inf (Inst'     a) = (Inst,    C (pp_pair pp_subst pp_thm)            a)
    | pp_inf (Factor'   a) = (Factor,  C pp_thm                               a)
    | pp_inf (Resolve'  a) = (Resolve, C (pp_triple pp_formula pp_thm pp_thm) a)
    | pp_inf (Equality' (lit, p, r, lr, th)) =
    (Equality,
     C (pp_record [("lit",  unit_pp pp_formula lit),
                   ("path", unit_pp (pp_list pp_int) p),
                   ("res",  unit_pp pp_term r),
                   ("lr",   unit_pp pp_bool lr),
                   ("thm",  unit_pp pp_thm th)]) ());
in
  fun pp_inference' pp inf =
  let
    open PP
    val (i, ppf) = pp_inf inf
  in
    (begin_block pp INCONSISTENT 0;
     pp_inference pp i;
     add_break pp (1, 0);
     ppf pp;
     end_block pp)
  end;
end;

val pp_proof = pp_list (pp_pair pp_thm pp_inference');

(* Purely functional pretty-printing *)

fun thm_to_string'       len = PP.pp_to_string len pp_thm;
fun inference_to_string' len = PP.pp_to_string len pp_inference';
fun proof_to_string'     len = PP.pp_to_string len pp_proof;

(* Pretty-printing using !LINE_LENGTH *)

fun thm_to_string       th  = thm_to_string'       (!LINE_LENGTH) th;
fun inference_to_string inf = inference_to_string' (!LINE_LENGTH) inf;
fun proof_to_string     p   = proof_to_string'     (!LINE_LENGTH) p;

(* ------------------------------------------------------------------------- *)
(* Theorem operations.                                                       *)
(* ------------------------------------------------------------------------- *)

local
  fun cmp Axiom    Axiom    = EQUAL
    | cmp Axiom    _        = LESS
    | cmp _        Axiom    = GREATER
    | cmp Refl     Refl     = EQUAL
    | cmp Refl     _        = LESS
    | cmp _        Refl     = GREATER
    | cmp Assume   Assume   = EQUAL
    | cmp Assume   _        = LESS
    | cmp _        Assume   = GREATER
    | cmp Inst     Inst     = EQUAL
    | cmp Inst     _        = LESS
    | cmp _        Inst     = GREATER
    | cmp Factor   Factor   = EQUAL
    | cmp Factor   _        = LESS
    | cmp _        Factor   = GREATER
    | cmp Resolve  Resolve  = EQUAL
    | cmp Resolve  Equality = LESS
    | cmp Equality Resolve  = GREATER
    | cmp Equality Equality = EQUAL;

  fun cm [] = EQUAL
    | cm ((th1, th2) :: l) =
    let
      val (l1, (p1, ths1)) = dest_thm th1
      val (l2, (p2, ths2)) = dest_thm th2
    in
      case Int.compare (length l1, length l2) of EQUAL
        => (case lex_compare formula_compare (zip l1 l2) of EQUAL
              => (case cmp p1 p2 of EQUAL
                    => cm (zip ths1 ths2 @ l)
                  | x => x)
            | x => x)
      | x => x
    end
in
  val thm_compare = cm o wrap;
end;

local
  val deps = snd o snd o dest_thm;
  val empty = Binarymap.mkDict thm_compare;
  fun peek th m = Binarymap.peek (m, th);
  fun ins (th, a) m = Binarymap.insert (m, th, a);
in
  fun thm_map f =
    let
      fun g th m =
        case peek th m of SOME a => (a, m)
        | NONE =>
          let
            val (al, m) = maps g (deps th) m
            val a = f (th, al)
          in
            (a, ins (th, a) m)
          end
    in
      fn th => fst (g th empty)
    end;
end;

local
  val deps = snd o snd o dest_thm;
  fun empty a = (Binaryset.empty thm_compare, a);
  fun mem th (s, _) = Binaryset.member (s, th);
  fun ins f th (s, a) = (Binaryset.add (s, th), f (th, a))
in
  fun thm_foldr f =
    let fun g (th, x) = if mem th x then x else ins f th (foldl g x (deps th))
    in fn a => fn th => snd (g (th, empty a))
    end;
end;

(* ------------------------------------------------------------------------- *)
(* Reconstructing proofs.                                                    *)
(* ------------------------------------------------------------------------- *)

fun reconstruct_resolvant cl1 cl2 (cl1', cl2') =
  case (subtract (setify cl1) cl1', subtract (setify cl2) cl2') of
    (_ :: _ :: _, _) => NONE
  | (_, _ :: _ :: _) => NONE
  | ([l], []) => SOME l
  | ([], [l']) => SOME (negate l')
  | ([l], [l']) => if negate l = l' then SOME l else NONE
  | ([], []) => SOME False;

fun reconstruct_equality l r =
  let
    fun recon_fn p (f, args) (f', args') rest =
      recon_tm
      (if f <> f' orelse length args <> length args' then rest
       else map (C cons p ## I) (enumerate 0 (zip args args')) @ rest)
    and recon_tm [] = NONE
      | recon_tm ((p, (tm, tm')) :: rest) =
      if tm = l andalso tm' = r then SOME (rev p)
      else
        case (tm, tm') of (Fn a, Fn a') => recon_fn p a a' rest
        | _ => recon_tm rest

    fun recon_lit (Not a) (Not a') = recon_lit a a'
      | recon_lit (Atom a) (Atom a') =
      if l <> r andalso a = a' then NONE else recon_tm [([], (a, a'))]
      | recon_lit _ _ = NONE
  in
    fn (lit, lit') =>
    case recon_lit lit lit' of SOME p => SOME (lit, p) | NONE => NONE
  end;

fun reconstruct (cl, (Axiom, [])) = Axiom' cl
  | reconstruct ([lit], (Refl, [])) = Refl' (lhs lit)
  | reconstruct ([fm, _], (Assume, [])) = Assume' fm
  | reconstruct (cl, (Inst, [th])) =
  Inst' (matchl_literals |<>| (zip (clause th) cl), th)
  | reconstruct (_, (Factor, [th])) = Factor' th
  | reconstruct (cl, (Resolve, [th1, th2])) =
  let
    val f = reconstruct_resolvant (clause th1) (clause th2)
    val l =
      case f (cl, cl) of SOME l => l
      | NONE =>
        case first f (List.tabulate (length cl, split cl)) of SOME l => l
        | NONE =>
          raise BUG "inference"
          ("couldn't reconstruct resolvant" ^
           "\nth = " ^ thm_to_string (AXIOM cl) ^
           "\nth1 = " ^ thm_to_string th1 ^
           "\nth2 = " ^ thm_to_string th2)
  in
    Resolve' (l, th1, th2)
  end
  | reconstruct (Not eq :: cl, (Equality, [th])) =
    if length (clause th) < length cl then
      let
        val (l, r) = dest_eq eq
        val lit = hd cl
        fun f (p |-> t) =
          if t = l then SOME (p, false)
          else if t = r then SOME (p, true)
          else NONE
      in
        case first f (literal_subterms lit) of SOME (p, lr) =>
          let
            val (l, r) = if lr then (l, r) else (r, l)
            val lit = literal_rewrite (p |-> l) lit
          in
            Equality' (lit, p, r, lr, th)
          end
        | NONE => raise BUG "inference" "couldn't reconstruct weak equality"
      end
    else
      let
        val line = zip (clause th) cl
        fun sync l r = first (reconstruct_equality l r) line
        val (l, r) = dest_eq eq
      in
        case sync l r of SOME (lit, p) => Equality' (lit, p, r, true, th)
        | NONE =>
          case sync r l of SOME (lit, p) => Equality' (lit, p, l, false, th)
          | NONE => raise BUG "inference" "couldn't reconstruct equality step"
      end
  | reconstruct _ = raise BUG "inference" "malformed inference";

fun inference th =
  let
    val i = reconstruct (dest_thm th)
    val _ =
      (primitive_inference i = th) orelse
      raise BUG "inference"
      ("failed:\nth = " ^ thm_to_string th ^ "\ninf = " ^ inference_to_string i
       ^ "\ninf_th = " ^ thm_to_string (primitive_inference i))
  in
    i
  end;

val proof = thm_foldr (fn (th, l) => (th, inference th) :: l) [];

(* ------------------------------------------------------------------------- *)
(* Contradictions and units.                                                 *)
(* ------------------------------------------------------------------------- *)

val is_contradiction = null o clause;

fun dest_unit th =
  case clause th of [lit] => lit | _ => raise ERR "dest_unit" "not a unit";

val is_unit = can dest_unit;

val dest_unit_eq = dest_eq o dest_unit;

val is_unit_eq = can dest_unit_eq;

(* ------------------------------------------------------------------------- *)
(* Derived rules                                                             *)
(* ------------------------------------------------------------------------- *)

fun CONTR lit th = RESOLVE (negate lit) (ASSUME lit) th;

fun WEAKEN lits th = foldl (uncurry CONTR) th (rev lits);

fun FRESH_VARSL ths =
  let
    val fvs = FVL [] (List.concat (map clause ths))
    val vvs = new_vars (length fvs)
    val sub = mlibSubst.from_maplets (zipwith (curry op |->) fvs vvs)
  in
    map (INST sub) ths
  end
  handle ERR_EXN _ => raise BUG "FRESH_VARSL" "shouldn't fail";

val FRESH_VARS = unwrap o FRESH_VARSL o wrap;

fun UNIT_SQUASH th =
  case clause th of [] => raise ERR "UNIT_SQUASH" "contradiction"
  | [_] => th
  | _ :: _ :: _ =>
    let
      fun squash env (x :: (xs as y :: _)) = squash (unify_literals env x y) xs
        | squash env _ = env
    in
      FACTOR (INST (squash |<>| (clause th)) th)
    end;
  
val REFLEXIVITY = REFL (Var "x");

val SYMMETRY =
  EQUALITY (mk_eq (Var "x", Var "x")) [0] (Var "y") true REFLEXIVITY;

val TRANSITIVITY =
  EQUALITY (mk_eq (Var "y", Var "z")) [0] (Var "x") false
  (ASSUME (Not (mk_eq (Var "y", Var "z"))));

fun FUN_CONGRUENCE (function, arity) =
  let
    val xs = List.tabulate (arity, fn i => Var ("x" ^ int_to_string i))
    val ys = List.tabulate (arity, fn i => Var ("y" ^ int_to_string i))
    fun f (i, th) =
      EQUALITY (List.last (clause th)) [1,i] (List.nth (ys, i)) true th
    val refl = INST (("x" |-> Fn (function, xs)) ::> |<>|) REFLEXIVITY
  in
    foldl f refl (rev (interval 0 arity))
  end;

fun REL_CONGRUENCE (relation, arity) =
  let
    val xs = List.tabulate (arity, fn i => Var ("x" ^ int_to_string i))
    val ys = List.tabulate (arity, fn i => Var ("y" ^ int_to_string i))
    fun f (i, th) =
      EQUALITY (List.last (clause th)) [i] (List.nth (ys, i)) true th
    val refl = ASSUME (Not (Atom (Fn (relation, xs))))
  in
    foldl f refl (rev (interval 0 arity))
  end;

fun SYM lit th =
  let
    fun g x y = RESOLVE lit th (EQUALITY (refl x) [0] y true (REFL x))
    fun f (true, (x,y)) = g x y | f (false, (x,y)) = g y x
  in
    f ((I ## dest_eq) (dest_literal lit))
  end;

local
  fun psym lit =
    let
      val (s, (x,y)) = (I ## dest_eq) (dest_literal lit)
      val () = assert (x <> y) (ERR "psym" "refl")
    in
      mk_literal (s, mk_eq (y,x))
    end;

  fun syms [] th = th
    | syms (l :: ls) th =
    syms ls
    (case total psym l of NONE => th
     | SOME l' => if mem l' ls then SYM l th else th);
in
  val EQ_FACTOR = FACTOR o (W (syms o clause)) o FACTOR;
end;

fun SUBST (rw, lr, r) (th, lit, p) =
  RESOLVE (dest_unit rw) rw (EQUALITY lit p r lr th);

fun REWR (rw, lr) tm =
  let
    val (l,r) = (if lr then I else swap) (dest_unit_eq rw)
    val env = match l tm
  in
    (INST env rw, lr, term_subst env r)
  end;

fun DEPTH conv =
  let
    fun rewr1 (th, lit) (x as (_,_,r)) p =
      (SUBST x (th, lit, p), literal_rewrite (p |-> r) lit)

    fun rewr_top thl tm p =
      (case total conv tm of NONE => (thl, tm)
       | SOME (x as (_,_,r)) => rewr_top (rewr1 thl x (rev p)) r p)

    fun rewr thl tm_orig p =
      let
        val (thl, tm) = rewr_top thl tm_orig p
        val (thl, tm) = rewr_sub thl tm p
      (*val () = chat 3 ("rewr: " ^ term_to_string tm_orig ^ " --> " ^ term_to_string tm ^ "\n")*)
      in
        if tm = tm_orig then (thl, tm) else rewr thl tm p
      end
    and rewr_sub thl (tm as Var _) _ = (thl, tm)
      | rewr_sub thl (tm as Fn (name, xs)) p =
      let
        fun f ((n, x), (tl, ys)) =
          let val (tl, y) = rewr tl x (n :: p) in (tl, y :: ys) end
        val (thl, ys) = (I ## rev) (foldl f (thl, []) (enumerate 0 xs))
      in
        (thl, if ys = xs then tm else Fn (name, ys))
      end

    fun rewr_lits (lit, th) =
      if not (mem lit (clause th)) then
        (assert (is_eq (negate lit)) (BUG "DEPTH" "weird"); th)
      else fst (fst (rewr_sub (th, lit) (dest_atom (literal_atom lit)) []))
  in
    fn th => foldl rewr_lits th (clause th)
(***    handle ERR_EXN _ => raise BUG "DEPTH" "shouldn't fail"*)
  end;
 
fun REWRITE ths =
  let
    fun f th = let val (l,_) = dest_unit_eq th in T.insert (l |-> th) end
    val net = foldl (uncurry f) T.empty ths
    fun mat tm = first (fn th => total (REWR (th,true)) tm) (T.match net tm)
  in
    DEPTH (partial (ERR "REWRITE" "no matching rewrites") mat)
  end;

fun ORD_REWRITE ord rws =
  let
    fun f rw =
      let
        val lr as (l,r) = dest_unit_eq rw
      in
        case ord lr of SOME EQUAL => I
        | SOME LESS => T.insert (r |-> (rw,false,r,l))
        | SOME GREATER => T.insert (l |-> (rw,true,l,r))
        | NONE => T.insert (l|->(rw,true,l,r)) o T.insert (r|->(rw,false,r,l))
      end
    val net = foldl (uncurry f) T.empty rws
    fun g tm (rw,lr,l,r) =
      let
        val env = match l tm
        val (l,r) = Df (term_subst env) (l,r)
        val () = assert (ord (l,r) = SOME GREATER)
                        (ERR "ORD_REWRITE" "order violation")
      in
        (INST env rw, lr, r)
      end      
    fun mat tm = first (total (g tm)) (T.match net tm)
  in
    fn th => DEPTH (partial (ERR "ORD_REWRITE" "no matching rewrites") mat) th
    handle ERR_EXN _ =>
      (print ("\nrewrs: " ^ PP.pp_to_string 60 (pp_list pp_thm) rws ^
              "\nth: " ^ PP.pp_to_string 60 pp_thm th ^ "\n");
       raise BUG "ORD_REWRITE" "shouldn't fail")
  end;

end
