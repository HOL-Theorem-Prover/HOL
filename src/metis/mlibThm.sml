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

val module = "mlibThm";
val () = traces := {module = module, alignment = I} :: !traces;
fun chatting l = tracing {module = module, level = l};
fun chat s = (trace s; true)

fun chattrans n s a b pp =
  if not (chatting n) then ()
  else (chat (s ^ ": " ^ pp a ^ " --> " ^ pp b ^ "\n"); ());

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

fun primitive_inference (Axiom' cl) = AXIOM cl
  | primitive_inference (Refl' tm) = REFL tm
  | primitive_inference (Assume' l) = ASSUME l
  | primitive_inference (Inst' (s,th)) = INST s th
  | primitive_inference (Factor' th) = FACTOR th
  | primitive_inference (Resolve' (l,th1,th2)) = RESOLVE l th1 th2
  | primitive_inference (Equality' (l,p,t,s,th)) = EQUALITY l p t s th;

val clause = fst o dest_thm;

fun dest_axiom th =
  case dest_thm th of (lits,(Axiom,[])) => lits
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
  open PP;

  fun pp_inf (Axiom' a) = (Axiom, C (pp_list pp_formula) a)
    | pp_inf (Refl' a) = (Refl, C pp_term a)
    | pp_inf (Assume' a) = (Assume, C pp_formula a)
    | pp_inf (Factor' a) = (Factor, C pp_thm a)
    | pp_inf (Inst' (sub,thm)) =
    (Inst,
     fn pp =>
     (begin_block pp INCONSISTENT 1;
      add_string pp "{";
      pp_binop " =" pp_string pp_subst pp ("sub",sub);
      add_string pp ","; add_break pp (1,0);
      pp_binop " =" pp_string pp_thm pp ("thm",thm);
      add_string pp "}";
      end_block pp))
    | pp_inf (Resolve' (res,pos,neg)) =
    (Resolve,
     fn pp =>
     (begin_block pp INCONSISTENT 1;
      add_string pp "{";
      pp_binop " =" pp_string pp_formula pp ("res",res);
      add_string pp ","; add_break pp (1,0);
      pp_binop " =" pp_string pp_thm pp ("pos",pos);
      add_string pp ","; add_break pp (1,0);
      pp_binop " =" pp_string pp_thm pp ("neg",neg);
      add_string pp "}";
      end_block pp))
    | pp_inf (Equality' (lit,path,res,lr,thm)) =
    (Equality,
     fn pp =>
     (begin_block pp INCONSISTENT 1;
      add_string pp "{";
      pp_binop " =" pp_string pp_formula pp ("lit",lit);
      add_string pp ","; add_break pp (1,0);
      pp_binop " =" pp_string (pp_list pp_int) pp ("path",path);
      add_string pp ","; add_break pp (1,0);
      pp_binop " =" pp_string pp_term pp ("res",res);
      add_string pp ","; add_break pp (1,0);
      pp_binop " =" pp_string pp_bool pp ("lr",lr);
      add_string pp ","; add_break pp (1,0);
      pp_binop " =" pp_string pp_thm pp ("thm",thm);
      add_string pp "}";
      end_block pp));
in
  fun pp_inference' pp inf =
    let
      val (i,ppf) = pp_inf inf
    in
      (begin_block pp INCONSISTENT 0;
       pp_inference pp i;
       (if i = Axiom then () else (add_break pp (1,0); ppf pp));
       end_block pp)
    end;
end;

fun pp_proof pp =
  let
    open PP
    fun pp_a (th,i) = (pp_thm pp th; add_newline pp; pp_inference' pp i)
    fun pp_x x = (add_newline pp; add_newline pp; pp_a x)
    fun pp_p [] = raise BUG "pp_proof" "empty"
      | pp_p (h :: t) = (pp_a h; app pp_x t)
  in
    fn p =>
    (begin_block pp CONSISTENT 0;
     begin_block pp CONSISTENT 1;
     add_string pp "[[[";
     add_newline pp;
     pp_p p;
     end_block pp;
     add_newline pp;
     add_string pp "]]]";
     end_block pp)
  end;

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
    | cm ((th1,th2) :: l) =
    if th1 = th2 then cm l else
      let
        val (l1,(p1,ths1)) = dest_thm th1
        val (l2,(p2,ths2)) = dest_thm th2
      in
        case lex_compare formula_compare (l1,l2) of EQUAL
          => (case cmp p1 p2 of EQUAL => cm (zip ths1 ths2 @ l) | x => x)
        | x => x
      end;
in
  fun thm_compare th1_th2 = cm [th1_th2];
end;

local
  val deps = snd o snd o dest_thm;
  val empty = Binarymap.mkDict thm_compare;
  fun peek th m = Binarymap.peek (m,th);
  fun ins (th,a) m = Binarymap.insert (m,th,a);
in
  fun thm_map f =
    let
      fun g th m =
        case peek th m of SOME a => (a,m)
        | NONE =>
          let
            val (al,m) = maps g (deps th) m
            val a = f (th,al)
          in
            (a, ins (th,a) m)
          end
    in
      fn th => fst (g th empty)
    end;
end;

local
  val deps = snd o snd o dest_thm;
  fun empty a = (Binaryset.empty thm_compare, a);
  fun mem th (s,_) = Binaryset.member (s,th);
  fun ins f th (s,a) = (Binaryset.add (s,th), f (th,a))
in
  fun thm_foldr f =
    let fun g (th,x) = if mem th x then x else ins f th (foldl g x (deps th))
    in fn a => fn th => snd (g (th, empty a))
    end;
end;

(* ------------------------------------------------------------------------- *)
(* Reconstructing proofs.                                                    *)
(* ------------------------------------------------------------------------- *)

fun reconstruct_resolvant cl1 cl2 (cl1',cl2') =
  case (subtract (setify cl1) cl1', subtract (setify cl2) cl2') of
    (_ :: _ :: _, _) => NONE
  | (_, _ :: _ :: _) => NONE
  | ([l],[]) => SOME l
  | ([],[l']) => SOME (negate l')
  | ([l],[l']) => if negate l = l' then SOME l else NONE
  | ([],[]) => SOME False;

fun reconstruct_equality l r =
  let
    fun recon_fn p (f,args) (f',args') rest =
      recon_tm
      (if f <> f' orelse length args <> length args' then rest
       else map (C cons p ## I) (enumerate 0 (zip args args')) @ rest)
    and recon_tm [] = NONE
      | recon_tm ((p,(tm,tm')) :: rest) =
      if tm = l andalso tm' = r then SOME (rev p)
      else
        case (tm,tm') of (Fn a, Fn a') => recon_fn p a a' rest
        | _ => recon_tm rest

    fun recon_lit (Not a) (Not a') = recon_lit a a'
      | recon_lit (Atom a) (Atom a') =
      if l <> r andalso a = a' then NONE else recon_tm [([],(a,a'))]
      | recon_lit _ _ = NONE
  in
    fn (lit,lit') =>
    case recon_lit lit lit' of SOME p => SOME (lit,p) | NONE => NONE
  end;

fun reconstruct (cl,(Axiom,[])) = Axiom' cl
  | reconstruct ([lit],(Refl,[])) = Refl' (lhs lit)
  | reconstruct ([fm, _], (Assume,[])) = Assume' fm
  | reconstruct (cl, (Inst,[th])) =
  Inst' (matchl_literals |<>| (zip (clause th) cl), th)
  | reconstruct (_, (Factor,[th])) = Factor' th
  | reconstruct (cl, (Resolve, [th1, th2])) =
  let
    val f = reconstruct_resolvant (clause th1) (clause th2)
    val l =
      case f (cl,cl) of SOME l => l
      | NONE =>
        case first f (List.tabulate (length cl, split cl)) of SOME l => l
        | NONE =>
          raise BUG "inference"
          ("couldn't reconstruct resolvant" ^
           "\nth = " ^ thm_to_string (AXIOM cl) ^
           "\nth1 = " ^ thm_to_string th1 ^
           "\nth2 = " ^ thm_to_string th2)
  in
    Resolve' (l,th1,th2)
  end
  | reconstruct (Not eq :: cl, (Equality,[th])) =
    if length (clause th) < length cl then
      let
        val (l,r) = dest_eq eq
        val lit = hd cl
        fun f (p |-> t) =
          if t = l then SOME (p,false)
          else if t = r then SOME (p,true)
          else NONE
      in
        case first f (literal_subterms lit) of SOME (p,lr) =>
          let
            val (l,r) = if lr then (l,r) else (r,l)
            val lit = literal_rewrite (p |-> l) lit
          in
            Equality' (lit,p,r,lr,th)
          end
        | NONE => raise BUG "inference" "couldn't reconstruct weak equality"
      end
    else
      let
        val line = zip (clause th) cl
        fun sync l r = first (reconstruct_equality l r) line
        val (l,r) = dest_eq eq
      in
        case sync l r of SOME (lit,p) => Equality' (lit,p,r,true,th)
        | NONE =>
          case sync r l of SOME (lit,p) => Equality' (lit,p,l,false,th)
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

val proof = thm_foldr (fn (th,l) => (th, inference th) :: l) [];

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

fun FUN_CONGRUENCE (function,arity) =
  let
    val xs = List.tabulate (arity, fn i => Var ("x" ^ int_to_string i))
    val ys = List.tabulate (arity, fn i => Var ("y" ^ int_to_string i))
    fun f (i,th) =
      EQUALITY (List.last (clause th)) [1,i] (List.nth (ys,i)) true th
    val refl = INST (("x" |-> Fn (function,xs)) ::> |<>|) REFLEXIVITY
  in
    foldl f refl (rev (interval 0 arity))
  end;

fun REL_CONGRUENCE (relation,arity) =
  let
    val xs = List.tabulate (arity, fn i => Var ("x" ^ int_to_string i))
    val ys = List.tabulate (arity, fn i => Var ("y" ^ int_to_string i))
    fun f (i,th) =
      EQUALITY (List.last (clause th)) [i] (List.nth (ys,i)) true th
    val refl = ASSUME (Not (Atom (Fn (relation,xs))))
  in
    foldl f refl (rev (interval 0 arity))
  end;

fun SYM lit th =
  let
    fun g x y = RESOLVE lit th (EQUALITY (refl x) [0] y true (REFL x))
    fun f (true,(x,y)) = g x y | f (false,(x,y)) = g y x
  in
    f ((I ## dest_eq) (dest_literal lit))
  end;

local
  fun psym lit =
    let
      val (s,(x,y)) = (I ## dest_eq) (dest_literal lit)
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

local
  fun rewr (rw,lr) (eq,r) (th,lit,p) = RESOLVE eq rw (EQUALITY lit p r lr th);

  fun exp (rw,lr) =
    let val eq = dest_unit rw
    in (eq, let val (l,r) = dest_eq eq in if lr then r else l end)
    end;
in
  fun REWR rw_lr th_lit_p = rewr rw_lr (exp rw_lr) th_lit_p;

  fun REWR' rw_lr ((th,lit),tm) p =
    let val eq_r as (eq,r) = exp rw_lr
    in ((rewr rw_lr eq_r (th,lit,p), literal_rewrite (p |-> r) lit), r)
    end;  
end;

fun DEPTH conv =
  let
    fun rewr_top (thl_tm as (_,tm)) p =
      (case total conv tm of NONE => thl_tm
       | SOME rw_lr => rewr_top (REWR' rw_lr thl_tm (rev p)) p)

    fun rewr new thl tm_orig p =
      let
        val (thl,tm) = rewr_top (thl,tm_orig) p
        val () = chattrans 2 "rewr" tm_orig tm term_to_string
      in
        if new orelse tm <> tm_orig then rewr_sub thl tm p else (thl,tm)
      end
    and rewr_sub thl tm_orig p =
      let
        val (thl,tm) = rewr_below thl tm_orig p
        val () = chattrans 3 "rewr_sub" tm_orig tm term_to_string
      in
        if tm <> tm_orig then rewr false thl tm p else (thl,tm)
      end
    and rewr_below thl (tm as Var _) _ = (thl,tm)
      | rewr_below thl (tm as Fn (name,xs)) p =
      let
        fun f ((n,x),(tl,ys)) =
          let val (tl,y) = rewr true tl x (n :: p) in (tl, y :: ys) end
        val (thl,ys) = (I ## rev) (foldl f (thl,[]) (enumerate 0 xs))
      in
        (thl, if xs = ys then tm else Fn (name,ys))
      end

    fun rewr_lits (lit,th) =
      if not (mem lit (clause th)) then
        (assert (is_eq (negate lit)) (BUG "DEPTH" "weird"); th)
      else fst (fst (rewr_below (th,lit) (dest_atom (literal_atom lit)) []))
  in
    fn th =>
    let
      val th' = foldl rewr_lits th (clause th)
      val () = chattrans 1 "DEPTH" th th' thm_to_string
    in
      th'
    end
    handle ERR_EXN _ => raise BUG "DEPTH" "shouldn't fail"
  end;

end
