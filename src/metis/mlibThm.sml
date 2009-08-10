(* ========================================================================= *)
(* INTERFACE TO THE LCF-STYLE LOGICAL KERNEL, PLUS SOME DERIVED RULES        *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
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
  | _ => raise Error "dest_axiom";

val is_axiom = can dest_axiom;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing of theorems                                               *)
(* ------------------------------------------------------------------------- *)

fun pp_thm pp th =
  (PP.begin_block pp PP.INCONSISTENT 3;
   PP.add_string pp "|- ";
   pp_formula pp (list_mk_disj (clause th));
   PP.end_block pp);

fun inference_to_string Axiom = "Axiom"
  | inference_to_string Refl = "Refl"
  | inference_to_string Assume = "Assume"
  | inference_to_string Inst = "Inst"
  | inference_to_string Factor = "Factor"
  | inference_to_string Resolve = "Resolve"
  | inference_to_string Equality = "Equality";

val pp_inference = pp_map inference_to_string pp_string;

fun dest_inference' (Axiom' _) = Axiom
  | dest_inference' (Refl' _) = Refl
  | dest_inference' (Assume' _) = Assume
  | dest_inference' (Factor' _) = Factor
  | dest_inference' (Inst' _) = Inst
  | dest_inference' (Resolve' _) = Resolve
  | dest_inference' (Equality' _) = Equality;

local
  open PP;

  fun pp_inf pp_ax pp_th pp inf =
    let
      fun pp_i (Axiom' a) = pp_ax pp a
        | pp_i (Refl' a) = (add_break pp (1,0); pp_term pp a)
        | pp_i (Assume' a) = (add_break pp (1,0); pp_formula pp a)
        | pp_i (Factor' a) = (add_break pp (1,0); pp_th pp a)
        | pp_i (Inst' (sub,thm)) =
        (add_break pp (1,0);
         begin_block pp INCONSISTENT 1;
         add_string pp "{";
         pp_binop " =" pp_string pp_subst pp ("sub",sub);
         add_string pp ","; add_break pp (1,0);
         pp_binop " =" pp_string pp_th pp ("thm",thm);
         add_string pp "}";
         end_block pp)
        | pp_i (Resolve' (res,pos,neg)) =
        (add_break pp (1,0);
         begin_block pp INCONSISTENT 1;
         add_string pp "{";
         pp_binop " =" pp_string pp_formula pp ("res",res);
         add_string pp ","; add_break pp (1,0);
         pp_binop " =" pp_string pp_th pp ("pos",pos);
         add_string pp ","; add_break pp (1,0);
         pp_binop " =" pp_string pp_th pp ("neg",neg);
         add_string pp "}";
         end_block pp)
        | pp_i (Equality' (lit,path,res,lr,thm)) =
        (add_break pp (1,0);
         begin_block pp INCONSISTENT 1;
         add_string pp "{";
         pp_binop " =" pp_string pp_formula pp ("lit",lit);
         add_string pp ","; add_break pp (1,0);
         pp_binop " =" pp_string (pp_list pp_int) pp ("path",path);
         add_string pp ","; add_break pp (1,0);
         pp_binop " =" pp_string pp_term pp ("res",res);
         add_string pp ","; add_break pp (1,0);
         pp_binop " =" pp_string pp_bool pp ("lr",lr);
         add_string pp ","; add_break pp (1,0);
         pp_binop " =" pp_string pp_th pp ("thm",thm);
         add_string pp "}";
         end_block pp)
    in
      begin_block pp INCONSISTENT 0;
      pp_inference pp (dest_inference' inf);
      pp_i inf;
      end_block pp
    end;

  fun pp_axiom pp fms = (add_break pp (1,0); pp_list pp_formula pp fms);
in
  val pp_inference' = pp_inf pp_axiom pp_thm;

  fun pp_proof pp prf =
    let
      fun thm_string n = "(" ^ int_to_string n ^ ")"
      val prf = enumerate 0 prf
      fun pp_th pp th =
        case List.find (fn (_,(t,_)) => t = th) prf of
          NONE => add_string pp "(???)"
        | SOME (n,_) => add_string pp (thm_string n)
      fun pp_step (n,(th,i)) =
        let
          val s = thm_string n
        in
          begin_block pp CONSISTENT (1 + size s);
          add_string pp (s ^ " ");
          pp_thm pp th;
          add_break pp (2,0);
          pp_bracket "[" "]" (pp_inf (fn _ => fn _ => ()) pp_th) pp i;
          end_block pp;
          add_newline pp
        end
    in
      begin_block pp CONSISTENT 0;
      add_string pp "START OF PROOF";
      add_newline pp;
      app pp_step prf;
      add_string pp "END OF PROOF";
      add_newline pp;
      end_block pp
    end;
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
        case lex_list_order formula_compare (l1,l2) of EQUAL
          => (case cmp p1 p2 of EQUAL => cm (zip ths1 ths2 @ l) | x => x)
        | x => x
      end;
in
  fun thm_compare th1_th2 = cm [th1_th2];
end;

local
  val deps = snd o snd o dest_thm;
  fun empty () = Binarymap.mkDict thm_compare;
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
      fn th => fst (g th (empty ()))
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
        case first f (List.tabulate (length cl, divide cl)) of SOME l => l
        | NONE =>
          raise Bug
          ("inference: couldn't reconstruct resolvant" ^
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
        | NONE => raise Bug "inference: couldn't reconstruct weak equality"
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
          | NONE => raise Bug "inference: couldn't reconstruct equality step"
      end
  | reconstruct _ = raise Bug "inference: malformed inference";

fun inference th =
  let
    val i = reconstruct (dest_thm th)
    val _ =
      (primitive_inference i = th) orelse
      raise Bug
        ("inference: failed:\nth = " ^ thm_to_string th ^ "\ninf = "
         ^ inference_to_string i ^ "\ninf_th = "
         ^ thm_to_string (primitive_inference i))
  in
    i
  end;

val proof = rev o thm_foldr (fn (th,l) => (th, inference th) :: l) [];

(* ------------------------------------------------------------------------- *)
(* Contradictions and units.                                                 *)
(* ------------------------------------------------------------------------- *)

val is_contradiction = null o clause;

fun dest_unit th =
  case clause th of [lit] => lit | _ => raise Error "dest_unit: not a unit";

val is_unit = can dest_unit;

val dest_unit_eq = dest_eq o dest_unit;

val is_unit_eq = can dest_unit_eq;

(* ------------------------------------------------------------------------- *)
(* Derived rules                                                             *)
(* ------------------------------------------------------------------------- *)

fun CONTR False th = th
  | CONTR lit th = RESOLVE (negate lit) (ASSUME lit) th;

fun WEAKEN lits th = foldl (uncurry CONTR) th (rev lits);

fun FRESH_VARSL ths =
  let
    val fvs = FVL [] (List.concat (map clause ths))
    val vvs = new_vars (length fvs)
    val sub = mlibSubst.from_maplets (zipwith (curry op |->) fvs vvs)
  in
    map (INST sub) ths
  end
  handle Error _ => raise Bug "FRESH_VARSL: shouldn't fail";

val FRESH_VARS = hd o FRESH_VARSL o sing;

fun UNIT_SQUASH th =
  case clause th of [] => raise Error "UNIT_SQUASH: contradiction"
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
      val () = assert (x <> y) (Error "psym: refl")
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

fun REWR' (rw,r,lr) ((th,lit),tm) p =
  let
    val eq = if lr then mk_eq (tm,r) else mk_eq (r,tm)
    val th' = RESOLVE eq rw (EQUALITY lit p r lr th)
    val lit' = literal_rewrite (p |-> r) lit
    val tm' = r
  in
    ((th',lit'),tm')
  end;

fun REWR (rw,lr) (th,lit,p) =
  let val r = let val (x,y) = dest_unit_eq rw in if lr then y else x end
  in fst (fst (REWR' (rw,r,lr) ((th,lit), literal_subterm p lit) p))
  end;

fun DEPTH1 conv =
  let
    fun rewr_top (thl_tm as (_,tm)) p =
      (case total conv tm of NONE => thl_tm
       | SOME rw_r_lr => rewr_top (REWR' rw_r_lr thl_tm (rev p)) p)

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

    fun rewr_lit th lit =
      fst (rewr_below (th,lit) (dest_atom (literal_atom lit)) [])
  in
    fn (th,lit) =>
    let
      val () = assert (mem lit (clause th)) (Bug "DEPTH1: no such literal")
      val (th',lit') = rewr_lit th lit
      val () = chattrans 3 "DEPTH1 (thm)" th th' thm_to_string
      val () = chattrans 2 "DEPTH1 (lit)" lit lit' formula_to_string
    in
      (th',lit')
    end
    handle Error _ => raise Bug "DEPTH1: shouldn't fail"
  end;

fun DEPTH conv =
  let
    fun rewr_lit (lit,th) =
      if mem lit (clause th) then fst (DEPTH1 conv (th,lit))
      else (assert (is_eq (negate lit)) (Bug "DEPTH: vanished"); th)
  in
    fn th =>
    let
      val th' = foldl rewr_lit th (clause th)
      val () = chattrans 1 "DEPTH" th th' thm_to_string
    in
      th'
    end
    handle Error _ => raise Bug "DEPTH: shouldn't fail"
  end;

(* ------------------------------------------------------------------------- *)
(* Converting to clauses                                                     *)
(* ------------------------------------------------------------------------- *)

val axiomatize = map AXIOM o mlibCanon.clausal;

val eq_axioms =
  let
    val functions' = List.filter (fn (_,n) => 0 < n) o functions
    val relations' = List.filter (non (equal eq_rel)) o relations
    val eqs = [REFLEXIVITY, SYMMETRY, TRANSITIVITY]
    val rels = map REL_CONGRUENCE o relations'
    val funs = map FUN_CONGRUENCE o functions'
  in
    fn fm => eqs @ funs fm @ rels fm
  end;

local
  fun eq_axs g = if eq_occurs g then eq_axioms g else [];
  fun raw a b = (axiomatize a, axiomatize b);
  fun semi g a b = (eq_axs g @ axiomatize a, axiomatize (Not b));
  fun full g = ([], eq_axs g @ axiomatize (Not g));
  fun is_raw a b = mlibCanon.is_cnf a andalso mlibCanon.is_cnf b;
  fun is_semi a b = mlibCanon.is_cnf a andalso mlibCanon.is_clause b andalso b <> False;
in
  fun clauses g =
      let
        val g = generalize g
        val (thms,hyps) =
            case g of
              Imp (a, Imp (b, False)) => if is_raw a b then raw a b else full g
            | Imp (a,b) => if is_semi a b then semi g a b else full g
            | _ => full g
      in
        {thms = thms, hyps = hyps}
      end;
end;

end
