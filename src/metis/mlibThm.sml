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
  | primitive_inference (Inst'     (s,th)         ) = INST s th
  | primitive_inference (Factor'   th              ) = FACTOR th
  | primitive_inference (Resolve'  (l,th1,th2)   ) = RESOLVE l th1 th2
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
  val thm_compare = cm o wrap;
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

fun SUBST (rw,lr,r) (th,lit,p) =
  RESOLVE (dest_unit rw) rw (EQUALITY lit p r lr th);

fun REWR (rw,lr) tm =
  let
    val (l,r) = (if lr then I else swap) (dest_unit_eq rw)
    val env = match l tm
  in
    (INST env rw, lr, term_subst env r)
  end;

fun DEPTH conv =
  let
    fun rewr1 (th,lit) (x as (_,_,r)) p =
      (SUBST x (th,lit,p), literal_rewrite (p |-> r) lit)

    fun rewr_top thl tm p =
      (case total conv tm of NONE => (thl,tm)
       | SOME (x as (_,_,r)) => rewr_top (rewr1 thl x (rev p)) r p)

    fun rewr thl tm_orig p =
      let
        val _ = chatting 3 andalso
                chat ("rewr input: " ^ term_to_string tm_orig ^ "\n")
        val (thl,tm) = rewr_top thl tm_orig p
        val (thl,tm) = rewr_sub thl tm p
        val _ = chatting 2 andalso
                chat ("rewr: " ^ term_to_string tm_orig ^
                      " --> " ^ term_to_string tm ^ "\n")
      in
        if tm = tm_orig then (thl,tm) else rewr thl tm p
      end
    and rewr_sub thl (tm as Var _) _ = (thl,tm)
      | rewr_sub thl (tm as Fn (name,xs)) p =
      let
        val _ = chatting 3 andalso
                chat ("rewr_sub input: " ^ term_to_string tm ^ "\n")
        fun f ((n,x),(tl,ys)) =
          let val (tl,y) = rewr tl x (n :: p) in (tl, y :: ys) end
        val (thl,ys) = (I ## rev) (foldl f (thl,[]) (enumerate 0 xs))
      in
        (thl, if ys = xs then tm else Fn (name,ys))
      end

    fun rewr_lits (lit,th) =
      if not (mem lit (clause th)) then
        (assert (is_eq (negate lit)) (BUG "DEPTH" "weird"); th)
      else fst (fst (rewr_sub (th,lit) (dest_atom (literal_atom lit)) []))
  in
    fn th =>
    let
      val th' = foldl rewr_lits th (clause th)
      val _ = chatting 1 andalso
              chat ("DEPTH: " ^ thm_to_string th ^
                    " --> " ^ thm_to_string th' ^ "\n")
    in
      th'
    end
    handle ERR_EXN _ => raise BUG "DEPTH" "shouldn't fail"
  end;
 
(* ------------------------------------------------------------------------- *)
(* Rewriting                                                                 *)
(* ------------------------------------------------------------------------- *)

type rewrs =
  (term * term -> order option) *
  (bool * int * thm * bool * term * term) T.termnet;

fun empty_rewrs ord : rewrs = (ord, T.empty ());

fun reset_rewrs ((ord,_) : rewrs) : rewrs = (ord, T.empty ());

fun add_rewr (i,rw) (ord,net) =
  let
    val lr as (l,r) = dest_unit_eq rw
    val f =
      case ord lr of SOME EQUAL => I
      | SOME GREATER => T.insert (l |-> (true,i,rw,true,l,r))
      | SOME LESS => T.insert (r |-> (true,i,rw,false,r,l))
      | NONE => T.insert (l |-> (false,i,rw,true,l,r)) o
                T.insert (r |-> (false,i,rw,false,r,l))
  in
    (ord, f net)
  end
  handle ERR_EXN _ => raise BUG "add_rewr" "shouldn't fail";

fun rewrite (_,net) ord (i,th) =
  if T.size net = 0 then th else
    let
      fun f tm (x,j,rw,lr,l,r) =
        let
          val () = assert (i <> j) (ERR "rewrite" "same theorem")
          val sub = match l tm
          val r = term_subst sub r
          val () = assert (x orelse ord (tm,r) = SOME GREATER)
            (ERR "rewrite" "order violation")
        in
          (INST sub rw, lr, r)
        end
      fun mat tm = first (total (f tm)) (rev (T.match net tm))
    in
      DEPTH (partial (ERR "rewrite" "no matching rewrites") mat) th
    end;

fun ORD_REWRITE ord ths =
  let
    val rws = empty_rewrs ord
    val rws = foldl (fn (th,n) => add_rewr (0, FRESH_VARS th) n) rws ths
  in
    rewrite rws ord o pair 1
  end;

val REWRITE = ORD_REWRITE (K (SOME GREATER));

end
