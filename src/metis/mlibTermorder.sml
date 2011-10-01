(* ========================================================================= *)
(* KNUTH-BENDIX TERM ORDERING CONSTRAINTS                                    *)
(* Copyright (c) 2002-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

(*
app load ["Binaryset", "mlibOmega", "mlibTerm", "mlibSubst"];
*)

(*
*)
structure mlibTermorder :> mlibTermorder =
struct

infix ## |-> ::>;

open mlibUseful mlibTerm;

structure O = Option; local open Option in end;
structure S = Binaryset; local open Binaryset in end;
structure B = Binarymap; local open Binarymap in end;
structure M = mlibMultiset; local open mlibMultiset in end;

type subst   = mlibSubst.subst;
type 'a mset = 'a M.mset;

val |<>|          = mlibSubst.|<>|;
val op::>         = mlibSubst.::>;
val term_subst    = mlibSubst.term_subst;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val module = "mlibTermorder";
val () = traces := {module = module, alignment = I} :: !traces;
fun chatting l = tracing {module = module, level = l};
fun chat s = (trace s; true)

(* ------------------------------------------------------------------------- *)
(* Parameters                                                                *)
(* ------------------------------------------------------------------------- *)

type parameters =
  {weight     : string * int -> int,
   precedence : (string * int) * (string * int) -> order,
   precision  : int};

(* Default weight = uniform *)

val uniform : string * int -> int = fn _ => 1;

(* Default precedence = by arity *)

val arity : (string * int) * (string * int) -> order =
  fn ((f,m),(g,n)) =>
  if m < n then LESS else if m > n then GREATER else
  let val p = String.size f
      and q = String.size g
  in if p < q then LESS else if p > q then GREATER else String.compare (f,g)
  end;

val defaults =
  {weight     = uniform,
   precedence = arity,
   precision  = 3};

fun update_precision f (parm : parameters) : parameters =
  let val {weight = w, precedence = p, precision = r} = parm
  in {weight = w, precedence = p, precision = f r}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

val eqn_sum = M.foldl (fn (_,n,m) => n + m) 0;

fun eqn_var _ ("",_,vs) = vs | eqn_var f (v,_,vs) = f v vs;

fun list_eqn vars =
  let val vars = vars @ [""] in fn eqn => map (M.count eqn) vars end;

local
  val no_vars = mlibMultiset.empty String.compare;
  fun one_var v = mlibMultiset.insert (v,1) no_vars;

  fun kb_weight w =
    let
      fun weight (Var v) = (0, one_var v)
        | weight (Fn (f, a)) = foldl wght (w (f, length a), no_vars) a
      and wght (t, (n, v)) = (curry op+ n ## mlibMultiset.union v) (weight t)
    in
      weight
    end;
in
  fun weight wf t = let val (n,w) = kb_weight wf t in M.insert ("",n) w end;
end;

local
  val emptys = S.empty String.compare;
  fun inserts v vs = S.add (vs,v);
in
  val calc_vars =
    S.listItems o foldl (fn (q,v) => M.foldl (eqn_var inserts) v q) emptys;
end;

fun partialorder_to_string (SOME LESS) = "SOME LESS"
  | partialorder_to_string (SOME GREATER) = "SOME GREATER"
  | partialorder_to_string (SOME EQUAL) = "SOME EQUAL"
  | partialorder_to_string NONE = "NONE";

(* ------------------------------------------------------------------------- *)
(* Normalizing equations means checking for trivial cases and tidying up     *)
(* ------------------------------------------------------------------------- *)

fun divide_gcd eqn =
  let val g = M.foldl (fn (_,m,n) => gcd m n) 0 eqn
  in if g <= 1 then eqn else M.map (fn (_,n) => n div g) eqn
  end;

(* If an equation satisfies this it's inconsistent: some var must be <= 0 *)
fun inconsistent_eqn q =
  M.all (fn ("",_) => true | (_,n) => n < 0) q andalso eqn_sum q < 0;

local
  (* If an equation satisfies pos then it's completely uninformative *)
  fun pos q =
    M.all (fn ("",_) => true | (_,n) => 0 <= n) q andalso 0 <= eqn_sum q;

  (* bad is a weaker condition, a compromise for efficiency *)
  fun bad q =
    0 <= M.foldl (fn ("",_,m) => m | (_,n,m) => n + m) 0 q andalso
    0 <= M.foldl (fn ("",_,m) => m | (_,n,m) => if 0<n then m+1 else m-1) 0 q;

  (* An equation being unbounded is an incredibly weak condition *)
  fun trivial q = M.nonzero q=0 orelse M.nonzero q=1 andalso 0<M.count q "";
  fun unbounded q = M.exists (fn ("",_) => false | (_,n) => 0 < n) q;
in
  fun good_eqn (parm : parameters) eqn =
    if inconsistent_eqn eqn then raise Error "good_eqn: inconsistent"
    else if #precision parm <= 0 then false
    else if #precision parm <= 1 then not (unbounded eqn orelse trivial eqn)
    else if #precision parm <= 2 then not (bad eqn)
    else not (pos eqn);
end;

fun normalize parm =
  let
    fun g (q,l) = if good_eqn parm q then q :: l else l
    fun f (q,l) = g (divide_gcd q, l)
  in
    foldl f []
  end;

(* ------------------------------------------------------------------------- *)
(* Deriving an equation from a term comparison.                              *)
(* ------------------------------------------------------------------------- *)

datatype eqn = Equal | Less | Greater | Equation of string mset;

fun mk_eqn (parm : parameters) =
  let
    val {weight = wf, precedence, ...} = parm
    fun f [] = Equal
      | f ((l,r) :: rest) =
      if l = r then f rest else
        let val w = M.subtract (weight wf r) (weight wf l)
        in if M.nonzero w = 0 then g l r rest else Equation (divide_gcd w)
        end
    and g (Fn (f1,a1)) (Fn (f2,a2)) rest =
      (case precedence ((f1, length a1), (f2, length a2)) of LESS => Less
       | GREATER => Greater
       | EQUAL => f (zip a1 a2 @ rest))
      | g (Var _) _ _ = Less
      | g _ (Var _) _ = Greater;
  in
    fn lr => f [lr]
  end;

(* ------------------------------------------------------------------------- *)
(* A partial order on equations, designed to be quick to check.              *)
(* ------------------------------------------------------------------------- *)

local
  fun gen_stronger cmp eqn1 eqn2 =
    M.all (fn ("",_) => true | (v,i) => i <= M.count eqn2 v) eqn1 andalso
    M.all (fn ("",_) => true | (v,i) => M.count eqn1 v <= i) eqn2 andalso
    cmp (eqn_sum eqn1, eqn_sum eqn2);
in
  val stronger = gen_stronger op<=;
  val strictly_stronger = gen_stronger op<;
end;

fun weaker eqn1 eqn2 = stronger eqn2 eqn1;
fun strictly_weaker eqn1 eqn2 = strictly_stronger eqn2 eqn1;

fun superfluous eqn eqns = List.exists (weaker eqn) eqns;
fun strictly_superfluous eqn eqns = List.exists (strictly_weaker eqn) eqns;

(* ------------------------------------------------------------------------- *)
(* The termorder type.                                                       *)
(*                                                                           *)
(* Invariants:                                                               *)
(*                                                                           *)
(* 1. The string list contains precisely the variables that appear (with     *)
(*    non-zero coefficient) in the eqns.                                     *)
(*                                                                           *)
(* 2. All the equations satisfy good_eqn.                                    *)
(*                                                                           *)
(* 3. The boolean is true whenever there are no equations, and otherwise     *)
(*    only if the termorder is known to be satisfiable.                      *)
(* ------------------------------------------------------------------------- *)

datatype termorder = TO of parameters * string list * string mset list * bool;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

fun pp_equation vars =
  let
    fun pp_tm pp ("",n) = pp_string pp (int_to_string n)
      | pp_tm pp (v,n) =
      pp_string pp ((if n=1 then "" else (int_to_string n^"*")) ^ v)
    fun pp_tms pp [] = pp_string pp "0"
      | pp_tms pp [tm] = pp_tm pp tm
      | pp_tms pp (tm :: tms) = pp_binop " +" pp_tm pp_tms pp (tm,tms)
  in
    fn pp => fn eqn =>
    let
      val eqn = zip (vars @ [""]) (list_eqn vars eqn)
      val tms = List.filter (fn (_,n) => n <> 0) eqn
      val (pos,neg) = List.partition (fn (_,n) => 0 < n) tms
      val neg = map (I ## ~) neg
    in
      pp_binop " <=" pp_tms pp_tms pp (neg,pos)
    end
  end;

fun pp_termorder pp (TO (_,vars,eqns,sat)) =
  pp_bracket "{" (if sat then "}*" else "}")
  (pp_binop " |" (pp_sequence "" pp_string)
   (pp_sequence "," (pp_equation vars))) pp (vars,eqns);

val termorder_to_string = PP.pp_to_string (!LINE_LENGTH) pp_termorder;

local
  val q2s = PP.pp_to_string (!LINE_LENGTH)
            (pp_list (pp_binop " |->" pp_string pp_int)) o M.to_list;

  fun wf_eqn vars eqn =
    if M.all (fn ("",_) => true | (v,_) => mem v vars) eqn then ()
    else raise Bug ("wf_eqn: malformed equation: " ^ q2s eqn);
in
  fun chatto n s (to as TO (_,vars,eqns,_)) =
    if not (chatting n) then () else
      (chat (s ^ ":\n" ^ termorder_to_string to ^ "\n");
       app (wf_eqn vars) eqns);
end;

(* ------------------------------------------------------------------------- *)
(* Basic operations                                                          *)
(* ------------------------------------------------------------------------- *)

fun empty parm = TO (parm,[],[],true);

fun TON parm eqns =
  let val eqns = normalize parm eqns
  in TO (parm, calc_vars eqns, eqns, null eqns)
  end;

fun tnull (TO (_,[],[],_)) = true | tnull _ = false;

fun vars (TO (_,fvs,_,_)) = fvs;

fun add_leq lr (to as TO (parm,vars,eqns,_)) =
  let
    fun keep eqn =
      good_eqn parm eqn andalso
      not (superfluous eqn eqns) andalso
      (if not (strictly_superfluous (M.compl eqn) eqns) then true
       else raise Error "add_leq: direct contradiction")

    fun inc eqn =
      let
        val () = chatto 1 "add_leq input" to
        val vars' = M.foldl (eqn_var insert) vars eqn
        val eqns' = eqn :: List.filter (not o stronger eqn) eqns
        val to = TO (parm,vars',eqns',false)
        val () = chatto 1 "add_leq result" to
      in
        to
      end
  in
    case mk_eqn parm lr of Equal => to
    | Less => to
    | Greater => raise Error "add_leq: violates order (weight)"
    | Equation eqn => if keep eqn then inc eqn else to
  end;

fun add_leqs lrs to = foldl (uncurry add_leq) to lrs;

local
  fun table_to_string vars vars' tab =
    let
      fun nicevar "" = "1" | nicevar v = v;
      fun nicerow l = "[" :: map (fn x => " " ^ x) (l @ ["]"])
      fun makerow v =
        nicevar v :: map (int_to_string o M.count (B.find (tab,v))) vars
    in
      join "\n"
      (align_table {left = false, pad = #" "}
       (map nicerow (("" :: map nicevar vars) :: map makerow vars'))) ^ "\n"
    end;

  fun new_vars vars mapl =
    let val (ls,rs) = unzip (map (fn x |-> y => (x,y)) mapl)
    in FVTL (List.filter (not o C mem ls) vars) rs
    end;

  val m0 = M.empty String.compare;
  fun m1 xi = M.insert xi m0;
  fun mn xis = foldl (uncurry M.insert) m0 xis;

  fun table_add parm vars' ((v |-> t), tab) =
    let
      val {weight = wf, ...} : parameters = parm
      fun add (w,i,t) = B.insert (t, w, M.insert (v, i) (B.find (t, w)))
      val tab = if not (mem v vars') then tab else add (v,~1,tab)
    in
      M.foldl add tab (weight wf t)
    end;

  fun mk_table parm vars vars' =
    let
      fun init (v,m) = B.insert (m, v, if mem v vars then m1 (v,1) else m0)
      val tab = foldl init (B.mkDict String.compare) vars'
    in
      foldl (table_add parm vars') tab
    end;

  fun new_eqn vars vars' tab eqn =
    let
      fun g (v,i,n) = n + M.count eqn v * i
      fun f (v,m) = M.insert (v, M.foldl g 0 (B.find (tab,v))) m
    in
      foldl f m0 vars'
    end;

  fun nontriv mapl (to as TO (parm,vars,eqns,_)) =
    let
      val () = chatto 1 "subst input" to
      val vars1 = "" :: vars
      val vars2 = "" :: new_vars vars mapl
      val tab = mk_table parm vars1 vars2 mapl
      val _ = chatting 1 andalso
              chat ("subst table:\n"^table_to_string vars1 vars2 tab)
      val eqns' = map (new_eqn vars1 vars2 tab) eqns
      val to = TON parm eqns'
      val () = chatto 1 "subst result" to
    in
      to
    end;
in
  fun subst sub (to as TO (_,vars,_,_)) =
    let val mapl = mlibSubst.to_maplets (mlibSubst.norm (mlibSubst.restrict vars sub))
    in if null mapl then to else nontriv mapl to
    end;
end;

local
  fun cast_away eqns = List.filter (fn eqn => not (superfluous eqn eqns));
in
  fun merge (TO (_,_,[],_)) to = to
    | merge to (TO (_,_,[],_)) = to
    | merge to1 to2 =
    let
      val () = chatto 1 "merge input1" to1
      val () = chatto 1 "merge input2" to2
      val TO (parm,_,eqns1,_) = to1
      val TO (_,_,eqns2,_) = to2
      val eqns1 = cast_away eqns2 eqns1
      val eqns2 = cast_away eqns1 eqns2
      val to =
        if null eqns1 then to2 else if null eqns2 then to1 else
          let val eqns = eqns1 @ eqns2
          in TO (parm, calc_vars eqns, eqns, false)
          end
      val () = chatto 1 "merge result" to
    in
      to
    end;
end;

(* ------------------------------------------------------------------------- *)
(* Interface to mlibOmega.                                                       *)
(* ------------------------------------------------------------------------- *)

local
  val raw_equations_to_string =
    String.concat o
    map (fn x => PP.pp_to_string (!LINE_LENGTH) (pp_list pp_int) x ^ "\n");

  fun pos_eqns n =
    snd (funpow n (fn (t,r) => (0 :: t, (1 :: t) :: map (cons 0) r)) ([~1],[]));

  (* Remember that list_eqn does partial evaluation on vars *)
  fun omega_eqns vars eqns = pos_eqns (length vars) @ map (list_eqn vars) eqns;

  open mlibOmega;

  fun mk_db normalc eqns db exc =
    case eqns of [] => normalc db
    | c :: cs =>
      add_check_factoid db (gcd_check_dfactoid (fromList c, ASM ()))
      (mk_db normalc cs) exc;

  fun check eqns =
    mk_db (fn db => work db I) eqns (dbempty (length (hd eqns))) I;

  fun inconsistent (SATISFIABLE _) = false
    | inconsistent (CONTR _) = true
    | inconsistent NO_CONCL = false;

  (* Uncomment this check function to print out the linear arithmetic problems
  val THRESHOLD = 1.0;

  fun result_to_string (SATISFIABLE _) = "satisfiable"
    | result_to_string (CONTR _) = "inconsistent"
    | result_to_string NO_CONCL = "no conclusion";

  val check = fn eqns =>
    let
      val (t,r) = timed check eqns
      val () =
        if t < THRESHOLD then () else
          print ("\n\nOMEGA: time = " ^ Real.fmt (StringCvt.FIX (SOME 3)) t ^
                 "s\n" ^ raw_equations_to_string eqns ^
                 "OMEGA: " ^ result_to_string r ^ "\n\n")
    in
      r
    end;
  *)
in
  fun consistent (to as TO (_,_,_,true)) = SOME to
    | consistent (to as TO (parm,vars,eqns,false)) =
    let
      val () = chatto 1 "consistent" to
    in
      if inconsistent (check (omega_eqns vars eqns)) then NONE
      else SOME (TO (parm,vars,eqns,true))
    end;
(* This bug has now been fixed, but others may appear in the future :-)
    handle Option =>
      (print ("BUG in mlibOmega library: uncaught Option exception" ^
              "\ntermorder was:\n" ^ termorder_to_string to ^
              "\nsent to mlibOmega:\n" ^ raw_equations_to_string (omega_eqns to) ^
              "\n\n"); true)
*)
end;

(* ------------------------------------------------------------------------- *)
(* Query.                                                                    *)
(* ------------------------------------------------------------------------- *)

fun subsumes (TO (_,_,eqns1,_)) (TO (_,_,eqns2,_)) =
  List.all (fn eqn => superfluous eqn eqns2) eqns1;

local
  fun cmp _ _ Equal = SOME EQUAL
    | cmp _ _ Less = SOME LESS
    | cmp _ _ Greater = SOME GREATER
    | cmp parm eqns (Equation eqn) =
    let
      val eqn' = M.compl eqn
    in
      if inconsistent_eqn eqn then SOME GREATER
      else if inconsistent_eqn eqn' then SOME LESS
      else if strictly_superfluous eqn eqns then SOME LESS
      else if strictly_superfluous eqn' eqns then SOME GREATER
      else NONE
    end;
in
  fun compare (to as TO (parm,_,eqns,_)) lr =
    let
      val () = chatto 1 "compare input" to
      val _ = chatting 1 andalso
              chat ("comparing " ^ term_to_string (fst lr) ^
                    " and " ^ term_to_string (snd lr) ^ "\n")
      val res = cmp parm eqns (mk_eqn parm lr)
      val _ = chatting 1 andalso
              chat ("compare result = " ^ partialorder_to_string res ^ "\n")
    in
      res
    end;
end;

(* ------------------------------------------------------------------------- *)
(* Name binding.                                                             *)
(* ------------------------------------------------------------------------- *)

val null = tnull;

(* Quick testing
app load ["mlibThm"];
val () = quotation := true;
val T = parse_term;
val F = parse_formula;
installPP pp_termorder;
installPP mlibSubst.pp_subst;
installPP mlibThm.pp_thm;

val to = empty defaults;
val to = try (C add_leq to) (T`f x (f y z)`, T`f (f x y) z`);
val x = (total o try) (C add_leq to) (T`f (f x y) z`, T`f x (f y z)`);
val to = try (C add_leq to) (T`P (f a b)`, T`P x`);
val to = try (C add_leq to) (T`P y`, T`P (g a b c)`);
val to = try (C add_leq to) (T`x + y`, T`y + x`);
val c = consistent to;
val to = try (subst (("x" |-> T`v`) ::> |<>|)) to;
val to = try (subst (("v" |-> T`f x x x x a a a a`) ::> |<>|)) to;
val c = consistent to;

val to = empty defaults;
val to = try (C add_leq to) (T`P y`, T`P (g a b c d e f)`);
val to = try (C add_leq to) (T`x + y`, T`y + x`);
val to = try (C add_leq to) (T`x + y`, T`y + x`);
val to = try (subst (("x" |-> T`f x x x`) ::> |<>|)) to;
val c = consistent to;
val to = try (subst (("x" |-> T`f w v`) ::> |<>|)) to;
val c = consistent to;

val to = empty defaults;
val to = try (C add_leq to) (T`f x y`, T`f y x`);
val to = try (subst (("x" |-> T`f x`) ::> |<>|)) to;
val x = compare to (T`f x`, T`g y`);
val x = compare to (T`g x`, T`f y`);
val x = compare to (T`g a`, T`f a`);
val x = compare to (T`f a`, T`g a`);
val th =
  mlibThm.ORD_REWRITE (compare to)
  (map (mlibThm.AXIOM o wrap o F)
   [`x + (y + z) = y + (x + z)`, `(x + y) + z = x + (y + z)`])
  (mlibThm.AXIOM [F`P (y + x + y + x + y + x + 0)`]);
*)

end
