(* ========================================================================= *)
(* ORDERED REWRITING                                                         *)
(* Created by Joe Hurd, June 2003                                            *)
(* ========================================================================= *)

(*
app load ["mlibHeap", "mlibTerm", "mlibSubst", "mlibMatch", "mlibThm", "mlibTermorder"];
*)

(*
*)
structure mlibRewrite :> mlibRewrite =
struct

infix ## |-> ::>;

open mlibUseful mlibTerm mlibThm mlibMatch;

structure O = Option; local open Option in end;
structure M = Intmap; local open Intmap in end;
structure S = Intset; local open Intset in end;
structure T = mlibTermnet; local open mlibTermnet in end;

type 'a intmap  = 'a M.intmap;
type intset     = S.intset;
type subst      = mlibSubst.subst;
type 'a termnet = 'a T.termnet;

val |<>|          = mlibSubst.|<>|;
val op::>         = mlibSubst.::>;
val term_subst    = mlibSubst.term_subst;
val formula_subst = mlibSubst.formula_subst;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val module = "mlibRewrite";
val () = traces := {module = module, alignment = I} :: !traces;
fun chatting l = tracing {module = module, level = l};
fun chat s = (trace s; true)

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

val pick = S.find (K true);

fun retrieve known i =
  (case M.peek (known,i) of SOME rw_ort => rw_ort
   | NONE => raise ERR "rewrite" "rewr has been rewritten away!");

(* ------------------------------------------------------------------------- *)
(* Representing ordered rewrites.                                            *)
(* ------------------------------------------------------------------------- *)

datatype orient = Refl | LtoR | RtoL | Both;

datatype rewrs = REWRS of
  {order    : term * term -> order option,
   known    : (thm * orient) intmap,
   rewrites : (int * bool) termnet,
   subterms : (int * int list) termnet,
   waiting  : intset};

fun update_waiting waiting rw =
  let
    val REWRS {order, known, rewrites, subterms, waiting = _} = rw
  in
    REWRS {order = order, known = known, rewrites = rewrites,
           subterms = subterms, waiting = waiting}
  end;

fun waiting_del i (rw as REWRS {waiting, ...}) =
  update_waiting (S.delete (waiting,i)) rw;

(* ------------------------------------------------------------------------- *)
(* Basic operations                                                          *)
(* ------------------------------------------------------------------------- *)

fun empty order =
  REWRS {order = order, known = M.empty (), rewrites = T.empty (),
         subterms = T.empty (), waiting = S.empty};

fun reset (REWRS {order, ...}) = empty order;

fun peek (REWRS {known, ...}) i = O.map fst (M.peek (known,i));

fun size (REWRS {known, ...}) = M.numItems known;

fun eqns (REWRS {known, ...}) =
  map (fn (i,(th,_)) => (i,th)) (M.listItems known);

(* ------------------------------------------------------------------------- *)
(* Pretty-printing                                                           *)
(* ------------------------------------------------------------------------- *)

local fun f Refl = "Refl" | f LtoR = "LtoR" | f RtoL = "RtoL" | f Both = "Both";
in val pp_orient = pp_map f pp_string;
end;

local
  val simple = pp_map (map snd o eqns) (pp_list pp_thm);

  fun kws (REWRS {known, waiting, subterms, ...}) =
    (M.listItems known,
     S.listItems waiting,
     subterms);

  val pp_kws =
    pp_triple
    (pp_list (pp_pair pp_int (pp_pair pp_thm pp_orient)))
    (pp_list pp_int)
    (T.pp_termnet (pp_pair pp_int (pp_list pp_int)));

  val complicated = pp_map kws pp_kws;
in
  fun pp_rewrs pp = (if chatting 3 then complicated else simple) pp;
end;

fun rewrs_to_string rw = PP.pp_to_string (!LINE_LENGTH) pp_rewrs rw;

fun chatrewrs s rw =
  chat (module ^ "." ^ s ^ ":\n" ^ rewrs_to_string rw ^ "\n");

(* ------------------------------------------------------------------------- *)
(* Add an equation into the system                                           *)
(* ------------------------------------------------------------------------- *)

fun orient (SOME EQUAL) = Refl
  | orient (SOME GREATER) = LtoR
  | orient (SOME LESS) = RtoL
  | orient NONE = Both;

fun add_rewrite i (th,ort) rewrites =
  let
    val (l,r) = dest_unit_eq th
  in
    case ort of Refl => raise BUG "add_rewrite" "Refl"
    | LtoR => T.insert (l |-> (i,true)) rewrites
    | RtoL => T.insert (r |-> (i,false)) rewrites
    | Both => T.insert (l |-> (i,true)) (T.insert (r |-> (i,false)) rewrites)
  end;

fun add ith rw =
  let
    val (i,th) = ith
    val REWRS {order, known, rewrites, subterms, waiting} = rw
    val ort = orient (order (dest_unit_eq th))
    val () = assert (ort <> Refl) (BUG "mlibRewrite.add" "can't add reflexive eqns")
    val known = M.insert (known, i, (th,ort))
    val rewrites = add_rewrite i (th,ort) rewrites
    val waiting = S.add (waiting,i)
    val rw = REWRS {order = order, known = known, rewrites = rewrites,
                    subterms = subterms, waiting = waiting}
    val _ = chatting 1 andalso chatrewrs "add" rw
  in
    rw
  end;

(* ------------------------------------------------------------------------- *)
(* Rewriting (the order must be a refinement of the initial order)           *)
(* ------------------------------------------------------------------------- *)

fun thm_match known order (i,th) =
  let
    fun orw (l,r) tm =
      let val sub = match l tm
      in assert (order (tm, term_subst sub r) = SOME GREATER) (ERR "orw" "")
      end
    fun rw ((l,_),LtoR) tm = can (match l) tm
      | rw ((_,r),RtoL) tm = can (match r) tm
      | rw ((l,r),Both) tm = can (orw (l,r)) tm orelse can (orw (r,l)) tm
      | rw (_,Refl) _ = raise BUG "mlibRewrite.rewrite" "encountered a Refl"
    fun f (_,(th,ort)) = (dest_unit_eq th, ort)
    val eqs = (map f o List.filter (not o equal i o fst) o M.listItems) known
    fun can_rw tm = List.exists (fn eq => rw eq tm) eqs orelse can_depth tm
    and can_depth (Var _) = false
      | can_depth (Fn (_,tms)) = List.exists can_rw tms
    val lit_match = can_depth o dest_atom o literal_atom
  in
    List.exists lit_match (clause th)
  end;

local
  fun agree false LtoR = false | agree true RtoL = false | agree _ _ = true;

  fun redex_residue lr th = (if lr then I else swap) (dest_unit_eq th);

  val reorder = rev o sort (fn ((i,_),(j,_)) => Int.compare (i,j));

  fun rewr' known rewrites order i =
    let
      fun f tm (j,lr) =
        let
          val () = assert (j <> i) (ERR "rewrite" "same theorem")
          val (rw,ort) = retrieve known j
          val () = assert (agree lr ort) (ERR "rewrite" "bad orientation")
          val (l,r) = redex_residue lr rw
          val sub = match l tm
          val () = assert
            (ort <> Both orelse order (tm, term_subst sub r) = SOME GREATER)
            (ERR "rewrite" "order violation")
        in
          (INST sub rw, lr)
        end
      fun mat tm = first (total (f tm)) (reorder (T.match rewrites tm))
    in
      DEPTH (partial (ERR "rewrite" "no matching rewrites") mat)
    end;

  fun rewr known rewrites order i th =
    if not (chatting 2) then rewr' known rewrites order i th else
      let
        val th' = rewr' known rewrites order i th
        val m = thm_match known order (i,th')
        val _ = chat ("rewrite:\n" ^ thm_to_string th ^ "\n ->\n" ^
                      thm_to_string th' ^ "\n")
        val () = assert (not m) (BUG "rewrite" "still matches after rewriting")
      in
        th'
      end;
in
  fun rewrite (REWRS {known, rewrites, ...}) order (i,th) =
    if M.numItems known = 0 then th else rewr known rewrites order i th;
end;

(* ------------------------------------------------------------------------- *)
(* Inter-reduce the equations in the system                                  *)
(* ------------------------------------------------------------------------- *)

fun add_subterms i =
  let fun f ((p |-> tm), subterms) = T.insert (tm |-> (i,p)) subterms
  in fn th => fn subterms => foldl f subterms (literal_subterms (dest_unit th))
  end;

fun same_redex eq ort eq' =
  let
    val (l,r) = dest_eq eq
    val (l',r') = dest_eq eq'
  in
    case ort of
      Refl => raise BUG "reduce" "Refl in waiting list"
    | LtoR => l = l'
    | RtoL => r = r'
    | Both => l = l' andalso r = r'
  end;

fun redex_residues eq ort =
  let
    val (l,r) = dest_eq eq
  in
    case ort of
      Refl => raise BUG "reduce" "Refl in redexes"
    | LtoR => [(l,r,true)]
    | RtoL => [(r,l,true)]
    | Both => [(l,r,false),(r,l,false)]
  end;

fun reduce1 new i (rpl,spl,todo,rw) =
  let
    val REWRS {order, known, rewrites, subterms, waiting} = rw
    val (th0,ort0) = M.retrieve (known,i)
    val eq0 = dest_unit th0
    val th = rewrite rw order (i,th0)
    val eq = dest_unit th
    val identical = eq = eq0
    val same = identical orelse (ort0 <> Both andalso same_redex eq0 ort0 eq)
    val ort = if same then ort0 else orient (order (dest_eq eq))
    val known =
      if identical then known
      else if ort = Refl then fst (M.remove (known,i))
      else M.insert (known,i,(th,ort))
    val rpl = if same then rpl else S.add (rpl,i)
    val rewrites =
      if same orelse ort = Refl then rewrites
      else add_rewrite i (th,ort) rewrites
    val todo = if same andalso not new orelse ort = Refl then todo else
      let
        fun valid (l,r,ord) (j,p) =
          let
            val t = literal_subterm p (dest_unit (fst (retrieve known j)))
            val s = match l t
          in
            assert (ord orelse order (t, term_subst s r) = SOME GREATER)
            (ERR "valid" "violates order")
          end
        fun ck lr (jp as (j,_), todo) =
          if i <> j andalso not (S.member (todo,j)) andalso can (valid lr) jp
          then S.add (todo,j) else todo
        fun check (lr as (l,_,_), todo) =
          foldl (ck lr) todo (T.matched subterms l)
      in
        foldl check todo (redex_residues eq ort)
      end
    val spl = if new orelse identical then spl else S.add (spl,i)
    val subterms = if identical andalso not new orelse ort = Refl then subterms
                   else add_subterms i th subterms
  in
    (rpl, spl, todo,
     REWRS {order = order, known = known, rewrites = rewrites,
            subterms = subterms, waiting = waiting})
  end;

fun add_rewrs known (i,rewrs) =
  (case M.peek (known,i) of NONE => rewrs
   | SOME th_ort => add_rewrite i th_ort rewrs);

fun add_stms known (i,stms) =
  (case M.peek (known,i) of NONE => stms
   | SOME (th,_) => add_subterms i th stms);

fun rebuild rpl spl rw =
  let
    val REWRS {order, known, rewrites, subterms, waiting} = rw
    val rewrites =
      if S.isEmpty rpl then rewrites
      else T.filter (fn (i,_) => not (S.member (rpl,i))) rewrites
    val rewrites = S.foldl (add_rewrs known) rewrites rpl
    val subterms =
      if S.isEmpty spl then subterms
      else T.filter (fn (i,_) => not (S.member (spl,i))) subterms
    val subterms = S.foldl (add_stms known) subterms spl
  in
    REWRS {order = order, known = known, rewrites = rewrites,
           subterms = subterms, waiting = waiting}
  end;

fun reduce_acc (rpl, spl, todo, rw as REWRS {waiting, ...}) =
  case pick todo of
    SOME i => reduce_acc (reduce1 false i (rpl, spl, S.delete (todo,i), rw))
  | NONE =>
    case pick waiting of
      SOME i => reduce_acc (reduce1 true i (rpl, spl, todo, waiting_del i rw))
    | NONE => rebuild rpl spl rw;

fun reduce' rw = reduce_acc (S.empty, S.empty, S.empty, rw);

fun reduce rw =
  if not (chatting 2) then reduce' rw else
    let
      val REWRS {known, order, ...} = rw
      val rw' = reduce' rw
      val REWRS {known = known', ...} = rw'
      val eqs = map (fn (i,(th,_)) => (i,th)) (M.listItems known')
      val m = List.exists (thm_match known order) eqs
      val _ = chatrewrs "reduce before" rw
      val _ = chatrewrs "reduce after" rw'
      val () = assert (not m) (BUG "reduce" "not fully reduced")
    in
      rw'
    end;

(* ------------------------------------------------------------------------- *)
(* Rewriting as a derived rule                                               *)
(* ------------------------------------------------------------------------- *)

local
  fun f (th,(n,rw)) = (n + 1, add (n, FRESH_VARS th) rw);
in
  fun ORD_REWRITE ord ths =
    let val (_,rw) = foldl f (0, empty ord) ths
    in rewrite rw ord o pair ~1
    end;
end;

val REWRITE = ORD_REWRITE (K (SOME GREATER));

end
