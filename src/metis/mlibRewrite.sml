(* ========================================================================= *)
(* ORDERED REWRITING                                                         *)
(* Copyright (c) 2003-2004 Joe Hurd.                                         *)
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

val blind_pick = S.find (K true);

fun retrieve known i =
  (case M.peek (known,i) of SOME rw_ort => rw_ort
   | NONE => raise Error "rewrite: rewr has been rewritten away!");

(* ------------------------------------------------------------------------- *)
(* Representing ordered rewrites.                                            *)
(* ------------------------------------------------------------------------- *)

datatype orient = LtoR | RtoL | Both;

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
  REWRS {order = order, known = M.empty (), rewrites = T.empty {fifo = false},
         subterms = T.empty {fifo = false}, waiting = S.empty};

fun reset (REWRS {order, ...}) = empty order;

fun peek (REWRS {known, ...}) i = M.peek (known,i);

fun size (REWRS {known, ...}) = M.numItems known;

fun eqns (REWRS {known, ...}) =
  map (fn (i,(th,_)) => th) (M.listItems known);

(* ------------------------------------------------------------------------- *)
(* Pretty-printing                                                           *)
(* ------------------------------------------------------------------------- *)

local fun f LtoR = "LtoR" | f RtoL = "RtoL" | f Both = "Both";
in val pp_orient = pp_map f pp_string;
end;

local
  val simple = pp_map eqns (pp_list pp_thm);

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

fun orient (SOME EQUAL) = NONE
  | orient (SOME GREATER) = SOME LtoR
  | orient (SOME LESS) = SOME RtoL
  | orient NONE = SOME Both;

fun add_rewrite i (th,ort) rewrites =
  let
    val (l,r) = dest_unit_eq th
  in
    case ort of
      LtoR => T.insert (l |-> (i,true)) rewrites
    | RtoL => T.insert (r |-> (i,false)) rewrites
    | Both => T.insert (l |-> (i,true)) (T.insert (r |-> (i,false)) rewrites)
  end;

fun add (i,th) (rw as REWRS {known, ...}) =
  if Option.isSome (M.peek (known,i)) then rw else
    let
      val REWRS {order, rewrites, subterms, waiting, ...} = rw
      val ort =
        case orient (order (dest_unit_eq th)) of SOME x => x
        | NONE => raise Bug "mlibRewrite.add: can't add reflexive eqns"
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
      in assert (order (tm, term_subst sub r) = SOME GREATER) (Error "orw")
      end
    fun rw ((l,_),LtoR) tm = can (match l) tm
      | rw ((_,r),RtoL) tm = can (match r) tm
      | rw ((l,r),Both) tm = can (orw (l,r)) tm orelse can (orw (r,l)) tm
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

  local val reorder = sort (fn ((i,_),(j,_)) => Int.compare (j,i));
  in fun get_rewrs rw tm = reorder (T.match rw tm);
  end;

  local
    fun compile_neq (SOME LtoR, lit) =
      let val lit' = dest_neg lit val (l,r) = dest_eq lit'
      in SOME (l, (ASSUME lit', r, true))
      end
      | compile_neq (SOME RtoL, lit) =
      let val lit' = dest_neg lit val (l,r) = dest_eq lit'
      in SOME (r, (ASSUME lit', l, false))
      end
      | compile_neq _ = NONE;
  in
    val compile_neqs = List.mapPartial compile_neq;
  end;

  fun rewr known rewrites order i =
    let
      fun rewr_lit neqs =
        let
          fun f tm (j,lr) =
            let
              val () = assert (j <> i) (Error "rewrite: same theorem")
              val (rw,ort) = retrieve known j
              val () = assert (agree lr ort) (Error "rewrite: bad orientation")
              val (l,r) = redex_residue lr rw
              val sub = match l tm
              val r' = term_subst sub r
              val () = assert
                (ort <> Both orelse order (tm,r') = SOME GREATER)
                (Error "rewrite: order violation")
            in
              (INST sub rw, r', lr)
            end
          fun rewr_conv tm = first (total (f tm)) (get_rewrs rewrites tm)
          fun neq_conv tm = Option.map snd (List.find (equal tm o fst) neqs)
          fun conv tm =
            case rewr_conv tm of SOME x => x
            | NONE => (case neq_conv tm of SOME x => x
                       | NONE => raise Error "rewrite: no matching rewrites")
        in
          DEPTH1 conv
        end

      fun orient_neq neq = orient (order (dest_eq (negate neq)))

      fun orient_neqs neqs = map (fn neq => (orient_neq neq, neq)) neqs

      fun rewr_neqs dealt [] th = (rev dealt, th)
        | rewr_neqs dealt ((ort,neq) :: neqs) th =
        if not (mem neq (clause th)) then rewr_neqs dealt neqs th else
          let
            val other_neqs = List.revAppend (dealt,neqs)
            val (th,neq') = rewr_lit (compile_neqs other_neqs) (th,neq)
          in
            if neq' = neq then rewr_neqs ((ort,neq) :: dealt) neqs th else
              let
                val ort = orient_neq neq'
                val active = ort = SOME LtoR orelse ort = SOME RtoL
              in
                if active then rewr_neqs [(ort,neq')] other_neqs th
                else rewr_neqs ((ort,neq') :: dealt) neqs th
              end
          end

      fun rewr' th =
        let
          val lits = clause th
          val (neqs,rest) = List.partition (is_eq o negate) lits
          val (neqs,th) = rewr_neqs [] (orient_neqs neqs) th
          val neqs = compile_neqs neqs
        in
          if M.numItems known = 0 andalso null neqs then th
          else foldl (fst o rewr_lit neqs o swap) th rest
        end
    in
      fn th =>
      if not (chatting 2) then rewr' th else
        let
          val th' = rewr' th
          val m = thm_match known order (i,th')
          val _ = chat ("rewrite:\n" ^ thm_to_string th
                        ^ "\n ->\n" ^ thm_to_string th' ^ "\n")
          val () = assert (not m) (Bug "rewrite: should be normalized")
        in
          th'
        end
    end;
in
  fun rewrite (REWRS {known,rewrites,...}) order (i,th) =
    rewr known rewrites order i th;
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
      LtoR => l = l'
    | RtoL => r = r'
    | Both => l = l' andalso r = r'
  end;

fun redex_residues eq ort =
  let
    val (l,r) = dest_eq eq
  in
    case ort of
      LtoR => [(l,r,true)]
    | RtoL => [(r,l,true)]
    | Both => [(l,r,false),(r,l,false)]
  end;

fun find_rws order known subterms i =
  let
    fun valid_rw (l,r,ord) (j,p) =
      let
        val t = literal_subterm p (dest_unit (fst (retrieve known j)))
        val s = match l t
      in
        assert (ord orelse order (t, term_subst s r) = SOME GREATER)
               (Error "valid: violates order")
      end

    fun check_subtm lr (jp as (j,_), todo) =
      if i <> j andalso not (S.member (todo,j)) andalso can (valid_rw lr) jp
      then S.add (todo,j) else todo

    fun find (lr as (l,_,_), todo) =
      foldl (check_subtm lr) todo (T.matched subterms l)
  in
    foldl find
  end;

fun reduce1 new i (rpl,spl,todo,rw) =
  let
    val REWRS {order, known, rewrites, subterms, waiting} = rw
    val (th0,ort0) = M.retrieve (known,i)
    val eq0 = dest_unit th0
    val th = rewrite rw order (i,th0)
    val eq = dest_unit th
    val identical = eq = eq0
    val same_red = identical orelse (ort0<>Both andalso same_redex eq0 ort0 eq)
    val rpl = if same_red then rpl else S.add (rpl,i)
    val spl = if new orelse identical then spl else S.add (spl,i)
  in
    case (if same_red then SOME ort0 else orient (order (dest_eq eq))) of
      NONE =>
      (rpl, spl, todo,
       REWRS {order = order, known = fst (M.remove (known,i)),
              rewrites = rewrites, subterms = subterms, waiting = waiting})
    | SOME ort =>
      let
        val known = if identical then known else M.insert (known,i,(th,ort))
        val rewrites =
          if same_red then rewrites else add_rewrite i (th,ort) rewrites
        val todo =
          if same_red andalso not new then todo
          else find_rws order known subterms i todo (redex_residues eq ort)
        val subterms =
          if identical andalso not new then subterms
          else add_subterms i th subterms
      in
        (rpl, spl, todo,
         REWRS {order = order, known = known, rewrites = rewrites,
                subterms = subterms, waiting = waiting})
      end
  end;

fun add_rewrs known (i,rewrs) =
  case M.peek (known,i) of NONE => rewrs
  | SOME th_ort => add_rewrite i th_ort rewrs;

fun add_stms known (i,stms) =
  case M.peek (known,i) of NONE => stms
  | SOME (th,_) => add_subterms i th stms;

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

fun pick known s =
  case S.find (fn i => snd (retrieve known i) <> Both) s of SOME x => SOME x
  | NONE => blind_pick s;

fun reduce_acc (rpl, spl, todo, rw as REWRS {known, waiting, ...}) =
  case pick known todo of
    SOME i => reduce_acc (reduce1 false i (rpl, spl, S.delete (todo,i), rw))
  | NONE =>
    case pick known waiting of
      SOME i => reduce_acc (reduce1 true i (rpl, spl, todo, waiting_del i rw))
    | NONE => (rebuild rpl spl rw, rpl);

fun reduce_newr rw =
  let
    val REWRS {waiting, ...} = rw
    val (rw,changed) = reduce_acc (S.empty, S.empty, S.empty, rw)
    val newr = S.union (changed,waiting)
    val REWRS {known, ...} = rw
    fun filt (i,l) = if Option.isSome (M.peek (known,i)) then i :: l else l
    val newr = S.foldr filt [] newr
  in
    (rw,newr)
  end;

fun reduce' rw =
  if not (chatting 2) then reduce_newr rw else
    let
      val REWRS {known, order, ...} = rw
      val res as (rw',_) = reduce_newr rw
      val REWRS {known = known', ...} = rw'
      val eqs = map (fn (i,(th,_)) => (i,th)) (M.listItems known')
      val m = List.exists (thm_match known order) eqs
      val _ = chatrewrs "reduce before" rw
      val _ = chatrewrs "reduce after" rw'
      val () = assert (not m) (Bug "reduce: not fully reduced")
    in
      res
    end;

val reduce = fst o reduce';

fun reduced (REWRS {waiting, ...}) = Intset.isEmpty waiting;

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
