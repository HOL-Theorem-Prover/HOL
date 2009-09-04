structure regAllocation =
struct

local open HolKernel Parse boolLib pairLib bossLib

(* ---------------------------------------------------------------------------------------------------------------------*)
(* Definition of types		                                                                                        *)
(* ---------------------------------------------------------------------------------------------------------------------*)

structure T = IntMapTable(type key = int fun getInt n = n);
structure S = Binaryset;
structure G = Graph;

in

type edgeLab = int;

(* ---------------------------------------------------------------------------------------------------------------------*)
(* Machine model                                                                                         		*)
(* ---------------------------------------------------------------------------------------------------------------------*)

(* NumRegs is the number of registers 	*)
val NumRegs = ref (11);

(* The following flag controls whether we spill only one node at a time         *)
(* If set to be false, then all potential nodes are spilled at once.            *)
val spillOneOnce = ref (true);

(* ---------------------------------------------------------------------------------------------------------------------*)
(* Inputs of the whole program 												*)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun intOrder (s1:int,s2:int) =
  if s1 > s2 then GREATER
  else if s1 = s2 then EQUAL
  else LESS;

val precolored : (int S.set) ref = ref (S.empty intOrder);
val firstnArgL : (int list) ref = ref [];

val tmpTable : (string T.table) ref = ref (T.empty);
fun newTmp () =
   let
      val tmps = T.listItems (!tmpTable);

      fun getNewVarNo n =
	  case List.find (fn x => x = Temp.makestring n) tmps of
	    SOME y => getNewVarNo (n+1)
	  | NONE => n;

      val newVarNo = getNewVarNo (Temp.newtemp())
   in
      ( tmpTable := T.enter(!tmpTable, newVarNo, Temp.makestring newVarNo);
   	newVarNo
      )
   end;

val cfg : (({def : int list, instr : Assem.instr, use : int list}, edgeLab) G.graph) ref  = ref (G.empty);

val memIndex = ref (~1);         (* the stack pointer pointing at the next available memory slot for spilling	*)

(* ---------------------------------------------------------------------------------------------------------------------*)
(* for debugging	                                                                                         	*)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun els ([]:(int Binaryset.set) list) = []
 |  els (x::xs) = (S.listItems x)::els xs;

(* ---------------------------------------------------------------------------------------------------------------------*)
(* Data Structures                                                                                                      *)
(* ---------------------------------------------------------------------------------------------------------------------*)
(*
   Node work-lists, sets, and stacks:
        precolored: machine registers, preassigned color
        intial: temporary registers, not precolored and not yet processed
        simplifyWorklist: list of low-degree non-move-related nodes
        freezeWorklist: low-degree move-related nodes
        spillWorklist: high-degree nodes
        spilledNodes: nodes marked for spilling during this round; initially empty
        coalescedNodes: registers that have been coalesced; when u <- v is coalesced, v
                        is added to this set and u put back on some work-list (or vice versa)
        coloredNodes: nodes successfully colored
        selectStack: stack containing temporaries removed from the graph

   Move sets:
        coalescedMoves: moves that have been coalesced
        constainedMoves: moves whose source and target interfere
        frozenMoves: moves that will no longer be considered for coalescing
        worklistMoves: moves enabled for possible coalescing
        activeMoves: moves not yet ready for coalescing

   Other data Structures:
        adjSet: the set of interference edges (u,v) in the graph. If (u,v) in adjSet then (v,u) in adjSet
        adjList: adjacency list representation of the graph; for each non-precolored temporary u,
                adjList[u] is the set of nodes that interfere with u
        degree: an array containing the current degree of each node
        moveList: a mapping from a node to the list of moves it is associated with
        alias: when a move (u,v) has been coalesced, and v put in coalescedNodes, then alias(v) = u.
        color: the color chosen by the algorithm for a node; for precolored nodes this is
                initialized to the given color.
*)

fun intTupleOrder ((u1,v1):int*int,(u2,v2):int*int) =
  if u1 > u2 then GREATER
  else if u1 < u2 then LESS
  else if v1 > v2 then GREATER
  else if v1 < v2 then LESS
  else EQUAL;

fun buildNumList m n =
  if m > n then []
  else m :: buildNumList (m+1) n;

val initial : (int S.set) ref = ref (S.empty intOrder);

val simplifyWorklist : (int S.set) ref = ref (S.empty intOrder);
val freezeWorklist : (int S.set) ref = ref (S.empty intOrder);
val spillWorklist : (int S.set) ref = ref (S.empty intOrder);
val spilledNodes : (int S.set) ref = ref (S.empty intOrder);
val toBeSpilled : (int S.set) ref = ref (S.empty intOrder);
val coalescedNodes : (int S.set) ref = ref (S.empty intOrder);
val coloredNodes : (int S.set) ref = ref (S.empty intOrder);
val selectStack  : (int Stack.stack) ref = ref (Stack.empty ());

val coalescedMoves : (int S.set) ref = ref (S.empty intOrder);
val constrainedMoves: (int S.set) ref = ref (S.empty intOrder);
val frozenMoves: (int S.set) ref = ref (S.empty intOrder);
val worklistMoves: (int S.set) ref = ref (S.empty intOrder);
val activeMoves: (int S.set) ref = ref (S.empty intOrder);

val adjSet : ((int * int) S.set) ref = ref (S.empty intTupleOrder);
val adjList : ((int S.set) T.table) ref = ref (T.empty);
val degree : (int T.table) ref = ref (T.empty);
val moveList : (int S.set T.table) ref = ref (T.empty);

val alias : (int T.table) ref = ref (T.empty);
val color : (int T.table) ref = ref (T.empty);

val spilledTmps = ref (S.empty intOrder);

val MAX_DEGREE = 65535;

val memT : (int T.table) ref = ref (T.empty);

(* ---------------------------------------------------------------------------------------------------------------------*)
(* Auxiliary functions                                                                                                  *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun forall p []      = true
  | forall p (x::xs) = p(x) andalso forall p xs;

fun zip ([], [])      = []
  | zip (x::xs, y::ys) = (x,y) :: zip(xs,ys);


fun getNodeLab (n:int) =
   #3 (G.context(n, !cfg));

fun mk_edge ((n0:G.node,n1:G.node,lab:edgeLab), gr:('a,edgeLab) G.graph) =
    if n0 = n1 then gr
    else if (List.find (fn m => #2 m = n0) (#1(G.context(n1,gr)))) <> NONE then gr
    else
       let val ((p1,m1,l1,s1), del_n1) = G.match(n1,gr)
       in G.embed(((lab,n0)::p1,m1,l1,s1),del_n1)
    end;

fun rm_edge ((n0:G.node,n1:G.node), gr:('a,edgeLab) G.graph) =
    if n0 = n1 then gr
    else if (List.find (fn m => #2 m = n0) (#1(G.context(n1,gr)))) = NONE then raise G.Edge
    else
       let val ((p1,m1,l1,s1), del_n1) = G.match(n1,gr)
       in G.embed((List.filter (fn el => #2 el <> n0) (#1(G.context(n1,gr))),
                m1,l1,s1),del_n1)
    end;

fun PrintProgram (cfg : ({instr : Assem.instr, use : int list, def : int list}, edgeLab) G.graph, tmpT) =
    List.map (fn inst => print ((Assem.formatInst inst) ^ "\n"))
		(CFG.linearizeCFG cfg);

fun isMoveInst  (Assem.MOVE {dst = Assem.TEMP d1, src = Assem.TEMP s1}) = true
 |  isMoveInst _ = false


(* ---------------------------------------------------------------------------------------------------------------------*)
(* Calculate liveness of a program	                                                                                *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun computeUseDef (gr : ({instr:Assem.instr, use:int list, def:int list}, edgeLab) Graph.graph) =
      G.ufold (fn ((predL,nodeNo,inst,sucL),
	(use:Temp.temp Binaryset.set T.table,def:Temp.temp Binaryset.set T.table)) =>
	      (	let val (dst,src) = (#def inst, #use inst) in
		    ( T.enter(use, nodeNo, S.addList(S.empty intOrder, src)),
		      T.enter(def, nodeNo, S.addList(S.empty intOrder, dst)))
		end))
                (T.empty,T.empty) gr;

fun CalLiveness (cfg)
=
  let
     val inS = List.map (fn elm => (S.empty intOrder)) (G.nodes cfg);
     val outS = inS;
     val (useT,defT) = computeUseDef cfg;

     fun unionAll [] = S.empty intOrder
      |  unionAll (h::tl) = S.union(h, unionAll tl);

     (* discard spurious edges (i.e. those whose labels equal to 2 ) *)
     fun getSuc n =
	let val sucEdges = #4 (G.context(n,cfg))
	    val realEdges = List.filter (fn edge => not (#1 edge = 2)) sucEdges
	in
	    List.map (fn edge => #2 edge) realEdges
	end

     fun compOut 0 inS = []
      |  compOut n inS =
           compOut (n-1) inS @ [unionAll (List.map (fn index => (List.nth(inS,index))) (getSuc (n-1)))];

     fun round (inS, outS)=
       let
        val old_inS = inS;
        val old_outS = outS;

        val inS = List.map
                       (fn n => S.union(T.look(useT,n), S.difference(List.nth(outS,n),T.look(defT,n))))
                       (G.nodes cfg);

        val outS = compOut (length inS) inS
        in
          if forall (fn (x1,x2) => S.equal(x1,x2)) (zip(inS,old_inS)) andalso
             forall (fn (x1,x2) => S.equal(x1,x2)) (zip(outS,old_outS))
          then (inS, outS)
          else round(inS,outS)
        end
     in
        round (inS,outS)
  end;


(* -------------------------------------------------------------------------------------------------------------------*)
(* Initialize data structures, then compute the values of these structures                                            *)
(* -------------------------------------------------------------------------------------------------------------------*)

(* When a valid allocation isn't found, the whole process is needed to restart. Procedure init() initializes
   data structures													*)

fun init (cfg, tmpTable) =
    (

	spilledTmps := S.union (!spilledNodes, !spilledTmps);

       	initial := S.difference (S.difference(S.addList(S.empty intOrder, T.listKeys tmpTable),
                	 !precolored), !spilledTmps);

	simplifyWorklist := S.empty intOrder;
	freezeWorklist := S.empty intOrder;
	spillWorklist := S.empty intOrder;
	spilledNodes := S.empty intOrder;
	coalescedNodes := S.empty intOrder;
	coloredNodes := S.empty intOrder;
	selectStack  := Stack.empty ();

	coalescedMoves := S.empty intOrder;
	constrainedMoves := S.empty intOrder;
	frozenMoves := S.empty intOrder;
	worklistMoves := S.empty intOrder;
	activeMoves := S.empty intOrder;

	adjSet := S.empty intTupleOrder;
	adjList := List.foldl (fn (n,ll) => T.enter(ll,n,S.empty intOrder)) (!adjList) (T.listKeys (tmpTable));
	degree := List.foldl (fn (n,ll) => T.enter(ll,n,0)) (T.empty) (T.listKeys (tmpTable));
	moveList := !adjList;

	alias := List.foldl (fn (n,ll) => T.enter(ll,n,~1)) (T.empty) (T.listKeys (tmpTable));
	color := !alias

    );


fun AddEdge (u:G.node, v:G.node) =
    if not (S.member(!adjSet,(u,v))) andalso (u <> v) then
       (adjSet := S.add(S.add(!adjSet,(u,v)),(v,u));
	if not (S.member(!precolored,u)) then
	     (adjList := T.enter (!adjList, u, S.add (T.look(!adjList,u),v));
	      degree := T.enter (!degree, u, T.look(!degree,u)+1))
	else ();
        if not (S.member(!precolored,v)) then
             (adjList := T.enter (!adjList, v, S.add (T.look(!adjList,v),u));
              degree := T.enter (!degree, v, T.look(!degree,v)+1))
        else ())
    else ();

(* Construct the interference graph using the results of static liveness analysis,
   and initializes the worklistMoves to contain all the moves.				*)

fun Build (cfg) =
  let

    val (inS,outS) = CalLiveness cfg;

    fun investigate_one_node nodeNo =
      let
	val nd = getNodeLab nodeNo;
	val (def,use) = (#def nd, #use nd);
	val (def,use) = (S.addList(S.empty intOrder, def), S.addList(S.empty intOrder, use));
	val inst = #instr(nd);
	val live = List.nth(outS,nodeNo);
        val _ = if isMoveInst inst then
	       let val live = S.difference(live, use)
               in  moveList := List.foldl
		    (fn (varNo,lst) => T.enter(lst,varNo,S.add(T.look(lst,varNo),nodeNo)))
                          (!moveList) (S.listItems(S.union(def,use)));
	     	worklistMoves := S.add (!worklistMoves,nodeNo)
	       end
	     else ();
        val live = S.union(live, def);
        val _ = List.foldl
		(fn (d,lv) => List.foldl (fn (l,lv) => (AddEdge(l,d);lv)) lv (S.listItems live))
		live (S.listItems def)
      in
        S.union(use, S.difference(live, def))
      end

  in
      List.map investigate_one_node (G.nodes cfg)
  end;


fun NodeMoves n =
   S.intersection(T.look(!moveList,n),
		  S.union(!activeMoves, !worklistMoves));

fun MakeWorklist() =
   let
      fun round n =
	(initial := S.delete(!initial,n);
	 if T.look(!degree,n) >= (!NumRegs) then
	    spillWorklist := S.add(!spillWorklist,n)
	 else if not (S.isEmpty(NodeMoves n)) then
	    freezeWorklist := S.add(!freezeWorklist,n)
   	 else
	    simplifyWorklist := S.add(!simplifyWorklist,n))

      val _ = List.foldl (fn (i,s) => round i) () (S.listItems (!initial))
   in
         toBeSpilled := !spillWorklist
   end;

(* -------------------------------------------------------------------------------------------------------------------*)
(* Merge moves, push simplified nodes into the stack			                                              *)
(* -------------------------------------------------------------------------------------------------------------------*)

fun Adjacent n =
   S.difference (T.look(!adjList, n),
	S.union(Stack.stack2set (!selectStack, S.empty intOrder), !coalescedNodes));

(* When the degree of a neighbor transitions from K to K - 1, moves associated with its neighbors may be enabled *)

fun EnableMoves nodes =
   let fun round n =
       List.foldl
           (fn (m,s) => (
                if S.member(!activeMoves,m) then
                    (activeMoves := S.delete (!activeMoves, m);
                     worklistMoves := S.add (!worklistMoves,m))
                else ()))
             ()  (S.listItems (NodeMoves n))
   in
       List.foldl (fn (n,s) => round n) () (S.listItems nodes)
   end;


fun DecrementDegree m =
   let val d =  T.look(!degree,m) in
     (degree := T.enter(!degree, m, d-1);
      if (d = !NumRegs) then
	(EnableMoves (S.add(Adjacent m, m));
	 spillWorklist := S.difference(!spillWorklist,S.add(S.empty intOrder,m));
	 if not (S.isEmpty(NodeMoves m)) then
	        freezeWorklist := S.add (!freezeWorklist,m)
	 else
	        simplifyWorklist := S.add (!simplifyWorklist,m))
      else ()
      )
   end;

(* Add a low degree node into the select stack *)

fun Simplify() =
   let val n = hd(S.listItems (!simplifyWorklist))
   in (
	simplifyWorklist := S.delete (!simplifyWorklist,n);
	selectStack := Stack.push(n, !selectStack);
	List.foldl (fn (m,x) => DecrementDegree m) ()
	    (S.listItems (S.difference(Adjacent n, !precolored)))
      )
   end;

(* Coalesce moves                                                    *)

fun AddWorklist u =
  if not (S.member (!precolored,u)) andalso S.isEmpty(NodeMoves u) andalso
	T.look(!degree,u) < (!NumRegs) then
	(freezeWorklist := S.delete (!freezeWorklist,u);
	 simplifyWorklist := S.add (!simplifyWorklist,u))
  else ();

fun OK (t,r) =
   T.look(!degree,t) < (!NumRegs) orelse
   S.member (!precolored,t) orelse
   S.member (!adjSet, (t,r));

fun Conservative nodes =
   let val k = List.foldl (fn (n,k) => if T.look(!degree,n) >= (!NumRegs) then k+1 else k) 0 (S.listItems nodes)
   in  k < (!NumRegs)
   end;

(*
fun Conservative(u,v) =
   let
     fun dgr u n = if S.member(Adjacent u, n) then T.look(!degree,n)-1 else T.look(!degree,n);
   val k =
	List.foldl (fn (n,k) => if dgr n >= (!NumRegs) then k+1 else k) 0 (S.listItems (Adjacent v))
   in k < (!NumRegs) end;
*)

fun GetAlias n =
   if S.member (!coalescedNodes, n) then
	GetAlias (T.look(!alias,n))
   else n;

fun Combine (u,v) =
   ( if S.member(!freezeWorklist,v) then
	freezeWorklist := S.delete (!freezeWorklist,v)
     else
	spillWorklist := S.difference (!spillWorklist,S.add(S.empty intOrder,v));
     coalescedNodes := S.add(!coalescedNodes,v);
     alias := T.enter(!alias, v, GetAlias u);
     moveList := T.enter (!moveList, u, S.union(T.look(!moveList,u), T.look(!moveList,v)));
     EnableMoves (S.add(S.empty intOrder,v));
     List.foldl (fn (t,s) => (AddEdge(t,u);DecrementDegree t)) ()
		(S.listItems (Adjacent v));
     if T.look(!degree,u)>=(!NumRegs) andalso S.member(!freezeWorklist,u) then
	(freezeWorklist := S.delete (!freezeWorklist,u);
	 spillWorklist := S.add (!spillWorklist,u))
     else ()
   );

fun Coalesce () =
   let  val m = hd(S.listItems (!worklistMoves));
	val inst = getNodeLab m;
	val (def,use) = (#def inst, #use inst);
        val (x,y) = (GetAlias (hd def), GetAlias (hd use));
	val (u,v) = if (S.member(!precolored,y))
			then (y,x) else (x,y)
   in
	(worklistMoves := S.delete (!worklistMoves,m);
	 if u = v then
	    ( coalescedMoves := S.add(!coalescedMoves,m);
	      AddWorklist u)
	 else if S.member(!precolored,v) orelse S.member(!adjSet,(u,v)) then
	    ( constrainedMoves := S.add(!constrainedMoves,m);
	      AddWorklist u;
	      AddWorklist v)
	 else if S.member(!precolored,u) andalso (forall (fn t => OK(t,u)) (S.listItems (Adjacent v)))
		orelse not (S.member(!precolored,u)) andalso
			Conservative (S.union(Adjacent u,Adjacent v)) then
	    ( coalescedMoves := S.add(!coalescedMoves,m);
	      Combine(u,v);
	      AddWorklist u)
	 else activeMoves := S.add(!activeMoves,m))
   end;

fun FreezeMoves u =
  let fun freezeOneMove m =
     let
	val inst = getNodeLab m;
        val (x,y) = (hd (#def inst), hd (#use inst));
	val v = if GetAlias y = GetAlias u then GetAlias x else GetAlias y
     in
      ( activeMoves := S.difference (!activeMoves, S.add(S.empty intOrder,m));
	frozenMoves := S.add (!frozenMoves, m);
	if S.isEmpty(NodeMoves v) andalso (T.look(!degree,v) < (!NumRegs)) then
	  ( freezeWorklist := S.difference (!freezeWorklist, S.add(S.empty intOrder, v));
	    simplifyWorklist := S.add (!simplifyWorklist, v))
	else ()
      ) end
   in List.foldl (fn (m,s) => freezeOneMove m) () (S.listItems (NodeMoves u))
   end;


fun Freeze () =
   let val u = hd (S.listItems (!freezeWorklist)) in
       (freezeWorklist := S.delete (!freezeWorklist, u);
        simplifyWorklist := S.add (!simplifyWorklist, u);
        FreezeMoves u)
   end;

fun spillPriorities nodes =
    List.foldl (fn (n,max) => if T.look(!degree,n) > T.look(!degree,max) then n else max)
        (hd(S.listItems nodes)) (S.listItems nodes);

fun SelectSpill () =
   let
      val m = spillPriorities (!spillWorklist)
   in
    ( spillWorklist := S.delete (!spillWorklist,m);
      simplifyWorklist := S.add(!simplifyWorklist,m);
      FreezeMoves m)
   end;

(* -------------------------------------------------------------------------------------------------------------------*)
(* Assign colors to nodes, spill nodes when a valid allocation couldn't be found                                      *)
(* -------------------------------------------------------------------------------------------------------------------*)

(* In a effort to compile with the APCS standard *)
(* The arguemtns are in r0-r9 and then the stack *)

fun AssignColors () =
   let

     fun initColors ~1 = S.empty intOrder
      |  initColors n = S.add(initColors (n-1),n);

     fun assign_precolored () =
        List.foldl (fn (n,c) => (color := T.enter(!color,n,c);c+1)) 0 (!firstnArgL);

     fun spillNodes n =
        if (!spillOneOnce) then
		S.add(S.empty intOrder, spillPriorities (!toBeSpilled))
        else
            (!toBeSpilled)

     fun chaseColor n =
	let val c = T.look(!color, GetAlias n) in
	if (c = ~1) then
	    chaseColor (GetAlias n)
	else c end;

     fun assign () =
      if Stack.isEmpty (!selectStack) then
	  (List.foldl (fn (n,s) => color := T.enter(!color,n,T.look(!color, GetAlias n)))
			 ()
			 (S.listItems (!coalescedNodes));
			 ())
      else
	  let val n = Stack.top (!selectStack);
	      val _ = (selectStack := Stack.pop(!selectStack));
	      val okColors = initColors ((!NumRegs)-1);
	      val okColors = List.foldl (fn (w,s) => if S.member(S.union(!coloredNodes,!precolored),GetAlias w) then
					S.difference (s, S.add(S.empty intOrder, T.look(!color, GetAlias w)))
				  		else s)
		    		okColors
				(S.listItems (T.look(!adjList,n)))
	  in
	      if S.isEmpty(okColors) then
		  (spilledNodes := spillNodes n;
		   selectStack := Stack.empty ())
	      else
		  ( coloredNodes := S.add(!coloredNodes, n);
		    color := T.enter(!color, n, hd (S.listItems okColors));
		    assign()
		  )
	  end
   in
	( assign_precolored();
	  assign()
        )
   end;

(* -------------------------------------------------------------------------------------------------------------------*)
(* When a node is spilled, we modify the program by replacing the temporary with a memory slot                        *)
(* -------------------------------------------------------------------------------------------------------------------*)

fun updateNode(cfg, n:int, inst) =
   let
        val ((preN,nodeNo,nodeLab,sucN),cfg1) = G.match (n,cfg);
   in
        G.embed((preN,nodeNo,inst,sucN), cfg1)
   end;


fun insertBefore(cfg, n:int, inst) =
   let
	val (preN,nodeNo,nodeLab,sucN) = G.context (n,cfg);
	val newCfg = List.foldl (fn (p,gr) => rm_edge((p,n),gr)) cfg (List.map (fn (lab,n) => n) preN);
	val ct = (preN, G.noNodes cfg, inst, [(0,n)])
   in
	G.embed(ct, newCfg)

   end;

fun insertAfter(cfg, n:int, inst) =
   let
	val (preN,nodeNo,nodeLab,sucN) = G.context (n,cfg);
        val newCfg = List.foldl (fn (s,gr) => rm_edge((n,s),gr)) cfg (List.map (fn (lab,n) => n) sucN);
        val ct = ([(0,n)], G.noNodes cfg, inst, sucN)
   in
        G.embed(ct, newCfg)
   end;


(* t : TmpTable,  gr : control-flow graph	*)
fun updateProgram (old_cfg, spilled : int S.set) =
   let

     fun replace l old new = List.map (fn x => (if (x = old) then new else x)) l;
     fun substituteVars (Assem.OPER {oper = p, dst = d1, src = s1, jump = j1}) old new rhs lhs =
	    Assem.OPER {oper = p, dst = if rhs then replace d1 old new else d1,
		src = if lhs then replace s1 old new else s1, jump = j1}
      |  substituteVars (Assem.LABEL x) old new rhs lhs = Assem.LABEL x
      |  substituteVars (Assem.MOVE {dst = d1, src = s1}) old new rhs lhs =
	    Assem.MOVE {dst = if rhs andalso d1 = old then new else d1,
		src = if lhs andalso s1 = old then new else s1};

     fun not_bl (Assem.OPER {oper = (Assem.BL, NONE, false), ...}) = false
      |  not_bl _ = true
     fun is_nop (Assem.OPER {oper = (Assem.NOP, NONE, false), ...}) = true
             |  is_nop _ = false


     fun update_node gr nodeNo (varNo,newVarNo) (for_lhs,for_rhs) =
         let
              val {instr = curInst, def = df, use = us} = #3 (G.context(nodeNo,gr))
         in
	      updateNode(gr, nodeNo,
			(if not_bl curInst andalso not (is_nop curInst) then
				{ def = if for_lhs andalso List.exists (fn n => n = varNo) df then newVarNo ::
					(List.filter (fn n => not (n = varNo orelse n = newVarNo)) df) else df,
                          	  use = if for_rhs andalso List.exists (fn n => n = varNo) us then newVarNo ::
					(List.filter (fn n => not (n = varNo orelse n = newVarNo)) us) else us,
			  	  instr = substituteVars curInst (Assem.TEMP varNo) (Assem.TEMP newVarNo) for_lhs for_rhs
				}
			 else
                                { def = if for_lhs then (List.filter (fn n => not (n = varNo)) df) else df,
                                  use = if for_rhs then (List.filter (fn n => not (n = varNo)) us) else us,
				  instr = substituteVars curInst (Assem.TEMP varNo) (Assem.TMEM (!memIndex)) for_lhs for_rhs
                                }
			 ))
          end

     fun insertLoadInst gr nodeNo varNo =
	   let val newVarNo = newTmp ();
	       val {instr = curInst, def = df, use = us} = #3 (G.context(nodeNo,gr));
	       val newInst = {instr = Assem.OPER {oper = (Assem.LDR,NONE,false),
						 dst = [Assem.TEMP newVarNo],
						 src = [Assem.TMEM (!memIndex)],
						 jump = NONE},
			      def = [newVarNo], use = []};
	       val gr1 = update_node gr nodeNo (varNo,newVarNo) (false,true)
	   in
	       if not_bl curInst andalso not (is_nop curInst) then
	      	   insertBefore(gr1, nodeNo, newInst)
	       else gr1
           end;

     fun insertStoreInst gr nodeNo varNo =
           let val newVarNo = newTmp ();
	       val {instr = curInst, def = df, use = us} = #3 (G.context(nodeNo,gr));
               val newInst = {instr = Assem.OPER {oper = (Assem.STR,NONE,false),
						 dst = [Assem.TMEM (!memIndex)],
						 src = [Assem.TEMP newVarNo],
						 jump = NONE},
			     def = [], use = [newVarNo]};
	       val gr1 = update_node gr nodeNo (varNo,newVarNo) (true,false)
           in
               if not_bl curInst andalso not (is_nop curInst) then
                   insertAfter(gr1, nodeNo, newInst)
	       else gr1
           end;

    fun process_one_variable gr varNo =
	let
	    val _ = (memIndex:= !memIndex + 1;
		     memT := T.enter(!memT, varNo, !memIndex)
		    )
	in
	    G.ufold (fn ((predL,nodeNo,inst,sucL),gr) =>
            	  let val (def,use) = (#def inst, #use inst);
                      val (def,use) = (S.addList(S.empty intOrder, def), S.addList(S.empty intOrder, use));
		      val gr1 = if S.member(use, varNo) then
				  (if isMoveInst (#instr inst) then
				     	let val (Assem.MOVE {dst = d1, src = s1}) = #instr inst in
				            updateNode(gr,nodeNo,
					        {instr = Assem.OPER {oper = (Assem.LDR,NONE,false), dst = [d1],
						  	            src = [Assem.TMEM (!memIndex)], jump = NONE},
                                	   	 def = #def inst, use = []})
				     	end
				   else
                                	insertLoadInst gr nodeNo varNo
				  )
                              else gr
		  in
		      if S.member(def, varNo) then
                       	  insertStoreInst gr1 nodeNo varNo
                      else gr1 end)
	        gr gr
	end

    in
        List.foldl (fn (varNo, gr) => process_one_variable gr varNo) old_cfg (S.listItems (spilled))
    end;


fun RewriteProgram () =
      (	cfg := updateProgram (!cfg,!spilledNodes);
	init (!cfg,!tmpTable)
      );


(* -------------------------------------------------------------------------------------------------------------------*)
(* Register Allocation				                                                                      *)
(* -------------------------------------------------------------------------------------------------------------------*)

fun printAllocation () =
  let
  fun color2reg c =
     if c >= 0 andalso c < (!NumRegs) then "r" ^ Int.toString c
     else "not found";

  fun allocation tmps =
     List.foldl
	(fn (n,_) => if S.member (!spilledTmps, n) then ()
	    else let val c =  T.look(!color,n) in
	         print (T.look(!tmpTable, n) ^ "\t" ^ (Int.toString c) ^ "\t" ^ (color2reg c) ^ "\n")
                 end)
    () (T.listKeys (!tmpTable))
  in
   ( print "Node\tColor\tRegister\n";
     allocation ((T.numItems (!tmpTable)) - 1))
  end;

fun AllocateReg () =
  let
     fun allocate () =
      ( if not (S.isEmpty (!simplifyWorklist)) then Simplify()
	else if not (S.isEmpty (!worklistMoves)) then Coalesce()
	else if not (S.isEmpty (!freezeWorklist)) then Freeze()
	else if not (S.isEmpty (!spillWorklist)) then SelectSpill ()
	else ();
	if S.isEmpty (!simplifyWorklist) andalso S.isEmpty (!worklistMoves) andalso
	   S.isEmpty (!freezeWorklist) andalso S.isEmpty (!spillWorklist) then
		()
	else allocate ())

  in
  ( Build(!cfg);
    MakeWorklist();
    allocate();
    AssignColors();
    if not (S.isEmpty (!spilledNodes)) then
	( RewriteProgram ();
	     AllocateReg ())
    else ()
  )
  end;


fun RewrWithReg () =
  let

     fun subs (Assem.PAIR(a,b)) = Assem.PAIR(subs a, subs b)
      |  subs ( Assem.TEMP n) = Assem.REG (T.look(!color, n))
      |  subs x = x

     fun replace ll = List.map subs ll;
     fun substituteVars (Assem.OPER {oper = p, dst = d1, src = s1, jump = j1}) =
            Assem.OPER {oper = p, dst = replace d1, src = replace s1, jump = j1}
      |  substituteVars (Assem.LABEL x) = Assem.LABEL x
      |  substituteVars (Assem.MOVE {dst = d1, src = s1}) =
            Assem.MOVE {dst = hd (replace [d1]), src = hd (replace [s1])};

    in
        G.ufold (fn ((predL,nodeNo,nd,sucL),gr) =>
	         let val {use = us, def = df, instr = stm} = nd in
		 	updateNode (gr, nodeNo, {use = us, def = df, instr = substituteVars stm})
		 end) (!cfg) (!cfg)
    end;


(* ---------------------------------------------------------------------------------------------------------------------*)
(* Interface                                                                                                            *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun RegisterAllocation (gr, tmpT, preC) =
  ( tmpTable := tmpT;

    firstnArgL := List.take (preC, if length preC > !NumRegs then !NumRegs else length preC);
    precolored := S.addList(S.empty intOrder, !firstnArgL);

    cfg := gr;

    memIndex := ~1;
    memT := T.empty;

    spilledTmps := S.empty intOrder;

    init (gr, tmpT);

    AllocateReg ();

    PrintProgram(!cfg, !tmpTable);
    printAllocation ();
    (RewrWithReg (),!tmpTable)
  );

 fun regOrder (r1,r2) =
      let val (Assem.REG n1, Assem.REG n2) = (r1, r2) in
                if n1 > n2 then GREATER
                else if n1 = n2 then EQUAL
                else LESS
      end

 fun getModifiedRegs stms =
      List.foldl (fn (Assem.OPER {dst = d, ...}, regs) =>
                (List.foldl (fn (Assem.REG r, regs)  => Binaryset.add(regs,Assem.REG r)
                                     |   _ => regs) regs d)
              |  (Assem.MOVE {dst = d, ...}, regs) => Binaryset.add(regs,d)
              |  (_,regs) => regs
             )
             (Binaryset.empty regOrder) stms

fun convert_to_ARM prog =
  let
    fun replace_with_regs (Assem.PAIR(v1,v2)) =
		Assem.PAIR (replace_with_regs v1, replace_with_regs v2)
     |  replace_with_regs (Assem.TEMP v) =
	  ( case T.peek(!memT, v) of
		 NONE => Assem.REG (T.look(!color, v))
	     |   SOME n => Assem.TMEM n
	  )
     |  replace_with_regs v = v

    val ((fun_name, fun_type, args, gr, outs), t) = CFG.convert_to_CFG prog;
    val argL = List.map Assem.eval_exp (Assem.pair2list args);
    val (gr',t) = RegisterAllocation (gr, t, argL);

    val (args,outs) = (replace_with_regs args, replace_with_regs outs);
    val stms = CFG.linearizeCFG gr';
    val rs = getModifiedRegs stms

  in
    (fun_name, fun_type, args, gr', outs, rs)
  end

(* ---------------------------------------------------------------------------------------------------------------------*)
(* Verification of register allocation on origial program                                                               *)
(* ---------------------------------------------------------------------------------------------------------------------*)

fun RewrBody rules body =
 let
   fun stripInst insts =
     if not (is_let insts) then subst rules insts
     else
       let
           val (lt, rhs) = dest_let insts;
           val (lhs, rest) = dest_pabs lt;
           val lhs = subst rules lhs
       in
           mk_let (mk_pabs (lhs, stripInst rest), subst rules rhs)
       end
 in
    stripInst body
 end


fun check_allocation prog =
  let
     fun mk_reg_rules tp =
        List.map (fn n => {redex = mk_var (T.look(!tmpTable,n), tp),
                           residue = mk_var ("r" ^ Int.toString (T.look(!color,n)), tp)})
		(List.filter (fn n => n >= 0 andalso T.peek(!memT,n) = NONE) (T.listKeys (!tmpTable)));

    fun mk_mem_rules tp =
        List.map (fn n => {redex = mk_var (T.look(!tmpTable,n), tp),
                           residue = mk_var ("m" ^ Int.toString(T.look(!memT,n)), tp)})
		(List.filter (fn n => n >= 0) (T.listKeys (!memT)));

     val rw =   (RewrBody (mk_mem_rules (Type `:num`))) o (RewrBody (mk_mem_rules (Type `:word32`))) o
		(RewrBody (mk_reg_rules (Type `:num`))) o (RewrBody (mk_reg_rules (Type `:word32`)));

     fun replace exp =
        if is_let exp then
            let val (lt, rhs) = dest_let exp;
                val (lhs, rest) = dest_pabs lt
            in
                mk_let (mk_pabs(replace lhs, replace rest), replace rhs)
            end
        else if is_cond exp then
            let val (c,t,f) = dest_cond exp
            in
                mk_cond (replace c, replace t, replace f)
            end
        else if is_pair exp then
            let val (t1,t2) = dest_pair exp
            in  mk_pair (replace t1, replace t2)
            end
        else rw exp

     val (decl,body) =
           dest_eq(concl(SPEC_ALL prog))
           handle HOL_ERR _
           => (print "not an program in function format\n";
             raise ERR "buildCFG" "invalid program format");
     val (f, args) = dest_comb decl;

     val newDecl = mk_comb (f, rw args)
     val newProg = mk_eq(newDecl, replace body)

  in
    GEN_ALL (prove (
        newProg,
        METIS_TAC [prog, LET_THM]
    ))
  end

end (* local open *)
end (* structure *)

