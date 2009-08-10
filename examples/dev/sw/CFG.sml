structure CFG =
struct

exception CFG;

type node = {instr:Assem.instr, def : int list, use : int list};
type Cfg = (node,int) Graph.graph;
type dataSeg = Assem.instr list;

exception CFG


(* Translate Tree expressions to Assem expressions							*)

 fun one_exp (Tree.TEMP e) =
        Assem.TEMP e
  |  one_exp (Tree.NAME e) =
        Assem.NAME e
  |  one_exp (Tree.NCONST e) =
        Assem.NCONST e
  |  one_exp (Tree.WCONST e) =
        Assem.WCONST e
  |  one_exp (Tree.CALL(f, args)) =
        Assem.CALL (one_exp f,
                    one_exp args)
  |  one_exp (Tree.PAIR(e1,e2)) =
        Assem.PAIR(one_exp e1, one_exp e2)
  |  one_exp _ = raise CFG
  ;

fun buildCFG tmpT (args,stmList,outs) =
 let

  structure T = IntMapTable(type key = int  fun getInt n = n);
  val relopT : (Tree.relop T.table) ref  = ref (T.empty);
  val labT : (int T.table) ref  = ref (T.empty);

  fun bi_operator Tree.PLUS = Assem.ADD
   |  bi_operator Tree.MINUS = Assem.SUB
   |  bi_operator Tree.MUL = Assem.MUL
   |  bi_operator Tree.AND = Assem.AND
   |  bi_operator Tree.OR = Assem.ORR
   |  bi_operator Tree.XOR = Assem.EOR
   |  bi_operator Tree.LSHIFT = Assem.LSL
   |  bi_operator Tree.RSHIFT = Assem.LSR
   |  bi_operator Tree.ARSHIFT = Assem.ASR
   |  bi_operator Tree.ROR = Assem.ROR
   |  bi_operator Tree.DIV = raise CFG

  fun cjump e =
    let val x = T.look(!relopT, e)
    in  if x = Tree.EQ then Assem.EQ
	else if x = Tree.NE then Assem.NE
	else if x = Tree.LT then Assem.LT
	else if x = Tree.GT then Assem.GT
	else if x = Tree.LE then Assem.LE
	else if x = Tree.GE then Assem.GE
	else if x = Tree.CC then Assem.CC
	else if x = Tree.LS then Assem.LS
	else if x = Tree.HI then Assem.HI
	else if x = Tree.CS then Assem.CS
	else Assem.NE					(* there may be no relational operation defined previously, so if e!=0 then jump *)
    end;



  fun getTmp (Tree.TEMP x) = x
   |  getTmp _ = 0;

  fun tmpIndexL [] = []
   |  tmpIndexL ((Tree.TEMP x)::rest) = x :: (tmpIndexL rest)
   |  tmpIndexL _ = [];

  fun tmpIndexL2 [] = []
   |  tmpIndexL2 ((Assem.TEMP x)::rest) = x :: (tmpIndexL2 rest)
   |  tmpIndexL2 _ = [];


  (* Translate a Tree expression to the Assem expression including use and def information					*)
  fun one_stm (Tree.MOVE(d, Tree.BINOP(bop, e1, e2))) =
    let
      val not_change = if (bop = Tree.MUL) then
        [{instr = Assem.OPER {oper = (Assem.NOP,NONE,false), dst = [], src = [], jump = NONE},
      def = [], use = tmpIndexL [e1]}]
        else [];
    in
	 ({ instr = Assem.OPER {oper = (bi_operator bop,NONE,false), dst = [one_exp d], src = [one_exp e1, one_exp e2], jump = NONE},
	   def = tmpIndexL [d],
	   use = tmpIndexL [e1,e2]
	 }::not_change)
  end
   |  one_stm (Tree.MOVE(d, Tree.RELOP(rop, e1, e2))) =
	let
	    val _= relopT := T.enter(!relopT, getTmp d, rop) in
	    [{ instr = Assem.OPER {oper = (Assem.CMP,NONE,false), dst = [one_exp d], src = [one_exp e1, one_exp e2], jump = NONE},
	      def = tmpIndexL [d],
	      use = tmpIndexL [e1, e2]
	    }]
	end
   |  one_stm (Tree.MOVE(d, Tree.CALL(name, args))) =
	let val (Tree.NAME fun_name) = name;
	    val outL = Tree.pair2list d in
	    [{ instr = Assem.OPER {oper = (Assem.BL,NONE,false),
				 dst = [one_exp d],
				 src = [one_exp args],
				 jump = SOME [fun_name]},
	      def = tmpIndexL outL,
	      use = tmpIndexL (Tree.pair2list args)
	    }]
        end
   |  one_stm (Tree.MOVE(d, s)) =
            [{ instr = Assem.MOVE {dst = one_exp d, src = one_exp s},
	      def = tmpIndexL [d],
	      use = tmpIndexL [s]
	    }]
   |  one_stm (Tree.JUMP lab) =
	    [{ instr = Assem.OPER {oper = (Assem.B,SOME Assem.AL,false), dst = [], src = [], jump = SOME [lab]},
	      def = [],
	      use = []
	    }]
   |  one_stm (Tree.CJUMP(e,lab)) =
	    [{ instr = Assem.OPER {oper = (Assem.B, SOME (cjump (getTmp e)), false), dst = [], src = [one_exp e], jump = SOME [lab]},
	      def = [],
	      use = tmpIndexL [e]
	    }]
   |  one_stm (Tree.LABEL lab) =
	    [{ instr = Assem.LABEL {lab = lab},
	      def = [],
	      use = []
	    }]
   |  one_stm _ = raise CFG

   (* Calcuate the number of the node holding a label, this number serves as the tail of an edge corresponding to an jump	*)

    fun calLabels ({instr = Assem.LABEL {lab = lab1}, def = d1, use = s1} :: rest, i) =
 	    ( labT := T.enter(!labT, Symbol.index lab1, i);
	      calLabels (rest, i+1)
	    )
     |  calLabels ([],i) = ()
     |  calLabels (stm :: rest, i) = calLabels (rest, i+1);


    (* Build edges for the whole CFG												*)

    fun buildEdges instL =
	let val edgeL = ref ([])
	    val i = ref 0;
	    val ll = length instL;
	    fun one_stm (stm:{instr:Assem.instr, use:int list, def:int list}) =
		case (#instr stm) of
		    Assem.OPER x =>
                        (case #jump (x) of
                              NONE => (edgeL := (!i,!i+1,0) :: (!edgeL))
                           |  SOME labs => (case T.peek(!labT, Symbol.index (hd labs)) of
						 NONE => edgeL := (!i,!i+1,0) :: (!edgeL)
					     |   SOME j =>
						      let val (op',cond',flag') = #oper x
						      in
						          if (cond' = SOME (Assem.AL)) orelse (op' = Assem.BL) then
 							      edgeL := (!i, j, 1) :: (!i,!i+1,2) :: (!edgeL)
						          else
							      edgeL := (!i, j, 1) :: (!i,!i+1,0) :: (!edgeL)
						      end))

                 |  _ => (edgeL := (!i,!i+1,0) :: (!edgeL))
	in
	  (  List.map (fn stm => (one_stm stm; i := !i + 1)) instL;
	     List.filter (fn (a,b,l) => b < ll) (!edgeL)
          )
	end;

    val insts = Lib.flatten (List.map (fn inst => one_stm inst) stmList);
    val augmentedInsts = ({instr = Assem.OPER{oper = (Assem.NOP,NONE,false), dst = [], src = [], jump = NONE},
			  def = tmpIndexL2 (Assem.pair2list args),use = []}) ::
	insts @ [{instr = Assem.OPER {oper = (Assem.NOP,NONE,false), dst = [], src = [], jump = NONE},
		  def = [], use = tmpIndexL2 (Assem.pair2list outs)}];
    val _ = calLabels (augmentedInsts,0);
    val edgeL = List.rev (buildEdges augmentedInsts)
  in
	Graph.mkgr(augmentedInsts, edgeL)
  end


fun convert_to_CFG prog =
  let
     val (fun_name, fun_type, args, stms, outs) = IR.convert_to_IR prog
     val (args, outs) = (one_exp args, one_exp outs)
  in
     ((fun_name, fun_type, args, buildCFG (!IR.tmpT) (args,stms,outs), outs), !IR.tmpT)
  end


fun linearizeCFG (cfg : ({instr : Assem.instr, use : int list, def : int list}, int) Graph.graph) =
   let
      fun intOrder (s1:int,s2:int) =
        if s1 > s2 then GREATER
        else if s1 = s2 then EQUAL
        else LESS;

      val visited = ref(Binaryset.empty intOrder);
      val instL = ref [];

      fun visit n =
          if Binaryset.numItems (!visited) = Graph.noNodes cfg then ()
          else if not (Binaryset.member (!visited, n)) then
             let val (nd,nextL) = Graph.fwd (n,cfg);
                 val next = if nextL = [] then n
                            else if length nextL = 1 then #2 (hd nextL)
                            else if #1(hd nextL)=1 then #2 (hd(tl(nextL)))
                            else #2 (hd nextL)
             in
                 (  instL := !instL @ [#instr nd];
                    visited := Binaryset.add(!visited, n);
                    visit next
                 )
             end
          else ()
      in
         (visit 0;
          tl(List.take(!instL, length (!instL) - 1)))
   end

(*
fun linearizeCFG (cfg : ({instr : Assem.instr, use : int list, def : int list}, bool) Graph.graph) =
   let

      val stack : (int list ref) = ref [];
      fun push (i:int) = (stack := i :: (!stack));
      fun pop () = let val x = hd (!stack) in
		      ( stack := tl (!stack);
		  	x)
	          end

      fun intOrder (s1:int,s2:int) =
          if s1 > s2 then GREATER
          else if s1 = s2 then EQUAL
          else LESS;
      val lastNode = ref 0;
      val sucS = ref (Array.fromList(
		List.map (fn n =>
			( lastNode := (if null (Graph.suc(n,cfg)) then n else (!lastNode));
			  Binaryset.addList(Binaryset.empty intOrder, Graph.suc(n,cfg)))) (Graph.nodes cfg)));
      val _ = push (!lastNode);

      fun find_first_free_node () =
	  let val i = pop () in
	      if Binaryset.isEmpty (Array.sub(!sucS,i)) then i
	      else find_first_free_node ()
	  end;

      fun round () =
	let val cur_node = find_first_free_node ();
      	    val in_edges = #1 (Graph.context(cur_node, cfg));
      	    val _ = if length in_edges = 1 then push (#2 (hd in_edges))
	            else if length in_edges = 2 then
		   	( if #1 (hd in_edges) then (push (#2 (hd in_edges)); push (#2 (hd (tl in_edges))))
			  else (push (#2 (hd (tl in_edges))); push (#2 (hd in_edges))))
             	    else ();
      	    val _ = List.map (fn n => Array.update(!sucS, n, Binaryset.delete(Array.sub(!sucS,n), cur_node))) (Graph.pred (cur_node, cfg))
       in
	    if null in_edges then [cur_node]
	    else (round()) @ [cur_node]
       end;

       val stms = List.map (fn node => #instr (#3 (Graph.context(node,cfg)))) (round())

     in
	tl(List.take(stms, length stms - 1))
     end
*)

end
