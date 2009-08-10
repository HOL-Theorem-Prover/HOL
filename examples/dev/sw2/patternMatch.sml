
structure patternMatch =
struct

(*****************************************************************************************)
(* Decision Tree for pattern matching.                                                   *)
(* When compiling a function in clausal form, we build a decision tree which determines  *)
(* the order in which subterms of any term are to be examined to find the first patter n *)
(* that matches that term. We attempt to make this decision tree optimal or minimal, in  *)
(* the sense that the order imposed on subterm-testing is such that the matching pattern *)
(* can be found with a minimum number of tests. Each node of a decision tree represents  *)
(* a test that can be carried out on a sub-term discriminating between constructor cases.*)
(* The branches coming out of a node correspond to the possible results of the test      *)
(* performed at that node (i.e. possible constructors for that subterm, which are        *)
(* determined by the type of the subterm). Each branch is labeled with a type constuctor *)
(* and a set of pattern indices representing the patterns that were still possibly       *)
(* matching (live) before the test and that have this construct or as result of the test.*)
(* At run-time, when a value term has to be matched against one of the patterns, the     *)
(* code executed corresponds to going down the decision tree from the root to one of the *)
(* leaves, executing the tests corresponding to the test nodes along the path.           *)
(*****************************************************************************************)

open HolKernel Parse;

structure S = Binaryset

(*****************************************************************************************)
(* Decision Tree.                                                                        *)
(*****************************************************************************************)

datatype 'a subterm = Wildcard          (* _ *)
                    | Var of 'a         (* variables *)
                    | Constr of 'a      (* constructor *)
                    | ConS of 'a S.set    (* constructor set *)

type rule_type = int * (string subterm) list;
type test_type = int * string;

datatype 'a tree = Node of {tset : test_type S.set,    (* tests *)
                            rlist : rule_type list,    (* rules *)
                            ledge : test_type,         (* left out-coming edge *)
                            left : 'a tree,            (* left sub-tree *)
                            right : 'a tree}           (* right subtree *)
                 | Leaf of rule_type list              (* a single rule *)

fun strOrder (name1 : string, name2 : string) =
      if name1 > name2 then GREATER
      else if name1 = name2 then EQUAL
      else LESS

fun testOrder ((index1, name1) : int * string, (index2, name2) : int * string) =
    if index1 > index2 then GREATER
    else if index1 = index2 then
      if name1 > name2 then GREATER
      else if name1 = name2 then EQUAL
      else LESS
    else LESS;

(*****************************************************************************************)
(* Attempt to choose the optimal test.                                                   *)
(*****************************************************************************************)

fun match_constr(Constr x, v) = x = v
 |  match_constr(ConS s, v) = S.member(s,v)
 |  match_constr(_, v) = true

fun relevant_indices(test_set, rule) =
  let
    val test_list = S.listItems(test_set)
    val relevant_list =
      List.filter (fn (index,name) =>
         (index = fst rule) andalso
         not (match_constr (List.nth(snd rule, index), name))) test_list
  in
    relevant_list
  end

fun next_indices (test_set, rules) =
  let
      fun first_index(remaining_rules) =
        if length remaining_rules = 0 then
          []
        else
          let val v = relevant_indices(test_set, hd remaining_rules)
          in  if length v = 0 then
                first_index(tl remaining_rules)
              else
                v
          end
   in
      first_index(rev rules)
   end

(*****************************************************************************************)
(* Eliminate redundant rules in a rule list.                                             *)
(*****************************************************************************************)

fun zip ([],[]) = []
 |  zip (x1::l1,x2::l2) = (x1,x2)::zip(l1,l2)

fun elim_redundant_rules rules =
  let
    fun cover rule1 rule2 =
      List.all (fn (t1,t2) =>
                  case t1 of
                      Constr x =>
                       (case t2 of
                           Constr y => x = y
                         | ConS s => S.listItems s = [x]
                         | _ => false        (* Wildcard or variables *)
                       )
                    | ConS s1 =>
		       (case t2 of
                           Constr y => S.member(s1, y)
                         | ConS s2 => S.isSubset(s2,s1)
                         | _ => false        (* Wildcard or variables *)
                       )
                    | _ => true)
                (zip(rule1,rule2))
  in
    List.foldl (fn (rule2, r_rules) =>
                 if List.exists (fn rule1 => cover (snd rule1) (snd rule2)) r_rules     (* rule1 consumes rule2 *)
                 then r_rules
                 else r_rules @ [rule2]
               )
               [] rules
  end

(*****************************************************************************************)
(* Modify the rule by instantializing it with constructor information.                   *)
(*****************************************************************************************)

fun inst_rule (rule : rule_type, index, subterm) =
  (#1(rule), List.take(#2 rule, index) @ [subterm] @ List.drop(#2 rule, index + 1))

fun inst_rules(rules : rule_type list, test_set) =
  let val l = S.listItems test_set
      val index = fst (hd (l))
      val constr_set = S.addList(S.empty strOrder, List.map snd l)
  in
     List.foldl (fn (rule, r_rules) =>
         case List.nth(#2 rule, index) of
            Constr x => if S.member(constr_set, x)
                        then r_rules @ [inst_rule(rule, index, Constr x)]
                        else r_rules
          | ConS s => let val sub_s = S.intersection(constr_set, s) in
                          if S.isEmpty sub_s then r_rules
                          else if S.numItems s = 1 then
			    r_rules @ [inst_rule(rule, index, Constr (hd (S.listItems s)))]
                          else
			    r_rules @ [inst_rule(rule, index, ConS constr_set)]
                      end
          | _ => r_rules @ [inst_rule(rule, index,
			    if S.numItems constr_set = 1
                            then Constr (hd (S.listItems constr_set))
                            else ConS constr_set)]
          )
          [] rules
  end

(*****************************************************************************************)
(* Build the decision tree in a top-down manner.                                         *)
(* A test on a subterm is relevant to a pattern pi if and only if pi does not agree with *)
(* all the possible values on that subterm. In terms of decision-trees, a test on a sub  *)
(* term is relevant to a pattern pi if and only if i does not appear in the set of live  *)
(* rule indices which label each successor of that test. Given a set of possible tests   *)
(* tset and a set of live rule indices rset, the relevance heuristic searches for the    *)
(* least index i in rset such that at least one test in tset is relevant to pi. If there *)
(* is no such index, no test in tset is relevant to any pattern in rset and one has      *)
(* reached a leaf of the tree. Otherwise, one computes the sub set trel of tset          *)
(* containing the tests that are relevant to pi. If trel is a singleton, its element is  *)
(* the next desired next test. Otherwise, the next heuristic selection is applied on     *)
(* trel.                                                                                 *)
(*****************************************************************************************)

fun build_tree(test_set, rules) =
  let
     val indices = next_indices (test_set, rules)
  in
     if null indices then
       Leaf rules
     else
       let
         val test = hd indices
         val left_set = S.add(S.empty testOrder, test)
         val right_set = S.addList(S.empty testOrder, List.filter (fn (n,x) => n = fst test)
                         (S.listItems(S.delete(test_set, test))))
         val next_set = S.delete(test_set, test)

         val left_rules = elim_redundant_rules(inst_rules(rules, left_set))
         val right_rules = elim_redundant_rules(inst_rules(rules, right_set))
      in
         Node {tset = test_set,                              (* tests *)
               rlist = rules,                                (* rules *)
               ledge = test,                                 (* left out-coming edge *)
               left = build_tree(next_set, left_rules),      (* left sub-tree *)
               right = build_tree(next_set, right_rules)     (* right subtree *)
              }
      end
  end

(* val test_set = S.addList(S.empty testOrder,
         [(0,"nil"), (0,"cons"), (1,"nil"), (1,"cons")]);
   val rules = [(0, [Constr "nil", Var ""]), (1, [Var "", Constr "nil"])];

   build_tree(test_set, rules)

*)

(*****************************************************************************************)
(* Branching Factor Heuristic.                                                           *)
(* The branching factor heuristic tries to minimize the number of test-nodes by favoring *)
(* the choice of tests with low branching factor first.                                  *)
(*****************************************************************************************)

fun select_index(test_set, indices) =
  if length indices = 1 then
    hd indices
  else
    let
      val test_list = S.listItems test_set
      val (min_index, min_value) =
        List.foldl
          (fn ((index,name), (i,j)) =>
             let val n = length (List.filter (fn (n,x) => n = i) test_list)
	     in  if n < j then (index, n)
                 else (i,j)
             end
           )
        (0, length test_list) indices
    in
       valOf (List.find (fn(index,name) => index = min_index) indices)
    end

(* val test_set = S.addList(S.empty testOrder,
         [(0,"true"), (0,"false"), (1,"red"), (1,"blue"), (1,"green")]);
   val test_set = S.addList(S.empty testOrder,
         [(0,"true"), (0,"false"), (1,"green"), (1,"red/blue")]);
   val rules = [(0, [Constr "true", Constr "green"]), (1, [Constr "false", Constr "green"])];

   build_tree(test_set, rules)

*)

end

(*
Define `(f 0 _ = 0) /\
          (f (SUC i) 0 = i) /\
          (f (SUC i) (SUC j) = i + j)
         `;
*)
