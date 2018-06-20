% FILE		: btree.ml						%
%									%
% DESCRIPTION   : creates a theory of binary trees, and illustrates how %
%		  to use them with a few simple examples.		%
%									%
% READS FILES	: <none>						%
% WRITES FILES	: btree.th						%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 89.05.11						%

% Create the new theory							%
new_theory `btree`;;

% --------------------------------------------------------------------- %
% Define a recursive type of binary trees.				%
%									%
% Every tree has one two forms:						%
%									%
%	 LEAF (x:*)       NODE (x:**) t1 t2				%
%									%
% where t1 and t2 are trees.  Leaf nodes are labelled with values of    %
% type :* and internal nodes are labelled with values of type :**.	%
%									%
% The following call to define_tree makes an appropriate definition     %
% for this type, and proves the following `axiom' for binary trees:	%
%									%
% |- !f0 f1. ?! fn.							%
%     (!x. fn(LEAF x) = f0 x) /\					%
%     (!x b b'. fn(NODE x b b') = f1(fn b)(fn b')x b b')		%
%									%
% --------------------------------------------------------------------- %

let btree = define_type `btree` `btree = LEAF * | NODE ** btree btree`;;

% --------------------------------------------------------------------- %
% Prove an induction theorem for trees from the axiom for btree.	%
% --------------------------------------------------------------------- %

let btree_Induct = save_thm(`btree_Induct`, prove_induction_thm btree);;

% --------------------------------------------------------------------- %
% Prove that the function NODE is one-to-one.				%
% --------------------------------------------------------------------- %

let NODE_one_one = 
    save_thm(`NODE_one_one`, prove_constructors_one_one btree);;

% --------------------------------------------------------------------- %
% Prove that LEAF's and NODE's are different				%
% --------------------------------------------------------------------- %

let LEAF_NEQ_NODE = 
    save_thm(`LEAF_NEQ_NODE`, prove_constructors_distinct btree);;

% --------------------------------------------------------------------- %
% Prove a cases theorem for trees. (Note that this is proved from the   %
% induction theorem)							%
% --------------------------------------------------------------------- %

let btree_CASES = save_thm(`btree_CASES`, prove_cases_thm btree_Induct);;


% ===================================================================== %
% The following examples illustrate how to define recursive functions   %
% (or just simple functions defined by cases) on trees.			%
% ===================================================================== %

% ---------------------------------------------------------------------	%
% Define a height function on trees.					%
%									%
% 1) first define Max for the maximum of two numbers.			%
%									%
% 2) then define Height recursively.  The parameters are:		%
%      									%
%     - false     =     don't make Height an infix function.		%
%     - btree	  =     the "axiom" for trees.				%
%     - `Height`  =     the name of where to store the resulting 	%
%		        definition in btree.th				%
%     - "... "    =     the desired definition of Height		%
% --------------------------------------------------------------------- %

let Max = new_definition (`Max` , "Max n m = (n < m => m | n)");;

let Height = 
    new_recursive_definition false btree `Height` 
      "(Height (LEAF (x:*)) = 0) /\
       (Height (NODE (y:**) t1 t2) = SUC(Max (Height t1) (Height t2)))";;

% --------------------------------------------------------------------- %
% The next one counts the number of leaves in the tree.			%
% --------------------------------------------------------------------- %

let Leaves = 
    new_recursive_definition false btree `Leaves` 
      "(Leaves (LEAF (x:*)) = 1) /\
       (Leaves (NODE (y:**) t1 t2) = (Leaves t1) + (Leaves t2))";;

% --------------------------------------------------------------------- %
% You can also define non-recursive functions by "cases".  Here are the %
% definitions of functions for accessing parts of trees.		%
%									%
%       LVAL = the label value on a leaf				%
%	NVAL = the label value on an internal node.			%
%       LTREE = the left subtree					%
%       RTREE = the right subtree					%
% --------------------------------------------------------------------- %

let LVAL =  new_recursive_definition false btree `LVAL` 
            "LVAL (LEAF x:(*,**)btree) = x";;

let NVAL =  new_recursive_definition false btree `NVAL` 
            "NVAL (NODE y t1 t2:(*,**)btree) = y";;

let LTREE =  new_recursive_definition false btree `LTREE` 
            "LTREE (NODE y t1 t2:(*,**)btree) = t1";;

let RTREE =  new_recursive_definition false btree `RTREE` 
            "RTREE (NODE y t1 t2:(*,**)btree) = t2";;

% ===================================================================== %
% Induction.  Here's a little proof to show how to do induction on 	%
% trees.  The main tactic is: INDUCT_THEN bintree_Induct.  Note that it %
% takes the induction theorem as an argument.				%
% ===================================================================== %

let Leaves_non_zero = 
    TAC_PROOF(([], "!tr:(*,**)btree. ?n. Leaves tr = SUC n"),
	      INDUCT_THEN btree_Induct STRIP_ASSUME_TAC THEN 
              GEN_TAC THENL
	      [EXISTS_TAC "0" THEN REWRITE_TAC [Leaves;num_CONV "1"];
	       REWRITE_TAC [Leaves] THEN REPEAT (POP_ASSUM SUBST1_TAC) THEN
	       EXISTS_TAC "SUC (n+n')" THEN REWRITE_TAC [ADD_CLAUSES]]);;

% --------------------------------------------------------------------- %
% end.									%
% --------------------------------------------------------------------- %
close_theory();;