(****************************************************************************)
(* FILE          : waterfall.sml                                            *)
(* DESCRIPTION   : `Waterfall' of heuristics. Clauses pour over. Some       *)
(*                 evaporate. Others collect in a pool to be cleaned up.    *)
(*                 Heuristics that act on a clause send the new clauses to  *)
(*                 the top of the waterfall.                                *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 9th May 1991                                             *)
(*                                                                          *)
(* TRANSLATED BY : R.J.Boulton                                              *)
(* DATE          : 3rd October 1995                                         *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 5th October 1995                                         *)
(****************************************************************************)

structure BoyerMooreWaterfall =
struct

local

open HolKernel Parse basicHol90Lib Psyntax BoyerMooreSupport;
infix ##;

fun failwith_message function message =
   raise HOL_ERR {origin_structure = "BoyerMooreWaterfall",
                  origin_function = function,
                  message = message};

fun failwith function = failwith_message function "";

in

(*==========================================================================*)
(* Some auxiliary functions                                                 *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* proves : thm -> term -> bool                                             *)
(*                                                                          *)
(* Returns true if and only if the theorem proves the term without making   *)
(* any assumptions.                                                         *)
(*--------------------------------------------------------------------------*)

fun proves th tm =
   let val (hyp,concl) = dest_thm th
   in  (null hyp) andalso (concl = tm)
   end;

(*--------------------------------------------------------------------------*)
(* apply_proof : proof -> term list -> proof                                *)
(*                                                                          *)
(* Converts a proof into a new proof that checks that the theorems it is    *)
(* given have no hypotheses and have conclusions equal to the specified     *)
(* terms. Used to make a proof robust.                                      *)
(*--------------------------------------------------------------------------*)

fun apply_proof f tms ths =
   (if (itlist (fn (tm,th) => fn b => (proves th tm) andalso b)
           (combine (tms,ths)) true)
    then f ths
    else failwith ""
   ) handle HOL_ERR _ => failwith "apply_proof";

(*==========================================================================*)
(* The `waterfall' for heuristics                                           *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* proof_printing : bool ref                                                *)
(*                                                                          *)
(* Assignable variable. If true, clauses are printed as they are `poured'   *)
(* over the waterfall.                                                      *)
(*--------------------------------------------------------------------------*)

val proof_printing = ref false;

(*--------------------------------------------------------------------------*)
(* proof_printer : bool -> bool                                             *)
(*                                                                          *)
(* Function for setting the flag that controls the printing of clauses as   *)
(* are `poured' over the waterfall.                                         *)
(*--------------------------------------------------------------------------*)

fun proof_printer state =
   let val old_state = !proof_printing
   in  proof_printing := state; old_state
   end;

(*--------------------------------------------------------------------------*)
(* proof_print_depth : int ref                                              *)
(*                                                                          *)
(* Assignable variable. A number indicating the `depth' of the proof and    *)
(* more practically the number of spaces printed before a term.             *)
(*--------------------------------------------------------------------------*)

val proof_print_depth = ref 0;

(*--------------------------------------------------------------------------*)
(* inc_print_depth : 'a -> 'a                                               *)
(*                                                                          *)
(* Identity function that has the side-effect of incrementing the           *)
(* print_proof_depth.                                                       *)
(*--------------------------------------------------------------------------*)

fun inc_print_depth x = (proof_print_depth := !proof_print_depth + 1; x);

(*--------------------------------------------------------------------------*)
(* dec_print_depth : 'a -> 'a                                               *)
(*                                                                          *)
(* Identity function that has the side-effect of decrementing the           *)
(* print_proof_depth.                                                       *)
(*--------------------------------------------------------------------------*)

fun dec_print_depth x =
   if (!proof_print_depth < 1)
   then (proof_print_depth := 0; x)
   else (proof_print_depth := !proof_print_depth - 1; x);

(*--------------------------------------------------------------------------*)
(* proof_print_term : term -> term                                          *)
(*                                                                          *)
(* Identity function on terms that has the side effect of printing the term *)
(* if the `proof_printing' flag is set to true.                             *)
(*--------------------------------------------------------------------------*)

fun proof_print_term tm =
   if !proof_printing
   then (print (funpow (!proof_print_depth) (curry (op ^) " ") "");
         print_term tm; print "\n"; tm)
   else tm;

(*--------------------------------------------------------------------------*)
(* proof_print_newline : 'a -> 'a                                           *)
(*                                                                          *)
(* Identity function that has the side effect of printing a newline if the  *)
(* `proof_printing' flag is set to true.                                    *)
(*--------------------------------------------------------------------------*)

fun proof_print_newline x =
   if !proof_printing
   then (print "\n"; x)
   else x;

(*--------------------------------------------------------------------------*)
(* Recursive type for holding partly processed clauses.                     *)
(*                                                                          *)
(* A clause is either still to be proved, has been proved, or can be proved *)
(* once sub-clauses have been. A clause that is still to be proved carries  *)
(* a flag indicating whether or not it is an induction step.                *)
(*--------------------------------------------------------------------------*)

datatype clause_tree = Clause of term * bool
                     | Clause_proved of thm
                     | Clause_split of clause_tree list * (thm list -> thm);

(*--------------------------------------------------------------------------*)
(* Exception for proof attempt failure.                                     *)
(*--------------------------------------------------------------------------*)

exception CannotProve;

(*--------------------------------------------------------------------------*)
(* waterfall : ((term * bool) -> ((term * bool) list * proof)) list ->      *)
(*             (term * bool) ->                                             *)
(*             clause_tree                                                  *)
(*                                                                          *)
(* `Waterfall' of heuristics. Takes a list of heuristics and a term as      *)
(* arguments. Each heuristic should fail if it can do nothing with its      *)
(* input. Otherwise the heuristic should return a list of new clauses to be *)
(* proved together with a proof of the original clause from these new       *)
(* clauses.                                                                 *)
(*                                                                          *)
(* Clauses that are not processed by any of the heuristics are placed in a  *)
(* leaf node of the tree, to be proved later. The heuristics are attempted  *)
(* in turn. If a heuristic returns an empty list of new clauses, the proof  *)
(* is applied to an empty list, and the resultant theorem is placed in the  *)
(* tree as a leaf node. Otherwise, the tree is split, and each of the new   *)
(* clauses is passed to ALL of the heuristics.                              *)
(*--------------------------------------------------------------------------*)

fun waterfall heuristics tmi =
   let fun flow_on_down rest_of_heuristics tmi =
          if (is_F (#1 tmi)) then raise CannotProve
          else if (null rest_of_heuristics) then (Clause tmi)
          else let val (tms,f) = hd rest_of_heuristics tmi
               in  if (null tms) then Clause_proved (f [])
                   else if (null (tl tms)) then
                      (Clause_split ([waterfall heuristics (hd tms)],f))
                   else Clause_split
                           ((dec_print_depth o
                             map (waterfall heuristics o proof_print_newline) o
                             inc_print_depth) tms,
                            f)
               end
               handle CannotProve =>
                         failwith_message "waterfall" "cannot prove"
                    | HOL_ERR _ => flow_on_down (tl rest_of_heuristics) tmi
   in  flow_on_down heuristics ((proof_print_term ## I) tmi)
   end;

(*--------------------------------------------------------------------------*)
(* fringe_of_clause_tree : clause_tree -> (term * bool) list                *)
(*                                                                          *)
(* Computes the fringe of a clause_tree, including in the resultant list    *)
(* only those clauses that remain to be proved.                             *)
(*--------------------------------------------------------------------------*)

fun fringe_of_clause_tree (Clause tmi) = [tmi]
  | fringe_of_clause_tree (Clause_proved _) = []
  | fringe_of_clause_tree (Clause_split (trees,_)) =
   flatten (map fringe_of_clause_tree trees);

(*--------------------------------------------------------------------------*)
(* prove_clause_tree : clause_tree -> proof                                 *)
(*                                                                          *)
(* Given a clause_tree, returns a proof that if given theorems for the      *)
(* unproved clauses in the tree, returns a theorem for the clause at the    *)
(* root of the tree. The list of theorems must be in the same order as the  *)
(* clauses appear in the fringe of the tree.                                *)
(*--------------------------------------------------------------------------*)

fun prove_clause_tree tree ths =
   let fun prove_clause_trees [] ths = ([],ths)
         | prove_clause_trees (tree::trees) ths =
          let val (th,ths') = prove_clause_tree' tree ths
              val (thl,ths'') = prove_clause_trees trees ths'
          in  (th::thl,ths'')
          end
       and prove_clause_tree' (Clause (tm,_)) ths =
          let val th = hd ths handle List.Empty => failwith ""
          in  if (proves th tm)
              then (th,tl ths)
              else failwith "prove_clause_tree"
          end
         | prove_clause_tree' (Clause_proved th) ths = (th,ths)
         | prove_clause_tree' (Clause_split (trees,f)) ths =
          let val (thl,ths') = prove_clause_trees trees ths
          in  (f thl,ths')
          end
   in  case (prove_clause_tree' tree ths) of (th,[]) => th | _ => failwith ""
   end
   handle HOL_ERR _ => failwith "prove_clause_tree";

(*==========================================================================*)
(* Eliminating instances in the `pool' of clauses remaining to be proved    *)
(*                                                                          *)
(* Constructing partial orderings is probably overkill. It may only be      *)
(* necessary to split the clauses into two sets, one of most general        *)
(* clauses and the rest. This would still be computationally intensive, but *)
(* it would avoid comparing two clauses that are both instances of some     *)
(* other clause.                                                            *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* inst_of : term -> term -> thm -> thm                                     *)
(*                                                                          *)
(* Takes two terms and computes whether the first is an instance of the     *)
(* second. If this is the case, a proof of the first term from the second   *)
(* (assuming they are formulae) is returned. Otherwise the function fails.  *)
(*--------------------------------------------------------------------------*)

fun inst_of tm patt =
   let val (tm_bind,ty_bind) = match_term patt tm
       val (insts,vars) = split tm_bind
       val f = (SPECL insts) o (GENL vars) o (INST_TYPE ty_bind)
   in  fn th => apply_proof (f o hd) [patt] [th]
   end
   handle HOL_ERR _ => failwith "inst_of";

(*--------------------------------------------------------------------------*)
(* Recursive datatype for a partial ordering of terms using the             *)
(* `is an instance of' relation.                                            *)
(*                                                                          *)
(* The leaf nodes of the tree are terms that have no instances. The other   *)
(* nodes have a list of instance trees and proofs of each instance from the *)
(* term at that node.                                                       *)
(*                                                                          *)
(* Each term carries a number along with it. This is used to keep track of  *)
(* where the term came from in a list. The idea is to take the fringe of a  *)
(* clause tree, number the elements, then form partial orderings so that    *)
(* only the most general theorems have to be proved.                        *)
(*--------------------------------------------------------------------------*)

datatype inst_tree = No_insts of term * int
                   | Insts of term * int * (inst_tree * (thm -> thm)) list;

(*--------------------------------------------------------------------------*)
(* insert_into_inst_tree : (term * int) -> inst_tree -> inst_tree           *)
(* insert_into_inst_trees : (term * int * (thm -> thm)) ->                  *)
(*                          (inst_tree * (thm -> thm)) list ->              *)
(*                          (inst_tree * (thm -> thm)) list                 *)
(*                                                                          *)
(* Mutually recursive functions for constructing partial orderings, ordered *)
(* by `is an instance of' relation. The algorithm is grossly inefficient.   *)
(* Structures are repeatedly destroyed and rebuilt. Reference variables     *)
(* should be used for efficiency.                                           *)
(*                                                                          *)
(* Inserting into a single tree:                                            *)
(*                                                                          *)
(* If tm' is an instance of tm, tm is put in the root node, with the old    *)
(* tree as its single child. If tm is not an instance of tm', the function  *)
(* fails. Assume now that tm is an instance of tm'. If the tree is a leaf,  *)
(* it is made into a branch and tm is inserted as the one and only child.   *)
(* If the tree is a branch, an attempt is made to insert tm in the list of  *)
(* sub-trees. If this fails, tm is added as a leaf to the list of           *)
(* instances. Note that if tm is not an instance of tm', then it cannot be  *)
(* an instance of the instances of tm'.                                     *)
(*                                                                          *)
(* Inserting into a list of trees:                                          *)
(*                                                                          *)
(* The list of trees carry proofs with them. The list is split into those   *)
(* whose root is an instance of tm, and those whose root is not. The proof  *)
(* associated with a tree that is an instance is replaced by a proof of the *)
(* term from tm. If the list of trees that are instances is non-empty, they *)
(* are made children of a node containing tm, and this new tree is added to *)
(* the list of trees that are n't instances. If tm has instances in the     *)
(* list, it cannot be the case that tm is an instance of one of the other   *)
(* trees in the list, for the trees in a list must be unrelated.            *)
(*                                                                          *)
(* If there are no instances of tm in the list of trees, an attempt is made *)
(* to insert tm into the list. If it is unrelated to all of the trees, this *)
(* attempt fails, in which case tm is made into a leaf and added to the     *)
(* list.                                                                    *)
(*--------------------------------------------------------------------------*)

fun insert_into_inst_tree (tm,n) (No_insts (tm',n')) =
   (let val f = inst_of tm' tm
    in  Insts (tm,n,[(No_insts (tm',n'),f)])
    end
    handle HOL_ERR _ =>
    let val f =
           inst_of tm tm' handle HOL_ERR _ => failwith "insert_into_inst_tree"
    in  Insts (tm',n',[(No_insts (tm,n),f)])
    end)
  | insert_into_inst_tree (tm,n) (Insts (tm',n',insts)) =
   (let val f = inst_of tm' tm
    in  Insts (tm,n,[(Insts (tm',n',insts),f)])
    end
    handle HOL_ERR _ =>
    let val f =
           inst_of tm tm' handle HOL_ERR _ => failwith "insert_into_inst_tree"
    in  Insts (tm',n',insert_into_inst_trees (tm,n,f) insts)
        handle HOL_ERR _ => Insts (tm',n',(No_insts (tm,n),f)::insts)
    end)
and insert_into_inst_trees (tm,n,f) insts =
   let fun instances (tm,n) [] = ([],[])
         | instances (tm,n) ((inst as (h,f))::insts) =
          let val (not_instl,instl) = instances (tm,n) insts
              val (tm',n') =
                 case h of No_insts (tm',n') => (tm',n')
                         | Insts (tm',n',_) => (tm',n')
          in  let val f' = inst_of tm' tm
              in  (not_instl,(h,f')::instl)
              end
              handle HOL_ERR _ => (inst::not_instl,instl)
          end
       and insert_into_inst_trees' (tm,n) [] =
          failwith "insert_into_inst_trees'"
         | insert_into_inst_trees' (tm,n) (tree::trees) =
          ((insert_into_inst_tree (tm,n) tree)::trees
           handle HOL_ERR _ => tree::(insert_into_inst_trees' (tm,n) trees))
       val (not_instl,instl) = instances (tm,n) insts
   in  if (null instl)
       then ((combine o (insert_into_inst_trees' (tm,n) ## I)) (split insts)
             handle HOL_ERR _ => (No_insts (tm,n),f)::insts)
       else (Insts (tm,n,instl),f)::not_instl
   end;

(*--------------------------------------------------------------------------*)
(* mk_inst_trees : (term * int) list -> inst_tree list                      *)
(*                                                                          *)
(* Constructs a partial ordering of terms under the `is an instance of'     *)
(* relation from a list of numbered terms.                                  *)
(*                                                                          *)
(* A dummy proof is passed to the call of insert_into_inst_trees. The       *)
(* result of the call has a proof associated with the root of each tree.    *)
(* These proofs are dummies and so are discarded before the final result is *)
(* returned.                                                                *)
(*--------------------------------------------------------------------------*)

fun mk_inst_trees tmnl =
   let fun mk_inst_trees' insts [] = insts
         | mk_inst_trees' insts ((tm,n)::tmns) =
          mk_inst_trees' (insert_into_inst_trees (tm,n,I) insts) tmns
   in  map #1 (mk_inst_trees' [] tmnl)
   end;

(*--------------------------------------------------------------------------*)
(* roots_of_inst_trees : inst_tree list -> term list                        *)
(*                                                                          *)
(* Computes the terms at the roots of a list of partial orderings.          *)
(*--------------------------------------------------------------------------*)

fun roots_of_inst_trees [] = []
  | roots_of_inst_trees (tree::trees) =
   let val tm =
          case tree
          of No_insts (tm,_) => tm
           | Insts (tm,_,_) => tm
   in  tm::(roots_of_inst_trees trees)
   end;

(*--------------------------------------------------------------------------*)
(* prove_inst_tree : inst_tree -> thm -> (thm * int) list                   *)
(*                                                                          *)
(* Given a partial ordering of terms and a theorem for its root, returns a  *)
(* list of theorems for the terms in the tree.                              *)
(*--------------------------------------------------------------------------*)

fun prove_inst_tree (No_insts (tm,n)) th =
   if (proves th tm) then [(th,n)] else failwith "prove_inst_tree"
  | prove_inst_tree (Insts (tm,n,insts)) th =
   if (proves th tm)
   then (th,n)::(flatten (map (fn (tr,f) => prove_inst_tree tr (f th)) insts))
   else failwith "prove_inst_tree";

(*--------------------------------------------------------------------------*)
(* prove_inst_trees : inst_tree list -> thm list -> thm list                *)
(*                                                                          *)
(* Given a list of partial orderings of terms and a list of theorems for    *)
(* their roots, returns a sorted list of theorems for the terms in the      *)
(* trees. The sorting is done based on the integer labels attached to each  *)
(* term in the trees.                                                       *)
(*--------------------------------------------------------------------------*)

fun prove_inst_trees trees ths =
   map #1
      (sort_on_snd
          (flatten (map (uncurry prove_inst_tree) (combine (trees,ths)))))
   handle HOL_ERR _ => failwith "prove_inst_trees";

(*--------------------------------------------------------------------------*)
(* prove_pool : conv -> term list -> thm list                               *)
(*                                                                          *)
(* Attempts to prove the pool of clauses left over from the waterfall, by   *)
(* applying the conversion, conv, to the most general clauses.              *)
(*--------------------------------------------------------------------------*)

fun prove_pool conv tml =
   let val tmnl = number_list tml
       val trees = mk_inst_trees tmnl
       val most_gen_terms = roots_of_inst_trees trees
       val ths = map conv most_gen_terms
   in  prove_inst_trees trees ths
   end;

(*==========================================================================*)
(* Boyer-Moore prover                                                       *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* WATERFALL : ((term * bool) -> ((term * bool) list * proof)) list ->      *)
(*             ((term * bool) -> ((term * bool) list * proof)) ->           *)
(*             (term * bool) ->                                             *)
(*             thm                                                          *)
(*                                                                          *)
(* Boyer-Moore style automatic proof procedure. Takes a list of heuristics, *)
(* and a single heuristic that does induction, as arguments. The result is  *)
(* a function that, given a term and a Boolean, attempts to prove the term. *)
(* The Boolean is used to indicate whether the term is the step of an       *)
(* induction. It will normally be set to false for an external call.        *)
(*--------------------------------------------------------------------------*)

fun WATERFALL heuristics induction (tm,(ind:bool)) =
   let fun conv tm =
          let val (tmil,proof) = induction (tm,false)
          in  dec_print_depth
                 (proof (map (WATERFALL heuristics induction)
                            (inc_print_depth tmil)))
          end
       val void = proof_print_newline ()
       val tree = waterfall heuristics (tm,ind)
       val tmil = fringe_of_clause_tree tree
       val thl = prove_pool conv (map #1 tmil)
   in  prove_clause_tree tree thl
   end;

(*==========================================================================*)
(* Some sample heuristics                                                   *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* conjuncts_heuristic : (term * bool) -> ((term * bool) list * proof)      *)
(*                                                                          *)
(* `Heuristic' for splitting a conjunction into a list of conjuncts.        *)
(* Right conjuncts are split recursively.                                   *)
(* Fails if the argument term is not a conjunction.                         *)
(*--------------------------------------------------------------------------*)

fun conjuncts_heuristic (tm,(i:bool)) =
   let val tms = conj_list tm
   in  if (length tms = 1)
       then failwith "conjuncts_heuristic"
       else (map (fn tm => (tm,i)) tms,apply_proof LIST_CONJ tms)
   end;

(*--------------------------------------------------------------------------*)
(* refl_heuristic : (term * bool) -> ((term * bool) list * proof)           *)
(*                                                                          *)
(* `Heuristic' for proving that terms of the form (--`x = x`--) are true.   *)
(* Fails if the argument term is not of this form. Otherwise it returns an  *)
(* empty list of new clauses, and a proof of the original term.             *)
(*--------------------------------------------------------------------------*)

fun refl_heuristic (tm,(i:bool)) =
   (if (lhs tm = rhs tm)
    then ([]:(term * bool) list,apply_proof (fn ths => REFL (lhs tm)) [])
    else failwith "")
   handle HOL_ERR _ => failwith "refl_heuristic";

(*--------------------------------------------------------------------------*)
(* clausal_form_heuristic : (term * bool) -> ((term * bool) list * proof)   *)
(*                                                                          *)
(* `Heuristic' that tests a term to see if it is in clausal form, and if    *)
(* not converts it to clausal form and returns the resulting clauses as new *)
(* `goals'. It is critical for efficiency that the normalization is only    *)
(* done if the term is not in clausal form. Note that the functions         *)
(* `conjuncts' and `disjuncts' are not used for the testing because they    *)
(* split trees of conjuncts (disjuncts) rather than simply `linear'         *)
(* con(dis)junctions. If the term is in clausal form, but is not a single   *)
(* clause, it is split into single clauses. If the term is in clausal form  *)
(* but contains Boolean constants, the normalizer is applied to it. A       *)
(* single new goal will be produced in this case unless the result of the   *)
(* normalization was true.                                                  *)
(*--------------------------------------------------------------------------*)

fun clausal_form_heuristic (tm,(i:bool)) =
   let fun is_atom tm =
          (not (BoyerMooreClausalForm.has_boolean_args_and_result tm)) orelse
          (is_var tm) orelse (is_const tm)
       fun is_literal tm =
          (is_atom tm) orelse
          (is_neg tm) andalso (is_atom (rand tm) handle HOL_ERR _ => false)
       fun is_clause tm = forall is_literal (disj_list tm)
   in  if (forall is_clause (conj_list tm)) andalso
          (not (free_in (--`T`--) tm)) andalso (not (free_in (--`F`--) tm))
       then if (is_conj tm)
            then let val tms = conj_list tm
                 in  (map (fn tm => (tm,i)) tms,apply_proof LIST_CONJ tms)
                 end
            else failwith ""
       else let val th = BoyerMooreClausalForm.CLAUSAL_FORM_CONV tm
                val tm' = rhs (concl th)
            in  if (is_T tm')
                then ([],apply_proof (fn _ => EQT_ELIM th) [])
                else let val tms = conj_list tm'
                     in  (map (fn tm => (tm,i)) tms,
                          apply_proof ((EQ_MP (SYM th)) o LIST_CONJ) tms)
                     end
            end
   end
   handle HOL_ERR _ => failwith "clausal_form_heuristic";

end;

end; (* BoyerMooreWaterfall *)
