(****************************************************************************)
(* FILE          : induction.sml                                            *)
(* DESCRIPTION   : Induction.                                               *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 26th June 1991                                           *)
(*                                                                          *)
(* TRANSLATED BY : R.J.Boulton                                              *)
(* DATE          : 4th October 1995                                         *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 5th October 1995                                         *)
(****************************************************************************)

structure BoyerMooreInduction =
struct

local

open HolKernel Parse basicHol90Lib Psyntax BoyerMooreSupport;

fun failwith function =
   raise HOL_ERR {origin_structure = "BoyerMooreInduction",
                  origin_function = function,
                  message = ""};

in

(*--------------------------------------------------------------------------*)
(* is_rec_const_app : term -> bool                                          *)
(*                                                                          *)
(* This function returns true if the term it is given is an application of  *)
(* a currently known recursive function constant.                           *)
(*--------------------------------------------------------------------------*)

fun is_rec_const_app tm =
   let val (f,args) = strip_comb tm
       val (n,defs) =
          (#2 o BoyerMooreEnvironment.get_def o #Name o Rsyntax.dest_const) f
   in  (n > 0) andalso
       ((length o #2 o strip_comb o lhs o concl o #2 o hd) defs = length args)
   end
   handle HOL_ERR _ => false | List.Empty => false;

(*--------------------------------------------------------------------------*)
(* remove_el : int -> 'a list -> ('a * 'a list)                             *)
(*                                                                          *)
(* Removes a specified (by numerical position) element from a list.         *)
(*--------------------------------------------------------------------------*)

fun remove_el n l =
   if ((null l) orelse (n < 1))
   then failwith "remove_el"
   else if (n = 1)
        then (hd l,tl l)
        else let val (x,l') = remove_el (n - 1) (tl l)
             in  (x,(hd l)::l')
             end;

(*--------------------------------------------------------------------------*)
(* possible_inductions : term -> (term list * term list)                    *)
(*                                                                          *)
(* Function to compute two lists of variables on which induction could be   *)
(* performed. The first list of variables for which the induction is        *)
(* unflawed and the second is of variables for which the induction is       *)
(* flawed.                                                                  *)
(*                                                                          *)
(* From a list of applications of recursive functions, the arguments are    *)
(* split into those that are in a recursive argument position and those     *)
(* that are not. Possible inductions are on the variables in the recursive  *)
(* argument positions, but if the variable also appears in a non-recursive  *)
(* argument position then the induction is flawed.                          *)
(*--------------------------------------------------------------------------*)

fun possible_inductions tm =
   let val apps = find_bm_terms is_rec_const_app tm
       val (rec_args,other_args) =
          split (map (fn app =>
                         let val (f,args) = strip_comb app
                             val name = #Name (Rsyntax.dest_const f)
                             val n =
                                (#1 o #2 o BoyerMooreEnvironment.get_def) name
                         in  remove_el n args
                         end) apps)
       val vars = mk_set (filter is_var rec_args)
       val others = mk_set (flatten other_args)
   in  partition (fn v => not (mem v others)) vars
   end;

(*--------------------------------------------------------------------------*)
(* DEPTH_FORALL_CONV : conv -> conv                                         *)
(*                                                                          *)
(* Given a term of the form (--`!x1 ... xn. t`--), this function applies    *)
(* the argument conversion to (--`t`--).                                    *)
(*--------------------------------------------------------------------------*)

fun DEPTH_FORALL_CONV conv tm =
   if (is_forall tm)
   then RAND_CONV (ABS_CONV (DEPTH_FORALL_CONV conv)) tm
   else conv tm;

(*--------------------------------------------------------------------------*)
(* induction_heuristic : (term * bool) -> ((term * bool) list * proof)      *)
(*                                                                          *)
(* Heuristic for induction. It performs one of the possible unflawed        *)
(* inductions on a clause, or failing that, one of the flawed inductions.   *)
(* The heuristic fails if no inductions are possible.                       *)
(*                                                                          *)
(* Having obtained a variable on which to perform induction, the function   *)
(* computes the name of the top-level type constructor in the type of the   *)
(* variable. The appropriate induction theorem is then obtained from the    *)
(* shell environment. The theorem is specialised for the argument clause    *)
(* and beta-reduction is performed at the appropriate places.               *)
(*                                                                          *)
(* The resulting theorem will be of the form:                               *)
(*                                                                          *)
(*    |- (case1 /\ ... /\ casen) ==> (!x. f[x])                         (1) *)
(*                                                                          *)
(* So, if we can establish casei for each i, we shall have |- !x. f[x].     *)
(* When specialised with the induction variable, this theorem has the       *)
(* original clause as its conclusion. Each casei is of one of these forms:  *)
(*                                                                          *)
(*    !x1 ... xn. s ==> (!y1 ... ym. t)                                     *)
(*    !x1 ... xn. t                                                         *)
(*                                                                          *)
(* where the yi's do not appear in s. We simplify the casei's that have the *)
(* first form by proving theorems like:                                     *)
(*                                                                          *)
(*    |- (!x1 ... xn. s ==> (!y1 ... ym. t)) =                              *)
(*       (!x1 ... xn y1 ... ym. s ==> t)                                    *)
(*                                                                          *)
(* For consistency, theorems of the form |- (!x1...xn. t) = (!x1...xn. t)   *)
(* are proved for the casei's that have the second form. The bodies of the  *)
(* right-hand sides of these equations are returned as the new goal         *)
(* clauses. A body that is an implication is taken to be an inductive step  *)
(* and so is returned paired with true. Bodies that are not implications    *)
(* are paired with false.                                                   *)
(*                                                                          *)
(* The proof of the original clause from these new clauses proceeds as      *)
(* follows. The universal quantifications that were stripped from the       *)
(* right-hand sides are restored by generalizing the theorems. From the     *)
(* equations we can then obtain theorems for the left-hand sides. These are *)
(* conjoined and used to satisfy the antecedant of the theorem (1). As      *)
(* described above, specialising the resulting theorem gives a theorem for  *)
(* the original clause.                                                     *)
(*--------------------------------------------------------------------------*)

fun induction_heuristic (tm,(ind:bool)) =
   let val (unflawed,flawed) = possible_inductions tm
       val var = hd unflawed 
             handle List.Empty => hd flawed 
                                   handle List.Empty => failwith ""
       val ty_name = #Tyop (Rsyntax.dest_type (type_of var))
       val induct_thm = #induct (BoyerMooreShells.sys_shell_info ty_name)
       val P = mk_abs (var,tm)
       val th1 = ISPEC P induct_thm
       val th2 =
          CONV_RULE
             (ONCE_DEPTH_CONV
                 (fn tm =>
                     if (rator tm = P) then BETA_CONV tm else failwith "")) th1
       val new_goals = conj_list (rand (rator (concl th2)))
       val ths =
          map (REPEATC (DEPTH_FORALL_CONV RIGHT_IMP_FORALL_CONV)) new_goals
       val (varsl,tml) = split (map (strip_forall o rhs o concl) ths)
       fun proof thl =
          let val thl' = map (uncurry GENL) (combine (varsl,thl))
              val thl'' =
                 map (fn (eq,th) => EQ_MP (SYM eq) th) (combine (ths,thl'))
          in  SPEC var (MP th2 (LIST_CONJ thl''))
          end
   in  (map (fn tm => (tm,(is_imp tm) andalso (not (is_neg tm)))) tml,
        BoyerMooreWaterfall.apply_proof proof tml)
   end
   handle HOL_ERR _ => failwith "induction_heuristic";

end;

end; (* BoyerMooreInduction *)
