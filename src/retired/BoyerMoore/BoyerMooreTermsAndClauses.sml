(****************************************************************************)
(* FILE          : terms_and_clauses.sml                                    *)
(* DESCRIPTION   : Rewriting terms and simplifying clauses.                 *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 7th June 1991                                            *)
(*                                                                          *)
(* TRANSLATED BY : R.J.Boulton                                              *)
(* DATE          : 4th October 1995                                         *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 13th October 1995                                        *)
(****************************************************************************)

structure BoyerMooreTermsAndClauses =
struct

local

open HolKernel Parse basicHol90Lib Num_conv Psyntax BoyerMooreSupport;
infix THEN THENC ORELSEC;

fun failwith function =
   raise HOL_ERR {origin_structure = "BoyerMooreTermsAndClauses",
                  origin_function = function,
                  message = ""};

in

(*--------------------------------------------------------------------------*)
(* rewrite_with_lemmas : (term list -> term list -> conv) ->                *)
(*                        term list -> term list -> conv                    *)
(*                                                                          *)
(* Function to rewrite with known lemmas (rewrite rules) in the reverse     *)
(* order in which they were introduced. Applies the first applicable lemma, *)
(* or if none are applicable it leaves the term unchanged.                  *)
(*                                                                          *)
(* A rule is applicable if its LHS matches the term, and it does not        *)
(* violate the `alphabetical' ordering rule if it is a permutative rule. To *)
(* be applicable, the hypotheses of the rules must be satisfied. The        *)
(* function takes a general rewrite rule, a chain of hypotheses and a list  *)
(* of assumptions as arguments. It uses these to try to satisfy the         *)
(* hypotheses. If a hypotheses is in the assumption list, it is assumed.    *)
(* Otherwise a check is made that the hypothesis is not already a goal of   *)
(* the proof procedure. This is to prevent looping. If it's not already a   *)
(* goal, the function attempts to rewrite the hypotheses, with it added to  *)
(* the chain of hypotheses.                                                 *)
(*                                                                          *)
(* Before trying to establish the hypotheses of a rewrite rule, it is       *)
(* necessary to instantiate any free variables in the hypotheses. This is   *)
(* done by trying to find an instantiation that makes one of the hypotheses *)
(* equal to a term in the assumption list.                                  *)
(*--------------------------------------------------------------------------*)

fun rewrite_with_lemmas rewrite hyp_chain assumps tm =
   let fun rewrite_hyp h =
          EQT_INTRO (ASSUME (find (fn tm => tm = h) assumps))
          handle HOL_ERR _ =>
          (if (mem h hyp_chain)
           then ALL_CONV h
           else rewrite (h::hyp_chain) assumps h)
       fun try_rewrites assumps [] = failwith "try_rewrites"
         | try_rewrites assumps (th::ths) =
          let val th' = BoyerMooreRewriteRules.inst_frees_in_hyps assumps th
              val hyp_ths = map (EQT_ELIM o rewrite_hyp) (hyp th')
          in  itlist PROVE_HYP hyp_ths th'
          end
          handle HOL_ERR _ => try_rewrites assumps ths
   in  try_rewrites assumps (BoyerMooreRewriteRules.applicable_rewrites tm)
       handle HOL_ERR _ => ALL_CONV tm
   end;

(*--------------------------------------------------------------------------*)
(* rewrite_explicit_value : conv                                            *)
(*                                                                          *)
(* Explicit values are normally unchanged by rewriting, but in the case of  *)
(* a numeric constant, it is expanded out into SUC form.                    *)
(*--------------------------------------------------------------------------*)

fun rewrite_explicit_value tm =
   let fun conv tm = (num_CONV THENC TRY_CONV (RAND_CONV conv)) tm
   in  ((TRY_CONV conv) THENC
        (TRY_CONV (ARGS_CONV rewrite_explicit_value))) tm
   end;

(*--------------------------------------------------------------------------*)
(* COND_T = |- (T => t1 | t2) = t1                                          *)
(* COND_F = |- (F => t1 | t2) = t2                                          *)
(*--------------------------------------------------------------------------*)

val (COND_T,COND_F) =
   case (CONJUNCTS (SPEC_ALL COND_CLAUSES))
   of [COND_T,COND_F] => (COND_T,COND_F)
    | _ => raise Bind;

(*--------------------------------------------------------------------------*)
(* COND_LEFT =                                                              *)
(* |- !b x x' y. (b ==> (x = x')) ==> ((b => x | y) = (b => x' | y))        *)
(*--------------------------------------------------------------------------*)

val COND_LEFT =
   prove
      ((--`!b x x' (y:'a).
              (b ==> (x = x')) ==> ((b => x | y) = (b => x' | y))`--),
       REPEAT GEN_TAC THEN
       BOOL_CASES_TAC (--`b:bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* COND_RIGHT =                                                             *)
(* |- !b y y' x. (~b ==> (y = y')) ==> ((b => x | y) = (b => x | y'))       *)
(*--------------------------------------------------------------------------*)

val COND_RIGHT =
   prove
      ((--`!b y y' (x:'a).
              (~b ==> (y = y')) ==> ((b => x | y) = (b => x | y'))`--),
       REPEAT GEN_TAC THEN
       BOOL_CASES_TAC (--`b:bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* COND_ID = |- !b t. (b => t | t) = t                                      *)
(*--------------------------------------------------------------------------*)

(* Already defined in HOL *)

(*--------------------------------------------------------------------------*)
(* COND_RIGHT_F = |- (b => b | F) = b                                       *)
(*--------------------------------------------------------------------------*)

val COND_RIGHT_F =
   prove
      ((--`(b => b | F) = b`--),
       BOOL_CASES_TAC (--`b:bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* COND_T_F = |- (b => T | F) = b                                           *)
(*--------------------------------------------------------------------------*)

val COND_T_F =
   prove
      ((--`(b => T | F) = b`--),
       BOOL_CASES_TAC (--`b:bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* rewrite_conditional : (term list -> conv) -> term list -> conv           *)
(*                                                                          *)
(* Rewriting conditionals. Takes a general rewrite function and a list of   *)
(* assumptions as arguments.                                                *)
(*                                                                          *)
(* The function assumes that the term it is given is of the form            *)
(* (--`b => x | y`--). First it recursively rewrites b to b'. If b' is T or *)
(* F, the conditional is reduced to x or y, respectively. The result is     *)
(* then rewritten recursively. If b' is not T or F, both x and y are        *)
(* rewritten, under suitable additional assumptions about b'. An attempt is *)
(* then made to rewrite the new conditional with one of the following:      *)
(*                                                                          *)
(*    (b => x | x) ---> x                                                   *)
(*    (b => b | F) ---> b                                                   *)
(*    (b => T | F) ---> b                                                   *)
(*                                                                          *)
(* The three rules are tried in the order shown above.                      *)
(*--------------------------------------------------------------------------*)

fun rewrite_conditional rewrite assumps tm =
   let val th1 = RATOR_CONV (RATOR_CONV (RAND_CONV (rewrite assumps))) tm
       val tm1 = rhs (concl th1)
       val (b',x,y) = dest_cond tm1
   in  if (is_T b') then
          TRANS th1 (((REWR_CONV COND_T) THENC (rewrite assumps)) tm1)
       else if (is_F b') then
          TRANS th1 (((REWR_CONV COND_F) THENC (rewrite assumps)) tm1)
       else let val th2 = DISCH b' (rewrite (b'::assumps) x)
                val x' = rand (rand (concl th2))
                val th3 = MP (ISPECL [b',x,x',y] COND_LEFT) th2
                val tm3 = rhs (concl th3)
                val notb' = mk_neg b'
                val th4 = DISCH notb' (rewrite (notb'::assumps) y)
                val y' = rand (rand (concl th4))
                val th5 = MP (ISPECL [b',y,y',x'] COND_RIGHT) th4
                val th6 = ((REWR_CONV COND_ID) ORELSEC
                           (REWR_CONV COND_RIGHT_F) ORELSEC
                           (TRY_CONV (REWR_CONV COND_T_F))) (rhs (concl th5))
            in  TRANS (TRANS (TRANS th1 th3) th5) th6
            end
   end
   handle HOL_ERR _ => failwith "rewrite_conditional";

(*--------------------------------------------------------------------------*)
(* EQ_T = |- (x = T) = x                                                    *)
(*--------------------------------------------------------------------------*)

val EQ_T =
   prove
      ((--`(x = T) = x`--),
       BOOL_CASES_TAC (--`x:bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* EQ_EQ = |- (x = (y = z)) = ((y = z) => (x = T) | (x = F))                *)
(*--------------------------------------------------------------------------*)

val EQ_EQ =
   prove
      ((--`(x = ((y:'a) = z)) = ((y = z) => (x = T) | (x = F))`--),
       BOOL_CASES_TAC (--`x:bool`--) THEN
       BOOL_CASES_TAC (--`(y:'a) = z`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* EQ_F = |- (x = F) = (x => F | T)                                         *)
(*--------------------------------------------------------------------------*)

val EQ_F =
   prove
      ((--`(x = F) = (x => F | T)`--),
       BOOL_CASES_TAC (--`x:bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* prove_terms_not_eq : term -> term -> thm                                 *)
(*                                                                          *)
(* Function to prove that the left-hand and right-hand sides of an equation *)
(* are not equal. Works with Boolean constants, explicit values, and terms  *)
(* involving constructors and variables.                                    *)
(*--------------------------------------------------------------------------*)

fun prove_terms_not_eq l r =
   let fun STRUCT_CONV tm =
          (bool_EQ_CONV ORELSEC
           reduceLib.NEQ_CONV ORELSEC
           (fn tm => let val (l,r) = dest_eq tm
                         val ty_name = (#Tyop o Rsyntax.dest_type) (type_of l)
                         val ty_conv =
                            #struct_conv
                               (BoyerMooreShells.sys_shell_info ty_name)
                     in  ty_conv STRUCT_CONV tm
                     end) ORELSEC
           (* REFL_CONV ORELSEC   Omitted because it cannot generate false*)
           ALL_CONV) tm
   in  let val th = STRUCT_CONV (mk_eq (l,r))
       in  if (is_F (rhs (concl th))) then th else failwith ""
       end
       handle HOL_ERR _ => failwith "prove_terms_not_eq"
   end;

(*--------------------------------------------------------------------------*)
(* rewrite_equality : (term list -> term list -> conv) ->                   *)
(*                     term list -> term list -> conv                       *)
(*                                                                          *)
(* Function for rewriting equalities. Takes a general rewrite function, a   *)
(* chain of hypotheses and a list of assumptions as arguments.              *)
(*                                                                          *)
(* The left-hand and right-hand sides of the equality are rewritten         *)
(* recursively. If the two sides are then identical, the term is rewritten  *)
(* to T. If it can be shown that the two sides are not equal, the term is   *)
(* rewritten to F. Otherwise, the function rewrites with the first of the   *)
(* following rules that is applicable (or it leaves the term unchanged if   *)
(* none are applicable):                                                    *)
(*                                                                          *)
(*    (x = T)       ---> x                                                  *)
(*    (x = (y = z)) ---> ((y = z) => (x = T) | (x = F))                     *)
(*    (x = F)       ---> (x => F | T)                                       *)
(*                                                                          *)
(* The result is then rewritten using the known lemmas (rewrite rules).     *)
(*--------------------------------------------------------------------------*)

fun rewrite_equality rewrite hyp_chain assumps tm =
   let val th1 = ((RATOR_CONV (RAND_CONV (rewrite hyp_chain assumps))) THENC
                  (RAND_CONV (rewrite hyp_chain assumps))) tm
       val tm1 = rhs (concl th1)
       val (l,r) = dest_eq tm1
   in  if (l = r)
       then TRANS th1 (EQT_INTRO (ISPEC l EQ_REFL))
       else TRANS th1 (prove_terms_not_eq l r)
            handle HOL_ERR _ =>
            let val th2 = ((REWR_CONV EQ_T) ORELSEC
                           (REWR_CONV EQ_EQ) ORELSEC
                           (TRY_CONV (REWR_CONV EQ_F))) tm1
                val th3 = rewrite_with_lemmas rewrite hyp_chain assumps
                             (rhs (concl th2))
            in  TRANS (TRANS th1 th2) th3
            end
   end
   handle HOL_ERR _ => failwith "rewrite_equality";

(*--------------------------------------------------------------------------*)
(* rewrite_application :                                                    *)
(*    (term -> string list -> term list -> term list -> conv) ->            *)
(*     term -> string list -> term list -> term list -> conv                *)
(*                                                                          *)
(* Function for rewriting applications. It takes a general rewriting        *)
(* function, a literal (the literal containing the function call), a list   *)
(* of names of functions that are tentatively being opened up, a chain of   *)
(* hypotheses, and a list of assumptions as arguments.                      *)
(*                                                                          *)
(* The function begins by rewriting the arguments. It then determines the   *)
(* name of the function being applied. If this is a constructor, no further *)
(* rewriting is done. Otherwise, from the function name, the number of the  *)
(* argument used for recursion (or zero if the definition is not recursive) *)
(* and expansion theorems for each possible constructor are obtained. If    *)
(* the function is not recursive the call is opened up and the body is      *)
(* rewritten. If the function has no definition, the application is         *)
(* rewritten using the known lemmas.                                        *)
(*                                                                          *)
(* If the definition is recursive, but this function has already been       *)
(* tentatively opened up, the version of the application with the arguments *)
(* rewritten is returned.                                                   *)
(*                                                                          *)
(* Otherwise, the application is rewritten with the known lemmas. If any of *)
(* the lemmas are applicable the result of the rewrite is returned.         *)
(* Otherwise the function determines the name of the constructor appearing  *)
(* in the recursive argument, and looks up its details. If this process     *)
(* fails due to either the recursive argument not being an application of a *)
(* constructor, or because the constructor is not known, the function call  *)
(* cannot be expanded, so the original call (with arguments rewritten) is   *)
(* returned.                                                                *)
(*                                                                          *)
(* Provided a valid constructor is present in the recursive argument        *)
(* position the call is tentatively opened up. The body is rewritten with   *)
(* the name of the function added to the `tentative openings' list.         *)
(* (Actually, the name is not added to the list if the recursive argument   *)
(* of the call was an explicit value). The result is compared with the      *)
(* unopened call to see if it has good properties. If it does, the          *)
(* simplified body is returned. Otherwise the unopened call is returned.    *)
(*--------------------------------------------------------------------------*)

fun rewrite_application rewrite lit funcs hyp_chain assumps tm =
   let val th1 = ARGS_CONV (rewrite lit funcs hyp_chain assumps) tm
       val tm1 = rhs (concl th1)
       val (f,args) = strip_comb tm1
       val name = #1 (dest_const f)
   in
   if (mem name (BoyerMooreShells.all_constructors ()))
   then th1
   else
   let val (_,(i,constructors)) = BoyerMooreEnvironment.get_def name
   in  if (i = 0) then
          let val th2 =
                 REWR_CONV (#2 (hd constructors 
                                  handle List.Empty => failwith "")) tm1
              val th3 = rewrite lit funcs hyp_chain assumps (rhs (concl th2))
          in  TRANS (TRANS th1 th2) th3
          end
       else if (mem name funcs) then th1
       else let val th2 = rewrite_with_lemmas (rewrite lit funcs) hyp_chain
                             assumps tm1
                val tm2 = rhs (concl th2)
            in  if (tm2 = tm1)
                then let val argi = el i args
                         val constructor =
                            #Name (Rsyntax.dest_const (#1 (strip_comb argi)))
                            handle HOL_ERR _ => ""
                     in  let val th = assoc constructor constructors
                             val th3 = REWR_CONV th tm1
                             val tm3 = rhs (concl th3)
                             val funcs' =
                                if (BoyerMooreDefinitions.is_explicit_value
                                       argi)
                                then funcs
                                else name::funcs
                             val th4 = rewrite lit funcs' hyp_chain assumps tm3
                             val tm4 = rhs (concl th4)
                         in  if (BoyerMooreDefinitions.good_properties assumps
                                    tm1 tm4 lit)
                             then TRANS (TRANS th1 th3) th4
                             else th1
                         end
                         handle HOL_ERR _ => th1
                              | NOT_FOUND => th1
                     end
                else TRANS th1 th2
            end
   end
   handle HOL_ERR {origin_structure = "BoyerMooreEnvironment",
                   origin_function = "get_def",message = ""} =>
   TRANS th1 (rewrite_with_lemmas (rewrite lit funcs) hyp_chain assumps tm1)
   end
   handle HOL_ERR _ => failwith "rewrite_application";

(*--------------------------------------------------------------------------*)
(* rewrite_term : term -> string list -> term list -> term list -> conv     *)
(*                                                                          *)
(* Function for rewriting a term. Arguments are as follows:                 *)
(*                                                                          *)
(*    lit       : the literal containing the term to be rewritten.          *)
(*    funcs     : names of functions that have been tentatively opened up.  *)
(*    hyp_chain : hypotheses that we are trying to satisfy by parent calls. *)
(*    assumps   : a list of assumptions.                                    *)
(*    tm        : the term to be rewritten.                                 *)
(*--------------------------------------------------------------------------*)

fun rewrite_term lit funcs hyp_chain assumps tm =
   (EQT_INTRO (ASSUME (find (fn t => t = tm) assumps)))
   handle HOL_ERR _ =>
   (EQF_INTRO (ASSUME (find (fn t => t = mk_neg tm) assumps)))
   handle HOL_ERR _ => 
   let val rewrite = rewrite_term lit funcs
   in  if (is_var tm) then ALL_CONV tm
       else if (BoyerMooreDefinitions.is_explicit_value tm) then
          rewrite_explicit_value tm
       else if (is_cond tm) then
          rewrite_conditional (rewrite hyp_chain) assumps tm
       else if (is_eq tm) then rewrite_equality rewrite hyp_chain assumps tm
       else rewrite_application rewrite_term lit funcs hyp_chain assumps tm
   end
   handle HOL_ERR _ => failwith "rewrite_term";

(*--------------------------------------------------------------------------*)
(* COND_RAND = |- !f b x y. f (b => x | y) = (b => f x | f y)               *)
(*--------------------------------------------------------------------------*)

(* Already defined in HOL *)

(*--------------------------------------------------------------------------*)
(* COND_RATOR = |- !b f g x. (b => f | g) x = (b => f x | g x)              *)
(*--------------------------------------------------------------------------*)

(* Already defined in HOL *)

(*--------------------------------------------------------------------------*)
(* MOVE_COND_UP_CONV : conv                                                 *)
(*                                                                          *)
(* Moves all conditionals in a term up to the top-level. Checks to see if   *)
(* the term contains any conditionals before it starts to do inference.     *)
(* This improves the performance significantly. Alternatively, failure      *)
(* could be used to avoid rebuilding unchanged sub-terms. This would be     *)
(* even more efficient.                                                     *)
(*--------------------------------------------------------------------------*)

fun MOVE_COND_UP_CONV tm =
   (if (not (can (find_term is_cond) tm)) then ALL_CONV tm
    else if (is_cond tm) then
       (RATOR_CONV (RATOR_CONV (RAND_CONV MOVE_COND_UP_CONV)) THENC
        RATOR_CONV (RAND_CONV MOVE_COND_UP_CONV) THENC
        RAND_CONV MOVE_COND_UP_CONV) tm
    else if (is_comb tm) then
       let val (f,arg) = dest_comb tm
       in  if (is_cond f) then
              ((REWR_CONV COND_RATOR) THENC MOVE_COND_UP_CONV) tm
           else if (is_cond arg) then
              ((REWR_CONV COND_RAND) THENC MOVE_COND_UP_CONV) tm
           else let val th = (RATOR_CONV MOVE_COND_UP_CONV THENC
                              RAND_CONV MOVE_COND_UP_CONV) tm
                    val tm' = rhs (concl th)
                in  if (tm' = tm)
                    then th
                    else TRANS th (MOVE_COND_UP_CONV tm')
                end
       end
    else ALL_CONV tm)
   handle HOL_ERR _ => failwith "MOVE_COND_UP_CONV";

(*--------------------------------------------------------------------------*)
(* COND_OR = |- (b => x | y) \/ z = (~b \/ x \/ z) /\ (b \/ y \/ z)         *)
(*--------------------------------------------------------------------------*)

val COND_OR =
   prove
      ((--`(b => x | y) \/ z = (~b \/ x \/ z) /\ (b \/ y \/ z)`--),
       BOOL_CASES_TAC (--`b:bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* COND_EXPAND = |- (x => y | z) = ((~x \/ y) /\ (x \/ z))                  *)
(*--------------------------------------------------------------------------*)

(* Already proved *)
val COND_EXPAND = BoyerMooreClausalForm.COND_EXPAND;

(*--------------------------------------------------------------------------*)
(* NOT_NOT_NORM = |- ~~x = x                                                *)
(*--------------------------------------------------------------------------*)

(* Already proved *)
val NOT_NOT_NORM = BoyerMooreClausalForm.NOT_NOT_NORM;

(*--------------------------------------------------------------------------*)
(* LEFT_OR_OVER_AND =                                                       *)
(* |- !t1 t2 t3. t1 \/ t2 /\ t3 = (t1 \/ t2) /\ (t1 \/ t3)                  *)
(*--------------------------------------------------------------------------*)

(* Already available in HOL *)

(*--------------------------------------------------------------------------*)
(* MOVE_NOT_THRU_CONDS_CONV : conv                                          *)
(*                                                                          *)
(* Function to push a negation down through (possibly) nested conditionals. *)
(* Eliminates any double-negations that may be introduced.                  *)
(*--------------------------------------------------------------------------*)

fun MOVE_NOT_THRU_CONDS_CONV tm =
   (if (is_neg tm)
    then if (is_cond (rand tm))
         then ((REWR_CONV COND_RAND) THENC
               (RATOR_CONV (RAND_CONV MOVE_NOT_THRU_CONDS_CONV)) THENC
               (RAND_CONV MOVE_NOT_THRU_CONDS_CONV)) tm
         else TRY_CONV (REWR_CONV NOT_NOT_NORM) tm
    else ALL_CONV tm)
   handle HOL_ERR _ => failwith "MOVE_NOT_THRU_CONDS_CONV";

(*--------------------------------------------------------------------------*)
(* EXPAND_ONE_COND_CONV : conv                                              *)
(*                                                                          *)
(* The function takes a term which it assumes to be either a conditional or *)
(* the disjunction of a conditional and some other term, and applies one of *)
(* the following rewrites as appropriate:                                   *)
(*                                                                          *)
(*    |- (b => x | y) = (~b \/ x) /\ (b \/ y)                               *)
(*                                                                          *)
(*    |- (b => x | y) \/ z = (~b \/ x \/ z) /\ (b \/ y \/ z)                *)
(*                                                                          *)
(* If b happens to be a conditional, the negation of ~b is moved down       *)
(* through the conditional (and any nested conditionals).                   *)
(*--------------------------------------------------------------------------*)

fun EXPAND_ONE_COND_CONV tm =
   (((REWR_CONV COND_OR) ORELSEC (REWR_CONV COND_EXPAND)) THENC
    (RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV MOVE_NOT_THRU_CONDS_CONV)))))
   tm
   handle HOL_ERR _ => failwith "EXPAND_ONE_COND_CONV";

(*--------------------------------------------------------------------------*)
(* OR_OVER_ANDS_CONV : conv -> conv                                         *)
(*                                                                          *)
(* Distributes an OR over an arbitrary tree of conjunctions and applies a   *)
(* conversion to each of the disjunctions that make up the new conjunction. *)
(*--------------------------------------------------------------------------*)

fun OR_OVER_ANDS_CONV conv tm =
   if (is_disj tm)
   then if (is_conj (rand tm))
        then ((REWR_CONV LEFT_OR_OVER_AND) THENC
              (RATOR_CONV (RAND_CONV (OR_OVER_ANDS_CONV conv))) THENC
              (RAND_CONV (OR_OVER_ANDS_CONV conv))) tm
        else conv tm
   else ALL_CONV tm;

(*--------------------------------------------------------------------------*)
(* EXPAND_COND_CONV : conv                                                  *)
(*                                                                          *)
(* The function takes a term which it assumes to be either a conditional or *)
(* the disjunction of a conditional and some other term, and expands the    *)
(* conditional into a disjunction using one of:                             *)
(*                                                                          *)
(*    |- (b => x | y) = (~b \/ x) /\ (b \/ y)                               *)
(*                                                                          *)
(*    |- (b => x | y) \/ z = (~b \/ x \/ z) /\ (b \/ y \/ z)                *)
(*                                                                          *)
(* The b, x and y may themselves be conditionals. If so, the function       *)
(* expands these as well, and so on, until there are no more conditionals.  *)
(* At each stage disjunctions are distributed over conjunctions so that the *)
(* final result is a conjunction `tree' where each of the conjuncts is a    *)
(* disjunction. The depth of a disjunction in the conjunction tree          *)
(* indicates the number of literals that have been added to the disjunction *)
(* compared to the original term.                                           *)
(*--------------------------------------------------------------------------*)

fun EXPAND_COND_CONV tm =
   (EXPAND_ONE_COND_CONV THENC
    (RATOR_CONV (RAND_CONV ((RAND_CONV EXPAND_COND_CONV) THENC
                            (OR_OVER_ANDS_CONV EXPAND_COND_CONV)))) THENC
    (RAND_CONV ((RAND_CONV EXPAND_COND_CONV) THENC
                (OR_OVER_ANDS_CONV EXPAND_COND_CONV)))) tm
   handle HOL_ERR _ => ALL_CONV tm;

(*--------------------------------------------------------------------------*)
(* SPLIT_CLAUSE_ON_COND_CONV : int -> conv                                  *)
(*                                                                          *)
(* The function takes a number n and a term which it assumes to be a        *)
(* disjunction of literals in which the (n-1)th argument has had all        *)
(* conditionals moved to the top level.                                     *)
(*                                                                          *)
(* The function dives down to the (n-1)th literal (disjunct) and expands    *)
(* the conditionals into disjunctions, resulting in a conjunction `tree' in *)
(* which each conjunct is a disjunction.                                    *)
(*                                                                          *)
(* As the function `backs out' from the (n-1)th literal it distributes the  *)
(* ORs over the conjunction tree.                                           *)
(*--------------------------------------------------------------------------*)

fun SPLIT_CLAUSE_ON_COND_CONV n tm =
   funpow n (fn conv => (RAND_CONV conv) THENC (OR_OVER_ANDS_CONV ALL_CONV))
      EXPAND_COND_CONV tm
   handle HOL_ERR _ => failwith "SPLIT_CLAUSE_ON_COND_CONV";

(*--------------------------------------------------------------------------*)
(* simplify_one_literal : int -> term -> (thm * int)                        *)
(*                                                                          *)
(* Attempts to simplify one literal of a clause assuming the negations of   *)
(* the other literals. The number n specifies which literal to rewrite. If  *)
(* n = 0, the first literal is rewritten. The function fails if n is out of *)
(* range.                                                                   *)
(*                                                                          *)
(* If the literal to be simplified is negative, the function simplifies the *)
(* corresponding atom, and negates the result. If this new result is T or   *)
(* F, the clause is rebuilt by discharging the assumptions. This process    *)
(* may reduce the number of literals in the clause, so the theorem returned *)
(* is paired with -1 (except when processing the last literal of a clause   *)
(* in which case returning 0 will, like -1, cause a failure when an attempt *)
(* is made to simplify the next literal, but is safer because it can't      *)
(* cause looping if the literal has not been removed. This is the case when *)
(* the last literal has been rewritten to F. In this situation, the         *)
(* discharging function does not eliminate the literal).                    *)
(*                                                                          *)
(* If the simplified literal contains conditionals, these are brought up to *)
(* the top-level. The clause is then rebuilt by discharging. If no          *)
(* conditionals were present the theorem is returned with 0, indicating     *)
(* that the number of literals has not changed. Otherwise the clause is     *)
(* split into a conjunction of clauses, so that the conditionals are        *)
(* eliminated, and the result is returned with the number 1 to indicate     *)
(* that the number of literals has increased.                               *)
(*--------------------------------------------------------------------------*)

fun simplify_one_literal n tm =
   let fun negate tm = if (is_neg tm) then (rand tm) else (mk_neg tm)
       and NEGATE th =
          let val tm = rhs (concl th)
              and th' = AP_TERM (--`$~`--) th
          in  if (is_T tm) then TRANS th' (el 2 (CONJUNCTS NOT_CLAUSES))
              else if (is_F tm) then TRANS th' (el 3 (CONJUNCTS NOT_CLAUSES))
              else th'
          end
       val (overs,y,unders) =
          case (chop_list n (disj_list tm))
          of (overs,y::unders) => (overs,y,unders)
           | _ => failwith ""
       val overs' = map negate overs
       and unders' = map negate unders
       val th1 =
          if (is_neg y)
          then NEGATE (rewrite_term y [] [] (overs' @ unders') (rand y))
          else rewrite_term y [] [] (overs' @ unders') y
       val tm1 = rhs (concl th1)
   in  if ((is_T tm1) orelse (is_F tm1))
       then (BoyerMooreRewriteRules.MULTI_DISJ_DISCH (overs',unders') th1,
             if (null unders) then 0 else (~1))
       else let val th2 = TRANS th1 (MOVE_COND_UP_CONV tm1)
                val tm2 = rhs (concl th2)
                val th3 = BoyerMooreRewriteRules.MULTI_DISJ_DISCH
                             (overs',unders') th2
            in  if (is_cond tm2)
                then (CONV_RULE (RAND_CONV (SPLIT_CLAUSE_ON_COND_CONV n)) th3,
                      1)
                else (th3,0)
            end
   end
   handle HOL_ERR _ => failwith "simplify_one_literal";

(*--------------------------------------------------------------------------*)
(* simplify_clause : int -> term -> (term list * proof)                     *)
(* simplify_clauses : int -> term -> (term list * proof)                    *)
(*                                                                          *)
(* Functions for simplifying a clause by rewriting each literal in turn     *)
(* assuming the negations of the others.                                    *)
(*                                                                          *)
(* The integer argument to simplify_clause should be zero initially. It     *)
(* will then attempt to simplify the first literal. If the result is true,  *)
(* no new clauses are produced. Otherwise, the function proceeds to         *)
(* simplify the next literal. This has to be done differently according to  *)
(* the changes that took place when simplifying the first literal.          *)
(*                                                                          *)
(* If there was a reduction in the number of literals, this must have been  *)
(* due to the literal being shown to be false, because the true case has    *)
(* already been eliminated. So, there must be one less literal, and so n is *)
(* unchanged on the recursive call. If there was no change in the number of *)
(* literals, n is incremented by 1. Otherwise, not only have new literals   *)
(* been introduced, but also the clause has been split into a conjunction   *)
(* of clauses. simplify_clauses is called to handle this case.              *)
(*                                                                          *)
(* When all the literals have been processed, n will become out of range    *)
(* and cause a failure. This is trapped, and the simplified clause is       *)
(* returned.                                                                *)
(*                                                                          *)
(* When the clause has been split into a conjunction of clauses, the depth  *)
(* of a clause in the tree of conjunctions indicates how many literals have *)
(* been added to that clause. simplify_clauses recursively splits           *)
(* conjunctions, incrementing n as it proceeds, until it reaches a clause.  *)
(* It then calls simplify_clause to deal with the clause.                   *)
(*--------------------------------------------------------------------------*)

fun simplify_clause n tm =
   let val (th,change_flag) = simplify_one_literal n tm
       val tm' = rhs (concl th)
   in  if (is_T tm')
       then ([],BoyerMooreWaterfall.apply_proof (fn ths => EQT_ELIM th) [])
       else let val (tms,proof) =
                   if (change_flag < 0) then simplify_clause n tm'
                   else if (change_flag = 0) then simplify_clause (n + 1) tm'
                   else simplify_clauses (n + 1) tm'
            in  (tms,fn ths => EQ_MP (SYM th) (proof ths))
            end
   end
   handle HOL_ERR _ => ([tm],BoyerMooreWaterfall.apply_proof hd [tm])

and simplify_clauses n tm =
   let val (tm1,tm2) = dest_conj tm
       val (tms1,proof1) = simplify_clauses (n + 1) tm1
       and (tms2,proof2) = simplify_clauses (n + 1) tm2
   in  (tms1 @ tms2,
        fn ths => let val (ths1,ths2) = chop_list (length tms1) ths
                  in  CONJ (proof1 ths1) (proof2 ths2)
                  end)
   end
   handle HOL_ERR _ => (simplify_clause n tm);

(*--------------------------------------------------------------------------*)
(* simplify_heuristic : (term * bool) -> ((term * bool) list * proof)       *)
(*                                                                          *)
(* Wrapper for simplify_clause. This function has the correct type and      *)
(* properties to be used as a `heuristic'. In particular, if the result of  *)
(* simplify_clause is a single clause identical to the input clause,        *)
(* a failure is generated.                                                  *)
(*--------------------------------------------------------------------------*)

fun simplify_heuristic (tm,(ind:bool)) =
   let val (tms,proof) = simplify_clause 0 tm
   in  if (tms = [tm])
       then failwith ""
       else (map (fn tm => (tm,ind)) tms,proof)
   end
   handle HOL_ERR _ => failwith "simplify_heuristic";

(*--------------------------------------------------------------------------*)
(* NOT_EQ_F = |- !x. ~(x = x) = F                                           *)
(*--------------------------------------------------------------------------*)

val NOT_EQ_F =
   GEN_ALL
      (TRANS (AP_TERM (--`$~`--) (SPEC_ALL REFL_CLAUSE))
          (el 2 (CONJUNCTS NOT_CLAUSES)));

(*--------------------------------------------------------------------------*)
(* subst_heuristic : (term * bool) -> ((term * bool) list * proof)          *)
(*                                                                          *)
(* `Heuristic' for eliminating from a clause, a negated equality between a  *)
(* variable and another term not containing the variable. For example,      *)
(* given the clause:                                                        *)
(*                                                                          *)
(*    x1 \/ ~(x = t) \/ x3 \/ f x \/ x5                                     *)
(*                                                                          *)
(* the function returns the clause:                                         *)
(*                                                                          *)
(*    x1 \/ F \/ x3 \/ f t \/ x5                                            *)
(*                                                                          *)
(* So, all occurrences of x are replaced by t, and the equality x = t is    *)
(* `thrown away'. The F could be eliminated, but the simplification         *)
(* heuristic will deal with it, so there is no point in duplicating the     *)
(* code.                                                                    *)
(*                                                                          *)
(* The function fails if there are no equalities that can be eliminated.    *)
(*                                                                          *)
(* The function proves the following three theorems:                        *)
(*                                                                          *)
(*    ~(x = t) |- x1 \/ ~(x = t) \/ x3 \/ f x \/ x5                         *)
(*                                                                          *)
(*       x = t |- x1 \/ ~(x = t) \/ x3 \/ f x \/ x5 =                       *)
(*                x1 \/     F    \/ x3 \/ f t \/ x5                         *)
(*                                                                          *)
(*             |- (x = t) \/ ~(x = t)                                       *)
(*                                                                          *)
(* and returns the term (--`x1 \/ F \/ x3 \/ f t \/ x5`--) to be proved.    *)
(* When given this term as a theorem, it is possible to prove from the      *)
(* second theorem:                                                          *)
(*                                                                          *)
(*       x = t |- x1 \/ ~(x = t) \/ x3 \/ f x \/ x5                         *)
(*                                                                          *)
(* which together with the first and third theorems yields a theorem for    *)
(* the original clause.                                                     *)
(*--------------------------------------------------------------------------*)

fun subst_heuristic (tm,(ind:bool)) =
   let fun check (v,t) = (is_var v) andalso (not (mem v (free_vars t)))
       fun split_disjuncts tml =
          (if (can (assert check o dest_eq o dest_neg) (hd tml))
           then ([],tml)
           else (fn (l1,l2) => ((hd tml)::l1,l2)) (split_disjuncts (tl tml)))
          handle List.Empty => failwith "" 
       val (overs,neq,unders) =
          case (split_disjuncts (disj_list tm))
          of (overs,neq::unders) => (overs,neq,unders)
           | _ => failwith ""
       val eq = dest_neg neq
       val (v,t) = dest_eq eq
       val ass = ASSUME neq
       val th1 = itlist DISJ2 overs
                    (DISJ1 ass (list_mk_disj unders) handle HOL_ERR _ => ass)
       and th2 = SUBS [ISPEC t NOT_EQ_F] (SUBST_CONV [(ASSUME eq,v)] tm tm)
       and th3 = SPEC eq EXCLUDED_MIDDLE
       val tm' = rhs (concl th2)
       fun proof th = DISJ_CASES th3 (EQ_MP (SYM th2) th) th1
   in  ([(tm',ind)],BoyerMooreWaterfall.apply_proof (proof o hd) [tm'])
   end
   handle HOL_ERR _ => failwith "subst_heuristic";

end;

end; (* BoyerMooreTermsAndClauses *)
