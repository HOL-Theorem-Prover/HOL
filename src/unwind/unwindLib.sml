(*****************************************************************************)
(* FILE          : unwindLib.sml                                             *)
(* DESCRIPTION   : Rules for unfolding, unwinding, pruning, etc.             *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : Originally written for LCF-LSM by Mike Gordon (MJCG).     *)
(* 21.May.1985   : Additions by Tom Melham (TFM).                            *)
(* 10.Mar.1988   : Modifications by David Shepherd (DES) of INMOS.           *)
(* 24.Mar.1988   : Bug fixes by David Shepherd (DES).                        *)
(* 23.Apr.1990   : Modifications by Tom Melham (TFM).                        *)
(* 22.Aug.1991   : Additions and tidying-up by Richard Boulton (RJB).        *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 3rd September 1991                                        *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                       *)
(*****************************************************************************)

structure unwindLib :> unwindLib =
struct

open HolKernel Parse boolLib Rsyntax ;

infix THENC ##;

val UNWIND_ERR = mk_HOL_ERR "Unwind";

val AND = boolSyntax.conjunction;

(*===========================================================================*)
(* Tools for manipulating device implementations `by hand'                   *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* DEPTH_FORALL_CONV : conv -> conv                                          *)
(*                                                                           *)
(* DEPTH_FORALL_CONV conv "!x1 ... xn. body" applies conv to "body" and      *)
(* returns a theorem of the form:                                            *)
(*                                                                           *)
(*    |- (!x1 ... xn. body) = (!x1 ... xn. body')                            *)
(*---------------------------------------------------------------------------*)

fun DEPTH_FORALL_CONV conv tm =
   if (is_forall tm)
   then RAND_CONV (ABS_CONV (DEPTH_FORALL_CONV conv)) tm
   else conv tm;

(*---------------------------------------------------------------------------*)
(* DEPTH_EXISTS_CONV : conv -> conv                                          *)
(*                                                                           *)
(* DEPTH_EXISTS_CONV conv "?x1 ... xn. body" applies conv to "body" and      *)
(* returns a theorem of the form:                                            *)
(*                                                                           *)
(*    |- (?x1 ... xn. body) = (?x1 ... xn. body')                            *)
(*---------------------------------------------------------------------------*)

fun DEPTH_EXISTS_CONV conv tm =
   if (is_exists tm)
   then RAND_CONV (ABS_CONV (DEPTH_EXISTS_CONV conv)) tm
   else conv tm;

(*---------------------------------------------------------------------------*)
(* FLATTEN_CONJ_CONV : conv                                                  *)
(*                                                                           *)
(*    "t1 /\ ... /\ tn"                                                      *)
(*    ---->                                                                  *)
(*    |- t1 /\ ... /\ tn = u1 /\ ... /\ un                                   *)
(*                                                                           *)
(* where the RHS of the equation is a flattened version of the LHS.          *)
(*---------------------------------------------------------------------------*)

fun FLATTEN_CONJ_CONV t = CONJUNCTS_CONV (t,list_mk_conj (strip_conj t));

(*===========================================================================*)
(* Moving universal quantifiers in and out of conjunctions                   *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* CONJ_FORALL_ONCE_CONV : conv                                              *)
(*                                                                           *)
(*    "(!x. t1) /\ ... /\ (!x. tn)"                                          *)
(*    ---->                                                                  *)
(*    |- (!x. t1) /\ ... /\ (!x. tn) = !x. t1 /\ ... /\ tn                   *)
(*                                                                           *)
(* where the original term can be an arbitrary tree of /\s, not just linear. *)
(* The structure of the tree is retained in both sides of the equation.      *)
(*                                                                           *)
(* To avoid deriving incompatible theorems for IMP_ANTISYM_RULE when one or  *)
(* more of the ti's is a conjunction, the original term is broken up as well *)
(* as the theorem. If this were not done, the conversion would fail in such  *)
(* cases.                                                                    *)
(*---------------------------------------------------------------------------*)

local exception NOT_ALL_SAME_VAR
in
fun CONJ_FORALL_ONCE_CONV t =
   let fun conj_tree_map f t th =
          let val {conj1,conj2} = dest_conj t
              and (th1,th2) = CONJ_PAIR th
          in CONJ (conj_tree_map f conj1 th1) (conj_tree_map f conj2 th2)
          end handle HOL_ERR _ => (f th)
       val conjs = strip_conj t
   in if (length conjs = 1) 
      then REFL t
      else let val var = 
                  case (mk_set (map (#Bvar o dest_forall) conjs))
                   of [x] => x
                    | _ => raise UNWIND_ERR "CONJ_FORALL_ONCE_CONV"
                                   "bound vars do not have same name"
               val th = GEN var (conj_tree_map (SPEC var) t (ASSUME t))
               val th1 = DISCH t th
               and th2 = DISCH (concl th)
                               (conj_tree_map (GEN var) t 
                                              (SPEC var (ASSUME (concl th))))
        in IMP_ANTISYM_RULE th1 th2
        end
   end
   handle (e as HOL_ERR{origin_function = "CONJ_FORALL_ONCE_CONV",...})
          => raise e
        | HOL_ERR _ => raise UNWIND_ERR "CONJ_FORALL_ONCE_CONV" ""
end;

(*---------------------------------------------------------------------------*)
(* FORALL_CONJ_ONCE_CONV : conv                                              *)
(*                                                                           *)
(*    "!x. t1 /\ ... /\ tn"                                                  *)
(*    ---->                                                                  *)
(*    |- !x. t1 /\ ... /\ tn = (!x. t1) /\ ... /\ (!x. tn)                   *)
(*                                                                           *)
(* where the original term can be an arbitrary tree of /\s, not just linear. *)
(* The structure of the tree is retained in both sides of the equation.      *)
(*---------------------------------------------------------------------------*)

fun FORALL_CONJ_ONCE_CONV t =
   let fun conj_tree_map f th =
         let val (th1,th2) = CONJ_PAIR th
         in CONJ (conj_tree_map f th1) (conj_tree_map f th2)
         end handle HOL_ERR _ => f th
       val var = #Bvar (dest_forall t)
       val th = conj_tree_map (GEN var) (SPEC var (ASSUME t))
       val th1 = DISCH t th
       and th2 = DISCH (concl th)
                       (GEN var (conj_tree_map (SPEC var) (ASSUME (concl th))))
   in IMP_ANTISYM_RULE th1 th2
   end 
   handle HOL_ERR _ => raise UNWIND_ERR "FORALL_CONJ_ONCE_CONV" "";

(*---------------------------------------------------------------------------*)
(* CONJ_FORALL_CONV : conv                                                   *)
(*                                                                           *)
(*    "(!x1 ... xm. t1) /\ ... /\ (!x1 ... xm. tn)"                          *)
(*    ---->                                                                  *)
(*    |- (!x1 ... xm. t1) /\ ... /\ (!x1 ... xm. tn) =                       *)
(*       !x1 ... xm. t1 /\ ... /\ tn                                         *)
(*                                                                           *)
(* where the original term can be an arbitrary tree of /\s, not just linear. *)
(* The structure of the tree is retained in both sides of the equation.      *)
(*---------------------------------------------------------------------------*)

(*
local exception FAIL
in
fun CONJ_FORALL_CONV tm =
  (if (length (strip_conj tm) = 1)
   then raise FAIL
   else (CONJ_FORALL_ONCE_CONV THENC RAND_CONV (ABS_CONV CONJ_FORALL_CONV)) tm)
   handle _ => REFL tm
end;
*)

fun CONJ_FORALL_CONV tm =
  case (strip_conj tm)
   of [_] => REFL tm
    |  _  => (CONJ_FORALL_ONCE_CONV THENC 
              RAND_CONV (ABS_CONV CONJ_FORALL_CONV)) tm 
              handle HOL_ERR _ => REFL tm;


(*---------------------------------------------------------------------------*)
(* FORALL_CONJ_CONV : conv                                                   *)
(*                                                                           *)
(*    "!x1 ... xm. t1 /\ ... /\ tn"                                          *)
(*    ---->                                                                  *)
(*    |- !x1 ... xm. t1 /\ ... /\ tn =                                       *)
(*       (!x1 ... xm. t1) /\ ... /\ (!x1 ... xm. tn)                         *)
(*                                                                           *)
(* where the original term can be an arbitrary tree of /\s, not just linear. *)
(* The structure of the tree is retained in both sides of the equation.      *)
(*---------------------------------------------------------------------------*)

fun FORALL_CONJ_CONV tm =
   if (is_forall tm)
   then (RAND_CONV (ABS_CONV FORALL_CONJ_CONV) THENC FORALL_CONJ_ONCE_CONV) tm
   else REFL tm;

(*---------------------------------------------------------------------------*)
(* CONJ_FORALL_RIGHT_RULE : thm -> thm                                       *)
(*                                                                           *)
(*     A |- !z1 ... zr.                                                      *)
(*           t = ?y1 ... yp. (!x1 ... xm. t1) /\ ... /\ (!x1 ... xm. tn)     *)
(*    -------------------------------------------------------------------    *)
(*     A |- !z1 ... zr. t = ?y1 ... yp. !x1 ... xm. t1 /\ ... /\ tn          *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun CONJ_FORALL_RIGHT_RULE th =
   CONV_RULE
       (DEPTH_FORALL_CONV (RAND_CONV (DEPTH_EXISTS_CONV CONJ_FORALL_CONV))) th
   handle HOL_ERR _ => raise UNWIND_ERR "CONJ_FORALL_RIGHT_RULE" "";

(*---------------------------------------------------------------------------*)
(* FORALL_CONJ_RIGHT_RULE : thm -> thm                                       *)
(*                                                                           *)
(*     A |- !z1 ... zr. t = ?y1 ... yp. !x1 ... xm. t1 /\ ... /\ tn          *)
(*    -------------------------------------------------------------------    *)
(*     A |- !z1 ... zr.                                                      *)
(*           t = ?y1 ... yp. (!x1 ... xm. t1) /\ ... /\ (!x1 ... xm. tn)     *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun FORALL_CONJ_RIGHT_RULE th =
   CONV_RULE
       (DEPTH_FORALL_CONV (RAND_CONV (DEPTH_EXISTS_CONV FORALL_CONJ_CONV))) th
   handle HOL_ERR _ => raise UNWIND_ERR "FORALL_CONJ_RIGHT_RULE" "";

(*===========================================================================*)
(* Rules for unfolding                                                       *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(* UNFOLD_CONV : thm list -> conv                                            *)
(*                                                                           *)
(*    UNFOLD_CONV thl                                                        *)
(*                                                                           *)
(*    "t1 /\ ... /\ tn"                                                      *)
(*    ---->                                                                  *)
(*    B |- t1 /\ ... /\ tn = t1' /\ ... /\ tn'                               *)
(*                                                                           *)
(* where each ti' is the result of rewriting ti with the theorems in thl. The*)
(* set of assumptions B is the union of the instantiated assumptions of the  *)
(* theorems used for rewriting. If none of the rewrites are applicable to a  *)
(* ti, it is unchanged.                                                      *)
(*---------------------------------------------------------------------------*)

fun UNFOLD_CONV thl =
   let val the_net = Rewrite.add_rewrites Rewrite.empty_rewrites thl
       fun THENQC conv1 conv2 tm =
          let val th1 = conv1 tm
          in   TRANS th1 (conv2 (rhs (concl th1)))
          handle HOL_ERR _ => th1
          end handle HOL_ERR _ => conv2 tm
       fun CONJ_TREE_CONV conv tm =
          if (is_conj tm)
          then THENQC (RATOR_CONV (RAND_CONV (CONJ_TREE_CONV conv)))
                      (RAND_CONV (CONJ_TREE_CONV conv)) tm
          else conv tm
   in fn t => 
      if (null thl)
      then REFL t
      else CONJ_TREE_CONV (Rewrite.REWRITES_CONV the_net) t 
           handle HOL_ERR _ => REFL t
   end;

(*---------------------------------------------------------------------------*)
(* UNFOLD_RIGHT_RULE : thm list -> thm -> thm                                *)
(*                                                                           *)
(*    UNFOLD_RIGHT_RULE thl                                                  *)
(*                                                                           *)
(*         A |- !z1 ... zr. t = ?y1 ... yp. t1 /\ ... /\ tn                  *)
(*    --------------------------------------------------------               *)
(*     B u A |- !z1 ... zr. t = ?y1 ... yp. t1' /\ ... /\ tn'                *)
(*                                                                           *)
(* where each ti' is the result of rewriting ti with the theorems in thl. The*)
(* set of assumptions B is the union of the instantiated assumptions of the  *)
(* theorems used for rewriting. If none of the rewrites are applicable to a  *)
(* ti, it is unchanged.                                                      *)
(*---------------------------------------------------------------------------*)

fun UNFOLD_RIGHT_RULE thl th =
   CONV_RULE
      (DEPTH_FORALL_CONV (RAND_CONV (DEPTH_EXISTS_CONV (UNFOLD_CONV thl))))
      th
   handle HOL_ERR _ => raise UNWIND_ERR "UNFOLD_RIGHT_RULE" "";

(*===========================================================================*)
(* Rules for unwinding device implementations                                *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* line_var : term -> term                                                   *)
(*                                                                           *)
(*    line_var "!y1 ... ym. f x1 ... xn = t"  ----> "f"                      *)
(*---------------------------------------------------------------------------*)

fun line_var tm =
   (fst o strip_comb o lhs o snd o strip_forall) tm 
   handle HOL_ERR _ => raise UNWIND_ERR "line_var" "";

(*---------------------------------------------------------------------------*)
(* line_name : term -> string                                                *)
(*                                                                           *)
(*    line_name "!y1 ... ym. f x1 ... xn = t"  ----> "f"                     *)
(*---------------------------------------------------------------------------*)

fun line_name tm = (#Name o dest_var o line_var) tm 
                   handle HOL_ERR _ => raise UNWIND_ERR "line_name" "";

(*---------------------------------------------------------------------------*)
(* UNWIND_ONCE_CONV : (term -> bool) -> conv                                 *)
(*                                                                           *)
(* Basic conversion for parallel unwinding of equations defining wire values *)
(* in a standard device specification.                                       *)
(*                                                                           *)
(* USAGE: UNWIND_ONCE_CONV p tm                                              *)
(*                                                                           *)
(* DESCRIPTION: tm should be a conjunction of terms, equivalent under        *)
(*              associative-commutative reordering to:                       *)
(*                                                                           *)
(*                   t1 /\ t2 /\ ... /\ tn.                                  *)
(*                                                                           *)
(*              The function p:term->bool is a predicate which will be       *)
(*              used to partition the terms ti for 1 <= i <= n into two      *)
(*              disjoint sets:                                               *)
(*                                                                           *)
(*                   REW = {ti | p ti} and OBJ = {ti | ~p ti}                *)
(*                                                                           *)
(*              The terms ti for which p is true are then used as a set      *)
(*              of rewrite rules (thus they should be equations) to do a     *)
(*              single top-down parallel rewrite of the remaining terms.     *)
(*              The rewritten terms take the place of the original terms     *)
(*              in the input conjunction.                                    *)
(*                                                                           *)
(*              For example, if tm is:                                       *)
(*                                                                           *)
(*                 t1 /\ t2 /\ t3 /\ t4                                      *)
(*                                                                           *)
(*              and REW = {t1,t3} then the result is:                        *)
(*                                                                           *)
(*                 |-  t1 /\ t2 /\ t3 /\ t4 = t1 /\ t2' /\ t3 /\ t4'         *)
(*                                                                           *)
(*              where ti' is ti rewritten with the equations REW.            *)
(*                                                                           *)
(* IMPLEMENTATION NOTE:                                                      *)
(*                                                                           *)
(* The assignment:                                                           *)
(*                                                                           *)
(*    let pf,fn,eqns = trav p tm []                                          *)
(*                                                                           *)
(* makes                                                                     *)
(*                                                                           *)
(*    eqns = a list of theorems constructed by assuming each term for        *)
(*           which p is true, i.e., eqns = the list of rewrites.             *)
(*                                                                           *)
(*    fnn  = a function which, when applied to a rewriting conversion        *)
(*           will reconstruct the original term in the original structure,   *)
(*           but with the subterms for which p is not true rewritten         *)
(*           using the supplied conversion.                                  *)
(*                                                                           *)
(*    pf   = a function which maps |- tm to [|- t1;...;|- tj] where each     *)
(*           ti is a term for which p is true.                               *)
(*---------------------------------------------------------------------------*)

local
fun trav p tm rl =
   let val {conj1,conj2} = dest_conj tm
       val (pf2,fn2,tmp) = trav p conj2 rl
       val (pf1,fn1,rew) = trav p conj1 tmp
       val pf = (op @) o (pf1##pf2) o CONJ_PAIR
   in (pf,(fn rf => MK_COMB ((AP_TERM AND (fn1 rf)),(fn2 rf))),rew)
   end handle HOL_ERR _ 
         => if (p tm handle HOL_ERR _ => false)
            then ((fn th => [th]),(fn rf => REFL tm),(ASSUME tm :: rl))
            else ((fn th => []),(fn rf => rf tm),rl)
in
fun UNWIND_ONCE_CONV p tm =
   let val (pf,fnn,eqns) = trav p tm []
       val rconv = ONCE_DEPTH_CONV
                      (REWRITES_CONV 
                           (Rewrite.add_rewrites Rewrite.empty_rewrites eqns))
       val th = fnn rconv
       val {lhs,rhs} = dest_eq (concl th)
       val lth = ASSUME lhs
       and rth = ASSUME rhs
       val imp1 = DISCH lhs (EQ_MP (itlist PROVE_HYP (pf lth) th) lth)
       and imp2 = DISCH rhs (EQ_MP (SYM (itlist PROVE_HYP (pf rth) th)) rth)
   in IMP_ANTISYM_RULE imp1 imp2
   end 
   handle HOL_ERR _ => raise UNWIND_ERR "UNWIND_ONCE_CONV" ""
end;

(*---------------------------------------------------------------------------*)
(* UNWIND_CONV : (term -> bool) -> conv                                      *)
(*                                                                           *)
(* Unwind device behaviour using line equations eqnx selected by p until no  *)
(* change.                                                                   *)
(*                                                                           *)
(* WARNING -- MAY LOOP!                                                      *)
(*                                                                           *)
(*    UNWIND_CONV p                                                          *)
(*                                                                           *)
(*    "t1 /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn"                        *)
(*    ---->                                                                  *)
(*    |- t1  /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn =                    *)
(*       t1' /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn'                     *)
(*                                                                           *)
(* where ti' (for 1 <= i <= n) is ti rewritten with the equations            *)
(* eqni (1 <= i <= m). These equations are the conjuncts for which the       *)
(* predicate p is true. The ti terms are the conjuncts for which p is false. *)
(* The rewriting is repeated until no changes take place.                    *)
(*---------------------------------------------------------------------------*)

fun UNWIND_CONV p tm =
   let val th = UNWIND_ONCE_CONV p tm
   in if lhs (concl th) = rhs (concl th)
      then th
      else TRANS th (UNWIND_CONV p (rhs (concl th)))
   end;

(*---------------------------------------------------------------------------*)
(* UNWIND_ALL_BUT_CONV : string list -> conv                                 *)
(*                                                                           *)
(* Unwind all lines (except those in the list l) as much as possible.        *)
(*                                                                           *)
(* WARNING -- MAY LOOP!                                                      *)
(*                                                                           *)
(*    UNWIND_ALL_BUT_CONV l                                                  *)
(*                                                                           *)
(*    "t1 /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn"                        *)
(*    ---->                                                                  *)
(*    |- t1  /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn =                    *)
(*       t1' /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn'                     *)
(*                                                                           *)
(* where ti' (for 1 <= i <= n) is ti rewritten with the equations            *)
(* eqni (1 <= i <= m). These equations are those conjuncts with line name not*)
(* in l (and which are equations).                                           *)
(*---------------------------------------------------------------------------*)

fun UNWIND_ALL_BUT_CONV l tm =
   let val line_names = set_diff (mapfilter line_name (strip_conj tm)) l
       fun p line tm = (line_name tm) = line
       fun itfn line th = TRANS th (UNWIND_CONV (p line) (rhs (concl th)))
   in itlist itfn line_names (REFL tm)
   end 
   handle HOL_ERR _ => raise UNWIND_ERR"UNWIND_ALL_BUT_CONV" "";

(*---------------------------------------------------------------------------*)
(* UNWIND_AUTO_CONV : conv                                                   *)
(*                                                                           *)
(*    "?l1 ... lm. t1 /\ ... /\ tn"                                          *)
(*    ---->                                                                  *)
(*    |- (?l1 ... lm. t1 /\ ... /\ tn) = (?l1 ... lm. t1' /\ ... /\ tn')     *)
(*                                                                           *)
(* where tj' is tj rewritten with equations selected from the ti's. The      *)
(* function decides which equations to use by performing a loop analysis on  *)
(* the graph representing the dependencies of the lines. By this means the   *)
(* term can be unwound as much as possible without the risk of looping. The  *)
(* user is left to deal with the recursive equations.                        *)
(*                                                                           *)
(* The algorithms used for loop analysis in this function are extremely      *)
(* naive. There is also some inefficiency in that certain lines may be used  *)
(* in unwinding even though they do not appear in any RHS's.                 *)
(*                                                                           *)
(* Amongst other things, the internal function "graph_of_term' rearranges the*)
(* lines in the graph representation so that external lines come first. This *)
(* gives them priority over the internal lines when the function is          *)
(* determining where to "break" loops. This is useful because the line chosen*)
(* as the break will be left in the resultant term, and further manipulations*)
(* by the user should be easier if it is an external rather than an internal *)
(* line that is left in.                                                     *)
(*---------------------------------------------------------------------------*)

local fun FAIL s = UNWIND_ERR "UNWIND_AUTO_CONV" s
fun is_set [] = true
  | is_set (a::rst) = (not (mem a rst)) andalso is_set rst
fun pdeq tm = let val {lhs,rhs} = dest_eq tm in (lhs,rhs) end
fun graph_of_term tm =
   let val (internals,t) = strip_exists tm
       val (lines,rhs_free_vars) =
          unzip (mapfilter (((assert is_var o fst o strip_comb)##free_vars) o
                            pdeq o snd o strip_forall)
                           (strip_conj t))
   in if (is_set lines)
      then let val graph = zip lines (map (intersect lines) rhs_free_vars)
               val (intern,extern) = partition (fn p => mem (fst p) internals) 
                                               graph
           in  extern@intern
           end
      else raise FAIL "graph_of_term"
   end

fun loops_containing_line line graph chain =
   let val successors = map fst 
             (filter (fn (_,predecs) => mem (Lib.trye hd chain) predecs) graph)
       val not_in_chain = filter (fn line => not (mem line chain)) successors
       val new_chains = map (fn line => line::chain) not_in_chain
       (* flatten(map ...) should be an itlist *)
       val new_loops = flatten (map (loops_containing_line line graph) 
                                    new_chains)
   in if (mem line successors)
      then (rev chain)::new_loops
      else new_loops
   end

fun chop_at x (l as (a::rst)) =
      if (a = x) then ([],l)
      else let val (l1,l2) = chop_at x rst
           in (a::l1, l2)
           end
  | chop_at _ _ = raise FAIL "chop_at";

(* before has infix status in SML/NJ, so changed to befre *)
fun equal_loops lp1 lp2 =
   if (set_eq lp1 lp2)
   then let val (befre,rest) = chop_at (Lib.trye hd lp1) lp2
        in lp1 = (rest @ befre)
        end
   else false

fun distinct_loops [] = []
  | distinct_loops (h::t) =
       if (exists (fn lp => equal_loops lp h) t)
       then distinct_loops t
       else h ::(distinct_loops t)

(* Could use an itlist here again and collapse the maps. *)
fun loops_of_graph graph =
  distinct_loops
    (flatten
      (map (fn line => loops_containing_line line graph [line]) 
           (map fst graph)))

fun list_after x (l as (h::t)) =
     if (x = h) then t else list_after x t
  | list_after _ _ = raise UNWIND_ERR "list_after" "";

fun rev_front_of l n front =
  if (n < 0) 
  then raise FAIL "rev_front_of"
  else if (n = 0) 
       then front
       else rev_front_of (Lib.trye tl l) (n - 1) (Lib.trye hd l ::front)

fun next_comb_at_this_level source n (h::t) =
      let val l = list_after h source
      in   if (length l > n)
           then (rev_front_of l (n + 1) []) @ t
           else next_comb_at_this_level source (n + 1) t
      end
  | next_comb_at_this_level _ _ _ = raise FAIL "next_comb_at_this_level"

fun next_combination source previous =
  next_comb_at_this_level source 0 previous
  handle HOL_ERR _ => rev_front_of source ((length previous) + 1) []

fun break_all_loops lps lines previous =
   let val comb = next_combination lines previous
   in  if (all (fn lp => not (null (intersect lp comb))) lps)
       then comb
       else break_all_loops lps lines comb
   end

fun breaks internals graph =
   let val loops = loops_of_graph graph
       val single_el_loops = filter (fn l => length l = 1) loops
       val single_breaks = flatten single_el_loops
       val loops' = filter (null o (intersect single_breaks)) loops
       val only_internal_loops =
              filter (fn l => null (set_diff l internals)) loops'
       val only_internal_lines = end_itlist union only_internal_loops 
                                 handle HOL_ERR _ => []
       val internal_breaks =
              break_all_loops only_internal_loops only_internal_lines [] 
              handle HOL_ERR _ => []
       val external_loops = filter (null o (intersect internal_breaks)) loops'
       val external_lines =
              set_diff (end_itlist union external_loops handle HOL_ERR _ => [])
                       internals
       val external_breaks =
              break_all_loops external_loops external_lines [] 
              handle HOL_ERR _ => []
   in single_breaks @ (rev internal_breaks) @ (rev external_breaks)
   end


fun conv dependencies used t =
   let val vars = map fst (filter ((fn l => null (set_diff l used)) o snd)
                          dependencies)
   in if (null vars)
   then REFL t
   else ((UNWIND_ONCE_CONV (fn tm => mem (line_var tm) vars)) THENC
         (conv (filter (fn p => not (mem (fst p) vars)) dependencies)
               (used @ vars))) t
   end
in
fun UNWIND_AUTO_CONV tm =
   let val internals = fst (strip_exists tm)
       and graph = graph_of_term tm
       val brks = breaks internals graph
       val dependencies = map (I ## (fn l => set_diff l brks)) 
                              (filter (fn p => not (mem (fst p) brks)) graph)
   in DEPTH_EXISTS_CONV (conv dependencies []) tm
   end handle HOL_ERR _ => raise UNWIND_ERR "UNWIND_AUTO_CONV" ""
end;

(*---------------------------------------------------------------------------*)
(* UNWIND_ALL_BUT_RIGHT_RULE : string list -> thm -> thm                     *)
(*                                                                           *)
(* Unwind all lines (except those in the list l) as much as possible.        *)
(*                                                                           *)
(* WARNING -- MAY LOOP!                                                      *)
(*                                                                           *)
(*    UNWIND_ALL_BUT_RIGHT_RULE l                                            *)
(*                                                                           *)
(*     A |- !z1 ... zr.                                                      *)
(*           t =                                                             *)
(*           (?l1 ... lp. t1  /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn)    *)
(*    ---------------------------------------------------------------------  *)
(*     A |- !z1 ... zr.                                                      *)
(*           t =                                                             *)
(*           (?l1 ... lp. t1' /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn')   *)
(*                                                                           *)
(* where ti' (for 1 <= i <= n) is ti rewritten with the equations            *)
(* eqni (1 <= i <= m). These equations are those conjuncts with line name not*)
(* in l (and which are equations).                                           *)
(*---------------------------------------------------------------------------*)

fun UNWIND_ALL_BUT_RIGHT_RULE l th =
  CONV_RULE
    (DEPTH_FORALL_CONV (RAND_CONV (DEPTH_EXISTS_CONV (UNWIND_ALL_BUT_CONV l))))
    th
  handle HOL_ERR _ => raise UNWIND_ERR "UNWIND_ALL_BUT_RIGHT_RULE" "";

(*---------------------------------------------------------------------------*)
(* UNWIND_AUTO_RIGHT_RULE : thm -> thm                                       *)
(*                                                                           *)
(*     A |- !z1 ... zr. t = ?l1 ... lm. t1  /\ ... /\ tn                     *)
(*    ----------------------------------------------------                   *)
(*     A |- !z1 ... zr. t = ?l1 ... lm. t1' /\ ... /\ tn'                    *)
(*                                                                           *)
(* where tj' is tj rewritten with equations selected from the ti's. The      *)
(* function decides which equations to use by performing a loop analysis on  *)
(* the graph representing the dependencies of the lines. By this means the   *)
(* equations can be unwound as much as possible without the risk of looping. *)
(* The user is left to deal with the recursive equations.                    *)
(*---------------------------------------------------------------------------*)

fun UNWIND_AUTO_RIGHT_RULE th =
   CONV_RULE (DEPTH_FORALL_CONV (RAND_CONV UNWIND_AUTO_CONV)) th
   handle HOL_ERR _ => raise UNWIND_ERR "UNWIND_AUTO_RIGHT_RULE" "";

(*===========================================================================*)
(* Rules for pruning                                                         *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(* EXISTS_DEL1_CONV : conv                                                   *)
(*                                                                           *)
(*    "?x. t"                                                                *)
(*    ---->                                                                  *)
(*    |- (?x. t) = t                                                         *)
(*                                                                           *)
(* provided x is not free in t.                                              *)
(*                                                                           *)
(* Deletes one existential quantifier.                                       *)
(*---------------------------------------------------------------------------*)

fun EXISTS_DEL1_CONV tm =
   let val {Bvar,Body} = dest_exists tm
       val th = ASSUME Body
       val th1 = DISCH tm (CHOOSE (Bvar, ASSUME tm) th)
       and th2 = DISCH Body (EXISTS (tm,Bvar) th)
   in IMP_ANTISYM_RULE th1 th2
   end handle HOL_ERR _ => raise UNWIND_ERR"EXISTS_DEL1_CONV" "";

(*---------------------------------------------------------------------------*)
(* EXISTS_DEL_CONV : conv                                                    *)
(*                                                                           *)
(*    "?x1 ... xn. t"                                                        *)
(*    ---->                                                                  *)
(*    |- (?x1 ... xn. t) = t                                                 *)
(*                                                                           *)
(* provided x1,...,xn are not free in t.                                     *)
(*                                                                           *)
(* Deletes existential quantifiers. The conversion fails if any of the x's   *)
(* appear free in t. It does not perform a partial deletion; for example, if *)
(* x1 and x2 do not appear free in t but x3 does, the function will fail; it *)
(* will not return |- ?x1 ... xn. t = ?x3 ... xn. t.                         *)
(*---------------------------------------------------------------------------*)

local fun terms_and_vars tm =
       let val {Bvar,Body} = dest_exists tm
       in (tm,Bvar)::terms_and_vars Body
       end handle HOL_ERR _ => []
in
fun EXISTS_DEL_CONV tm =
  let val txs = terms_and_vars tm
      val t = #Body (dest_exists (fst (last txs))) handle _ => tm
      val th = ASSUME t
      val th1 = DISCH tm (itlist (fn (tm,x) => CHOOSE (x, ASSUME tm)) txs th)
      and th2 = DISCH t (itlist EXISTS txs th)
  in IMP_ANTISYM_RULE th1 th2
  end 
  handle HOL_ERR _ => raise UNWIND_ERR "EXISTS_DEL_CONV" ""
end;

(*---------------------------------------------------------------------------*)
(* EXISTS_EQN_CONV : conv                                                    *)
(*                                                                           *)
(*    "?l. !y1 ... ym. l x1 ... xn = t"                                      *)
(*    ---->                                                                  *)
(*    |- (?l. !y1 ... ym. l x1 ... xn = t) = T                               *)
(*                                                                           *)
(* provided l is not free in t. Both m and n may be zero.                    *)
(*---------------------------------------------------------------------------*)

fun EXISTS_EQN_CONV t =
   let val {Bvar = l,Body} = dest_exists t
       val (ys,A) = strip_forall Body
       val {lhs,rhs} = dest_eq A
       val xs = snd ((assert (curry (op =) l) ## I) (strip_comb lhs))
       val t3 = list_mk_abs (xs,rhs)
       val th1 = GENL ys (RIGHT_CONV_RULE LIST_BETA_CONV 
                                          (REFL (list_mk_comb (t3,xs))))
   in EQT_INTRO (EXISTS (t,t3) th1)
   end handle HOL_ERR _ => raise UNWIND_ERR "EXISTS_EQN_CONV" "";

(*---------------------------------------------------------------------------*)
(* PRUNE_ONCE_CONV : conv                                                    *)
(*                                                                           *)
(* Prunes one hidden variable.                                               *)
(*                                                                           *)
(*    "?l. t1 /\ ... /\ ti /\ eq /\ t(i+1) /\ ... /\ tp"                     *)
(*    ---->                                                                  *)
(*    |- (?l. t1 /\ ... /\ ti /\ eq /\ t(i+1) /\ ... /\ tp) =                *)
(*       (t1 /\ ... /\ ti /\ t(i+1) /\ ... /\ tp)                            *)
(*                                                                           *)
(* where eq has the form "!y1 ... ym. l x1 ... xn = b" and l does not appear *)
(* free in the ti's or in b. The conversion works if eq is not present,      *)
(* i.e. if l is not free in any of the conjuncts, but does not work if l     *)
(* appears free in more than one of the conjuncts. Each of m, n and p may be *)
(* zero.                                                                     *)
(*---------------------------------------------------------------------------*)

local val AP_AND = AP_TERM AND
in
fun PRUNE_ONCE_CONV tm =
 let val {Bvar,Body} = dest_exists tm
  in 
    case (partition (free_in Bvar) (strip_conj Body))
     of ([], _) => EXISTS_DEL1_CONV tm
      | ([eq],l2) =>
          let val th1 = EXISTS_EQN_CONV (mk_exists {Bvar=Bvar, Body=eq})
          in
            if (null l2) then th1
            else let val conj = list_mk_conj l2
                     val th2 = AP_THM (AP_AND th1) conj
                     val th3 = EXISTS_EQ Bvar 
                                 (CONJUNCTS_CONV
                                   (Body,mk_conj{conj1=eq, conj2=conj}))
                     val th4 = RIGHT_CONV_RULE EXISTS_AND_CONV th3
                 in 
                  TRANS th4 (TRANS th2 (CONJUNCT1 (SPEC conj AND_CLAUSES)))
                 end
          end
      | _ => raise UNWIND_ERR "" ""
 end handle HOL_ERR _ => raise UNWIND_ERR "PRUNE_ONCE_CONV" ""
end;

(*---------------------------------------------------------------------------*)
(* PRUNE_ONE_CONV : string -> conv                                           *)
(*                                                                           *)
(* Prunes one hidden variable.                                               *)
(*                                                                           *)
(*    PRUNE_ONE_CONV "lj"                                                    *)
(*                                                                           *)
(*    "?l1 ... lj ... lr. t1 /\ ... /\ ti /\ eq /\ t(i+1) /\ ... /\ tp"      *)
(*    ---->                                                                  *)
(*    |- (?l1 ... lj ... lr. t1 /\ ... /\ ti /\ eq /\ t(i+1) /\ ... /\ tp) = *)
(*       (?l1 ... l(j-1) l(j+1) ... lr.                                      *)
(*         t1 /\ ... /\ ti /\ t(i+1) /\ ... /\ tp)                           *)
(*                                                                           *)
(* where eq has the form "!y1 ... ym. lj x1 ... xn = b" and lj does not      *)
(* appear free in the ti's or in b. The conversion works if eq is not        *)
(* present, i.e. if lj is not free in any of the conjuncts, but does not work*)
(* if lj appears free in more than one of the conjuncts. Each of m, n and p  *)
(* may be zero.                                                              *)
(*                                                                           *)
(* If there is more than one line with the specified name (but with different*)
(* types), the one that appears outermost in the existential quantifications *)
(* is pruned.                                                                *)
(*---------------------------------------------------------------------------*)

fun PRUNE_ONE_CONV v tm =
   let val {Bvar,Body} = dest_exists tm
   in if (#Name (dest_var Bvar) = v)
      then if (is_exists Body)
           then (SWAP_EXISTS_CONV THENC
                 RAND_CONV (ABS_CONV (PRUNE_ONE_CONV v))) tm
           else PRUNE_ONCE_CONV tm
      else RAND_CONV (ABS_CONV (PRUNE_ONE_CONV v)) tm
   end handle HOL_ERR _ => raise UNWIND_ERR "PRUNE_ONE_CONV" "";

(*---------------------------------------------------------------------------*)
(* PRUNE_SOME_CONV : string list -> conv                                     *)
(*                                                                           *)
(* Prunes several hidden variables.                                          *)
(*                                                                           *)
(*    PRUNE_SOME_CONV ["li1";...;"lik"]                                      *)
(*                                                                           *)
(*    "?l1 ... lr. t1 /\ ... /\ eqni1 /\ ... /\ eqnik /\ ... /\ tp"          *)
(*    ---->                                                                  *)
(*    |- (?l1 ... lr. t1 /\ ... /\ eqni1 /\ ... /\ eqnik /\ ... /\ tp) =     *)
(*       (?li(k+1) ... lir. t1 /\ ... /\ tp)                                 *)
(*                                                                           *)
(* where for 1 <= j <= k, each eqnij has the form:                           *)
(*                                                                           *)
(*    "!y1 ... ym. lij x1 ... xn = b"                                        *)
(*                                                                           *)
(* and lij does not appear free in any of the other conjuncts or in b.       *)
(* The li's are related by the equation:                                     *)
(*                                                                           *)
(*    {li1,...,lik} u {li(k+1),...,lir} = {l1,...,lr}                        *)
(*                                                                           *)
(* The conversion works if one or more of the eqnij's are not present,       *)
(* i.e. if lij is not free in any of the conjuncts, but does not work if lij *)
(* appears free in more than one of the conjuncts. p may be zero, that is,   *)
(* all the conjuncts may be eqnij's. In this case the body of the result will*)
(* be T (true). Also, for each eqnij, m and n may be zero.                   *)
(*                                                                           *)
(* If there is more than one line with a specified name (but with different  *)
(* types), the one that appears outermost in the existential quantifications *)
(* is pruned. If such a line name is mentioned twice in the list, the two    *)
(* outermost occurrences of lines with that name will be pruned, and so on.  *)
(*---------------------------------------------------------------------------*)

fun PRUNE_SOME_CONV [] tm = REFL tm
  | PRUNE_SOME_CONV (h::t) tm = 
     (PRUNE_SOME_CONV t THENC PRUNE_ONE_CONV h) tm
     handle HOL_ERR _ => raise UNWIND_ERR "PRUNE_SOME_CONV" "";

(*---------------------------------------------------------------------------*)
(* PRUNE_CONV : conv                                                         *)
(*                                                                           *)
(* Prunes all hidden variables.                                              *)
(*                                                                           *)
(*    "?l1 ... lr. t1 /\ ... /\ eqn1 /\ ... /\ eqnr /\ ... /\ tp"            *)
(*    ---->                                                                  *)
(*    |- (?l1 ... lr. t1 /\ ... /\ eqn1 /\ ... /\ eqnr /\ ... /\ tp) =       *)
(*       (t1 /\ ... /\ tp)                                                   *)
(*                                                                           *)
(* where each eqni has the form "!y1 ... ym. li x1 ... xn = b" and li does   *)
(* not appear free in any of the other conjuncts or in b. The conversion     *)
(* works if one or more of the eqni's are not present, i.e. if li is not free*)
(* in any of the conjuncts, but does not work if li appears free in more than*)
(* one of the conjuncts. p may be zero, that is, all the conjuncts may be    *)
(* eqni's. In this case the result will be simply T (true). Also, for each   *)
(* eqni, m and n may be zero.                                                *)
(*---------------------------------------------------------------------------*)

fun PRUNE_CONV tm =
   if (is_exists tm)
   then (RAND_CONV (ABS_CONV PRUNE_CONV) THENC PRUNE_ONCE_CONV) tm
        handle HOL_ERR _ => raise UNWIND_ERR "PRUNE_CONV" ""
  else REFL tm;

(*---------------------------------------------------------------------------*)
(* PRUNE_SOME_RIGHT_RULE : string list -> thm -> thm                         *)
(*                                                                           *)
(* Prunes several hidden variables.                                          *)
(*                                                                           *)
(*    PRUNE_SOME_RIGHT_RULE ["li1";...;"lik"]                                *)
(*                                                                           *)
(*     A |- !z1 ... zr.                                                      *)
(*           t = ?l1 ... lr. t1 /\ ... /\ eqni1 /\ ... /\ eqnik /\ ... /\ tp *)
(*    -----------------------------------------------------------------------*)
(*     A |- !z1 ... zr. t = ?li(k+1) ... lir. t1 /\ ... /\ tp                *)
(*                                                                           *)
(* where for 1 <= j <= k, each eqnij has the form:                           *)
(*                                                                           *)
(*    "!y1 ... ym. lij x1 ... xn = b"                                        *)
(*                                                                           *)
(* and lij does not appear free in any of the other conjuncts or in b.       *)
(* The li's are related by the equation:                                     *)
(*                                                                           *)
(*    {li1,...,lik} u {li(k+1),...,lir} = {l1,...,lr}                        *)
(*                                                                           *)
(* The rule works if one or more of the eqnij's are not present, i.e. if lij *)
(* is not free in any of the conjuncts, but does not work if lij appears free*)
(* in more than one of the conjuncts. p may be zero, that is, all the        *)
(* conjuncts may be eqnij's. In this case the conjunction will be transformed*)
(* to T (true). Also, for each eqnij, m and n may be zero.                   *)
(*                                                                           *)
(* If there is more than one line with a specified name (but with different  *)
(* types), the one that appears outermost in the existential quantifications *)
(* is pruned. If such a line name is mentioned twice in the list, the two    *)
(* outermost occurrences of lines with that name will be pruned, and so on.  *)
(*---------------------------------------------------------------------------*)

fun PRUNE_SOME_RIGHT_RULE vs th =
   CONV_RULE (DEPTH_FORALL_CONV (RAND_CONV (PRUNE_SOME_CONV vs))) th
   handle HOL_ERR _ => raise UNWIND_ERR "PRUNE_SOME_RIGHT_RULE" "";

(*---------------------------------------------------------------------------*)
(* PRUNE_RIGHT_RULE : thm -> thm                                             *)
(*                                                                           *)
(* Prunes all hidden variables.                                              *)
(*                                                                           *)
(*     A |- !z1 ... zr.                                                      *)
(*           t = ?l1 ... lr. t1 /\ ... /\ eqn1 /\ ... /\ eqnr /\ ... /\ tp   *)
(*    ---------------------------------------------------------------------  *)
(*     A |- !z1 ... zr. t = t1 /\ ... /\ tp                                  *)
(*                                                                           *)
(* where each eqni has the form "!y1 ... ym. li x1 ... xn = b" and li does   *)
(* not appear free in any of the other conjuncts or in b. The rule works if  *)
(* one or more of the eqni's are not present, i.e. if li is not free in any  *)
(* of the conjuncts, but does not work if li appears free in more than one of*)
(* the conjuncts. p may be zero, that is, all the conjuncts may be eqni's. In*)
(* this case the result will be simply T (true). Also, for each eqni, m and n*)
(* may be zero.                                                              *)
(*---------------------------------------------------------------------------*)

fun PRUNE_RIGHT_RULE th =
   CONV_RULE (DEPTH_FORALL_CONV (RAND_CONV PRUNE_CONV)) th
   handle HOL_ERR _ => raise UNWIND_ERR "PRUNE_RIGHT_RULE" "";

(*===========================================================================*)
(* Functions which do unfolding, unwinding and pruning                       *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* EXPAND_ALL_BUT_CONV : string list -> thm list -> conv                     *)
(*                                                                           *)
(* Unfold with the theorems thl, then unwind all lines (except those in the  *)
(* list) as much as possible and prune the unwound lines.                    *)
(*                                                                           *)
(* WARNING -- MAY LOOP!                                                      *)
(*                                                                           *)
(*    EXPAND_ALL_BUT_CONV ["li(k+1)";...;"lim"] thl                          *)
(*                                                                           *)
(*    "?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn"              *)
(*    ---->                                                                  *)
(*    B |- (?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn) =       *)
(*         (?li(k+1) ... lim. t1' /\ ... /\ tn')                             *)
(*                                                                           *)
(* where each ti' is the result of rewriting ti with the theorems in thl. The*)
(* set of assumptions B is the union of the instantiated assumptions of the  *)
(* theorems used for rewriting. If none of the rewrites are applicable to a  *)
(* conjunct, it is unchanged. Those conjuncts that after rewriting are       *)
(* equations for the lines li1,...,lik (they are denoted by ui1,...,uik) are *)
(* used to unwind and the lines li1,...,lik are then pruned. If this is not  *)
(* possible the function will fail. It is also possible for the function to  *)
(* attempt unwinding indefinitely (to loop).                                 *)
(*                                                                           *)
(* The li's are related by the equation:                                     *)
(*                                                                           *)
(*    {li1,...,lik} u {li(k+1),...,lim} = {l1,...,lm}                        *)
(*---------------------------------------------------------------------------*)
fun EXPAND_ALL_BUT_CONV l thl tm =
   (DEPTH_EXISTS_CONV ((UNFOLD_CONV thl) THENC (UNWIND_ALL_BUT_CONV l)) THENC
    (fn tm => let val var_names = map (#Name o dest_var) (fst(strip_exists tm))
              in PRUNE_SOME_CONV (subtract var_names l) tm
              end))
   tm handle HOL_ERR _ => raise UNWIND_ERR"EXPAND_ALL_BUT_CONV" "";

(*---------------------------------------------------------------------------*)
(* EXPAND_AUTO_CONV : thm list -> conv                                       *)
(*                                                                           *)
(* Unfold with the theorems thl, then unwind as much as possible and prune   *)
(* the unwound lines.                                                        *)
(*                                                                           *)
(*    EXPAND_AUTO_CONV thl                                                   *)
(*                                                                           *)
(*    "?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn"              *)
(*    ---->                                                                  *)
(*    B |- (?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn) =       *)
(*         (?li(k+1) ... lim. t1' /\ ... /\ tn')                             *)
(*                                                                           *)
(* where each ti' is the result of rewriting ti with the theorems in thl. The*)
(* set of assumptions B is the union of the instantiated assumptions of the  *)
(* theorems used for rewriting. If none of the rewrites are applicable to a  *)
(* conjunct, it is unchanged. After rewriting the function decides which of  *)
(* the resulting terms to use for unwinding by performing a loop analysis on *)
(* the graph representing the dependencies of the lines.                     *)
(*                                                                           *)
(* Suppose the function decides to unwind the lines li1,...,lik using the    *)
(* terms ui1',...,uik' respectively. Then after unwinding the lines          *)
(* li1,...,lik are pruned (provided they have been eliminated from the RHS's *)
(* of the conjuncts that are equations, and from the whole of any other      *)
(* conjuncts) resulting in the elimination of ui1',...,uik'.                 *)
(*                                                                           *)
(* The li's are related by the equation:                                     *)
(*                                                                           *)
(*    {li1,...,lik} u {li(k+1),...,lim} = {l1,...,lm}                        *)
(*                                                                           *)
(* The loop analysis allows the term to be unwound as much as possible       *)
(* without the risk of looping. The user is left to deal with the recursive  *)
(* equations.                                                                *)
(*---------------------------------------------------------------------------*)

fun EXPAND_AUTO_CONV thl tm =
   (DEPTH_EXISTS_CONV (UNFOLD_CONV thl) THENC
    UNWIND_AUTO_CONV THENC
      (fn tm =>
        let val (internals,conjs) = (I ## strip_conj) (strip_exists tm)
            val vars = flatten (map 
                        (free_vars o (fn tm => (rhs tm) handle HOL_ERR _ => tm)
                                   o snd o strip_forall) conjs)
        in PRUNE_SOME_CONV(map (#Name o dest_var) (set_diff internals vars)) tm
        end))
   tm
   handle HOL_ERR _ => raise UNWIND_ERR "EXPAND_AUTO_CONV" "";

(*---------------------------------------------------------------------------*)
(* EXPAND_ALL_BUT_RIGHT_RULE : string list -> thm list -> thm -> thm         *)
(*                                                                           *)
(* Unfold with the theorems thl, then unwind all lines (except those in the  *)
(* list) as much as possible and prune the unwound lines.                    *)
(*                                                                           *)
(* WARNING -- MAY LOOP!                                                      *)
(*                                                                           *)
(*    EXPAND_ALL_BUT_RIGHT_RULE ["li(k+1)";...;"lim"] thl                    *)
(*                                                                           *)
(*         A |- !z1 ... zr.                                                  *)
(*               t = ?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn *)
(*    -----------------------------------------------------------------------*)
(*     B u A |- !z1 ... zr. t = ?li(k+1) ... lim. t1' /\ ... /\ tn'          *)
(*                                                                           *)
(* where each ti' is the result of rewriting ti with the theorems in thl. The*)
(* set of assumptions B is the union of the instantiated assumptions of the  *)
(* theorems used for rewriting. If none of the rewrites are applicable to a  *)
(* conjunct, it is unchanged. Those conjuncts that after rewriting are       *)
(* equations for the lines li1,...,lik (they are denoted by ui1,...,uik) are *)
(* used to unwind and the lines li1,...,lik are then pruned. If this is not  *)
(* possible the function will fail. It is also possible for the function to  *)
(* attempt unwinding indefinitely (to loop).                                 *)
(*                                                                           *)
(* The li's are related by the equation:                                     *)
(*                                                                           *)
(*    {li1,...,lik} u {li(k+1),...,lim} = {l1,...,lm}                        *)
(*---------------------------------------------------------------------------*)

fun EXPAND_ALL_BUT_RIGHT_RULE l thl th =
   CONV_RULE (DEPTH_FORALL_CONV (RAND_CONV (EXPAND_ALL_BUT_CONV l thl))) th
   handle HOL_ERR _ => raise UNWIND_ERR "EXPAND_ALL_BUT_RIGHT_RULE" "";

(*---------------------------------------------------------------------------*)
(* EXPAND_AUTO_RIGHT_RULE : thm list -> thm -> thm                           *)
(*                                                                           *)
(* Unfold with the theorems thl, then unwind as much as possible and prune   *)
(* the unwound lines.                                                        *)
(*                                                                           *)
(*    EXPAND_AUTO_RIGHT_RULE thl                                             *)
(*                                                                           *)
(*         A |- !z1 ... zr.                                                  *)
(*               t = ?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn *)
(*    -----------------------------------------------------------------------*)
(*     B u A |- !z1 ... zr. t = ?li(k+1) ... lim. t1' /\ ... /\ tn'          *)
(*                                                                           *)
(* where each ti' is the result of rewriting ti with the theorems in thl. The*)
(* set of assumptions B is the union of the instantiated assumptions of the  *)
(* theorems used for rewriting. If none of the rewrites are applicable to a  *)
(* conjunct, it is unchanged. After rewriting the function decides which of  *)
(* the resulting terms to use for unwinding by performing a loop analysis on *)
(* the graph representing the dependencies of the lines.                     *)
(*                                                                           *)
(* Suppose the function decides to unwind the lines li1,...,lik using the    *)
(* terms ui1',...,uik' respectively. Then after unwinding the lines          *)
(* li1,...,lik are pruned (provided they have been eliminated from the RHS's *)
(* of the conjuncts that are equations, and from the whole of any other      *)
(* conjuncts) resulting in the elimination of ui1',...,uik'.                 *)
(*                                                                           *)
(* The li's are related by the equation:                                     *)
(*                                                                           *)
(*    {li1,...,lik} u {li(k+1),...,lim} = {l1,...,lm}                        *)
(*                                                                           *)
(* The loop analysis allows the term to be unwound as much as possible       *)
(* without the risk of looping. The user is left to deal with the recursive  *)
(* equations.                                                                *)
(*---------------------------------------------------------------------------*)

fun EXPAND_AUTO_RIGHT_RULE thl th =
   CONV_RULE (DEPTH_FORALL_CONV (RAND_CONV (EXPAND_AUTO_CONV thl))) th
   handle HOL_ERR _ => raise UNWIND_ERR "EXPAND_AUTO_RIGHT_RULE" "";


end; (* unwindLib *)
