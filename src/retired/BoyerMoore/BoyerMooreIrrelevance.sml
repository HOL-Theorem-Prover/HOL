(****************************************************************************)
(* FILE          : irrelevance.sml                                          *)
(* DESCRIPTION   : Eliminating irrelevance.                                 *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 25th June 1991                                           *)
(*                                                                          *)
(* TRANSLATED BY : R.J.Boulton                                              *)
(* DATE          : 4th October 1995                                         *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 5th October 1995                                         *)
(****************************************************************************)

structure BoyerMooreIrrelevance =
struct

local

open HolKernel Parse basicHol90Lib Psyntax BoyerMooreSupport;

fun failwith function =
   raise HOL_ERR {origin_structure = "BoyerMooreIrrelevance",
                  origin_function = function,
                  message = ""};

in

(*--------------------------------------------------------------------------*)
(* partition_literals : (term * int) list -> (term * int) list list         *)
(*                                                                          *)
(* Function to partition a list of numbered terms into lists that share     *)
(* variables. A term in one partition has no variables in common with any   *)
(* term in one of the other partitions. Within a partition the terms are    *)
(* ordered as they were in the input list.                                  *)
(*                                                                          *)
(* The function begins by putting every term in a separate partition. It    *)
(* then tries to merge the first partition with one of the others. Two      *)
(* partitions can be merged if they have at least one variable in common.   *)
(* If a merge can be done, the process is repeated for the new head of the  *)
(* partition list. This continues until a merge cannot take place (this     *)
(* causes a failure in `merge_partitions' due to an attempt to split an     *)
(* empty list into a head and a tail). When this happens, the head          *)
(* partition is separated from the others because it cannot have any        *)
(* variables in common with the others. The entire process is repeated for  *)
(* the remaining partitions. This goes on until the list is exhausted.      *)
(*                                                                          *)
(* When as much merging as possible has been done, the terms within each    *)
(* partition are sorted based on the number they are paired with.           *)
(*--------------------------------------------------------------------------*)

fun partition_literals tmnl =
   let fun merge_partitions partition [] = failwith "merge_partitions"
         | merge_partitions partition (h::t) =
          if (null (intersect
                       ((mk_set o flatten o map (free_vars o fst)) partition)
                       ((mk_set o flatten o map (free_vars o fst)) h)))
          then h::(merge_partitions partition t)
          else (partition @ h)::t
       and repeated_merge [] = []
         | repeated_merge (partition::partitions) =
          repeated_merge (merge_partitions partition partitions)
          handle HOL_ERR _ => partition::(repeated_merge partitions)
   in  map sort_on_snd (repeated_merge (map (fn tmn => [tmn]) tmnl))
   end;

(*--------------------------------------------------------------------------*)
(* contains_recursive_fun : term list -> bool                               *)
(*                                                                          *)
(* Determines whether a list of terms (a partition) mentions a recursive    *)
(* function. A constant that does not have a definition in the environment  *)
(* is taken to be non-recursive.                                            *)
(*--------------------------------------------------------------------------*)

fun contains_recursive_fun tml =
   let val consts = flatten (mapfilter (find_terms is_const) tml)
       val names = mk_set (map (#1 o dest_const) consts)
   in  exists
          (fn name => (not ((#1 o #2 o BoyerMooreEnvironment.get_def) name = 0)
                       handle HOL_ERR _ => false)) names
   end;

(*--------------------------------------------------------------------------*)
(* is_singleton_rec_app : term list -> bool                                 *)
(*                                                                          *)
(* Returns true if the list of terms (a partition) given as argument is a   *)
(* single literal whose atom is of the form (f v1 ... vn) where f is a      *)
(* recursive function and the vi are distinct variables.                    *)
(*--------------------------------------------------------------------------*)

fun is_singleton_rec_app [tm] =
   (let val tm' = if (is_neg tm) then (rand tm) else tm
        val (f,args) = strip_comb tm'
        val name = #Name (Rsyntax.dest_const f)
    in  (not ((#1 o #2 o BoyerMooreEnvironment.get_def) name = 0)) andalso
        (forall is_var args) andalso
        (distinct args)
    end
    handle HOL_ERR _ => false)
  | is_singleton_rec_app _ = false;

(*--------------------------------------------------------------------------*)
(* merge_numbered_lists :                                                   *)
(*    ('a * int) list -> ('a * int) list -> ('a * int) list                 *)
(*                                                                          *)
(* Merges two numbered lists. The lists must be in increasing order by the  *)
(* number, and no number may appear more than once in a list or appear in   *)
(* both lists. The result will then be ordered by the numbers.              *)
(*--------------------------------------------------------------------------*)

fun merge_numbered_lists [] xnl2 = xnl2
  | merge_numbered_lists xnl1 [] = xnl1
  | merge_numbered_lists
       (xnl1 as (xn1 as (_,n1:int))::t1) (xnl2 as (xn2 as (_,n2))::t2) =
   if (n1 < n2)
   then xn1::(merge_numbered_lists t1 xnl2)
   else xn2::(merge_numbered_lists xnl1 t2);

(*--------------------------------------------------------------------------*)
(* find_irrelevant_literals :                                               *)
(*    term -> ((term * int) list * (term * int) list)                       *)
(*                                                                          *)
(* Given a clause, this function produces two lists of term/integer pairs.  *)
(* The first list is of literals deemed to be irrelevant. The second list   *)
(* is the remaining literals. The number with each literal is its position  *)
(* in the original clause.                                                  *)
(*--------------------------------------------------------------------------*)

fun find_irrelevant_literals tm =
   let fun can_be_falsified tmnl =
          let val tml = map fst tmnl
          in  (not (contains_recursive_fun tml)) orelse
              (is_singleton_rec_app tml)
          end
       val tmnll = partition_literals (number_list (disj_list tm))
       val (irrels,rels) = partition can_be_falsified tmnll
   in  (itlist merge_numbered_lists irrels [],
        itlist merge_numbered_lists rels [])
   end;

(*--------------------------------------------------------------------------*)
(* DISJ_UNDISCH : thm -> thm                                                *)
(*                                                                          *)
(*     A |- x \/ y                                                          *)
(*    -------------  DISJ_UNDISCH                                           *)
(*     A, ~x |- y                                                           *)
(*--------------------------------------------------------------------------*)

fun DISJ_UNDISCH th =
   UNDISCH (DISJ_IMP th) handle HOL_ERR _ => failwith "DISJ_UNDISCH";

(*--------------------------------------------------------------------------*)
(* DISJ_DISCH : term -> thm -> thm                                          *)
(*                                                                          *)
(*     A, ~x |- y                                                           *)
(*    -------------  DISJ_DISCH (--`x:bool`--)                              *)
(*     A |- x \/ y                                                          *)
(*--------------------------------------------------------------------------*)

fun DISJ_DISCH tm th =
   CONV_RULE
      (RATOR_CONV (RAND_CONV (REWR_CONV BoyerMooreClausalForm.NOT_NOT_NORM)))
      (IMP_ELIM (DISCH (mk_neg tm) th))
   handle HOL_ERR _ => failwith "DISJ_DISCH";

(*--------------------------------------------------------------------------*)
(* BUILD_DISJ : ((term * int) list * (term * int) list) -> thm -> thm       *)
(*                                                                          *)
(* Function to build a disjunctive theorem from another theorem that has as *)
(* its conclusion a subset of the disjuncts. The first argument is a pair   *)
(* of term/integer lists. Each list contains literals (disjuncts) and their *)
(* position within the required result. The first list is of those          *)
(* disjuncts not in the theorem. The second list is of disjuncts in the     *)
(* theorem. Both lists are assumed to be ordered by their numbers           *)
(* (increasing order).                                                      *)
(*                                                                          *)
(* Example:                                                                 *)
(*                                                                          *)
(*    BUILD_DISJ ([(--`x2`--,2),(--`x5`--,5),(--`x6`--,6)],                 *)
(*                [(--`x1`--,1),(--`x3`--,3),(--`x4`--,4)])                 *)
(*               |- x1 \/ x3 \/ x4                                          *)
(*                                                                          *)
(* The required result is:                                                  *)
(*                                                                          *)
(*    |- x1 \/ x2 \/ x3 \/ x4 \/ x5 \/ x6                                   *)
(*                                                                          *)
(* The first step is to undischarge all the disjuncts except for the last:  *)
(*                                                                          *)
(*    ~x1, ~x3 |- x4                                                        *)
(*                                                                          *)
(* The disjuncts not in the theorem, and which are to come after x4, are    *)
(* now `added' to the theorem. (Note that we have to undischarge all but    *)
(* the last disjunct in order to get the correct associativity of OR (\/)   *)
(* at this stage):                                                          *)
(*                                                                          *)
(*    ~x1, ~x3 |- x4 \/ x5 \/ x6                                            *)
(*                                                                          *)
(* We now repeatedly either discharge one of the assumptions, or add a      *)
(* disjunct from the `outs' list, according to the values of the numbers    *)
(* associated with the terms:                                               *)
(*                                                                          *)
(*    ~x1 |- x3 \/ x4 \/ x5 \/ x6                                           *)
(*                                                                          *)
(*    ~x1 |- x2 \/ x3 \/ x4 \/ x5 \/ x6                                     *)
(*                                                                          *)
(*    |- x1 \/ x2 \/ x3 \/ x4 \/ x5 \/ x6                                   *)
(*--------------------------------------------------------------------------*)

fun BUILD_DISJ (outs,ins) inth =
   let fun rebuild [] [] th = th
         | rebuild (rev_out::rev_outs) [] th =
          rebuild rev_outs [] (DISJ2 (fst rev_out) th)
         | rebuild [] (rev_in::rev_ins) th =
          rebuild [] rev_ins (DISJ_DISCH (fst rev_in) th)
         | rebuild (rev_outs as outh::outt) (rev_ins as inh::int) th =
          if (snd inh > snd outh)
          then rebuild rev_outs int (DISJ_DISCH (#1 inh) th)
          else rebuild outt rev_ins (DISJ2 (#1 outh) th)
       val last_in = snd (last ins)
       val (under_outs,over_outs) =
          partition (fn (_,n:int) => n > last_in) outs
       val over_ins = butlast ins
       val th1 = funpow (length over_ins) DISJ_UNDISCH inth
       val th2 =
          DISJ1 th1 (list_mk_disj (map #1 under_outs)) handle HOL_ERR _ => th1
   in  rebuild (rev over_outs) (rev over_ins) th2
   end
   handle HOL_ERR _ => failwith "BUILD_DISJ";

(*--------------------------------------------------------------------------*)
(* irrelevance_heuristic : (term * bool) -> ((term * bool) list * proof)    *)
(*                                                                          *)
(* Heuristic for eliminating irrelevant literals. The function splits the   *)
(* literals into two sets: those that are irrelevant and those that are     *)
(* not. If there are no relevant terms left, the heuristic fails in a way   *)
(* that indicates the conjecture cannot be proved. If there are no          *)
(* irrelevant literals, the function fails indicating that it cannot do     *)
(* anything with the clause. In all other circumstances the function        *)
(* returns a new clause consisting of only the relevant literals, together  *)
(* with a proof of the original clause from this new clause.                *)
(*--------------------------------------------------------------------------*)

fun irrelevance_heuristic (tm,(ind:bool)) =
   let val (outs,ins) = find_irrelevant_literals tm
   in  if (null ins)
       then raise BoyerMooreWaterfall.CannotProve
       else if (null outs)
            then failwith "irrelevance_heuristic"
            else let val tm' = list_mk_disj (map #1 ins)
                     and proof = BUILD_DISJ (outs,ins)
                 in  ([(tm',ind)],
                      BoyerMooreWaterfall.apply_proof (proof o hd) [tm'])
                 end
   end;

end;

end; (* BoyerMooreIrrelevance *)
