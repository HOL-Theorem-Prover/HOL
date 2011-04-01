(* ===================================================================== *)
(* FILE          : Rank.sml                                              *)
(* DESCRIPTION   : HOL ranks (of kinds).                                 *)
(*                                                                       *)
(* AUTHOR        : (c) Peter Vincent Homeier                             *)
(* DATE          : February 1, 2011                                      *)
(* ===================================================================== *)

structure Rank :> Rank =
struct

(*
In *scratch*, type
(hol-set-executable sml-executable)
and type Ctrl-j.

loadPath := "/usr/local/hol/hol/sigobj" :: !loadPath;
loadPath := "/usr/local/hol/hol/src/0" :: !loadPath;
app load ["Feedback","Lib","KernelTypes","Lexis"];
*)

open Feedback Lib KernelTypes;   infix |-> ## :=:;

type rank = KernelTypes.rank

val ERR = mk_HOL_ERR "Rank";
val WARN = HOL_WARNING "Rank";


(*---------------------------------------------------------------------------
       Rank operators
 ---------------------------------------------------------------------------*)

val rho = 0

fun check s f r = if r < 0 then raise mk_HOL_ERR s f "rank is negative"
                  else r

val rcheck = check "Rank"

fun suc rk = rk + 1

fun max (r, s) = Int.max(r,s)

fun ge_rk (r, s) = (r >= s)

local val chk = rcheck "promote"
in
fun promote rkS = (chk rkS; fn rk => chk rk + rkS)
end

(* ----------------------------------------------------------------------
    A total ordering on ranks.
    Rk
   ---------------------------------------------------------------------- *)

fun rank_compare (r1, r2) = Int.compare(r1,r2);

fun rank_size _ = 1

val rank_to_string = Int.toString

(*---------------------------------------------------------------------------*
 *    Matching ranks, determining the necessary delta to make proper.        *
 *                                                                           *
 * raw_match_rank compares a series of pattern ranks versus target ranks;    *
 * computes the minimum necessary delta to promote the pattern so that it    *
 * includes the target, and combines this with the previous substitution     *
 * (by taking the maximum of both) to produce a rank substitution that will  *
 * ensure that all the patterns include the targets, if possible.            *
 * If any of the patterns are constant ranks, they may fail to include their *
 * targets, or if the target is a variable rank, the rank matching will fail.*
 * The identity rank substitution, which does not change a rank, is 0.       *
 *---------------------------------------------------------------------------*)

local
  fun RERR s = raise ERR "raw_match_rank" s
  fun chk rk = rcheck "raw_match_rank" rk
  fun match pat_rk tar_rk rkS =
    if chk pat_rk >= chk tar_rk then rkS
    else Int.max(rkS, tar_rk - pat_rk)
  fun matchfixed pat_rk tar_rk rkS =
    if chk pat_rk + rkS >= chk tar_rk then rkS
    else RERR "cannot raise fixed rank"
in
fun raw_match_rank false pat tar rk = match pat tar (chk rk)
  | raw_match_rank true  pat tar rk = matchfixed pat tar (chk rk)
  | raw_match_rank _ any other thing = RERR "invalid rank substitution"
end

fun match_rank pat_rk tar_rk =
    raw_match_rank false pat_rk tar_rk rho
    handle (HOL_ERR{message=m,origin_function=f,origin_structure=s}) =>
    raise HOL_ERR{message=m,origin_function="match_rank",origin_structure="Rank"}
                               

end (* Rank *)
