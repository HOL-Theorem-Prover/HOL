(* ===================================================================== *)
(* FILE          : Rewrite.sml                                           *)
(* DESCRIPTION   : Basic rewriting routines. Translated from hol88.      *)
(*                                                                       *)
(* AUTHOR        : (c) Larry Paulson, University of Cambridge, for hol88 *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* REVISED       : November 1994, to encapsulate the type of rewrite     *)
(*                 rules. (KLS)                                          *)
(* ===================================================================== *)


structure Rewrite :> Rewrite =
struct

open HolKernel boolTheory boolSyntax Drule BoundedRewrites Abbrev;

val ERR = mk_HOL_ERR "Rewrite";

type pred = term -> bool

infix 3 ##

(*---------------------------------------------------------------------------*)
(* Datatype for controlling the application of individual rewrite rules      *)
(*---------------------------------------------------------------------------*)

datatype control = UNBOUNDED | BOUNDED of int ref


(*---------------------------------------------------------------------------*
 * Split a theorem into a list of theorems suitable for rewriting:           *
 *                                                                           *
 *   1. Specialize all variables (SPEC_ALL).                                 *
 *                                                                           *
 *   2. Then do the following:                                               *
 *                                                                           *
 *         |- t1 /\ t2 -->    [|- t1 ; |- t2]                                *
 *                                                                           *
 *   3. Then     |- t  --> |- t = T                                          *
 *       and     |- ~t --> |- t = F                                          *
 *                                                                           *
 *---------------------------------------------------------------------------*)


fun decompose tag th =
 let val th = SPEC_ALL th
     val t = concl th
 in
   if is_eq t   then [(th,tag)] else
   if is_conj t then (op@ o (decompose tag##decompose tag) o CONJ_PAIR) th else
   if is_neg t  then [(EQF_INTRO th,tag)]
                else [(EQT_INTRO th,tag)]
  end
  handle e => raise wrap_exn "Rewrite" "mk_rewrites.decompose" e;

fun local_mk_rewrites th =
 case total DEST_BOUNDED th
  of NONE => decompose UNBOUNDED th
   | SOME(th',n) => decompose (BOUNDED (ref n)) th';

val mk_rewrites = map fst o local_mk_rewrites;

(*---------------------------------------------------------------------------*)
(* Support for examining some aspects of the work of the rewriter            *)
(*---------------------------------------------------------------------------*)

val monitoring = ref false;

val _ = register_btrace ("Rewrite", monitoring) ;

(*---------------------------------------------------------------------------*)
(* Abstract datatype of rewrite rule sets.                                   *)
(*---------------------------------------------------------------------------*)

abstype rewrites = RW of {thms : thm list, net : conv Net.net}
with
 fun dest_rewrites(RW{thms, ...}) = thms
 fun net_of(RW{net,...})          = net
 val empty_rewrites = RW{thms = [], net= Net.empty}
 val implicit = ref empty_rewrites;
 fun implicit_rewrites() = !implicit
 fun set_implicit_rewrites rws = (implicit := rws);

fun add_rewrites (RW{thms,net}) thl =
 let val rewrites = itlist (append o local_mk_rewrites) thl []
     fun appconv (c,UNBOUNDED) tm     = c tm
       | appconv (c,BOUNDED(ref 0)) _ = failwith "exceeded bound"
       | appconv (c,BOUNDED r) tm     = c tm before Portable.dec r
 in
   RW{thms = thms@thl,
       net = itlist Net.insert
                (map (fn (th,tag) =>
                        (boolSyntax.lhs(concl th),
                         (appconv (Conv.REWR_CONV th,tag)))) rewrites)
                net}
 end

end (* abstype *)

(*---------------------------------------------------------------------------
     Create a conversion from some rewrites
 ---------------------------------------------------------------------------*)

fun REWRITES_CONV rws tm =
 let val net = net_of rws
 in if !monitoring
    then case mapfilter (fn f => f tm) (Net.match tm net)
          of []   => Conv.NO_CONV tm
           | [x]  => (HOL_MESG (String.concat
                       ["Rewrite:\n", Parse.thm_to_string x]) ; x)
           | h::t => (HOL_MESG (String.concat
                    ["Multiple rewrites possible (first taken):\n",
                  String.concatWith ",\n" (map Parse.thm_to_string (h::t))]); h)
    else Conv.FIRST_CONV (Net.match tm net) tm
 end;


(* Derived manipulations *)

fun add_implicit_rewrites thl =
    set_implicit_rewrites (add_rewrites (implicit_rewrites()) thl);

val bool_rewrites =
  add_rewrites empty_rewrites
     [REFL_CLAUSE,  EQ_CLAUSES,  NOT_CLAUSES,  AND_CLAUSES,
      OR_CLAUSES,   IMP_CLAUSES, COND_CLAUSES, FORALL_SIMP,
      EXISTS_SIMP,  ABS_SIMP];

val _ = set_implicit_rewrites bool_rewrites;

(* =====================================================================*)
(* Main rewriting conversion                         			*)
(* =====================================================================*)

fun GEN_REWRITE_CONV (rw_func:conv->conv) rws thl =
   rw_func (REWRITES_CONV (add_rewrites rws thl));

(* ---------------------------------------------------------------------*)
(* Rewriting conversions.                        			*)
(* ---------------------------------------------------------------------*)

val PURE_REWRITE_CONV = GEN_REWRITE_CONV Conv.TOP_DEPTH_CONV empty_rewrites
and
PURE_ONCE_REWRITE_CONV = GEN_REWRITE_CONV Conv.ONCE_DEPTH_CONV empty_rewrites;

fun REWRITE_CONV thl = GEN_REWRITE_CONV Conv.TOP_DEPTH_CONV
                                        (implicit_rewrites()) thl
and ONCE_REWRITE_CONV thl = GEN_REWRITE_CONV Conv.ONCE_DEPTH_CONV
                                        (implicit_rewrites()) thl;

(* Main rewriting rule *)
fun GEN_REWRITE_RULE f rws = Conv.CONV_RULE o GEN_REWRITE_CONV f rws;

val PURE_REWRITE_RULE = GEN_REWRITE_RULE Conv.TOP_DEPTH_CONV empty_rewrites
and
PURE_ONCE_REWRITE_RULE = GEN_REWRITE_RULE Conv.ONCE_DEPTH_CONV empty_rewrites;

fun REWRITE_RULE thl = GEN_REWRITE_RULE Conv.TOP_DEPTH_CONV
                                        (implicit_rewrites()) thl
and ONCE_REWRITE_RULE thl = GEN_REWRITE_RULE Conv.ONCE_DEPTH_CONV
                                             (implicit_rewrites()) thl;

(* Rewrite a theorem with the help of its assumptions *)

fun PURE_ASM_REWRITE_RULE thl th =
   PURE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
and
PURE_ONCE_ASM_REWRITE_RULE thl th =
   PURE_ONCE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
and
ASM_REWRITE_RULE thl th =
   REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
and
ONCE_ASM_REWRITE_RULE thl th =
   ONCE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th;


(* Main rewriting tactic *)

fun GEN_REWRITE_TAC f rws = Tactic.CONV_TAC o GEN_REWRITE_CONV f rws;

val PURE_REWRITE_TAC = GEN_REWRITE_TAC Conv.TOP_DEPTH_CONV empty_rewrites
and
PURE_ONCE_REWRITE_TAC = GEN_REWRITE_TAC Conv.ONCE_DEPTH_CONV empty_rewrites;

fun REWRITE_TAC thl = GEN_REWRITE_TAC Conv.TOP_DEPTH_CONV (implicit_rewrites())
                                      thl
and ONCE_REWRITE_TAC thl =
    GEN_REWRITE_TAC Conv.ONCE_DEPTH_CONV (implicit_rewrites()) thl;


(* Rewrite a goal with the help of its assumptions *)

fun PURE_ASM_REWRITE_TAC thl :tactic =
   Tactical.ASSUM_LIST (fn asl => PURE_REWRITE_TAC (asl @ thl))
and ASM_REWRITE_TAC thl :tactic      =
   Tactical.ASSUM_LIST (fn asl => REWRITE_TAC (asl @ thl))
and PURE_ONCE_ASM_REWRITE_TAC thl :tactic =
   Tactical.ASSUM_LIST (fn asl => PURE_ONCE_REWRITE_TAC (asl @ thl))
and ONCE_ASM_REWRITE_TAC thl :tactic      =
   Tactical.ASSUM_LIST (fn asl => ONCE_REWRITE_TAC (asl @ thl));

(* Rewriting using equations that satisfy a predicate  *)
fun FILTER_PURE_ASM_REWRITE_RULE f thl th =
    PURE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th
and FILTER_ASM_REWRITE_RULE f thl th =
    REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th
and FILTER_PURE_ONCE_ASM_REWRITE_RULE f thl th =
    PURE_ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th
and FILTER_ONCE_ASM_REWRITE_RULE f thl th =
    ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th;;

fun FILTER_PURE_ASM_REWRITE_TAC f thl =
    Tactical.ASSUM_LIST
          (fn asl => PURE_REWRITE_TAC ((filter (f o concl) asl)@thl))
and FILTER_ASM_REWRITE_TAC f thl =
    Tactical.ASSUM_LIST
          (fn asl => REWRITE_TAC ((filter (f o concl) asl) @ thl))
and FILTER_PURE_ONCE_ASM_REWRITE_TAC f thl =
    Tactical.ASSUM_LIST
         (fn asl => PURE_ONCE_REWRITE_TAC ((filter (f o concl) asl) @ thl))
and FILTER_ONCE_ASM_REWRITE_TAC f thl =
    Tactical.ASSUM_LIST
          (fn asl => ONCE_REWRITE_TAC ((filter (f o concl) asl) @ thl));


(*---------------------------------------------------------------------------*
 * SUBST_MATCH (|-u=v) th   searches for an instance of u in                 *
 * (the conclusion of) th and then substitutes the corresponding             *
 * instance of v.                                                            *
 *---------------------------------------------------------------------------*)

fun SUBST_MATCH eqth th =
  let val matchr = match_term (lhs(concl eqth))
      fun find_match t =
             matchr t              handle HOL_ERR _ =>
             find_match(rator t)   handle HOL_ERR _ =>
             find_match(rand t)    handle HOL_ERR _ =>
             find_match(body t)
      val (tm_inst,ty_inst) = find_match (concl th)
  in
     SUBS [INST tm_inst (INST_TYPE ty_inst eqth)] th
  end
  handle HOL_ERR _ => raise ERR "SUBST_MATCH" "";



fun pp_rewrites ppstrm rws =
    let open Portable
        val {add_string,add_break,begin_block,end_block,add_newline,...} =
               with_ppstream ppstrm
        val pp_thm = Parse.pp_thm ppstrm
        val thms = dest_rewrites rws
        val thms' = flatten (map mk_rewrites thms)
        val how_many = length thms'
    in
       begin_block CONSISTENT 0;
       if (how_many = 0)
       then (add_string "<empty rule set>")
       else ( begin_block INCONSISTENT 0;
              pr_list pp_thm (fn () => add_string";")
                             (fn () => add_break(2,0))
                             thms';
              end_block());
       add_newline();
       add_string("Number of rewrite rules = "^Lib.int_to_string how_many);
       add_newline();
       end_block()
    end;

end (* Rewrite *)
