(* ===================================================================== *)
(* FILE          : rewrite.sml                                           *)
(* DESCRIPTION   : The rewriting routines. Translated from hol88.        *)
(*                                                                       *)
(* AUTHOR        : (c) Larry Paulson, University of Cambridge, for hol88 *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* REVISED       : November 1994, to encapsulate the type of rewrite     *)
(*                 rules. (KLS)                                          *)
(* ===================================================================== *)


structure Ho_rewrite :> Ho_rewrite =
struct

open HolKernel Hol_pp Drule 
     Tactic Tactical Conv liteLib 
     Psyntax Ho_match Ho_net;

type term = Term.term
type thm = Thm.thm
type conv = Abbrev.conv
type tactic = Abbrev.tactic;


infixr 3 ##
infix THEN  ORELSE

fun WRAP_ERR p = STRUCT_WRAP "Ho_rewrite" p;

(*-----------------------------------------------------------------------------
 * Split a theorem into a list of theorems suitable for rewriting:
 *
 *   1. Specialize all variables (SPEC_ALL).
 *
 *   2. Then do the following:
 *
 *        |- t1 /\ t2     -->    [|- t1 ; |- t2]
 *
 *   3. Then |- t --> |- t = T and |- ~t --> |- t = F
 *
 *---------------------------------------------------------------------------*)
fun mk_rewrites th =
  let val th = SPEC_ALL th
      val t = concl th 
  in 
  if (is_eq t) then [th]
  else if (is_conj t)
       then (op @ o (mk_rewrites##mk_rewrites) o CONJ_PAIR) th
       else if (is_neg t)
            then [EQF_INTRO th]
            else [EQT_INTRO th]
  end
  handle e as (HOL_ERR _) => WRAP_ERR("mk_rewrites",e);


(* An abstract datatype of rewrite rule sets. *)

datatype rewrites = RW of {thms :thm list,  net :conv net}
fun dest_rewrites(RW{thms, ...}) = thms
val empty_rewrites = RW{thms = [],  net = empty_net}

 (* Create a conversion from some rewrites *)
fun REWRITES_CONV (RW{net,...}) tm = FIRST_CONV (lookup tm net) tm;

fun REWR_CONV th =
   let val instth = PART_MATCH lhs th handle e as (HOL_ERR _) 
           => WRAP_ERR("REWR_CONV: bad theorem argument: "
                       ^term_to_string (concl th),e)
   in fn tm => 
       let val eqn = instth tm
	   val l = lhs(concl eqn)
       in if (l = tm) then eqn 
	  else TRANS (ALPHA tm l) eqn
       end 
   handle HOL_ERR _ => failwith "REWR_CONV: lhs of theorem doesn't match term"
   end;

fun add_rewrites (RW{thms,net}) thl =
    RW{thms = thms@thl,
       net = itlist enter
       (map (fn th => (free_varsl (hyp th),lhs(concl th), REWR_CONV th))
	(itlist (append o mk_rewrites) thl [])) net}

val implicit = ref empty_rewrites;
fun implicit_rewrites() = #thms ((fn (RW x) => x) (!implicit));
fun set_implicit_rewrites thl =
    implicit := add_rewrites empty_rewrites thl;
fun add_implicit_rewrites thl = 
    implicit := add_rewrites (!implicit) thl;

(* =====================================================================*)
(* Main rewriting conversion                         			*)
(* =====================================================================*)

fun GEN_REWRITE_CONV' rw_func rws thl = 
   rw_func (REWRITES_CONV (add_rewrites rws thl));

(* ---------------------------------------------------------------------*)
(* Rewriting conversions.                        			*)
(* ---------------------------------------------------------------------*)

val PURE_REWRITE_CONV = GEN_REWRITE_CONV' TOP_DEPTH_CONV empty_rewrites
and 
PURE_ONCE_REWRITE_CONV = GEN_REWRITE_CONV' ONCE_DEPTH_CONV empty_rewrites;
 
fun REWRITE_CONV thl = GEN_REWRITE_CONV' TOP_DEPTH_CONV 
                                        (!implicit) thl
and ONCE_REWRITE_CONV thl = GEN_REWRITE_CONV' ONCE_DEPTH_CONV 
                                        (!implicit) thl;

(* Main rewriting rule *)
fun GEN_REWRITE_RULE f rws = CONV_RULE o GEN_REWRITE_CONV' f rws;

val PURE_REWRITE_RULE = GEN_REWRITE_RULE TOP_DEPTH_CONV empty_rewrites
and 
PURE_ONCE_REWRITE_RULE = GEN_REWRITE_RULE ONCE_DEPTH_CONV empty_rewrites;

fun REWRITE_RULE thl = GEN_REWRITE_RULE TOP_DEPTH_CONV 
                                        (!implicit) thl
and ONCE_REWRITE_RULE thl = GEN_REWRITE_RULE ONCE_DEPTH_CONV
                                             (!implicit) thl;

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

fun GEN_REWRITE_TAC f rws = CONV_TAC o GEN_REWRITE_CONV' f rws;

val PURE_REWRITE_TAC = GEN_REWRITE_TAC TOP_DEPTH_CONV empty_rewrites
and 
PURE_ONCE_REWRITE_TAC = GEN_REWRITE_TAC ONCE_DEPTH_CONV empty_rewrites;

fun REWRITE_TAC thl = GEN_REWRITE_TAC TOP_DEPTH_CONV (!implicit)
                                      thl
and ONCE_REWRITE_TAC thl = 
    GEN_REWRITE_TAC ONCE_DEPTH_CONV (!implicit) thl;


(* Rewrite a goal with the help of its assumptions *)

fun PURE_ASM_REWRITE_TAC thl  = 
   ASSUM_LIST (fn asl => PURE_REWRITE_TAC (asl @ thl))
and ASM_REWRITE_TAC thl       = 
   ASSUM_LIST (fn asl => REWRITE_TAC (asl @ thl))
and PURE_ONCE_ASM_REWRITE_TAC thl  = 
   ASSUM_LIST (fn asl => PURE_ONCE_REWRITE_TAC (asl @ thl))
and ONCE_ASM_REWRITE_TAC thl  = 
   ASSUM_LIST (fn asl => ONCE_REWRITE_TAC (asl @ thl));

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
    ASSUM_LIST 
          (fn asl => PURE_REWRITE_TAC ((filter (f o concl) asl)@thl))
and FILTER_ASM_REWRITE_TAC f thl =
    ASSUM_LIST
          (fn asl => REWRITE_TAC ((filter (f o concl) asl) @ thl))
and FILTER_PURE_ONCE_ASM_REWRITE_TAC f thl =
    ASSUM_LIST
         (fn asl => PURE_ONCE_REWRITE_TAC ((filter (f o concl) asl) @ thl))
and FILTER_ONCE_ASM_REWRITE_TAC f thl =
    ASSUM_LIST 
          (fn asl => ONCE_REWRITE_TAC ((filter (f o concl) asl) @ thl));


(***************************************************************************
 * SUBST_MATCH (|-u=v) th   searches for an instance of u in
 * (the conclusion of) th and then substitutes the corresponding
 * instance of v. Much faster than rewriting.
 ****************************************************************************)
local
(* Search a sub-term of t matching u *)
exception FIND_MATCH_ERR;
fun find_match u =
   let fun find_mt t =
          match_term [] u t
          handle HOL_ERR _ =>
          find_mt(rator t)
          handle HOL_ERR _ =>
          find_mt(rand t)
          handle HOL_ERR _ =>
          find_mt(body t)
          handle HOL_ERR _ =>
          raise FIND_MATCH_ERR
   in
   find_mt
   end
in
fun SUBST_MATCH eqth th =
   let val (tm_inst,ty_inst) = find_match (lhs(concl eqth)) (concl th)
   in SUBS [INST tm_inst (INST_TYPE ty_inst eqth)] th
   end
   handle FIND_MATCH_ERR => failwith "SUBST_MATCH"
end;

fun GEN_REWRITE_CONV rw_func thl = 
   rw_func (REWRITES_CONV (add_rewrites empty_rewrites thl));

fun GEN_REWRITE_RULE rw_func thl = 
    CONV_RULE (GEN_REWRITE_CONV rw_func thl);

fun GEN_REWRITE_TAC rw_func thl = 
    CONV_TAC (GEN_REWRITE_CONV rw_func thl);


val TAUT =
   let fun RTAUT_TAC (asl,w) =
      let fun ok t = 
	  type_of t = Type.bool andalso can (find_term is_var) t andalso 
	  free_in t w 
      in (REPEAT(W((fn x => REWRITE_TAC[] THEN x) o BOOL_CASES_TAC o
		 Lib.trye hd o sort free_in o (find_terms ok) o snd)) THEN
	  REWRITE_TAC []) (asl,w) 
      end
      val TAUT_TAC = REPEAT(GEN_TAC ORELSE CONJ_TAC) THEN RTAUT_TAC 
  in fn tm => prove(tm,TAUT_TAC)
  end;

fun TAUT_TAC (asms,gl) = 
    let val th = TAUT gl in ([],fn _ => th) end;

val TAUT_CONV = EQT_INTRO o TAUT;

val TAUT_PROVE = TAUT;

end (* struct *)


