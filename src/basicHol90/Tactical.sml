(* ===================================================================== *)
(* FILE          : tactical.sml                                          *)
(* DESCRIPTION   : Functions that glue tactics together. From LCF, and   *)
(*                 added to through the years. Translated from hol88.    *)
(*                                                                       *)
(* AUTHORS       : (c) University of Edinburgh and                       *)
(*                     University of Cambridge, for hol88                *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* Updated       : 1997 (to treat validity checking as an oracle) (KLS)  *)
(* ===================================================================== *)


structure Tactical :> Tactical =
struct

open HolKernel Drule;

type tactic = Abbrev.tactic;
type thm_tactic = Abbrev.thm_tactic;
type thm_tactical = Abbrev.thm_tactical;
type goal = Abbrev.goal;


fun TACTICAL_ERR function message =
         HOL_ERR{origin_structure = "Tactical",
                 origin_function = function,
                 message = message}


(*---------------------------------------------------------------------------
 * TAC_PROOF (g,tac) uses tac to prove the goal g
 *---------------------------------------------------------------------------*)
fun TAC_PROOF (g,tac) =
   case (tac g)
     of ([],p) => p []
      |     _  => raise TACTICAL_ERR "TAC_PROOF" "unsolved goals";


fun prove(t,tac) = TAC_PROOF(([],t), tac);

fun store_thm (name, tm, tac) =
  Theory.save_thm (name, prove (tm, tac)) handle e =>
    (print ("Failed to prove theorem "^name^"\n");
     Raise e)


fun mapshape [] _ _ =  []
  | mapshape (n1::nums) (f1::funcs) args =
     let val (f1_args,args') = split_after n1 args
     in
      f1 f1_args :: mapshape nums funcs args'
     end;

infix THEN THENL ORELSE;

(*---------------------------------------------------------------------------
 * fun (tac1:tactic) THEN (tac2:tactic) : tactic = fn g =>
 *    let val (gl,p) = tac1 g
 *        val (gll,pl) = unzip(map tac2 gl)
 *    in
 *    (flatten gll, (p o mapshape(map length gll)pl))
 *    end;
 *---------------------------------------------------------------------------*)

fun tac1 THEN tac2 = fn g =>
   let val (gl,vf) = tac1 g
   in case (itlist (fn goal => fn (G,V,lengths) =>
               case (tac2 goal)
               of ([],vfun) => let val th = vfun []
                               in (G, (fn [] => th)::V, 0::lengths)
                               end
                | (goals,vfun) => (goals@G, vfun::V, length goals::lengths))
            gl ([],[],[]))
      of ([],V,_) => ([], let val th = vf (map (fn f => f[]) V)
                          in fn [] => th end)
       | (G,V,lengths) => (G, (vf o mapshape lengths V))
   end
   handle HOL_ERR{origin_structure,origin_function,message} => raise
   TACTICAL_ERR "THEN" (origin_structure^"."^origin_function^": "^message);


(*---------------------------------------------------------------------------
 * fun (tac1:tactic) THENL (tac2l : tactic list) : tactic = fn g =>
 *    let val (gl,p) = tac1 g
 *        val tac2gl = zip tac2l gl
 *        val (gll,pl) = unzip (map (fn (tac2,g) => tac2 g) tac2gl)
 *    in
 *    (flatten gll, p o mapshape(map length gll) pl)
 *    end
 *    handle HOL_ERR{origin_structure,origin_function,message} =>
 *        raise TACTICAL_ERR{function = "THENL",
 * 			  message = (origin_structure^"."^origin_function^": "
 * 				     ^message)};
 *---------------------------------------------------------------------------*)
fun (tac1:tactic) THENL (tacl:tactic list) :tactic = fn g =>
 let val (gl,vf) = tac1 g
     val (G,V,lengths) = itlist2 (fn goal => fn tac => fn (G,V,lengths) =>
           case (tac goal)
           of ([],vfun) => let val th = vfun []
                           in (G, (fn [] => th)::V, 0::lengths) end
            | (goals,vfun) => (goals@G, vfun::V, length goals::lengths))
          gl tacl ([],[],[])
 in case G
   of [] => ([], let val th = vf (map (fn f => f[]) V) in fn [] => th end)
    | _  => (G, (vf o mapshape lengths V))
 end
 handle HOL_ERR{origin_structure,origin_function,message} => raise
 TACTICAL_ERR "THENL" (origin_structure^"."^origin_function^": " ^message);

fun (tac1 ORELSE tac2) g = tac1 g handle HOL_ERR _ => tac2 g;

(*---------------------------------------------------------------------------
 * Fail with the given token.  Useful in tactic programs to check that a
 * tactic produces no subgoals.  Write
 *
 *      TAC  THEN  FAIL_TAC "TAC did not solve the goal"
 *---------------------------------------------------------------------------*)
fun FAIL_TAC tok (g:goal) = raise TACTICAL_ERR "FAIL_TAC" tok;

(*---------------------------------------------------------------------------
 * Tactic that succeeds on no goals;  identity for ORELSE.
 *---------------------------------------------------------------------------*)
fun NO_TAC g = FAIL_TAC "NO_TAC" g;

(*---------------------------------------------------------------------------
 * Tactic that succeeds on all goals;  identity for THEN
 *---------------------------------------------------------------------------*)
val ALL_TAC:tactic = fn (g:goal) => ([g],hd);

fun TRY tac = tac ORELSE ALL_TAC;

(*---------------------------------------------------------------------------
 * The abstraction around g is essential to avoid looping, due to applicative
 * order semantics.
 *---------------------------------------------------------------------------*)
fun REPEAT tac g = ((tac THEN REPEAT tac) ORELSE ALL_TAC) g ;

(*---------------------------------------------------------------------------
 * Check whether a theorem achieves a goal, using no extra assumptions.
 *---------------------------------------------------------------------------*)
fun achieves th ((asl,w):goal) =
    (Term.aconv (concl th) w) andalso
    (all (fn h => (exists (Term.aconv h)) asl) (hyp th));


(*---------------------------------------------------------------------------
 * Check the goal list and proof returned by a tactic.
 *    At top-level, it is convenient to type "chktac it;"
 *
 *    MJCG 17/1/89 for HOL88: mk_thm used instead of mk_f This
 *    introduces slight insecurity into the system, but since chktak
 *    is assignable this insecurity can be removed by doing:
 *
 *    chktak := fn (gl,prf) => raise TACTICAL_ERR{function = "chktac",
 *                                                message  = ""};
 *
 * KLS 1997. Change to tagged inference scheme means that validity checking
 * is regarded as an oracle invocation (mk_tac_thm).
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * Check whether a prospective (goal list, proof) pair is valid.
 *  MJCG 17/1/89 for HOL88: "falsity.asl" changed to "asl".
 *---------------------------------------------------------------------------*)
fun check_valid g (gl,prf) = achieves (prf (map mk_tac_thm gl)) g;

(*---------------------------------------------------------------------------
 * Tactical to make any tactic valid.
 *    "VALID tac" is the same as "tac", except it will fail in the cases where
 *    "tac" returns an invalid proof.
 *
 *    VALID uses mk_thm; the proof could assign its arguments to
 *    global theorem variables, making them accessible outside.
 *
 *    This kind of insecurity is very unlikely to lead to accidental proof of
 *    false theorems; see comment preceding check_valid for how to remove
 *    insecurity.
 *
 *    Previously mk_fthm was used by check_valid instead of mk_thm (see
 *    hol-drule.ml), but this lead to problems with tactics (like resolution)
 *    that checked for "F". A possible solution would be to use another
 *    constant that was defined equal to F.
 *---------------------------------------------------------------------------*)
fun VALID (tac:tactic) :tactic = fn (g:goal) =>
   let val tac_res = tac g
   in if check_valid g tac_res then tac_res
      else raise TACTICAL_ERR "VALID" "Invalid tactic"
   end;


(*---------------------------------------------------------------------------
 * Provide a function (tactic) with the current assumption list.
 *---------------------------------------------------------------------------*)
fun ASSUM_LIST aslfun (g as (asl,_)) = aslfun (map ASSUME asl) g;

(*---------------------------------------------------------------------------
 * Pop the first assumption and give it to a function (tactic)
 *---------------------------------------------------------------------------*)
fun POP_ASSUM thfun (a::asl, w) = thfun (ASSUME a) (asl,w)
  | POP_ASSUM   _   ([], _) = raise TACTICAL_ERR "POP_ASSUM" "no assum";

(*---------------------------------------------------------------------------
 * Pop off the entire assumption list and give it to a function (tactic)
 *---------------------------------------------------------------------------*)
fun POP_ASSUM_LIST asltac (asl,w) = asltac (map ASSUME asl) ([],w);

(*---------------------------------------------------------------------------
 * Pop the first assumption matching (higher-order match) the given term
 * and give it to a function (tactic).
 *---------------------------------------------------------------------------*)

local fun match_with_constants constants pat ob = 
       let val (tm_inst, ty_inst) = Ho_match.match_term [] pat ob
           val bound_vars = map #2 tm_inst
       in
          null (intersect constants bound_vars)
       end handle HOL_ERR _ => false
in
fun PAT_ASSUM pat thfun (asl, w) = 
  case List.filter (can (Ho_match.match_term [] pat)) asl
   of [] => raise TACTICAL_ERR "PAT_ASSUM" "No assumptions match pattern"
    | [x] => let val (ob, asl') = Lib.pluck (fn t => t = x) asl
             in thfun (ASSUME ob) (asl', w)
             end
    | _ => let val fvars = free_varsl (w::asl)
               val (ob,asl') = Lib.pluck (match_with_constants fvars pat) asl
           in thfun (ASSUME ob) (asl',w)
           end
end


(*-- Tactical quantifiers -- Apply a list of tactics in succession. -------*)


(*---------------------------------------------------------------------------
 * Uses every tactic.
 *    EVERY [TAC1;...;TACn] =  TAC1  THEN  ...  THEN  TACn
 *---------------------------------------------------------------------------*)
fun EVERY tacl = itlist (curry (op THEN)) tacl ALL_TAC;

(*---------------------------------------------------------------------------
 * Uses first tactic that succeeds.
 *    FIRST [TAC1;...;TACn] =  TAC1  ORELSE  ...  ORELSE  TACn
 *---------------------------------------------------------------------------*)
fun FIRST [] g = NO_TAC g
  | FIRST (tac::rst) g = tac g handle HOL_ERR _ => FIRST rst g;

fun MAP_EVERY tacf lst = EVERY (map tacf lst);
fun MAP_FIRST tacf lst = FIRST (map tacf lst);


(*---------------------------------------------------------------------------
 * Call a thm-tactic for every assumption.
 *---------------------------------------------------------------------------*)
val EVERY_ASSUM = ASSUM_LIST o MAP_EVERY;


(*---------------------------------------------------------------------------
 * Call a thm-tactic for the first assumption at which it succeeds.
 *---------------------------------------------------------------------------*)

fun FIRST_ASSUM ttac (A,g) =
   let fun find ttac []     = raise TACTICAL_ERR "FIRST_ASSUM"  ""
         | find ttac (a::L) =
             ttac (ASSUME a) (A,g) handle HOL_ERR _ => find ttac L
   in
     find ttac A
   end;

(*----------------------------------------------------------------------
 * Call a thm-tactic for the first assumption at which it succeeds and
 * remove that assumption from the list.
 * Note that  UNDISCH_THEN is actually defined for public consumption
 * in Thm_cont.sml, but we can't use that here because Thm_cont builds
 * on this module. Arguably all of the ASSUM tactics are not tacticals
 * at all, and shouldn't be here along with THEN etc.
 ---------------------------------------------------------------------------*)

local fun UNDISCH_THEN tm ttac (asl, w) = 
       let val (_, asl') = Lib.pluck (fn a => a = tm) asl
       in
         ttac (ASSUME tm) (asl', w)
       end
in
fun FIRST_X_ASSUM ttac =
  FIRST_ASSUM (fn th => UNDISCH_THEN (concl th) ttac)
end;

(*---------------------------------------------------------------------------
 * Split off a new subgoal and provide it as a theorem to a tactic
 *
 *     SUBGOAL_THEN wa (\tha. tac)
 *
 * makes a subgoal of wa, and also assumes wa for proving the original goal.
 * Most convenient when the tactic solves the original goal, leaving only the
 * new subgoal wa.
 *---------------------------------------------------------------------------*)

fun SUBGOAL_THEN wa ttac (asl,w) =
    let val (gl,p) = ttac (ASSUME wa) (asl,w)
    in
     ((asl,wa)::gl,(fn (tha::thl) => PROVE_HYP tha (p thl)))
    end;

(*---------------------------------------------------------------------------
 * A tactical that makes a tactic fail if it has no effect.
 *---------------------------------------------------------------------------*)

fun CHANGED_TAC tac g =
 let val (gl,p) = tac g
 in if (set_eq gl [g]) then raise TACTICAL_ERR "CHANGED_TAC" "no change"
    else (gl,p)
 end;

end;  (* Tactical *)
