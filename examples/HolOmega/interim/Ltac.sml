
structure Ltac = struct 

local open goalStack Feedback in 

val ERR = mk_HOL_ERR "Ltac"; 

(* in Abbrev 
type list_validation = thm list -> thm list ;
type list_tactic = goal list -> goal list * list_validation ;
*)

(* REVERSE_LTAC : list_tactic *)
fun REVERSE_LTAC goals = (rev goals, rev) ;
fun INVALID_REVERSE_LTAC goals = (rev goals, Lib.I) ;
 
(* val el = proofManagerLib.expandl ; *)

(* DROP_N_LTAC : int -> list_tactic -> list_tactic *)
fun DROP_N_LTAC n ltac goals = 
  let val (gt, gd) = Lib.split_after n goals ;
    val (gr, vr) = ltac gd ;
    fun v ths = 
      let val (tt, td) = Lib.split_after n ths ;
      in tt @ vr td end ;
  in (gt @ gr, v) end ;
  
(* TAKE_N_LTAC : int -> list_tactic -> list_tactic *)
fun TAKE_N_LTAC n ltac goals = 
  let val (gt, gd) = Lib.split_after n goals ;
    val (gr, vr) = ltac gt ;
    val nr = length gr ;
    fun v ths = 
      let val (tt, td) = Lib.split_after nr ths ;
      in vr tt @ td end ;
  in (gr @ gd, v) end ;

(* HEADGOAL : tactic -> list_tactic *)
fun HEADGOAL (tac : tactic) (g :: gs : goal list) = 
  let val (gr, vr) = tac g ;
    val nr = length gr ;
    fun v ths = 
      let val (tt, td) = Lib.split_after nr ths ;
      in vr tt :: td end ;
  in (gr @ gs, v) end ;


(* rotate - code from goalStack.sml *)
fun rotl (a::rst) = rst@[a]
  | rotl [] = raise ERR "rotl" "empty list"

fun rotr lst =
  let val (front,back) = Lib.front_last lst
  in (back::front) end
  handle HOL_ERR _ => raise ERR "rotr" "empty list"

(* ROTATE_LTAC : int -> list_tactic *)
fun ROTATE_LTAC n goals = 
  if n > length goals then raise ERR "rotate"
      "More rotations than goals -- no rotation done"
  else (Lib.funpow n rotl goals, Lib.funpow n rotr) ;

fun INVALID_ROTATE_LTAC n goals = 
  if n > length goals then raise ERR "rotate"
      "More rotations than goals -- no rotation done"
  else (Lib.funpow n rotl goals, Lib.funpow n rotl) ;

fun DUPLICATE_TAC g = ([g,g], hd) ;

(* TACLIST, ALLGOALS - code taken from THENL, THEN in Tactical.sml *)
fun mapshape [] _ _ =  []
  | mapshape (n1::nums) (f1::funcs) args =
    let val (f1_args,args') = Lib.split_after n1 args
    in f1 f1_args :: mapshape nums funcs args' end;

(* TACLIST : tactic list -> list_tactic *)
fun TACLIST tacl gl = 
 let val (G,V,lengths) = Lib.itlist2 (fn goal => fn tac => fn (G,V,lengths) =>
           case tac goal
            of ([],vfun) => let val th = vfun []
                            in (G, (fn [] => th)::V, 0::lengths) end
             | (goals,vfun) => (goals@G, vfun::V, length goals::lengths))
          gl tacl ([],[],[])
 in case G
     of [] => ([], let val ths = (map (fn f => f[]) V) in fn [] => ths end)
      | _  => (G, (mapshape lengths V))
 end ;

(* ALLGOALS : tactic -> list_tactic *)
fun ALLGOALS tac2 gl =
 case (Lib.itlist (fn goal => fn (G,V,lengths) =>
               case (tac2 goal)
               of ([],vfun) => let val th = vfun []
                               in (G, (fn [] => th)::V, 0::lengths)
                               end
                | (goals,vfun) => (goals@G, vfun::V, length goals::lengths))
            gl ([],[],[]))
      of ([],V,_) =>
            ([], let val ths = (map (fn f => f[]) V) in fn [] => ths end)
       | (G,V,lengths) => (G, (mapshape lengths V)) ;
  
infix THEN_LTAC ORELSE_LTAC THEN_LT  ;

(* op THEN_LT : tactic * list_tactic -> tactic *)
fun (tac1 THEN_LT ltac2) goal = 
  let val (gs1, v1) = tac1 goal ;
    val (gs2, v2) = ltac2 gs1 ;
  in (gs2, v1 o v2) end ;

(* op THEN_LTAC : list_tactic * list_tactic -> list_tactic *)
fun (ltac1 THEN_LTAC ltac2) goals = 
  let val (gs1, v1) = ltac1 goals ;
    val (gs2, v2) = ltac2 gs1 ;
  in (gs2, v1 o v2) end ;

fun (tac1 ORELSE_LTAC tac2) g = tac1 g handle HOL_ERR _ => tac2 g;

fun FAIL_LTAC tok (g:goal list) = raise ERR "FAIL_LTAC" tok;
fun NO_LTAC g = FAIL_LTAC "NO_LTAC" g;
fun ALL_LTAC goals = (goals, fn ths => ths) ; 
fun TRY_LTAC ltac = ltac ORELSE_LTAC ALL_LTAC; 

(* TRY_LTAC : list_tactic -> list_tactic 
  EVERY_LTAC : list_tactic list -> list_tactic 
  FIRST_LTAC : list_tactic list -> list_tactic 
  *)
fun EVERY_LTAC tacl = Lib.itlist (Lib.curry (op THEN_LTAC)) tacl ALL_LTAC;
fun FIRST_LTAC [] g = NO_LTAC g
  | FIRST_LTAC (tac::rst) g = tac g 
    handle HOL_ERR _ => FIRST_LTAC rst g;

end (* local open goalStack Feedback *)

end ; (* structure Ltac *)

(* test
g `T /\ T /\ T /\ T /\ T /\ T /\ T` ;
e (REPEAT CONJ_TAC) ;
el (ALLGOALS (REWRITE_TAC [])) ; (* output !! *)

e (REPEAT CONJ_TAC THEN_LT ALLGOALS (REWRITE_TAC [])) ;
  
g `a /\ b /\ c /\ d /\ e /\ f /\ g` ;
e (REPEAT CONJ_TAC) ;
el REVERSE_LTAC ;
el (DROP_N_LTAC 3 REVERSE_LTAC) ;
el (TAKE_N_LTAC 3 REVERSE_LTAC) ;
el (ROTATE_LTAC 3) ;
el (INVALID_ROTATE_LTAC 3) ;
el (HEADGOAL DUPLICATE_TAC) ;
el (INVALID_ROTATE_LTAC 4) ;

val t7 = prove (``T /\ T /\ T /\ T /\ T /\ T /\ T``,
  REPEAT CONJ_TAC THEN_LT ALLGOALS (REWRITE_TAC [])) ;


*)
