open bossLib 
open deepMatchesLib


(* Introducing case expressions *)

val t = ``case x of (NONE, []) => 0``
val t' = convert_case t 
val thm_t = PMATCH_INTRO_CONV t

(* check that SIMP works *)
val thm_t' = PMATCH_REMOVE_ARB_CONV t'
val thm_t' = PMATCH_SIMP_CONV t'
		    
(* more fancy *)

val t = ``case x of 
   (NONE, []) => 0
 | (SOME 2, []) => 2
 | (SOME 3, (x :: xs)) => 3 + x
 | (SOME _, (x :: xs)) => x``

val t' = convert_case t 
val thm_t = PMATCH_INTRO_CONV t

val thm_t' = PMATCH_REMOVE_ARB_CONV t'
val thm_t' = PMATCH_SIMP_CONV t'

(* Playing around with some examples *)

val example1 = ``
PMATCH (a,x,xs)
     [PMATCH_ROW (\x. ((NONE,x,[]),x));
      PMATCH_ROW (\x. ((NONE,x,[2]),x));
      PMATCH_ROW (\(x,v18). ((NONE,x,[v18]),3));
      PMATCH_ROW (\(x,v12,v16,v17). ((NONE,x,v12::v16::v17),3));
      PMATCH_ROW (\(y,x,z,zs). ((SOME y,x,[z]),x+5+z));
      PMATCH_ROW (\(y,v23,v24). ((SOME y,0,v23::v24),v23+y));
      PMATCH_ROW (\(y,z,v23). ((SOME y,SUC z,[v23]),3));
      PMATCH_ROW (\(y,z). ((SOME y,SUC z,[1; 2]),y + z));
      PMATCH_ROW (\(y,z,v38). ((SOME y,SUC z,[1; v38]),3));
      PMATCH_ROW (\(y,x). ((y,x,[2;4;3]),3+x));
      PMATCH_ROW
        (\(y,z,v29,v36,v37). ((SOME y,SUC z,1::v29::v36::v37),z+v36+v29));
      PMATCH_ROW (\(y,z,v31,v29,v30). ((SOME y,SUC z,v31::v29::v30),v31+z))]``

val example2 = ``PMATCH (h::t)
  [PMATCH_ROW (\_ . ([],x));
   PMATCH_ROW (\_. ([2],x)); PMATCH_ROW (\v18. ([v18],3));
   PMATCH_ROW (\(v12,v16,v17). (v12::v16::v17,3));
   PMATCH_ROW (\_. ([2; 4; 3],3 + x))]``

val example3 = 
  ``PMATCH (NONE,x,xs)
          [PMATCH_ROW (\x. ((NONE,x,[]),x));
           PMATCH_ROW (\x. ((NONE,x,[2]),x));
           PMATCH_ROW (\(x,v18). ((NONE,x,[v18]),3));
           PMATCH_ROW (\(x,v12,v16,v17). ((NONE,x,v12::v16::v17),3));
           PMATCH_ROW (\(y,x). ((y,x,[2; 4; 3]),3 + x))]``;


(* turn off pretty printer *)

set_trace "use pmatch_pp" 0;
example1;
set_trace "use pmatch_pp" 1;
example1;


PMATCH_SIMP_CONV example1 
PMATCH_SIMP_CONV example2
PMATCH_SIMP_CONV example3

set_goal ([], ``^example1 = XXX``);

e (Cases_on `a`)
e (CONV_TAC (DEPTH_CONV PMATCH_SIMP_CONV))
e (Cases_on `xs`)
e (CONV_TAC (DEPTH_CONV PMATCH_SIMP_CONV))

proofManagerLib.restart ()

e (Cases_on `xs`)
e (CONV_TAC (DEPTH_CONV PMATCH_SIMP_CONV))

proofManagerLib.restart ()

e (Cases_on `x`)
e (CONV_TAC (DEPTH_CONV PMATCH_SIMP_CONV))
e (Cases_on `xs`)

proofManagerLib.rotate 1
e (CONV_TAC (DEPTH_CONV PMATCH_SIMP_CONV))
SIMP_TAC std_ss []

proofManagerLib.drop ()

