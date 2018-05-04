
let DIST_AND_OR =
 prove_thm
  (`DIST_AND_OR`,
   "!t t1 t2. 
     (t /\ (t1 \/ t2) = (t /\ t1) \/ (t /\ t2)) /\
     ((t1 \/ t2) /\ t = (t1 /\ t) \/ (t2 /\ t))",
   REPEAT GEN_TAC
    THEN ASM_CASES_TAC "t:bool"
    THEN ASM_REWRITE_TAC[]
    THEN ASM_CASES_TAC "t1:bool"
    THEN ASM_REWRITE_TAC[]
    THEN ASM_CASES_TAC "t2:bool"
    THEN ASM_REWRITE_TAC[]);;

let AND_OR_RULE = PURE_REWRITE_RULE[DIST_AND_OR];;

%  
 ?x. t1[x] \/ t2[x] --> |- (?x. t1[x] \/ t2[x]) = (?x. t1[x]) \/ (?x. t2[x])
%

let EXISTS_OR_CONV t =
 (let x,body = dest_exists t
  in
  let t1,t2 = dest_disj body
  in
  let Et1 = mk_exists(x,t1)
  and Et2 = mk_exists(x,t2)
  in
  let Et1t2 = mk_disj(Et1,Et2)
  in
  let th1 =
   DISCH
   t
   (CHOOSE
     (x, ASSUME t)
     (DISJ_CASES
      (ASSUME body) 
      (DISJ1 (EXISTS(Et1,x)(ASSUME t1)) Et2)
      (DISJ2 Et1 (EXISTS(Et2,x)(ASSUME t2)))))
  and th2 =
   DISCH
    Et1t2
    (DISJ_CASES
     (ASSUME Et1t2)
     (CHOOSE(x, ASSUME Et1)(EXISTS(t,x)(DISJ1 (ASSUME t1) t2)))
     (CHOOSE(x, ASSUME Et2)(EXISTS(t,x)(DISJ2 t1 (ASSUME t2)))))
  in
  IMP_ANTISYM_RULE th1 th2
 ) ? failwith `EXISTS_OR_CONV`;;

let EXISTS_OR_RULE = CONV_RULE(DEPTH_CONV EXISTS_OR_CONV);;

let test =
 "?x y. ((x = 1) \/ (x = 2)) /\
        ((y = 3) \/ (y = 4)) /\
        P x /\ Q y /\ R x y";;

let th1 = ASSUME test;;

let th2 = AND_OR_RULE th1;;

let th3 = EXISTS_OR_RULE th2;;

% Output:


#let th1 = ASSUME test;;

let th2 = AND_OR_RULE th1;;
th1 = 
. |- ?x y.
      ((x = 1) \/ (x = 2)) /\
      ((y = 3) \/ (y = 4)) /\
      P x /\
      Q y /\
      R x y

##
th2 = 
. |- ?x y.
      ((x = 1) /\ (y = 3) /\ P x /\ Q y /\ R x y \/
       (x = 1) /\ (y = 4) /\ P x /\ Q y /\ R x y) \/
      (x = 2) /\ (y = 3) /\ P x /\ Q y /\ R x y \/
      (x = 2) /\ (y = 4) /\ P x /\ Q y /\ R x y
Runtime: 59.7s
GC: 13.8s

##let th3 = EXISTS_OR_RULE th2;;
th3 = 
. |- (?x y.
       (x = 1) /\ (y = 3) /\ P x /\ Q y /\ R x y \/
       (x = 1) /\ (y = 4) /\ P x /\ Q y /\ R x y) \/
     (?x y.
       (x = 2) /\ (y = 3) /\ P x /\ Q y /\ R x y \/
       (x = 2) /\ (y = 4) /\ P x /\ Q y /\ R x y)
Runtime: 27.4s

%
