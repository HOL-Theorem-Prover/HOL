(*---------------------------------------------------------------------------
 * A theory about transitive closure of relations.
 *---------------------------------------------------------------------------*)

structure TCScript =
struct


open HolKernel Parse basicHol90Lib QLib mesonLib;
infix ORELSE THEN THENL |->;

val _ = new_theory "TC";


val TC_DEF = 
Q.new_definition
("TC_DEF",
  `TC (R:'a->'a->bool) a b = 
    !P. 
       (!x y. R x y ==> P x y) /\
       (!x y z. P x y /\ P y z ==> P x z)
       ==> P a b`);


val transitive_def = 
Q.new_definition
("transitive_def", 
   `transitive (R:'a->'a->bool) = !x y z. R x y /\ R y z ==> R x z`);


val TC_TRANSITIVE = Q.store_thm("TC_TRANSITIVE",
 `!R:'a->'a->bool. transitive(TC R)`,
REWRITE_TAC[transitive_def,TC_DEF]
 THEN REPEAT STRIP_TAC
 THEN RES_TAC THEN ASM_MESON_TAC[]);


val TC_SUBSET = Q.store_thm("TC_SUBSET",
`!R x (y:'a). R x y ==> TC R x y`,
REWRITE_TAC[TC_DEF] THEN MESON_TAC[]);


val TC_INDUCT = Q.store_thm("TC_INDUCT",
`!(R:'a->'a->bool) P.
   (!x y. R x y ==> P x y) /\ 
   (!x y z. P x y /\ P y z ==> P x z)
   ==> !u v. (TC R) u v ==> P u v`,
REWRITE_TAC[TC_DEF] THEN MESON_TAC[]);


val TC_INDUCT_TAC =
 let val tc_thm = TC_INDUCT
     fun tac (asl,w) =
      let val {Bvar=u,Body} = dest_forall w
          val {Bvar=v,Body} = dest_forall Body
          val {ant,conseq} = dest_imp Body
          val (TC,[R,u',v']) = Dsyntax.strip_comb ant
          val {Name = "TC",...} = dest_const TC
          val _ = assert (aconv u) u'
          val _ = assert (aconv v) v'
          val P = list_mk_abs([u,v], conseq)
          val tc_thm' = BETA_RULE(ISPEC P (ISPEC R tc_thm))
      in MATCH_MP_TAC tc_thm' (asl,w)
      end
      handle _ => raise HOL_ERR{origin_structure = "<top-level>",
                     origin_function = "TC_INDUCT_TAC", 
                     message = "Unanticipated term structure"}
 in tac
 end;


val TC_CASES1 = 
Q.store_thm
("TC_CASES1",
  `!R x z. TC R x z ==> R x z \/ ?y:'a. R x y /\ TC R y z`,
GEN_TAC
 THEN TC_INDUCT_TAC 
 THEN MESON_TAC [REWRITE_RULE[transitive_def] TC_TRANSITIVE, TC_SUBSET]);

val TC_CASES2 = 
Q.store_thm
("TC_CASES2",
    `!R x z. TC R x z ==> R x z \/ ?y:'a. TC R x y /\ R y z`,
GEN_TAC
 THEN TC_INDUCT_TAC 
 THEN MESON_TAC [REWRITE_RULE[transitive_def] TC_TRANSITIVE, TC_SUBSET]);


val _ = export_theory();

end;
