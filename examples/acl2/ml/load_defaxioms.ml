(*****************************************************************************)
(* Slurp in defaxioms.lisp.trans.ml and put results on variable defaxioms.   *)
(*****************************************************************************)

new_theory "defaxioms";

use (Globals.HOLDIR ^ "/examples/acl2/ml/load_sexp.ml");
use (Globals.HOLDIR ^ "/examples/acl2/lisp/defaxioms.lisp.trans.ml");

load_defaxioms();

val string_abbrev_thms = map snd (definitions "-");

val caar_def =
 Define
  `caar x = car(car x)`;

val cadr_def =
 Define
  `cadr x = car(cdr x)`;

val cdar_def =
 Define
  `cdar x = cdr(car x)`;

val cddr_def =
 Define
  `cddr x = cdr(cdr x)`;

val caaar_def =
 Define
  `caaar x = car(car(car x))`;

val cdaar_def =
 Define
  `cdaar x = cdr(car(car x))`;

val cadar_def =
 Define
  `cadar x = car(cdr(car x))`;

val cddar_def =
 Define
  `cddar x = cdr(cdr(car x))`;

val caadr_def =
 Define
  `caadr x = car(car(cdr x))`;

val cdadr_def =
 Define
  `cdadr x = cdr(car(cdr x))`;

val caddr_def =
 Define
  `caddr x = car(cdr(cdr x))`;

val cdddr_def =
 Define
  `cdddr x = cdr(cdr(cdr x))`;

val caaaar_def =
 Define
  `caaaar x = car(car(car(car x)))`;

val cadaar_def =
 Define
  `cadaar x = car(cdr(car(car x)))`;

val caadar_def =
 Define
  `caadar x = car(car(cdr(car x)))`;

val caddar_def =
 Define
  `caddar x = car(cdr(cdr(car x)))`;

val caaadr_def =
 Define
  `caaadr x = car(car(car(cdr x)))`;

val cadadr_def =
 Define
  `cadadr x = car(cdr(car(cdr x)))`;

val caaddr_def =
 Define
  `caaddr x = car(car(cdr(cdr x)))`;

val cadddr_def =
 Define
  `cadddr x = car(cdr(cdr(cdr x)))`;

val cdaaar_def =
 Define
  `cdaaar x = cdr(car(car(car x)))`;

val cddaar_def =
 Define
  `cddaar x = cdr(cdr(car(car x)))`;

val cdadar_def =
 Define
  `cdadar x = cdr(car(cdr(car x)))`;

val cdddar_def =
 Define
  `cdddar x = cdr(cdr(cdr(car x)))`;

val cdaadr_def =
 Define
  `cdaadr x = cdr(car(car(cdr x)))`;

val cddadr_def =
 Define
  `cddadr x = cdr(cdr(car(cdr x)))`;

val cdaddr_def =
 Define
  `cdaddr x = cdr(car(cdr(cdr x)))`;

val cddddr_def =
 Define
  `cddddr x = cdr(cdr(cdr(cdr x)))`;

(*
val caadr_def =
 Define
  `caadr x = car(car(cdr x))`;

val cdddr_def =
 Define
  `cdddr x = cdr(cdr(cdr x))`;

val cddddr_def =
 Define
  `cddddr x = cdr(cdr(cdr(cdr x)))`;

val cdddddr_def =
 Define
  `cdddddr x = cdr(cdr(cdr(cdr(cdr x))))`;

val cddddddr_def =
 Define
  `cddddddr x = cdr(cdr(cdr(cdr(cdr(cdr x)))))`;

val cadar_def =
 Define
  `cadar x = car(cdr(car x))`;

val cadadr_def =
 Define
  `cadadr x = car(cdr(car(cdr x)))`;

val caddddddddr_def =
 Define
  `caddddddddr x = car(cdr(cdr(cdr(cdr(cdr(cdr(cdr(cdr x))))))))`;

val cdaddddaddddddddr_def =
 Define
  `cdaddddaddddddddr x = 
    cdr(car(cdr(cdr(cdr(cdr(car(cdr(cdr(cdr(cdr(cdr(cdr(cdr(cdr x))))))))))))))`;

val caddddaddddddddr_def =
 Define
  `caddddaddddddddr x = 
    car(cdr(cdr(cdr(cdr(car(cdr(cdr(cdr(cdr(cdr(cdr(cdr(cdr x)))))))))))))`;

val cddddaddddddddr_def =
 Define
  `cddddaddddddddr x = cdr(cdr(cdr(cdr(car(cdr(cdr(cdr(cdr(cdr(cdr(cdr(cdr x))))))))))))`;

val cdddaddddddddr_def =
 Define
  `cdddaddddddddr x = cdr(cdr(cdr(car(cdr(cdr(cdr(cdr(cdr(cdr(cdr(cdr x)))))))))))`;

val cddaddddddddr_def =
 Define
  `cddaddddddddr x = cdr(cdr(car(cdr(cdr(cdr(cdr(cdr(cdr(cdr(cdr x))))))))))`;

val cdaddddddddr_def =
 Define
  `cdaddddddddr x = cdr(car(cdr(cdr(cdr(cdr(cdr(cdr(cdr(cdr x)))))))))`;

val caddddddddr_def =
 Define
  `caddddddddr x = car(cdr(cdr(cdr(cdr(cdr(cdr(cdr(cdr x))))))))`;

val cddddddddr_def =
 Define
  `cddddddddr x = cdr(cdr(cdr(cdr(cdr(cdr(cdr(cdr x)))))))`;

val cr_thms =
 map
  GSYM
  [cdaddddaddddddddr_def,caddddaddddddddr_def,cddddaddddddddr_def,
   cdddaddddddddr_def,cddaddddddddr_def,
   cdaddddddddr_def,caddddddddr_def,cddddddddr_def,caddddddddr_def,
   cddddddr_def,cdddddr_def,cddddr_def,cdddr_def,
   cadadr_def,caadr_def,cadar_def,cddr_def,cadr_def];
*)

val cr_thms =
 map
  GSYM
  [caar_def,cadr_def,cdar_def,cddr_def,
   caaar_def,cdaar_def,cadar_def,cddar_def,caadr_def,cdadr_def,caddr_def,cdddr_def,
   caaaar_def,cadaar_def,caadar_def,caddar_def,caaadr_def,cadadr_def,caaddr_def,cadddr_def,
   cdaaar_def,cddaar_def,cdadar_def,cdddar_def,cdaadr_def,cddadr_def,cdaddr_def,cddddr_def];

val List_def =
 Define
  `(List[s] = cons s nil)
    /\
   (List(s::sl) = cons s (List sl))`;

val andl_def =
 Define
  `(andl[] = t)
   /\
   (andl[s] = s)
   /\
   (andl(x::y::l) = ite x (andl(y::l)) nil)`;

val andl_fold =
 prove
  (``(ite x y nil = andl[x;y]) /\ (andl[x; andl(y::l)] = andl(x::y::l))``,
   RW_TAC std_ss [andl_def,ite_def,List_def]);

val andl_append =
 prove
  (``!l1 l2. andl(andl l1 :: l2) = andl(l1 ++ l2)``,
   Induct
    THEN RW_TAC list_ss [andl_def,ite_def,List_def]
    THENL
     [Cases_on `l2`
       THEN RW_TAC list_ss [andl_def,ite_def,List_def,EVAL ``t=nil``],
      Cases_on `h=nil`
       THEN RW_TAC list_ss [andl_def,ite_def,List_def,EVAL ``t=nil``]
       THENL
        [Cases_on `l1` THEN Cases_on `l2`
          THEN RW_TAC list_ss [andl_def,ite_def,List_def,EVAL ``t=nil``],
         Cases_on `l1`
          THEN RW_TAC list_ss [andl_def,ite_def,List_def,EVAL ``t=nil``]]]);

val andl_fold =
 prove
  (``(ite x y nil = andl[x;y])
     /\ 
     (andl[x; andl(y::l)] = andl(x::(y::l)))
     /\ 
     (andl(andl(x::y::l1)::l2) = andl(x::y::(l1++l2)))``,
   RW_TAC std_ss [andl_def,ite_def,List_def]
    THENL
     [Cases_on `l2`
       THEN RW_TAC std_ss [andl_def,ite_def,List_def],
      RW_TAC list_ss [andl_append]]);

val itel_def =
 Define
  `(itel [] val'               = val')
   /\
   (itel ((test,val)::sl) val' = ite test val (itel sl val'))`;

val itel_fold =
 prove
  (``(ite x y z = itel [(x,y)] z)
     /\
     (itel [p] (itel pl v) = itel (p::pl) v)``,
   Cases_on `p`
    THEN RW_TAC std_ss [itel_def,ite_def]);

(*
val itel_fold =
 prove
  (``(ite x y (itel l v) = itel ((x,y)::l) v)
     /\
     (ite x1 y1 (ite x2 y2 z) = itel [(x1,y1);(x2,y2)] z)
     /\
     (itel [p] (ite x y z) = itel (p::[(x,y)]) z)
     /\
     (itel l1 (itel l2 v) = itel (l1 ++ l2) v)``,
   Cases_on `p`
    THEN RW_TAC list_ss [itel_def,ite_def]
    THEN Induct_on `l1`
    THEN RW_TAC list_ss [itel_def,ite_def]
    THEN Induct_on `l1`
    THEN RW_TAC list_ss [itel_def,ite_def]
    THEN Cases_on `h`
    THEN Cases_on `q=nil`
    THEN RW_TAC list_ss [itel_def,ite_def,List_def,EVAL ``t=nil``]);
*)

val itel_append =
 prove
  (``itel l1 (itel l2 v) = itel (l1 ++ l2) v``,
   Induct_on `l1`
    THEN RW_TAC list_ss [itel_def,ite_def]
    THEN Cases_on `h`
    THEN Cases_on `q=nil`
    THEN RW_TAC list_ss [itel_def,ite_def,List_def,EVAL ``t=nil``]);

val asym_def = Define `asym = sym ACL2`;
val csym_def = Define `csym = sym COMMON_LISP`;
val ksym_def = Define `ksym = sym KEYWORD`;
val osym_def = Define `osym = sym ACL2_OUTPUT_CHANNEL`;

val let_simp =
 prove
  (``(!P1 v y. (let (x,y) = (v,y) in P1 x y) = (let x = v in P1 x y))
     /\
     (!P2 v y z. (let (x,y,z) = (v,y,z) in P2 x y z) = (let x = v in P2 x y z))
     /\
     (!P3 v y z w. (let (x,y,z,w) = (v,y,z,w) in P3 x y z w) = (let x = v in P3 x y z w))``,
   RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def]);

val simps = 
 [let_simp,andl_fold,itel_fold,itel_append]
 @
 (map 
   GSYM 
   [int_def,nat_def,List_def,asym_def,csym_def,ksym_def,osym_def]);

val simp_defaxioms = ref([] : thm list);
simp_defaxioms := !defaxioms;

simp_defaxioms := time (map(SIMP_RULE list_ss simps)) (!simp_defaxioms);

(*
simp_defaxioms :=
 time (foldl 
        (fn (th,thl) => map (SIMP_RULE std_ss [th]) thl) 
        (!simp_defaxioms)) 
        (rev cr_thms);
*)

simp_defaxioms :=
 time (foldl 
        (fn (th,thl) => map (SIMP_RULE std_ss [th]) thl) 
        (!simp_defaxioms)) 
        (GSYM(CONJUNCT1 itel_fold)::(rev cr_thms));

simp_defaxioms := time (map(SIMP_RULE std_ss string_abbrev_thms)) (!simp_defaxioms);

!simp_defaxioms;



(*
export_acl2_theory();

compile_theory();
*)


