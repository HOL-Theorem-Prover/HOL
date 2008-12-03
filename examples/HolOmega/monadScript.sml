(*---------------------------------------------------------------------------
                         Monads in HOL-Omega
                       (Peter Vincent Homeier)
 ---------------------------------------------------------------------------*)

(* Interactive use:
   app load ["bossLib", "Q", "pred_setTheory", "stringTheory"];
*)

structure monadScript =
struct

open HolKernel Parse boolLib
     bossLib

open combinTheory functorTheory


val _ = new_theory "monad";


(*---------------------------------------------------------------------------
            Monad operator type abbreviations
 ---------------------------------------------------------------------------*)

val _ = type_abbrev ("unit", Type `: \'M. !'a. 'a -> 'a 'M`);
val _ = type_abbrev ("bind", Type `: \'M. !'a 'b. 'a 'M -> ('a -> 'b 'M) -> 'b 'M`);
val _ = type_abbrev ("map" , Type `: \'M. !'a 'b. ('a -> 'b) -> ('a 'M -> 'b 'M)`);
val _ = type_abbrev ("join", Type `: \'M. !'a. 'a 'M 'M -> 'a 'M`);


(*---------------------------------------------------------------------------
            Monad predicate, on unit and bind term operators
 ---------------------------------------------------------------------------*)


val monad_def = new_definition("monad_def", Term
   `monad (unit: 'M unit,
           bind: 'M bind) =
      (* Left unit *)
          (!:'a 'b. !(a:'a) (k:'a -> 'b 'M).
                bind (unit a) k = k a) /\
      (* Right unit *)
          (!:'a. !(m:'a 'M).
                bind m unit = m) /\
      (* Associative *)
          (!:'a 'b 'c. !(m:'a 'M) (k:'a -> 'b 'M) (h:'b -> 'c 'M).
                bind (bind m k) h
              = bind m (\a. bind (k a) h))
     `);

val monad_umj_def = new_definition(
   "monad_umj_def",
   ``monad_umj (unit: 'M unit,
                map : 'M map ,
                join: 'M join) =
     (* map_I *)         (!:'a. map (I:'a -> 'a) = I) /\
     (* map_o *)         (!:'a 'b 'c. !(f:'a -> 'b) (g:'b -> 'c).
                                map (g o f) = map g o map f) /\
     (* map_unit *)      (!:'a 'b. !f:'a -> 'b.
                                map f o unit = unit o f) /\
     (* map_join *)      (!:'a 'b. !f:'a -> 'b.
                                map f o join = join o map (map f)) /\
     (* join_unit *)     (!:'a. join o unit = (I:'a 'M -> 'a 'M)) /\
     (* join_map_unit *) (!:'a. join o map unit = (I:'a 'M -> 'a 'M)) /\
     (* join_map_join *) (!:'a. join [:'a:] o map join = join o join)
   ``);


(*---------------------------------------------------------------------------
            Monad map and join operations,
            defined in terms of unit and bind;
            map is a functor, and join and unit are natural transformations.
 ---------------------------------------------------------------------------*)

val MMAP_def = Define
   `MMAP (unit: 'M unit, bind: 'M bind)
              (f:'a -> 'b) (m : 'a 'M) = bind m (\a. unit (f a))`;

val JOIN_def = Define
   `JOIN (unit: 'M unit, bind: 'M bind)
               (z : 'a 'M 'M) = bind z (\m.m)`;

(*---------------------------------------------------------------------------
            Another definition of monads, arising from category theory:

   "A monad consists of a category A, a functor t : A -> A,
   and natural transformations mu : t^2 -> t and eta : 1_A -> t
   satisfying three equations, as expressed by the commutative diagrams

                 t mu                    t eta         eta t
           t^3 -------> t^2           t -------> t^2 <------- t
            |            |              \_        |        _/
       mu t |            | mu              \_     |mu   _/
            |            |                1   \_  |  _/   1
            V            V                      V V V
           t^2 ------->  t                        t."
                  mu

   (From "The formal theory of monads II" by Stephen Lack and Ross Street.)
 ---------------------------------------------------------------------------*)

val MMAP_functor = store_thm
  ("MMAP_functor",
   ``!unit bind.
      monad(unit,bind) ==>
      functor ((\:'a 'b. MMAP(unit,bind)) : 'M functor)``,
   SRW_TAC[][monad_def,functor_def,MMAP_def,FUN_EQ_THM,ETA_AX]
  );

val JOIN_nattransf = store_thm
  ("JOIN_nattransf",
   ``!unit bind.
      monad(unit,bind) ==>
      nattransf ((\:'a 'b. MMAP(unit,bind) o MMAP(unit,bind)) : ('M o 'M) functor)
                ((\:'a 'b. MMAP(unit,bind))                   : 'M functor)
                ((\:'a.    JOIN(unit,bind))                   : 'M join)``,
   SRW_TAC[][monad_def,nattransf_def,MMAP_def,JOIN_def,FUN_EQ_THM]
  );

val unit_nattransf = store_thm
  ("unit_nattransf",
   ``!unit bind.
      monad(unit,bind) ==>
      nattransf ((\:'a 'b. I)                :  I functor)
                ((\:'a 'b. MMAP(unit,bind))  : 'M functor)
                (unit                        : 'M unit)``,
   SRW_TAC[][monad_def,nattransf_def,MMAP_def,FUN_EQ_THM]
  );



val MMAP_2_functor = store_thm
  ("MMAP_2_functor",
   ``!unit bind.
      monad(unit,bind) ==>
      functor ((\:'a 'b. MMAP(unit,bind) o MMAP(unit,bind)) : ('M o 'M) functor)``,
   REPEAT STRIP_TAC
   THEN HO_MATCH_MP_TAC functor_o
   THEN ASM_SIMP_TAC bool_ss [MMAP_functor]
  );

val MMAP_3_functor = store_thm
  ("MMAP_3_functor",
   ``!unit bind.
      monad(unit,bind) ==>
      functor ((\:'a 'b. MMAP(unit,bind) o MMAP(unit,bind) o MMAP(unit,bind)) : ('M o 'M o 'M) functor)``,
   REPEAT STRIP_TAC
   THEN IMP_RES_TAC MMAP_functor
   THEN IMP_RES_TAC functor_o
   THEN FULL_SIMP_TAC bool_ss []
  );


(*---------------------------------------------------------------------------
            Monad bind operation,
            defined in terms of map and join
 ---------------------------------------------------------------------------*)

val BIND_def = Define
   `BIND (map: 'M map, join: 'M join)
              (m : 'a 'M) (k:'a -> 'b 'M) = join (map k m)`;

val MMAP_BIND = store_thm
  ("MMAP_BIND",
   ``!:'M. !(unit:'M unit) (map:'M map) (join:'M join).
     MMAP(unit,\:'a 'b. BIND(map,join)) = \(f:'a -> 'b) (m : 'a 'M). BIND(map,join) m (\a. unit (f a))``,
   SRW_TAC[][FUN_EQ_THM,MMAP_def]
  );

val JOIN_BIND = store_thm
  ("JOIN_BIND",
   ``!:'M. !(unit:'M unit) (map:'M map) (join:'M join).
     JOIN(unit,\:'a 'b. BIND(map,join)) = \(z : 'a 'M 'M). BIND(map,join) z (\m.m)``,
   SRW_TAC[][FUN_EQ_THM,JOIN_def]
  );

(*---------------------------------------------------------------------------
            Monad laws
 ---------------------------------------------------------------------------*)

val MMAP_I = store_thm
  ("MMAP_I",
   ``!:'M. !(unit:'M unit) (bind:'M bind). monad(unit,bind) ==>
     (MMAP(unit,bind) (I:'a -> 'a) = I)``,
   SRW_TAC[][FUN_EQ_THM,MMAP_def,monad_def,ETA_AX]
  );

val MMAP_o = store_thm
  ("MMAP_o",
   ``!:'M. !(unit:'M unit) (bind:'M bind). monad(unit,bind) ==>
     (MMAP(unit,bind) ((g:'b -> 'c) o (f:'a -> 'b)) =
      MMAP(unit,bind) g o MMAP(unit,bind) f)``,
   SRW_TAC[][FUN_EQ_THM,MMAP_def,monad_def]
  );

val MMAP_unit = store_thm
  ("MMAP_unit",
   ``!:'M. !(unit:'M unit) (bind:'M bind). monad(unit,bind) ==>
     (MMAP(unit,bind) (f:'a -> 'b) o unit = unit o f)``,
   SRW_TAC[][FUN_EQ_THM,MMAP_def,monad_def]
  );

val MMAP_JOIN = store_thm
  ("MMAP_JOIN",
   ``!:'M. !(unit:'M unit) (bind:'M bind). monad(unit,bind) ==>
     !f:'a -> 'b.
     (MMAP(unit,bind) f o JOIN(unit,bind) =
      JOIN(unit,bind) o MMAP(unit,bind) (MMAP(unit,bind) f))``,
   SRW_TAC[][FUN_EQ_THM,monad_def,MMAP_def,JOIN_def]
  );

val JOIN_unit = store_thm
  ("JOIN_unit",
   ``!:'M. !(unit:'M unit) (bind:'M bind). monad(unit,bind) ==>
     !:'a.
     (JOIN(unit,bind) o unit = (I:'a 'M -> 'a 'M))``,
   SRW_TAC[][FUN_EQ_THM,monad_def,JOIN_def]
  );

val JOIN_MMAP_unit = store_thm
  ("JOIN_MMAP_unit",
   ``!:'M. !(unit:'M unit) (bind:'M bind). monad(unit,bind) ==>
     !:'a.
     (JOIN(unit,bind) o MMAP(unit,bind) unit = (I:'a 'M -> 'a 'M))``,
   SRW_TAC[][FUN_EQ_THM,monad_def,MMAP_def,JOIN_def,ETA_AX]
  );

val JOIN_MMAP_JOIN = store_thm
  ("JOIN_MMAP_JOIN",
   ``!:'M. !(unit:'M unit) (bind:'M bind). monad(unit,bind) ==>
     !:'a.
     ((JOIN(unit,bind) :'a 'M 'M -> 'a 'M) o MMAP(unit,bind) (JOIN(unit,bind)) =
      JOIN(unit,bind) o JOIN(unit,bind))``,
   SRW_TAC[][FUN_EQ_THM,monad_def,MMAP_def,JOIN_def]
  );

val bind_EQ_JOIN_MMAP = store_thm
  ("bind_EQ_JOIN_MMAP",
   ``!:'M. !(unit:'M unit) (bind:'M bind). monad(unit,bind) ==>
     !m (k:'a -> 'b 'M).
       bind m k = JOIN(unit,bind) (MMAP(unit,bind) k m)``,
   SRW_TAC[][FUN_EQ_THM,monad_def,MMAP_def,JOIN_def,ETA_AX]
  );

val laws_IMP_monad = store_thm
  ("laws_IMP_monad",
   ``!:'M. !(unit:'M unit) (bind:'M bind).
     (* MMAP_I *)     (!:'a. MMAP(unit,bind) (I:'a -> 'a) = I) /\
     (* MMAP_o *)     (!:'a 'b 'c. !(f:'a -> 'b) (g:'b -> 'c).
                            MMAP(unit,bind) (g o f) = MMAP(unit,bind) g o MMAP(unit,bind) f) /\
     (* MMAP_unit *)  (!:'a 'b. !f:'a -> 'b.
                            MMAP(unit,bind) f o unit = unit o f) /\
     (* MMAP_JOIN *)  (!:'a 'b. !f:'a -> 'b.
                            MMAP(unit,bind) f o JOIN(unit,bind) =
                            JOIN(unit,bind) o MMAP(unit,bind) (MMAP(unit,bind) f)) /\
     (* JOIN_unit *) (!:'a. JOIN(unit,bind) o unit = (I:'a 'M -> 'a 'M)) /\
     (* JOIN_MMAP_unit *)
                     (!:'a. JOIN(unit,bind) o MMAP(unit,bind) unit = (I:'a 'M -> 'a 'M)) /\
     (* JOIN_MMAP_JOIN *)
                     (!:'a. (JOIN(unit,bind) :'a 'M 'M -> 'a 'M) o MMAP(unit,bind) (JOIN(unit,bind)) =
                            JOIN(unit,bind) o JOIN(unit,bind)) /\
     (* bind_EQ_JOIN_MMAP *)
                     (!:'a 'b. !m (k:'a -> 'b 'M).
                        bind m k = JOIN(unit,bind) (MMAP(unit,bind) k m))

     ==> monad(unit,bind)``,
   REWRITE_TAC[monad_def]
   THEN REPEAT STRIP_TAC
   THENL
     [ FULL_SIMP_TAC bool_ss [FUN_EQ_THM,o_THM,I_THM,ETA_AX],

       FULL_SIMP_TAC bool_ss [FUN_EQ_THM,o_THM,I_THM,ETA_AX],

       POP_ASSUM (fn th => REWRITE_TAC[CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV[GSYM o_THM]))
                                                      (SPEC_ALL (TY_SPEC_ALL th))])
       THEN CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM o_THM])))
       THEN CONV_TAC (RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM o_THM])))))
       THEN REWRITE_TAC[ETA_AX]
       THEN ASM_REWRITE_TAC[o_ASSOC]
       THEN REWRITE_TAC[GSYM o_ASSOC]
       THEN CONV_TAC (RAND_CONV (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV[o_ASSOC]))))
       THEN REWRITE_TAC[GSYM (ASSUME ``!:'a 'b. !(f:'a -> 'b).
              MMAP (unit:'M unit,bind:'M bind) f o JOIN (unit,bind) =
              JOIN (unit,bind) o MMAP (unit,bind) (MMAP (unit,bind) f)``)]
       THEN REWRITE_TAC[o_ASSOC]
     ]
  );

val monad_IMP_laws = store_thm
  ("monad_IMP_laws",
   ``!:'M. !(unit:'M unit) (bind:'M bind).
     monad(unit,bind) ==>
     (* MMAP_I *)     (!:'a. MMAP(unit,bind) (I:'a -> 'a) = I) /\
     (* MMAP_o *)     (!:'a 'b 'c. !(f:'a -> 'b) (g:'b -> 'c).
                            MMAP(unit,bind) (g o f) = MMAP(unit,bind) g o MMAP(unit,bind) f) /\
     (* MMAP_unit *)  (!:'a 'b. !f:'a -> 'b.
                            MMAP(unit,bind) f o unit = unit o f) /\
     (* MMAP_JOIN *)  (!:'a 'b. !f:'a -> 'b.
                            MMAP(unit,bind) f o JOIN(unit,bind) =
                            JOIN(unit,bind) o MMAP(unit,bind) (MMAP(unit,bind) f)) /\
     (* JOIN_unit *) (!:'a. JOIN(unit,bind) o unit = (I:'a 'M -> 'a 'M)) /\
     (* JOIN_MMAP_unit *)
                     (!:'a. JOIN(unit,bind) o MMAP(unit,bind) unit = (I:'a 'M -> 'a 'M)) /\
     (* JOIN_MMAP_JOIN *)
                     (!:'a. (JOIN(unit,bind) :'a 'M 'M -> 'a 'M) o MMAP(unit,bind) (JOIN(unit,bind)) =
                            JOIN(unit,bind) o JOIN(unit,bind)) /\
     (* bind_EQ_JOIN_MMAP *)
                     (!:'a 'b. !m (k:'a -> 'b 'M).
                        bind m k = JOIN(unit,bind) (MMAP(unit,bind) k m))
   ``,
   SRW_TAC[][FUN_EQ_THM,monad_def,MMAP_def,JOIN_def,ETA_AX]
  );

val monad_EQ_monad_umj = store_thm
  ("monad_EQ_monad_umj",
   ``!:'M. !(unit:'M unit) (bind:'M bind).
     monad(unit,bind) =
     monad_umj(unit, (\:'a 'b. MMAP(unit,bind)):'M map, \:'a. JOIN(unit,bind)) /\
        (!:'a 'b. !(m:'a 'M) (k:'a -> 'b 'M).
                        (bind :'M bind) m k = JOIN (unit,bind) (MMAP (unit,bind) k m))``,
   REPEAT STRIP_TAC
   THEN REWRITE_TAC[monad_umj_def]
   THEN EQ_TAC
   THENL [ SRW_TAC[][monad_IMP_laws],
           SRW_TAC[][laws_IMP_monad]
         ]
  );

val o_LEMMA = TAC_PROOF(([],
   ``(!(f:'b -> 'c) (g:'a -> 'b). (\x. f (g x)) = f o g) /\
     (!(f:'b -> 'c) (g:'a -> 'b) (h:'z -> 'a). (\x. f (g (h x))) = f o g o h)``),
   SRW_TAC[][FUN_EQ_THM]
  );

val monad_umj_IMP_monad = store_thm
  ("monad_umj_IMP_monad",
   ``!:'M. !(unit:'M unit) (map:'M map) (join:'M join).
     monad_umj(unit,map,join) ==>
     monad(unit, \:'a 'b. BIND(map,join))``,
   REWRITE_TAC[monad_umj_def]
   THEN REPEAT STRIP_TAC
   THEN SRW_TAC[][monad_def,BIND_def]
   THENL
     [ CONV_TAC (RATOR_CONV (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM o_THM]))))
       THEN ASM_REWRITE_TAC[]
       THEN CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM o_THM])))
       THEN ASM_REWRITE_TAC[o_ASSOC,I_o_ID],

       CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM o_THM])))
       THEN ASM_REWRITE_TAC[o_ASSOC,I_THM],

       CONV_TAC (RAND_CONV (RAND_CONV (RATOR_CONV (RAND_CONV (ABS_CONV
                     (RAND_CONV (ONCE_REWRITE_CONV[GSYM o_THM])))))))
       THEN CONV_TAC (RAND_CONV (RAND_CONV (RATOR_CONV (RAND_CONV (ABS_CONV
                     (ONCE_REWRITE_CONV[GSYM o_THM]))))))
       THEN REWRITE_TAC[ETA_AX]
       THEN CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM o_THM]))
       THEN CONV_TAC (RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM o_THM])))))
       THEN CONV_TAC (RATOR_CONV (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM o_THM]))))
       THEN CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM o_THM])))
       THEN ASM_REWRITE_TAC[o_ASSOC]
       THEN CONV_TAC (RAND_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM o_ASSOC])))))
       THEN REWRITE_TAC[GSYM (ASSUME
       ``!:'a 'b. !f:'a -> 'b. (map:'M map) f o (join:'M join) = join o map (map f)``)]
       THEN REWRITE_TAC[o_ASSOC]
     ]
  );

val BIND_LEMMA = TAC_PROOF(([],
   ``(!(unit:'M unit) (map:'M map) (join:'M join).
      monad(unit, \:'a 'b. BIND(map,join)) ==>
      !:'a 'b. !(m:'a 'M) (k:'a -> 'b 'M).
      (\:'a 'b. BIND(map,join)) [:'a,'b:] m k =
      JOIN (unit,\:'a 'b. BIND(map,join)) (MMAP (unit,\:'a 'b. BIND(map,join)) k m))``),
   SRW_TAC[][monad_def,FUN_EQ_THM,JOIN_BIND,MMAP_BIND,BIND_def,ETA_AX]
  );


(*---------------------------------------------------------------------------
            Examples of Monads
 ---------------------------------------------------------------------------*)


val identity_monad = store_thm
  ("identity_monad",
   ``monad ((\:'a. I) : I unit, \:'a 'b. \(x:'a I) (f:'a -> 'b I). f x)``,
   REWRITE_TAC[monad_def]
   THEN TY_BETA_TAC
   THEN BETA_TAC
   THEN REWRITE_TAC[combinTheory.I_THM]
  );

val option_monad = store_thm
  ("option_monad",
   ``monad ((\:'a. SOME) : option unit,
            \:'a 'b. \(x:'a option) (f:'a -> 'b option). case x of NONE -> NONE || SOME (y:'a) -> f y)``,
   REWRITE_TAC[monad_def]
   THEN TY_BETA_TAC
   THEN REPEAT STRIP_TAC
   THEN SRW_TAC[][]
   THEN CASE_TAC
  );


val FLAT_APPEND = store_thm
  ("FLAT_APPEND",
   ``!(s:'a list list) t. FLAT (s ++ t) = FLAT s ++ FLAT t``,
   Induct
   THEN SRW_TAC[][listTheory.FLAT]
  );

val list_monad = store_thm
  ("list_monad",
   ``monad ((\:'a. \x:'a. [x]) : list unit,
            \:'a 'b. \(x:'a list) (f:'a -> 'b list). FLAT (MAP f x))``,
   REWRITE_TAC[monad_def]
   THEN TY_BETA_TAC
   THEN REPEAT STRIP_TAC
   THEN SRW_TAC[][]
   THENL [ Induct_on `m`
           THEN SRW_TAC[][listTheory.FLAT],

           Induct_on `m`
           THEN SRW_TAC[][listTheory.FLAT, FLAT_APPEND]
         ]
  );

local open stringTheory in end;

val _ = Hol_datatype `error = OK of 'a | FAIL of string`;

val error_11        = theorem "error_11"
val error_distinct  = theorem "error_distinct"
val error_case_cong = theorem "error_case_cong"
val error_nchotomy  = theorem "error_nchotomy"
val error_Axiom     = theorem "error_Axiom"
val error_induction = theorem "error_induction"

val error_monad = store_thm
  ("error_monad",
   ``monad ((\:'a. OK) : error unit,
            \:'a 'b. \(e:'a error) (f:'a -> 'b error).
                         case e of OK x -> f x
                                || FAIL s -> FAIL s)``,
   SRW_TAC[][monad_def]
   THEN CASE_TAC
  );

val _ = Hol_datatype `writer = RESULT of string => 'a`;

val writer_11        = theorem "writer_11"
(*val writer_distinct  = theorem "writer_distinct"*)
val writer_case_cong = theorem "writer_case_cong"
val writer_nchotomy  = theorem "writer_nchotomy"
val writer_Axiom     = theorem "writer_Axiom"
val writer_induction = theorem "writer_induction"

val writer_monad = store_thm
  ("writer_monad",
   ``monad ((\:'a. \x:'a. RESULT "" x) : writer unit,
            \:'a 'b. \(w:'a writer) (f:'a -> 'b writer).
                         case w of RESULT s x -> case f x of RESULT s' y -> RESULT (STRCAT s s') y)``,
   SRW_TAC[][monad_def]
   THEN REPEAT CASE_TAC
   THEN REWRITE_TAC[stringTheory.STRCAT_ASSOC]
  );

(*
val _ = type_abbrev ("reader", Type `: 'a fun`);
``:'a fun``;

val reader_monad = store_thm
  ("reader_monad",
   ``monad ((\:'a. \x:'a. K x) : !'a.'a -> 'a reader)
           (\:'a 'b. \(r:'a reader) (f:'a -> 'b reader). S r f)``,
   SRW_TAC[][monad_def]
   THEN REPEAT CASE_TAC
   THEN REWRITE_TAC[stringTheory.STRCAT_ASSOC]
  );
*)

(*
val _ = Hol_datatype `state = ST of 'S -> 'a # 'S`;

val STFun_def = Define `STFun (ST (f:'s -> 'a # 's)) = f`;

val state_11        = theorem "state_11"
(*val state_distinct  = theorem "state_distinct"*)
val state_case_cong = theorem "state_case_cong"
val state_nchotomy  = theorem "state_nchotomy"
val state_Axiom     = theorem "state_Axiom"
val state_induction = theorem "state_induction"

val ST_STFun = store_thm
  ("ST_STFun",
   ``!x: ('s,'a)state. ST (STFun x) = x``,
   Induct
   THEN REWRITE_TAC[STFun_def]
  );

val state_unit_def = Define
   `state_unit (x:'a) = ST (\s:'s. (x,s))`;

val state_bind_def = Define
   `state_bind (w:('s,'a)state) (f:'a -> ('s,'b)state) =
         ST (\s. let (x,s') = STFun w s in STFun (f x) s')`;
*)

val pair_case_id = store_thm
  ("pair_case_id",
   ``!x:'a # 'b. (case x of (a,b) -> (a,b)) = x``,
   Cases
   THEN SRW_TAC[][]
  );

val pair_let_id = store_thm
  ("pair_let_id",
   ``!M. (let (x:'a,y:'b) = M in (x,y)) = M``,
   Cases
   THEN SRW_TAC[][]
  );

val _ = type_abbrev ("state", Type `: \'s 'a. 's -> 'a # 's`);

val state_unit_def = Define
   `state_unit (x:'a) = \s:'s. (x,s)`;

val state_bind_def = Define
   `state_bind (w:('s,'a)state) (f:'a -> ('s,'b)state) =
         \s. let (x,s') = w s in f x s'`;

val _ = new_infix(">>=", ``:'a -> ('a -> 'b) -> 'b``, 450);

val _ = overload_on(">>=", ``state_bind : ('s,'a)state -> ('a -> ('s,'b)state) -> ('s,'b)state``);

val state_monad = store_thm
  ("state_monad",
   ``monad ((\:'a. state_unit) : 's state unit,
            \:'a 'b. state_bind)``,
   SRW_TAC[][monad_def,state_unit_def,state_bind_def,FUN_EQ_THM]
   THEN POP_ASSUM MP_TAC
   THEN ASM_SIMP_TAC std_ss []
  );

val [state_monad_left_unit,
     state_monad_right_unit,
     state_monad_assoc] = CONJUNCTS (SIMP_RULE bool_ss [monad_def] state_monad);

(* Define MAP (functor) for state monad in standard way using unit and bind: *)

val state_MAP_def = Define
   `(state_MAP : ('a -> 'b) -> ('s,'a)state -> ('s,'b)state) =
      MMAP ((\:'a. state_unit),(\:'a 'b. state_bind))`;

val state_MAP_THM = store_thm
  ("state_MAP_THM",
   ``state_MAP (f:'a -> 'b) (m : ('s,'a)state) = state_bind m (\a. state_unit (f a))``,
   SIMP_TAC bool_ss [state_MAP_def,MMAP_def]
  );

(* Define JOIN for state monad in standard way using unit and bind: *)

val state_JOIN_def = Define
   `(state_JOIN : 'a ('s state) ('s state) -> 'a ('s state)) =
      JOIN ((\:'a. state_unit),(\:'a 'b. state_bind))`;

val state_JOIN_THM = store_thm
  ("state_JOIN_THM",
   ``state_JOIN (z : 'a ('s state) ('s state)) = state_bind z I``,
   SIMP_TAC bool_ss [state_JOIN_def,JOIN_def,I_EQ]
  );

val state_MAP_functor = store_thm
  ("state_MAP_functor",
   ``functor ((\:'a 'b. state_MAP) : ('s state) functor)``,
   SIMP_TAC bool_ss [state_monad,state_MAP_def,MMAP_functor]
  );

val state_JOIN_nattransf = store_thm
  ("state_JOIN_nattransf",
   ``nattransf ((\:'a 'b. state_MAP o state_MAP) : ('s state o 's state) functor)
               ((\:'a 'b. state_MAP)             : 's state functor)
               ((\:'a.    state_JOIN)            : 's state join)``,
   SIMP_TAC bool_ss [state_monad,state_MAP_def,state_JOIN_def,JOIN_nattransf]
  );

val state_unit_nattransf = store_thm
  ("state_unit_nattransf",
   ``nattransf ((\:'a 'b. I)          :  I functor)
               ((\:'a 'b. state_MAP)  : 's state functor)
               ((\:'a.    state_unit) : 's state unit)``,
   SIMP_TAC bool_ss [state_monad,state_MAP_def,unit_nattransf]
  );

val [state_MAP_I, state_MAP_o, state_MAP_unit, state_MAP_JOIN,
     state_JOIN_unit, state_JOIN_MAP_unit, state_JOIN_MAP_JOIN,
     state_bind_EQ_JOIN_MAP
    ] = CONJUNCTS (SIMP_RULE bool_ss [monad_EQ_monad_umj,monad_umj_def,
                                      GSYM state_MAP_def, GSYM state_JOIN_def] state_monad);

val state_MAP_I = save_thm
  ("state_MAP_I",
    state_MAP_I
  );

val state_MAP_o = save_thm
  ("state_MAP_o",
    state_MAP_o
  );

val state_MAP_unit = save_thm
  ("state_MAP_unit",
    state_MAP_unit
  );

val state_MAP_JOIN = save_thm
  ("state_MAP_JOIN",
    state_MAP_JOIN
  );

val state_JOIN_unit = save_thm
  ("state_JOIN_unit",
    state_JOIN_unit
  );

val state_JOIN_MAP_unit = save_thm
  ("state_JOIN_MAP_unit",
    state_JOIN_MAP_unit
  );

val state_JOIN_MAP_JOIN = save_thm
  ("state_JOIN_MAP_JOIN",
    state_JOIN_MAP_JOIN
  );

val state_bind_EQ_JOIN_MAP = save_thm
  ("state_bind_EQ_JOIN_MAP",
    state_bind_EQ_JOIN_MAP
  );

val state_functor = store_thm
  ("state_functor",
   ``functor ((\:'a 'b. state_MAP) : ('s state)functor)``,
   SRW_TAC[][functor_def,state_MAP_I,state_MAP_o]
  );


(*---------------------------------------------------------------------------
            Monad type operator, with unit and bind term operators
            on a constant type, not 'a
 ---------------------------------------------------------------------------*)


val monadc_def = new_definition("monadc_def", Term
   `monadc (unit: 'a -> 'a 'M)
           (bind: !'b. 'a 'M -> ('a -> 'b 'M) -> 'b 'M) =
      (* Left unit *)
          (!:'b. !(a:'a) (k:'a -> 'b 'M).
                bind[:'b:] (unit a) k = k a) /\
      (* Right unit *)
          (!(m:'a 'M).
                bind[:'a:] m unit = m) /\
      (* Associative *)
          (!:'b. !(m:'a 'M) (k:'a -> 'a 'M) (h:'a -> 'b 'M).
                bind[:'b:] m (\a. bind[:'b:] (k a) h)
              = bind[:'b:] (bind[:'a:] m k) h)
     `) handle e => Raise e;


(*---------------------------------------------------------------------------
            Monad type operator, with unit and bind term operators
            from and to constant types, not 'a or 'b
 ---------------------------------------------------------------------------*)


val monadc2_def = new_definition("monadc2_def", Term
   `monadc2 (unit: 'a -> 'b)
            (bind: 'b -> ('a -> 'b) -> 'b) =
      (* Left unit *)
          (!(a:'a) (k:'a -> 'b).
                bind (unit a) k = k a) /\
      (* Right unit *)
          (!(m:'b).
                bind m unit = m) /\
      (* Associative *)
          (!(m:'b) (k:'a -> 'b) (h:'a -> 'b).
                bind m (\a. bind (k a) h)
              = bind (bind m k) h)
     `) handle e => Raise e;



val _ = html_theory "monad";

val _ = export_theory();

end; (* structure monadScript *)

