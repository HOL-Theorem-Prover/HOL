(*---------------------------------------------------------------------------
                         Monads in HOL-Omega
                       (Peter Vincent Homeier)
 ---------------------------------------------------------------------------*)

structure monadScript =
struct

(*
app load ["stringTheory","functorTheory"];
*)

open HolKernel Parse boolLib
     bossLib

open combinTheory functorTheory;

val _ = set_trace "Unicode" 1;
val _ = set_trace "kinds" 0;


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

(*---------------------------------------------------------------------------
            Monad predicate, on unit, map and join term operators
 ---------------------------------------------------------------------------*)
val _ = set_trace "debug_type_inference" 0;
val umj_monad_def = new_definition(
   "umj_monad_def",
   ``umj_monad (unit: 'M unit,
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
   `MMAP (unit: 'M unit, bind: 'M bind) = \:'a 'b. \(f:'a -> 'b) (m : 'a 'M).
                      bind m (\a. unit (f a))`;

val JOIN_def = Define
   `JOIN (unit: 'M unit, bind: 'M bind) = \:'a. \(z : 'a 'M 'M).
                      bind z I`;


(*---------------------------------------------------------------------------
            Monad bind operation,
            defined in terms of map and join
 ---------------------------------------------------------------------------*)

val BIND_def = Define
   `BIND (map: 'M map, join: 'M join) = \:'a 'b. \(m : 'a 'M) (k:'a -> 'b 'M).
                      join (map k m)`;

val MMAP_BIND = store_thm
  ("MMAP_BIND",
   ``!:'M. !(unit:'M unit) (map:'M map) (join:'M join).
     MMAP(unit,BIND(map,join)) = \:'a 'b. \(f:'a -> 'b) (m : 'a 'M). BIND(map,join) m (\a. unit (f a))``,
   SRW_TAC[][FUN_EQ_THM,MMAP_def]
  );

val JOIN_BIND = store_thm
  ("JOIN_BIND",
   ``!:'M. !(unit:'M unit) (map:'M map) (join:'M join).
     JOIN(unit,BIND(map,join)) = \:'a. \(z : 'a 'M 'M). BIND(map,join) z I``,
   SRW_TAC[][FUN_EQ_THM,JOIN_def]
  );

(*---------------------------------------------------------------------------
            Monad laws
 ---------------------------------------------------------------------------*)

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
     (* bind_EQ_BIND_JOIN_MMAP *)
                     (bind = BIND(MMAP(unit,bind), JOIN(unit,bind)))
   ``,
   SRW_TAC[][TY_FUN_EQ_THM,FUN_EQ_THM,monad_def,MMAP_def,JOIN_def,BIND_def,ETA_AX]
  );

val [MMAP_I, MMAP_o, MMAP_unit, MMAP_JOIN, JOIN_unit,
     JOIN_MMAP_unit, JOIN_MMAP_JOIN, bind_EQ_BIND_JOIN_MMAP] =
  (map (TY_GEN_ALL o GEN_ALL o DISCH_ALL) o
   CONJUNCTS o UNDISCH_ALL o SPEC_ALL o TY_SPEC_ALL) monad_IMP_laws;

val _ = save_thm("MMAP_I",MMAP_I);
val _ = save_thm("MMAP_o",MMAP_o);
val _ = save_thm("MMAP_unit",MMAP_unit);
val _ = save_thm("MMAP_JOIN",MMAP_JOIN);
val _ = save_thm("JOIN_unit",JOIN_unit);
val _ = save_thm("JOIN_MMAP_unit",JOIN_MMAP_unit);
val _ = save_thm("JOIN_MMAP_JOIN",JOIN_MMAP_JOIN);
val _ = save_thm("bind_EQ_BIND_JOIN_MMAP",bind_EQ_BIND_JOIN_MMAP);

val monad_IMP_umj_monad = store_thm
  ("monad_IMP_umj_monad",
   ``!:'M. !(unit:'M unit) (bind:'M bind).
     monad(unit,bind) ==>
     umj_monad(unit, (MMAP(unit,bind)):'M map, JOIN(unit,bind)) /\
     (bind = BIND(MMAP(unit,bind), JOIN(unit,bind)))``,
   REWRITE_TAC[umj_monad_def,GSYM CONJ_ASSOC]
   THEN TY_BETA_TAC
   THEN TY_GEN_TAC
   THEN MATCH_ACCEPT_TAC monad_IMP_laws
  );

val o_LEMMA = TAC_PROOF(([],
   ``(!(f:'b -> 'c) (g:'a -> 'b). (\x. f (g x)) = f o g) /\
     (!(f:'b -> 'c) (g:'a -> 'b) (h:'z -> 'a). (\x. f (g (h x))) = f o g o h)``),
   SRW_TAC[][FUN_EQ_THM]
  );

(*---------------------------------------------------------------------------
  The following proof of umj_monad_IMP_monad is due to Jeremy Dawson,
  who correctly noted that the theorem could be strengthened to include
  conclusions equating the map and join parameters with those derivable
  from MAP and JOIN, where the bind parameter to each of these is derived
  from BIND on map and join.  This is a clear improvement over the original.
 ---------------------------------------------------------------------------*)

val umj_monad_IMP_map_eq = store_thm ("umj_monad_IMP_map_eq",
  ``!:'M. !(unit:'M unit) (map:'M map) (join:'M join).
     umj_monad(unit,map,join) ==>
     (map = MMAP (unit, BIND (map, join)))``,
  SRW_TAC [] [MMAP_def, BIND_def, umj_monad_def, o_DEF, FUN_EQ_THM, TY_FUN_EQ_THM]) ;

val umj_monad_IMP_join_eq = store_thm ("umj_monad_IMP_join_eq",
  ``!:'M. !(unit:'M unit) (map:'M map) (join:'M join).
     umj_monad(unit,map,join) ==>
     (join = JOIN (unit, BIND (map, join)))``,
  SRW_TAC [] [JOIN_def, BIND_def, umj_monad_def, o_DEF, FUN_EQ_THM, TY_FUN_EQ_THM]) ;

val (umj_monadD, _) = EQ_IMP_RULE (SPEC_ALL umj_monad_def) ;
val [umjD1, umjD2, umjD3, umjD4, umjD5, umjD6, umjD7] =
  CONJUNCTS (UNDISCH umj_monadD) ;

val umj_monad_IMP_monad_bis = store_thm ("umj_monad_IMP_monad_bis",
  ``!:'M. !(unit:'M unit) (map:'M map) (join:'M join).
    umj_monad(unit,map,join) ==>
    monad(unit, BIND(map,join))``,
  SRW_TAC [] [monad_def, BIND_def]
    THENL [
      MAP_EVERY MP_TAC [umjD3, umjD5],
      MP_TAC umjD6,
      MAP_EVERY MP_TAC [umjD4, GSYM umjD7, GSYM umjD2]]
    THEN SRW_TAC [] [o_DEF, FUN_EQ_THM, I_THM]) ;

val umj_monad_IMP_monad = store_thm
  ("umj_monad_IMP_monad",
   ``!:'M. !(unit:'M unit) (map:'M map) (join:'M join).
     umj_monad(unit,map,join) ==>
     monad(unit, BIND(map,join)) /\
     (map = MMAP (unit, BIND (map, join))) /\
     (join = JOIN (unit, BIND (map, join)))``,
   REPEAT STRIP_TAC
   THENL [ MATCH_MP_TAC umj_monad_IMP_monad_bis,
           MATCH_MP_TAC umj_monad_IMP_map_eq,
           MATCH_MP_TAC umj_monad_IMP_join_eq ]
   THEN FIRST_ASSUM ACCEPT_TAC
  );

(* The following is like the last of the laws in monad_IMP_laws,
   namely bind_EQ_BIND_MMAP_JOIN, but with BIND expanded by its definition.
   It is useful to deserve its own theorem.                                 *)

val BIND_THM = store_thm
  ("BIND_THM",
   ``(!(unit:'M unit) (bind:'M bind).
      monad(unit, bind) ==>
      !:'a 'b. !(m :'a 'M) (k :'a -> 'b 'M).
      bind [:'a,'b:] m k = JOIN (unit,bind) (MMAP (unit,bind) k m))``,
   SRW_TAC[][monad_def,FUN_EQ_THM,JOIN_def,MMAP_def,ETA_AX]
  );

val monad_EQ_umj_monad = store_thm
  ("monad_EQ_umj_monad",
   ``!:'M. !(unit:'M unit) (bind:'M bind).
     monad(unit,bind) =
     umj_monad(unit, (MMAP(unit,bind)):'M map, JOIN(unit,bind)) /\
     (bind = BIND(MMAP(unit,bind), JOIN(unit,bind)))``,
   REPEAT STRIP_TAC
   THEN EQ_TAC
   THENL [ MATCH_ACCEPT_TAC monad_IMP_umj_monad,

           STRIP_TAC
           THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC[th])
           THEN IMP_RES_TAC umj_monad_IMP_monad
         ]
  );

val umj_monad_EQ_monad = store_thm
  ("umj_monad_EQ_monad",
   ``!:'M. !(unit:'M unit) (map:'M map) (join:'M join).
     umj_monad(unit,map,join) =
     monad(unit, BIND(map,join)) /\
     (map  = MMAP (unit,BIND (map,join))) /\
     (join = JOIN (unit,BIND (map,join)))``,
   REPEAT STRIP_TAC
   THEN EQ_TAC
   THENL [ MATCH_ACCEPT_TAC umj_monad_IMP_monad,

           STRIP_TAC
	   THEN (FIRST_X_ASSUM (MP_TAC o MATCH_MP monad_IMP_umj_monad))
	   THEN (POP_ASSUM_LIST (fn ths => REWRITE_TAC (map SYM ths)))
         ]
  );

val umj_monad_IFF_monad = store_thm
  ("umj_monad_IFF_monad",
  ``!:'M. !(unit:'M unit) (map:'M map) (join:'M join) (bind : 'M bind).
      umj_monad(unit,map,join) /\ (bind = BIND (map, join)) =
      monad(unit, bind) /\ 
        (map = MMAP (unit, bind)) /\ (join = JOIN (unit, bind))``,
  EVERY [ (REPEAT STRIP_TAC), EQ_TAC, STRIP_TAC, (ASM_REWRITE_TAC []) ]
  THENL
    [ (FIRST_ASSUM (ACCEPT_TAC o MATCH_MP umj_monad_IMP_monad)),
      (FIRST_ASSUM (ACCEPT_TAC o MATCH_MP monad_IMP_umj_monad)) ]) ;


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
            \:'a 'b. \(x:'a option) (f:'a -> 'b option). case x of NONE => NONE | SOME (y:'a) => f y)``,
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
                         case e of OK x => f x
                                 | FAIL s => FAIL s)``,
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
                         case w of RESULT s x => case f x of RESULT s' y => RESULT (STRCAT s s') y)``,
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

val pair_case_id = store_thm
  ("pair_case_id",
   ``!x:'a # 'b. (case x of (a,b) => (a,b)) = x``,
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
   `state_unit = \:'a. \(x:'a) (s:'s). (x,s)`;

(*
val state_bind_def = new_infixr_definition("state_bind",
    ``$>>= = \:'a 'b. \(w:('s,'a)state) (f:'a -> ('s,'b)state) s.
                           let (x,s') = w s in f x s'``,
    460);
*)

val state_bind_def = new_definition("state_bind",
    ``state_bind = \:'a 'b. \(w:('s,'a)state) (f:'a -> ('s,'b)state) s.
                           let (x,s') = w s in f x s'``);

val _ = new_infix(">>=", ``:'s state bind``, 460);
val _ = overload_on(">>=", ``state_bind : 's state bind``);

val state_monad = store_thm
  ("state_monad",
   ``monad (state_unit : 's state unit,
            $>>=)``,
   SRW_TAC[][monad_def,state_unit_def,state_bind_def,FUN_EQ_THM]
   THEN POP_ASSUM MP_TAC
   THEN ASM_SIMP_TAC std_ss []
  );

val [state_monad_left_unit,
     state_monad_right_unit,
     state_monad_assoc] = CONJUNCTS (SIMP_RULE bool_ss [monad_def] state_monad);

(* Define MAP (functor) for state monad in standard way using unit and bind: *)

val state_map_def = Define
   `(state_map : 's state map) = MMAP (state_unit,$>>=)`;

val state_map_THM = store_thm
  ("state_map_THM",
   ``state_map (f:'a -> 'b) (m : ('s,'a)state) = m >>= (\a. state_unit (f a))``,
   SIMP_TAC bool_ss [state_map_def,MMAP_def]
  );

(* Define JOIN for state monad in standard way using unit and bind: *)

val state_join_def = Define
   `(state_join : 's state join) = JOIN (state_unit,$>>=)`;

val state_join_THM = store_thm
  ("state_join_THM",
   ``state_join (z : 'a ('s state) ('s state)) = z >>= I``,
   SIMP_TAC bool_ss [state_join_def,JOIN_def,I_EQ]
  );

val [state_map_I, state_map_o, state_map_unit, state_map_join,
     state_join_unit, state_join_map_unit, state_join_map_join,
     state_bind_EQ_join_map
    ] = CONJUNCTS (SIMP_RULE bool_ss [monad_EQ_umj_monad,umj_monad_def,
                                      GSYM state_map_def, GSYM state_join_def] state_monad);

val state_map_I            = save_thm("state_map_I",            state_map_I);
val state_map_o            = save_thm("state_map_o",            state_map_o);
val state_map_unit         = save_thm("state_map_unit",         state_map_unit);
val state_map_join         = save_thm("state_map_join",         state_map_join);
val state_join_unit        = save_thm("state_join_unit",        state_join_unit);
val state_join_map_unit    = save_thm("state_join_map_unit",    state_join_map_unit);
val state_join_map_join    = save_thm("state_join_map_join",    state_join_map_join);
val state_bind_EQ_join_map = save_thm("state_bind_EQ_join_map", state_bind_EQ_join_map);

val state_functor = store_thm
  ("state_functor",
   ``functor (state_map : ('s state)functor)``,
   SRW_TAC[][functor_def,state_map_I,state_map_o]
  );


(*---------------------------------------------------------------------------
            Another definition of monads, arising from category theory:

   "A monad consists of a category A, a functor t : A -> A,
   and natural transformations mu : t^2 -> t and eta : 1_A -> t
   satisfying three equations, as expressed by the commutative diagrams

                 t mu                    t eta         eta t
           t^3 -------> t^2           t -------> t^2 <------- t
            |            |              \         |         /
       mu t |            | mu             \       |mu     /
            |            |                1 \     |     /   1
            V            V                    \   V   /
           t^2 ------->  t                      > t < ."
                  mu

   (From "The formal theory of monads II" by Stephen Lack and Ross Street.)
   In the diagrams above, the nodes are functors, and the arrows are
   natural transformations.
 ---------------------------------------------------------------------------*)

val cat_monad_def = new_definition(
   "cat_monad_def",
   ``cat_monad (t  :           'M  functor  ,
                mu : ('M o 'M, 'M) nattransf,
                eta: (   I   , 'M) nattransf) =
     (*   t is functor     (map) *)  functor t /\
     (*  mu is nat transf (join) *)  nattransf mu (t oo t) t /\
     (* eta is nat transf (unit) *)  nattransf eta (\:'a 'b. I) t /\
     (*         square commutes  *) (mu ooo (t foo mu) = mu ooo (mu oof t)) /\
     (*  left triangle commutes  *) (mu ooo (t foo eta) = (\:'a. I)) /\
     (* right triangle commutes  *) (mu ooo (eta oof t) = (\:'a. I))
   ``);

val umj_map_functor = store_thm
  ("umj_map_functor",
   ``!unit map join.
      umj_monad(unit,map,join) ==>
      functor (map : 'M functor)``,
   SRW_TAC[][umj_monad_def,functor_def,FUN_EQ_THM,ETA_AX]
  );

val umj_join_nattransf = store_thm
  ("umj_join_nattransf",
   ``!unit map join.
      umj_monad(unit,map,join) ==>
      nattransf (join         : 'M join)
                ((map oo map) : ('M o 'M) functor)
                (map          : 'M functor)``,
   SRW_TAC[][umj_monad_def,nattransf_def,oo_def,FUN_EQ_THM]
  );

val umj_unit_nattransf = store_thm
  ("umj_unit_nattransf",
   ``!unit map join.
      umj_monad(unit,map,join) ==>
      nattransf (unit         : 'M unit)
                ((\:'a 'b. I) :  I functor)
                (map          : 'M functor)``,
   SRW_TAC[][umj_monad_def,nattransf_def,FUN_EQ_THM]
  );

val map_2_functor = store_thm
  ("map_2_functor",
   ``!unit (map:'M map) join.
      umj_monad(unit,map,join) ==>
      functor (map oo map)``,
   REPEAT STRIP_TAC
   THEN REWRITE_TAC[oo_def]
   THEN HO_MATCH_MP_TAC functor_o
   THEN IMP_RES_TAC umj_map_functor
   THEN ASM_REWRITE_TAC[]
  );

val map_3_functor = store_thm
  ("map_3_functor",
   ``!unit (map:'M map) join.
      umj_monad(unit,map,join) ==>
      functor (map oo map oo map)``,
   REPEAT STRIP_TAC
   THEN IMP_RES_TAC umj_map_functor
   THEN IMP_RES_TAC functor_o
   THEN FULL_SIMP_TAC bool_ss [oo_def]
  );


val cat_monad_square = store_thm
  ("cat_monad_square",
   ``!(unit:'M unit) map join.
      umj_monad(unit,map,join) ==>
      (join ooo (map foo join) = join ooo (join oof map))``,
   SRW_TAC [] [umj_monad_def,ooo_def,foo_def,oof_def,TY_FUN_EQ_THM]
  );

val cat_monad_left_triangle = store_thm
  ("cat_monad_left_triangle",
   ``!(unit:'M unit) map join.
      umj_monad(unit,map,join) ==>
      (join ooo (map foo unit) = (\:'a. I))``,
   SRW_TAC [] [umj_monad_def,ooo_def,foo_def,TY_FUN_EQ_THM]
  );

val cat_monad_right_triangle = store_thm
  ("cat_monad_right_triangle",
   ``!(unit:'M unit) map join.
      umj_monad(unit,map,join) ==>
      (join ooo (unit oof map) = (\:'a. I))``,
   SRW_TAC [] [umj_monad_def,ooo_def,oof_def,TY_FUN_EQ_THM]
  );

val cat_monad_eq_umj_monad = store_thm
  ("cat_monad_eq_umj_monad",
   ``!(unit:'M unit) map join.
      cat_monad(map,join,unit) =
      umj_monad(unit,map,join)``,
   REPEAT STRIP_TAC
   THEN EQ_TAC
   THEN SRW_TAC [] [cat_monad_def,umj_monad_def,nattransf_def,functor_def,
                    ooo_def,foo_def,oof_def,oo_def,TY_FUN_EQ_THM]
  );


val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "monad";

val _ = export_theory();

end; (* structure monadScript *)

