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


val _ = new_theory "monad";


(*---------------------------------------------------------------------------
            Monad type operator, with unit and bind term operators
 ---------------------------------------------------------------------------*)


val monad_def = new_definition("monad_def", Term
   `monad (unit: !'a. 'a -> 'a 'M)
          (bind: !'a 'b. 'a 'M -> ('a -> 'b 'M) -> 'b 'M) =
      (* Left unit *)
          (!:'a 'b. !(a:'a) (k:'a -> 'b 'M).
                bind[:'a,'b:] (unit[:'a:] a) k = k a) /\
      (* Right unit *)
          (!:'a. !(m:'a 'M).
                bind[:'a,'a:] m (unit[:'a:]) = m) /\
      (* Associative *)
          (!:'a 'b 'c. !(m:'a 'M) (k:'a -> 'b 'M) (h:'b -> 'c 'M).
                bind[:'a,'c:] m (\a. bind[:'b,'c:] (k a) (\b. h b))
              = bind[:'b,'c:] (bind[:'a,'b:] m (\a. k a)) (\b. h b))
     `);

(*
val gl = ``monad ((\:'a. I) : !'a.'a -> 'a I) (\:'a 'b. \(x:'a I) (f:'a -> 'b I). f x)``;
set_goal([], gl);

e(PURE_REWRITE_TAC[monad_def]);
e(TY_BETA_TAC);
e(BETA_TAC);
e(REWRITE_TAC[combinTheory.I_THM]);

*)

val identity_monad = store_thm
  ("identity_monad",
   ``monad ((\:'a. I) : !'a.'a -> 'a I) (\:'a 'b. \(x:'a I) (f:'a -> 'b I). f x)``,
   REWRITE_TAC[monad_def]
   THEN TY_BETA_TAC
   THEN BETA_TAC
   THEN REWRITE_TAC[combinTheory.I_THM]
  );

val option_monad = store_thm
  ("option_monad",
   ``monad ((\:'a. SOME) : !'a.'a -> 'a option)
           (\:'a 'b. \(x:'a option) (f:'a -> 'b option). case x of NONE -> NONE || SOME (y:'a) -> f y)``,
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
   ``monad ((\:'a. \x:'a. [x]) : !'a.'a -> 'a list)
           (\:'a 'b. \(x:'a list) (f:'a -> 'b list). FLAT (MAP f x))``,
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

