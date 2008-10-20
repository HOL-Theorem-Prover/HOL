open bossLib parmonadsyntax
val _ = type_abbrev("M", ``:num list -> 'a # num list``)

val _ = temp_overload_on (monad_bind, ``BIND``)
val _ = temp_overload_on ("return", ``UNIT``)


(* not really parallel at all *)
val par_def = new_definition("par_def",
  ``par (f : 'a -> ('b # 'a)) (g : 'a -> ('c # 'a)) =
      do x <- f ; y <- g; return (x,y) od
  ``);

val _ = temp_overload_on (monad_par, ``par``)

val len_def = Define`
  (len : num M) x = (LENGTH x, x)
`;

val hd_def = Define`
  (hd : num option M) x = case x of [] -> (NONE, x) || h::t -> (SOME h, x)
`;

val cons_def = Define`
  cons x l = ((), x::l)
`;

val sum_def = Define`sum l = (SUM l, l)`

val prog = ``do
    x <- hd !! y <- len ;
    case x of NONE -> return ()
           || SOME h -> cons h ;
    cons y ;
    s <- sum ;
    cons s
  od``

val eval = SIMP_CONV (srw_ss()) [state_transformerTheory.BIND_DEF,
                                 state_transformerTheory.UNIT_DEF,
                                 par_def, len_def, hd_def, cons_def, sum_def]

val result_nil = eval ``^prog []``
val result_onethree = eval ``^prog [1;3]``

(* note error messages; not great *)
val failprog1 = ``do len ; cons x od``
val failprog2 = ``do x <- len !! hd ; cons x od``

val ignore_def = Define`
  ignore M = do x <- M ; return () od
`;

val prog2_revised = ``do x <- len !! ignore hd ; cons x od``;
