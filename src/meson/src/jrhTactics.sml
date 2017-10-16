structure jrhTactics :> jrhTactics =
  struct
    open HolKernel boolLib liteLib;

    type Goal         = (thm list * term)
    type Goalstate    = Goal list * validation
    type Tactic       = Goal -> Goalstate
    type Thm_Tactic   = thm -> Tactic
    type Thm_Tactical = Thm_Tactic -> Thm_Tactic
    type refinement   = Goalstate -> Goalstate

    infix >- |->;
    fun (f >- g) x = g(f x);
    fun butlast l = #1(Lib.front_last l)
    val ERR = mk_HOL_ERR"jrhTactics";

    fun mk_Goalstate g = ([g], hd)
    nonfix by

    fun by t ([], _) = raise ERR  "by" "Can't apply tactic to empty Goal list"
      | by t (g::others, vf) =
          let val (newgs, vf1) = t g
          in (newgs @ others,
              fn thl =>
                let val (t_thms, rest) = Lib.split_after (length newgs) thl
                in vf (vf1 t_thms::rest)
                end)
          end


    local fun rotate_p1 ([], just) = ([], just)
            | rotate_p1 ((g::gs), just) =
                let val newgs = gs @ [g]
                    fun newj ths = just (last ths::butlast ths)
                in (newgs, newj)
                end
          fun rotate_n1 ([], just) = ([], just)
            | rotate_n1 (gs, just) =
                let val (newg, newgs) = (last gs, butlast gs)
                    fun newj (th::ths) = just (ths @ [th])
                      | newj _ = raise Bind
                in (newg::newgs, newj)
                end
    in
    fun rotate n =
      if n > 0 then funpow n rotate_p1
               else funpow (~n) rotate_n1
    end

    local
      (* the first parameter n is used to record the rotations performed
         on the state, so that once the tactic list has been exhausted
         the goal list can be put back into order *)
      fun bysn n [] g = rotate n g
        | bysn n (t::ts) (g as (gl,j)) =
          let val newg as (newgl,j') = by t g
              val k = length newgl + 1 - length gl
          in bysn (n - k) ts (rotate k newg)
          end
    in
    fun bys l = bysn 0 l
    end


    infix THENL
    fun (t1 THENL tlist) g = bys tlist (by t1 (mk_Goalstate g))

    infix THEN
    fun (t1 THEN t2) g =
      let val g as (gls, jf) = by t1 (mk_Goalstate g)
      in bys (replicate (t2, length gls)) g
      end

    fun convert (T:Tactic) ((asl:term list), (g:term)) =
      let val (gs, jf) = T (map ASSUME asl, g)
          val newgs = map (fn (asl, g) => (map concl asl, g)) gs
      in (newgs, jf)
      end

    fun hd1 ths =
        case ths of
          [x] => x
        | _ => raise Bind
    fun Knil th ths =
        case ths of
          [] => th
        | _ => raise Bind


    (* our actual Tactics *)
    fun ASSUME_TAC th : Tactic =
      fn (asl, g) =>
      ([(th::asl, g)], PROVE_HYP th o hd1)

    fun POP_ASSUM thf (a::asl, g) = thf a (asl, g)
      | POP_ASSUM  _  ([],_)      = raise ERR "POP_ASSUM" "no assums" ;

    fun ASSUM_LIST thlf (asl, g)  = thlf asl (asl, g)
    fun POP_ASSUM_LIST thlf (asl, g) = thlf asl ([], g)
    fun FIRST_ASSUM ttac (asl, g) = tryfind (fn th => ttac th (asl, g)) asl

    fun UNDISCH_THEN tm ttac (asl,g) =
      let val (th, asl') = Lib.pluck (fn th => aconv (concl th) tm) asl
      in ttac th (asl', g)
      end

    fun FIRST_X_ASSUM ttac =
      FIRST_ASSUM (fn th => UNDISCH_THEN (concl th) ttac);

    fun ALL_TAC (asl, g) = ([(asl,g)], hd1)

    fun EVERY [] = ALL_TAC | EVERY (t::ts) = t THEN EVERY ts

    fun MAP_EVERY f l = EVERY (map f l)

    fun RULE_ASSUM_TAC f =
      POP_ASSUM_LIST (MAP_EVERY (f >- ASSUME_TAC) o rev)

    infix ORELSE
    fun (t1 ORELSE t2) g = t1 g handle HOL_ERR _ => t2 g
    fun REPEAT t g = ((t THEN REPEAT t) ORELSE ALL_TAC) g


    fun X_CHOOSE_TAC t xth (asl, g) =
      let val xtm = concl xth
          val (x, bod) = dest_exists xtm
          val pat = ASSUME (Term.subst [x |-> t] bod)
      in ([(pat::asl, g)], CHOOSE (t, xth) o hd1)
      end
      handle HOL_ERR _ => raise ERR "X_CHOOSE_TAC" ""

    fun CHOOSE_TAC xth (asl, g) =
      let val x = fst (dest_exists (concl xth))
                  handle HOL_ERR _ => raise ERR "CHOOSE_TAC" ""
          val union = op_union aconv
          val avoids = itlist (union o free_vars o concl) asl
                              (union (free_vars g) (thm_frees xth))
          val newvar = variant avoids x
      in
        X_CHOOSE_TAC newvar xth (asl, g)
      end


    fun CONJUNCTS_THEN ttac th =
      let val (c1, c2) = (CONJUNCT1 th, CONJUNCT2 th)
      in ttac c1 THEN ttac c2
      end

    fun DISJ_CASES_TAC dth =
      let val dtm = concl dth
          val (l,r) = dest_disj dtm
          val (thl, thr) = (ASSUME l, ASSUME r)
          fun vf ths =
              case ths of
                [th1, th2] => DISJ_CASES dth th1 th2
              | _ => raise Bind
      in fn (asl, g) => ([(thl::asl, g), (thr::asl, g)], vf)
      end

    fun DISJ_CASES_THEN ttac th =
      DISJ_CASES_TAC th THEN POP_ASSUM ttac;

    infix ORELSE_TCL
    fun (ttcl1 ORELSE_TCL ttcl2) ttac th =
      ttcl1 ttac th handle HOL_ERR _ => ttcl2 ttac th

    fun CONTR_TAC cth (asl, g) =
       let val th = CONTR g cth in ([], Knil th) end

    fun ACCEPT_TAC th (asl, g) =
      if aconv (concl th) g then ([], Knil th)
                            else raise ERR "ACCEPT_TAC" ""

end
