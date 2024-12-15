structure resolve_then :> resolve_then =
struct

open HolKernel boolSyntax Drule thmpos_dtype

fun match_subterm pat = find_term (can (match_term pat))

fun UDISCH' avoidnames th =
    let
      val (l,r) = dest_imp_only (concl th)
      fun buildcth nms0 t =
          case Lib.total dest_conj t of
              SOME (l,r) =>
              let
                val (lth, lcs, nms1) = buildcth nms0 l
                val (rth, rcs, nms2) = buildcth nms1 r
              in
                (CONJ lth rth, lcs @ rcs, nms2)
              end
            | NONE => (case Lib.total dest_exists t of
                           NONE => (ASSUME t, [t], nms0)
                         | SOME (bv, bod) =>
                           let
                             val (bvnm,bvty) = dest_var bv
                             val (c, cnm,bod') =
                                 let val cnm =
                                         Lexis.gen_variant Lexis.tmvar_vary
                                                           nms0
                                                           bvnm
                                     val c = mk_var(cnm, bvty)
                                 in
                                   (c, cnm, subst[bv |-> c] bod)
                                 end
                             val (bodth, bodcs, nms1) =
                                 buildcth (cnm::nms0) bod'
                           in
                             (EXISTS(t, c) bodth, bodcs, nms1)
                           end)
      val (th', conjuncts, nms') = buildcth avoidnames l
    in
      (PROVE_HYP th' (UNDISCH th), conjuncts, nms')
    end handle HOL_ERR _ => let
      val (bv,_) = dest_forall (concl th)
      val (bvnm, bvty) = dest_var bv
      val newnm = Lexis.gen_variant Lexis.tmvar_vary avoidnames bvnm
      val newv = mk_var(newnm, bvty)
    in
      (SPEC newv th, [], newnm::avoidnames)
    end

fun UDALL nms0 th0 =
    case Lib.total (UDISCH' nms0) th0 of
        NONE => (th0, [], nms0)
      | SOME (th', cs1, nms') =>
        let
          val (th, cs2, nms) = UDALL nms' th'
        in
          (th, cs1 @ cs2, nms)
        end

(* moves a bunch of hypotheses from a theorem into an implication, conjoining
   them all rather than creating iterated implications *)
fun DISCHl tms th =
    if null tms then th
    else
      let
        val cjt = list_mk_conj tms
      in
        th |> rev_itlist PROVE_HYP (CONJUNCTS $ ASSUME $ list_mk_conj tms)
           |> DISCH cjt
      end

(* turns G |- p   into G, ~p |- F, where p not negated; and
         G |- ~p  into G,  p |- F
   also returns the new hypothesis
*)
fun liftconcl th =
    let
      val c = concl th
    in
      let
        val c0 = dest_neg c
      in
        (UNDISCH th, c0)
      end handle HOL_ERR _ =>
                 let val h = mk_neg c
                 in
                   (EQ_MP (EQF_INTRO (ASSUME h)) th, h)
                 end
    end

(* val th2 = prim_recTheory.LESS_REFL
   val th1 = arithmeticTheory.LESS_TRANS
*)


fun gen_resolve_then mpos th1 th2 kont =
    (* conclusion of th1 unifies with some part of th2 *)
    let
      val th1 = GEN_ALL (GEN_TYVARIFY th1)
      val th2 = GEN_ALL (GEN_TYVARIFY th2)
      val fixed_tms1 = hyp_frees th1
      val fixed_tys1 = hyp_tyvars th1
      val fixed_tms2 = hyp_frees th2
      val fixed_tys2 = hyp_tyvars th2
      val fixed_tyl = HOLset.listItems (HOLset.union(fixed_tys1,fixed_tys2))
      val fixed_tms = HOLset.union(fixed_tms1,fixed_tms2)
      val fixed_tml = HOLset.listItems fixed_tms
      val hyps = HOLset.union(hypset th1, hypset th2)
      val badnames = HOLset.foldl(fn (v,A) =>HOLset.add(A,#1 (dest_var v)))
                                 (HOLset.empty String.compare)
                                 fixed_tms
      val (th1_ud, cs1, nms1) =
          UDALL (HOLset.listItems badnames) th1
      val (th2_ud, cs2, _) = UDALL nms1 th2
      val (th2_ud, con) =
          case mpos of
              Concl => liftconcl th2_ud
            | _ => (th2_ud, T)
      fun INSTT (tyi,tmi) th = th |> INST_TYPE tyi |> INST tmi
      fun instt (tyi,tmi) t = t |> Term.inst tyi |> Term.subst tmi
      open optmonad
      fun postprocess sigma th =
          let
            val thhyps = hypset th
            val dhyps0 = map (instt sigma) (cs1 @ cs2) |> op_mk_set aconv
            val dhyps =
                List.filter (fn t => not (HOLset.member(hyps,t)) andalso
                                     HOLset.member(thhyps, t))
                            dhyps0
          in
            DISCHl dhyps th |> GEN_ALL
          end
      fun try t k =
          case FullUnify.Env.fromEmpty
                 (FullUnify.unify fixed_tyl fixed_tml(t, concl th1_ud) >>
                                  FullUnify.collapse)
           of
              NONE => k()
            | SOME sigma =>
              let val kth =
                      PROVE_HYP (INSTT sigma th1_ud) (INSTT sigma th2_ud) |>
                      postprocess sigma
              in
                kont kth handle HOL_ERR _ => k()
              end
      val max = length cs2
      val fail = mk_HOL_ERR "Tactic" "resolve_then" "No unifier"
    in
      case mpos of
          Any =>
          let
            fun doit n =
                if n > max then raise fail
                else try (el n cs2) (fn _ => doit (n + 1))
          in
            doit 1
          end
        | Pos f =>
          (case Exn.capture f cs2 of
               Exn.Exn _ => raise fail
             | Exn.Res t => try t (fn _ => raise fail))
        | Pat q =>
          let
            open TermParse
            val pats =
                prim_ctxt_termS Parse.Absyn (Parse.term_grammar()) [] q
            fun doit ps n =
                if n > max then raise fail
                else
                  case seq.cases ps of
                      NONE => doit pats (n + 1)
                    | SOME (pat, rest) =>
                      if can (match_subterm pat) (el n cs2) then
                        try (el n cs2) (fn _ => doit rest n)
                      else doit rest n
          in
            doit pats 1
          end
        | Concl => try con (fn _ => raise fail)
    end

fun resolve_then mpos ttac th1 th2 g =
    gen_resolve_then mpos th1 th2 (fn th => ttac th g)

end (* struct *)
