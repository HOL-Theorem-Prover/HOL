structure TermParse :> TermParse =
struct

type term = Term.term
type hol_type = Type.hol_type
type grammar = term_grammar.grammar
type tygrammar = type_grammar.grammar
type absyn = Absyn.absyn
type preterm = Preterm.preterm
type 'a quotation = 'a Portable.frag list
type pprinters = ((term -> string) * (hol_type -> string)) option

open HolKernel GrammarSpecials

val ERROR = mk_HOL_ERR "Parse";
val ERRORloc = mk_HOL_ERRloc "Parse";
val WARN  = HOL_WARNING "Parse"

(* ----------------------------------------------------------------------
    absyn_phase1

    the ty argument is a type-parser, which invokers will need to construct
    by using parse_type and a tygrammar.
   ---------------------------------------------------------------------- *)

fun absyn_phase1 G ty = let
  open parse_term
  val pt = parse_term G ty
      handle PrecConflict(st1, st2) =>
             raise ERROR "Term"
               (String.concat
                 ["Grammar introduces precedence conflict between tokens ",
                  term_grammar.STtoString G st1, " and ",
                  term_grammar.STtoString G st2])
  open base_tokens qbuf
in
fn q => let
     open errormonad
     val ((qb,p), fsres) = pt (new_buffer q, initial_pstack)
         handle base_tokens.LEX_ERR (s,locn) =>
                raise (ERRORloc "Absyn" locn ("Lexical error - "^s))
   in
     case fsres of
       Some () => let
       in
         if is_final_pstack p then
           case current qb of
             (BT_EOI,locn) => (top_nonterminal p
                               handle ParseTermError (s,locn) =>
                                      raise (ERRORloc "Term" locn s))
           | (_,locn) =>
             raise (ERRORloc "Absyn" locn
                             (String.concat
                                  ["Can't make sense of remaining: ",
                                   Lib.quote (toString qb)]))
         else
           raise (ERRORloc "Absyn" (snd (current qb)) "Parse failed")
       end
     | Error (s,locn) => raise mk_HOL_ERRloc "Absyn" "Absyn" locn s
   end
end;

(* ----------------------------------------------------------------------
    absyn_phase2

    Moderately disgusting.  Hacks about with the absyn structure in order
    to handle let-expressions (and maybe other things).
   ---------------------------------------------------------------------- *)

fun to_vstruct t = let
  open Absyn
  fun ultimately s (IDENT (_, s'))      = (s = s')
    | ultimately s (TYPED (_, t', _))   = ultimately s t'
    | ultimately s _ = false
in
  case t of
    IDENT (locn,s)    => VIDENT (locn,s)
  | TYPED (locn,t,ty) => VTYPED(locn,to_vstruct t, ty)
  | AQ (locn,x)       => VAQ (locn,x)
  | APP(locn,APP(_,comma, t1), t2) =>
      if ultimately "," comma then VPAIR(locn,to_vstruct t1, to_vstruct t2)
      else raise Fail ("term "^locn.toString locn^" not suitable as varstruct")
  | t => raise Fail ("term "^locn.toString (locn_of_absyn t)^" not suitable as varstruct")
end

fun reform_def (t1, t2) =
 (to_vstruct t1, t2)
  handle Fail _ =>
   let open Absyn
       val (f, args) = strip_app t1
       val newlocn = locn.Loc_Near (locn_of_absyn t2) (*TODO:not quite right*)
       val newrhs = List.foldr (fn (a,body) => LAM(newlocn,to_vstruct a,body)) t2 args
   in (to_vstruct f, newrhs)
   end

fun munge_let binding_term body = let
  open Absyn
  fun strip_and pt A =
      case pt of
        APP(_,APP(_,IDENT(_,andstr),t1),t2) => if andstr = and_special then
                                                 strip_and t1 (strip_and t2 A)
                                               else pt::A
      | _ => pt::A
  val binding_clauses = strip_and binding_term []
  fun is_eq tm = case tm of APP(_,APP(_,IDENT (_,"="), _), _) => true
                          | _ => false
  fun dest_eq (APP(_,APP(_,IDENT (_,"="), t1), t2)) = (t1, t2)
    | dest_eq t = raise Fail (locn.toString (locn_of_absyn t)^
                              ":\n(pre-)term not an equality")
  val _ = List.all is_eq binding_clauses
          orelse raise ERRORloc "Term" (locn_of_absyn binding_term)
                                "let with non-equality"
  val (L,R) = ListPair.unzip (map (reform_def o dest_eq) binding_clauses)
  val binding_locn = locn.Loc_Near (locn_of_absyn binding_term)
                      (*:TODO:not quite right*)
  val central_locn = locn.Loc_Near (locn_of_absyn body) (*TODO:not quite right*)
  val central_abstraction =
      List.foldr (fn (v,M) => LAM(central_locn,v,M)) body L
in
  List.foldl (fn(arg, b) => APP(central_locn,
                                APP(binding_locn,IDENT (binding_locn,"LET"),b),
                                arg))
             central_abstraction
             R
end

fun traverse applyp f t = let
  open Absyn
  val traverse = traverse applyp f
in
  if applyp t then f traverse t
  else case t of
    APP(locn,t1,t2)   => APP(locn,traverse t1, traverse t2)
  | LAM(locn,vs,t)    => LAM(locn,vs, traverse t)
  | TYPED(locn,t,pty) => TYPED(locn,traverse t, pty)
  | allelse           => allelse
end


fun absyn_phase2 t0 = let
  open Absyn
  fun let_remove f (APP(_,APP(_,IDENT _, t1), t2)) = munge_let (f t1) (f t2)
    | let_remove _ _ = raise Fail "Can't happen"
  val t1 =
      traverse (fn APP(_,APP(_,IDENT (_,letstr), _), _) => letstr = let_special
                 | otherwise => false) let_remove t0
  val _ =
    traverse (fn IDENT(_,andstr) => andstr = and_special | _ => false)
    (fn _ => fn t => raise ERRORloc "Term" (locn_of_absyn t)
                                    "Invalid use of reserved word and") t1
in
  t1
end


(* ----------------------------------------------------------------------
    absyn_postprocess

    the user gets to do post-processing on Absyn values too...
   ---------------------------------------------------------------------- *)

fun absyn_postprocess G a = let
  val pps = term_grammar.absyn_postprocessors G
in
  foldl (fn ((_, f), acc) => f acc) a pps
end


(* ----------------------------------------------------------------------
    absyn

    putting it all together
   ---------------------------------------------------------------------- *)

fun absyn tmg tyg = let
  val typ_parse =
      parse_type.parse_type Pretype.termantiq_constructors false tyg
  val phase1 = absyn_phase1 tmg typ_parse
               (* isolate this computation so that precedence conflicts
                  only get detected/reported once *)
in
  fn q => q |> phase1 |> absyn_phase2 |> absyn_postprocess tmg
end

(* ----------------------------------------------------------------------
    Preterms
   ---------------------------------------------------------------------- *)

local open Parse_support Absyn
  fun to_vstruct t =
      case t of
        APP(l, APP(_, IDENT (_, ","), t1), t2) => VPAIR(l, to_vstruct t1,
                                                        to_vstruct t2)
      | AQ p => VAQ p
      | IDENT p  => VIDENT p
      | TYPED(l, t, pty) => VTYPED(l, to_vstruct t, pty)
      | _ => raise ERRORloc "Term" (locn_of_absyn t)
                            "Bad variable-structure"
in
  fun absyn_to_preterm_in_env oinfo t = let
    fun binder(VIDENT (l,s))    = make_binding_occ l s
      | binder(VPAIR(l,v1,v2))  = make_vstruct oinfo l [binder v1, binder v2]
                                               NONE
      | binder(VAQ (l,x))       = make_aq_binding_occ l x
      | binder(VTYPED(l,v,pty)) = make_vstruct oinfo l [binder v] (SOME pty)
    open parse_term Absyn Parse_support
    val to_ptmInEnv = absyn_to_preterm_in_env oinfo
  in
    case t of
      APP(l,APP(_,IDENT (_,"gspec special"), t1), t2) =>
        make_set_abs oinfo l (to_ptmInEnv t1, to_ptmInEnv t2)
    | APP(l,APP(_,APP(_,IDENT (_, "gspec2 special"), t1), t2), t3) => let
        val l3 = locn_of_absyn t3
        val newbody = APP(l3, APP(l3, QIDENT(l3, "pair", ","), t1), t3)
      in
        to_ptmInEnv (APP(l, QIDENT(l, "pred_set", "GSPEC"),
                         LAM(l, to_vstruct t2, newbody)))
      end
    | APP(l, APP(_, t0 as IDENT (_, caseform), t1), t2) => let
      in
        if caseform = GrammarSpecials.case_special then let
            (* handle possible arrows in t2 *)
            fun every_case base ab =
                case ab of
                  APP(l, APP(_, t0 as IDENT (_, casesplit), t1), t2) => let
                  in
                    if casesplit = GrammarSpecials.case_split_special then let
                        val t1' = every_case base t1
                        val t2' = every_case base t2
                      in
                        list_make_comb l [to_ptmInEnv t0, t1', t2']
                      end
                    else base ab
                  end
                | _ => base ab
            fun do_arrow ab =
                case ab of
                  APP(l, APP(_, t0 as IDENT (_, casearrow), t1), t2) => let
                  in
                    if casearrow = GrammarSpecials.case_arrow_special then
                      make_case_arrow oinfo l (to_ptmInEnv t1) (to_ptmInEnv t2)
                    else raise ERRORloc "Term" l
                                        "Mal-formed case expression (no arrow)"
                  end
                | _ => raise ERRORloc "Term" (locn_of_absyn ab)
                                      "Mal-formed case expression (no arrow)"
          in
            list_make_comb l [to_ptmInEnv t0, to_ptmInEnv t1,
                              every_case do_arrow t2]
          end
        else list_make_comb l (map to_ptmInEnv [t0, t1, t2])
      end
    | APP(l, t1, t2)     => list_make_comb l (map to_ptmInEnv [t1, t2])
    | IDENT (l, s)       => make_atom oinfo l s
    | QIDENT (l, s1, s2) => make_qconst oinfo l (s1,s2)
    | LAM(l, vs, t)      => bind_term l [binder vs] (to_ptmInEnv t)
    | TYPED(l, t, pty)   => make_constrained l (to_ptmInEnv t) pty
    | AQ (l, t)          => make_aq l t
  end
end;

fun absyn_to_preterm g a = let
  val oinfo = term_grammar.overload_info g
in
  a |> absyn_to_preterm_in_env oinfo |> Parse_support.make_preterm
end

fun preterm g tyg q = q |> absyn g tyg |> absyn_to_preterm g

(* ----------------------------------------------------------------------
    Targetting terms
   ---------------------------------------------------------------------- *)

val preterm_to_term = Preterm.typecheck

fun absyn_to_term pprinters g a = let
  val oinfo = term_grammar.overload_info g
in
  a |> absyn_to_preterm g
    |> Preterm.typecheck pprinters
end

fun term pprinters g tyg = let
  val ph1 = absyn g tyg
in
  fn q => q |> ph1 |> absyn_to_term pprinters g
end

(* ----------------------------------------------------------------------
    Parsing in context
   ---------------------------------------------------------------------- *)

(*----------------------------------------------------------------------*
 * parse_in_context                                                     *
 *----------------------------------------------------------------------*)

local
  open Preterm Pretype
  fun name_eq s M = ((s = fst(dest_var M)) handle HOL_ERR _ => false)
  exception UNCHANGED
  fun strip_csts (Constrained{Ptm,...}) = strip_csts Ptm
    | strip_csts t = t
  fun give_types_to_fvs ctxt boundvars tm = let
    val gtf = give_types_to_fvs ctxt
  in
    case tm of
      Var{Name, Ty, Locn} => let
      in
        if not(Lib.op_mem Preterm.eq tm boundvars) then
          case List.find (name_eq Name) ctxt of
            NONE => raise UNCHANGED
          | SOME ctxt_tm => Var{Locn = Locn, Name = Name,
                                Ty =  Pretype.fromType (type_of ctxt_tm)}
        else raise UNCHANGED
      end
    | Comb{Rator, Rand, Locn} => let
      in
        let
          val rator = gtf boundvars Rator
        in
          let
            val rand =  gtf boundvars Rand
          in
            Comb{Rator = rator, Rand = rand, Locn = Locn}
          end handle UNCHANGED => Comb{Rator = rator, Rand = Rand, Locn = Locn}
        end handle UNCHANGED =>
                   let val rand = gtf boundvars Rand
                   in
                     Comb{Rator = Rator, Rand = rand, Locn = Locn}
                   end
      end
    | Abs{Bvar, Body, Locn} => Abs{Bvar = Bvar,
                                   Body = gtf (strip_csts Bvar::boundvars) Body,
                                   Locn = Locn}
    | Constrained{Ptm,Locn,Ty} => Constrained{Ptm = gtf boundvars Ptm,
                                              Locn = Locn, Ty = Ty}
    | _ => raise UNCHANGED
  end
in
  fun parse_preterm_in_context0 pprinters FVs ptm0 = let
    val ptm = give_types_to_fvs FVs [] ptm0
              handle UNCHANGED => ptm0
  in
    preterm_to_term pprinters ptm
  end

  fun ctxt_preterm_to_term pprinters FVs ptm =
    Lib.with_flag (Globals.notify_on_tyvar_guess,false)
                  (parse_preterm_in_context0 pprinters FVs) ptm

  fun ctxt_term pprinters g tyg = let
    val ph1 = preterm g tyg
  in
    fn fvs => fn q => q |> ph1 |> ctxt_preterm_to_term pprinters fvs
  end

end


end (* struct *)