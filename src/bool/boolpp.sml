structure boolpp :> boolpp =
struct

open Parse HolKernel
open term_pp_types smpp term_pp_utils
infix >> >-

val ERRORloc = Feedback.mk_HOL_ERRloc "boolpp"

fun dest_cond tm =
  let
    val (f, args) = strip_comb tm
    val {Thy,Name,...} = dest_thy_const f
      handle HOL_ERR _ =>
             raise mk_HOL_ERR "boolpp" "dest_cond" "Not even a const at head"
  in
    if Thy = "bool" andalso Name = "COND" then
      case args of
          [gd, th, el] => (gd,th,el)
        | _ => raise mk_HOL_ERR "boolpp" "dest_cond" "Wrong number of arguments"
    else
      raise mk_HOL_ERR "boolpp" "dest_cond" "Not a COND-term"
  end

fun condprinter (tyg, tmg) backend printer ppfns (pgr,lgr,rgr) depth tm = let
  val _ =
      case Overload.oi_strip_comb (term_grammar.overload_info tmg) tm of
          SOME(f, _) =>
            if term_grammar.grammar_name tmg f = SOME "case"
            then ()
            else raise UserPP_Failed
        | NONE => raise UserPP_Failed
  val {add_string, ublock, add_break, ...} = ppfns:ppstream_funs
  fun paren c b p =
    if b then
      ublock c 1 (
        add_string "(" >> p >> add_string ")"
      )
    else p
  val paren_required =
      (case rgr of
         Prec(p, _) => p > 70
       | _ => false) orelse
      (case lgr of
         Prec(_, n) => n = GrammarSpecials.fnapp_special
       | _ => false)
  fun syspr gravs t =
    printer { gravs = gravs, depth = decdepth depth, binderp = false } t
  fun doguard needs_else (g,t) =
      block PP.CONSISTENT 0
            (block PP.CONSISTENT 0
                   ((if needs_else then
                       add_string "else" >> add_string " " >>
                       add_string "if"
                     else
                       add_string "if") >>
                    add_break (1,2) >>
                    block PP.CONSISTENT 0 (syspr (Top,Top,Top) g) >>
                    add_break (1,0) >>
                    add_string "then") >>
             add_break (1,2) >>
             block PP.CONSISTENT 0 (syspr (Top,Top,Top) t))

  fun doelse e = let
    val prec = Prec(70, "COND")
  in
    case Lib.total dest_cond e of
        SOME (g,t,e_next) => (doguard true (g,t) >> add_break(1,0) >>
                              doelse e_next)
      | NONE => block PP.CONSISTENT 0
                      (add_string "else" >> add_break (1,2) >>
                       block PP.CONSISTENT 0 (syspr (prec,prec,rgr) e))
  end
  val (g,t,e) = dest_cond tm
in
  paren PP.CONSISTENT paren_required (
    block PP.CONSISTENT 0 (doguard false (g,t) >> add_break(1,0) >> doelse e)
  )
end

val _ = term_grammar.userSyntaxFns.register_userPP
          {name = "bool.COND", code = condprinter}

(* ----------------------------------------------------------------------
    printing let terms
   ---------------------------------------------------------------------- *)

fun letprinter (tyg, tmg) backend printer ppfns (pgr,lgr,rgr) depth tm =
  let
    val eqprec =
        case term_grammar.get_precedence tmg "=" of
            SOME (Infix(_, i)) => Prec(i, "=")
          | _  => raise UserPP_Failed
    fun syspr gravs t =
      printer { gravs = gravs, depth = decdepth depth, binderp = false } t
    fun pr_vstruct v =
      case v of
          Simple t => printer {gravs = (Top,Top,Top), depth = decdepth depth,
                               binderp = true} t
        | Restricted _ => raise UserPP_Failed
    fun my_strip_abs tm = let
      fun recurse acc t = let
        val (v, body) = pp_dest_abs tmg t
      in
        recurse (v::acc) body
      end handle HOL_ERR _ => (List.rev acc, t)
    in
      recurse [] tm
    end
    val strip_vstructs = term_pp_utils.strip_vstructs tmg
    fun strip_nvstructs n tm = let
      fun strip n acc tm =
        if n <= 0 then (List.rev acc, tm)
        else let
          val (bvar, body) = dest_vstruct tmg {binder=NONE,restrictor=NONE} tm
        in
          strip (n - 1) (bvar :: acc) body
        end
    in
      strip n [] tm
    end

    (* allow any constant that overloads to the string "LET" to be treated as
       a let. *)
    fun is_let0 n tm = let
      val (let_tm,f_tm) = dest_comb(rator tm)
    in
      term_grammar.grammar_name tmg let_tm = SOME "LET" andalso
      (length (#1 (my_strip_abs f_tm)) >= n orelse is_let0 (n + 1) f_tm)
    end handle HOL_ERR _ => false
    val is_let = is_let0 1

    val {add_string, ublock, add_break, ...} = ppfns:ppstream_funs
    fun paren c b p =
      if b then
        ublock c 1 (
          add_string "(" >> p >> add_string ")"
        )
      else p
    fun spacep b = if b then add_break(1, 0) else nothing
    fun find_base acc tm =
      if is_let tm then let
        val (let_tm, args) = strip_comb tm
      in
        find_base (List.nth(args, 1)::acc) (hd args)
      end
      else (acc, tm)

    fun strip_let acc tm =
      if is_let tm then
        let
          val (values, abstr) = find_base [] tm
          val (varnames, body) = strip_nvstructs (length values) abstr
          val name_value_pairs = ListPair.zip (varnames, values)
        in
          strip_let (name_value_pairs :: acc) body
        end
      else (List.rev acc, tm)
    val (andbindings, body) = strip_let [] tm

    fun pr_leteq (bv, tm2) = let
      val (args, rhs_t) = strip_vstructs {binder=NONE,restrictor=NONE} tm2
      val fnarg_bvars = List.concat (map (free_vars o bv2term) args)
      val bvfvs = free_vars (bv2term bv)
    in
      block PP.INCONSISTENT 2
          (record_bvars bvfvs (pr_vstruct bv) >>
           spacep true >>
           record_bvars fnarg_bvars
             (pr_list pr_vstruct (spacep true) args >>
              spacep (not (null args)) >>
              add_string "=" >> add_break (1, 0) >>
              block PP.INCONSISTENT 0 (syspr (eqprec, Top, eqprec) rhs_t))) >>
        return bvfvs
    end

    fun record_bvars new =
      (* overriding term_pp_utils's version; this one has a different type
         also *)
      getbvs >- (fn old => setbvs (HOLset.addList(old,new)))

    fun pr_letandseq nvpairs =
      block PP.INCONSISTENT 0
           (mappr_list pr_leteq
                       (add_string " " >> add_string "and" >> spacep true)
                       nvpairs >-
           (return o List.concat)) >-
           record_bvars

    fun pr_let0 tm =
         add_string "let" >> add_break(1,2) >>
         (* let bindings list does not get a block to itself because you
            don't want something like
               let
                 x = e1 ; y = e2 ; z = e3
               in
                 e4
            Instead, all 6 components above are in the same printing block,
            and some are indented two, and some are in column 0
         *)
         pr_list pr_letandseq
                 (add_string " " >> add_string ";" >> add_break (1, 2))
                 andbindings >>
         add_break(1,0) >> add_string "in" >> add_break(1,2) >>
         block PP.INCONSISTENT 0 (syspr (RealTop, RealTop, RealTop) body)

    fun pr_let lgrav rgrav tm = let
      val addparens = lgrav <> RealTop orelse rgrav <> RealTop
    in
      getbvs >-
      (fn oldbvs => paren PP.CONSISTENT addparens (pr_let0 tm) >> setbvs oldbvs)
    end
in
  if is_let tm then pr_let lgr rgr tm
  else raise UserPP_Failed
end

val _ = term_grammar.userSyntaxFns.register_userPP
          {name = "bool.LET", code = letprinter}

(* ----------------------------------------------------------------------
    let_processor : absyn -> absyn

    Moderately disgusting.  Hacks about with the absyn structure in order
    to handle let-expressions
   ---------------------------------------------------------------------- *)

(* if it can see the LHS (t1) as a pair or single variable then, creates an
   pair of form (vstruct_of t1, t2).
   Otherwise, the LHS should be an application (because it's OK to write
   things like  “let f x1 x2 = body in t”), so returns pair
      (VIDENT "f", (\x1 x2. t2))
*)
fun reform_def (t1, t2) =
 (Absyn.to_vstruct t1, t2)
  handle HOL_ERR _ =>
   let open Absyn
       val (f, args) = strip_app t1
       val newlocn = locn.Loc_Near (locn_of_absyn t2) (*TODO:not quite right*)
       val newrhs =
           List.foldr (fn (a,body) => LAM(newlocn,to_vstruct a,body)) t2 args
   in
     (to_vstruct f, newrhs)
   end

fun munge_let binding_term body = let
  open Absyn GrammarSpecials
  fun strip_and pt A =
      case pt of
        APP(_,APP(_,IDENT(_,andstr),t1),t2) => if andstr = and_special then
                                                 strip_and t1 (strip_and t2 A)
                                               else pt::A
      | _ => pt::A
  val binding_clauses = strip_and binding_term []
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

fun let_processor0 G t0 = let
  open Absyn GrammarSpecials
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

fun let_processor G t = let
  open Absyn GrammarSpecials
  fun nilcheck (APP (_, IDENT (_, nilstr), body)) = nilstr = letnil_special
    | nilcheck _ = false
  fun conspresent (APP (_,
                        APP (_, IDENT (_, letstr),
                             APP (_,
                                  APP(_, IDENT(_, constr), eq1),
                                  eqs)),
                        bod)) =
         constr = letcons_special andalso letstr = let_special
    | conspresent _ = false
  fun foldcons (a, bod) =
    case a of
        APP (l1, APP (l2, IDENT(_, constr), eq1), eqs) =>
          if constr = letcons_special then
            APP (l1, APP (l2, IDENT(l2, let_special), eq1), foldcons(eqs, bod))
          else raise ERRORloc "let_processor" l1 "Mal-formed LET"
      | IDENT(loc, nilstr) =>
          if nilstr = letnil_special then bod
          else raise ERRORloc "let_processor" loc "Mal-formed LET"
      | _ => raise ERRORloc "let_processor" (locn_of_absyn a) "Mal-formed LET"
  fun let_args tf a = let
    val (fx, y) = dest_app a
    val (_, x) = dest_app fx
  in
    (tf x, tf y)
  end
in
  traverse
    conspresent
    (fn tf => fn a => let_processor0 G (foldcons (let_args tf a))) t
end

val _ = term_grammar.userSyntaxFns.register_absynPostProcessor
          {name = "bool.LET", code = let_processor}


end
