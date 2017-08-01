structure boolpp :> boolpp =
struct

open Parse HolKernel
open term_pp_types smpp term_pp_utils
infix >> >-

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
  val paren_required =
      (case rgr of
         Prec(p, _) => p > 70
       | _ => false) orelse
      (case lgr of
         Prec(_, n) => n = GrammarSpecials.fnapp_special
       | _ => false)
  val doparen = if paren_required then (fn c => add_string c)
                else (fn c => nothing)
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
                    syspr (Top,Top,Top) g >>
                    add_break (1,0) >>
                    add_string "then") >>
             add_break (1,2) >>
             syspr (Top,Top,Top) t)

  fun doelse e = let
    val prec = Prec(70, "COND")
  in
    case Lib.total dest_cond e of
        SOME (g,t,e_next) => (doguard true (g,t) >> add_break(1,0) >>
                              doelse e_next)
      | NONE => block PP.CONSISTENT 0
                      (add_string "else" >> add_break (1,2) >>
                       syspr (prec,prec,rgr) e)
  end
  val (g,t,e) = dest_cond tm
in
  doparen "(" >>
  block PP.CONSISTENT 0
    (doguard false (g,t) >> add_break(1,0) >> doelse e) >>
  doparen ")"
end

val _ = term_grammar.userSyntaxFns.register_userPP
          {name = "bool.COND", code = condprinter}

(* ----------------------------------------------------------------------
    printing let terms
   ---------------------------------------------------------------------- *)

fun letprinter (tyg, tmg) backend printer ppfns (pgr,lgr,rgr) depth tm =
  let
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
    fun pbegin b = if b then add_string "(" else nothing
    fun pend b = if b then add_string ")" else nothing
    fun spacep b = if b then add_break(1, 0) else nothing

    fun pr_let0 tm = let
      fun find_base acc tm =
        if is_let tm then let
          val (let_tm, args) = strip_comb tm
        in
          find_base (List.nth(args, 1)::acc) (hd args)
        end
        else (acc, tm)
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
              add_string "=" >> spacep true >>
              block PP.INCONSISTENT 2 (syspr (Top, Top, Top) rhs_t))) >>
        return bvfvs
      end
      val (values, abstr) = find_base [] tm
      val (varnames, body) = strip_nvstructs (length values) abstr
      val name_value_pairs = ListPair.zip (varnames, values)
      val bodyletp = is_let body
      fun record_bvars new =
        (* overriding term_pp_utils's version; this one has a different type
           also *)
        getbvs >- (fn old => setbvs (HOLset.addList(old,new)))
    in
      (* put a block around the "let ... in" phrase *)
      block PP.CONSISTENT 0
        (add_string "let" >> add_string " " >>
         (* put a block around the variable bindings *)
         block PP.INCONSISTENT 0
           (mappr_list pr_leteq
                       (add_string " " >> add_string "and" >> spacep true)
                       name_value_pairs >-
            (return o List.concat)) >-
         record_bvars >>
         (if bodyletp then (spacep true >> add_string "in")
          else nothing)) >>
       spacep true >>
       (if bodyletp then pr_let0 body
        else add_string "in" >> add_break(1,2) >>
             syspr (RealTop, RealTop, RealTop) body)
    end

    fun pr_let lgrav rgrav tm = let
      val addparens = lgrav <> RealTop orelse rgrav <> RealTop
    in
      getbvs >-
      (fn oldbvs =>
          pbegin addparens >>
          block PP.CONSISTENT 0 (pr_let0 tm) >>
          pend addparens >>
          setbvs oldbvs)
    end
in
  if is_let tm then pr_let lgr rgr tm
  else raise UserPP_Failed
end

val _ = term_grammar.userSyntaxFns.register_userPP
          {name = "bool.LET", code = letprinter}

end
