open Term HolKernel Portable term_grammar HOLtokens HOLgrammars

(* Some comments on what this code should achieve:
     prefix commands
     ---------------

     This is something of a thorny issue.  We want to have the
     following terms printed as given here:
       ~p                            (not p)
       ~~p                           (not (not p))
       P (\x. x + 1)
       P (if x then y else z)
       p /\ !x. Q x \/ R y

     It seems that prefixes that are atomic and symbolic should not be
     followed by a space.  This would correctly print the first two
     lines.  This form of printing could lead to ambiguity in the
     presence of other functions, in this case, think of ~~ being
     defined as a separate identifier.  Thus, we must have the
     space-consuming under the control of some sort of global flag.

     The rules for bracketting would seem to be:
       - always bracket lambda abstractions

       - always bracket non-atomic prefixes, except at the very top
         level of a term.

       - never bracket non-lambda binders except to resolve ambiguity
         (the three cases above with parentheses all have unnecessary
         parens) *)


(* need to :
    app (fn s => (print ("Loading "^s^"\n"); load s))
        ["Polyhash", "Psyntax", "term_grammar", "type_pp"]
*)

fun PP_ERR f mesg = HOL_ERR {origin_structure = "term_pp",
                             origin_function = f,
                             message = mesg}

fun string_of_nspaces n = String.concat (List.tabulate(n, (fn _ => " ")))


datatype grav = Top | RealTop | Prec of (int * string)
fun grav_name (Prec(n, s)) = s | grav_name _ = ""
fun grav_prec (Prec(n,s)) = n | grav_prec _ = ~1

fun pneeded_by_style (rr: term_grammar.rule_record, pgrav, fname, fprec) =
  case #paren_style rr of
    Always => true
  | OnlyIfNecessary => false
  | ParoundName => grav_name pgrav <> fname
  | ParoundPrec => grav_prec pgrav <> fprec

fun countP P [] = 0
  | countP P (x::xs) = if P x then 1 + countP P xs else countP P xs
val numTMs = countP (fn TM => true | _ => false)

fun find_partial f [] = NONE
  | find_partial f (x::xs) = let
      val result = f x
    in
      case result of
        SOME x => result
      | NONE => find_partial f xs
    end

fun splitP P thelist = let
  fun with_acc acc [] = acc
    | with_acc (inlist, outlist) (x::xs) = let
      in
        if P x then with_acc (x::inlist, outlist) xs
        else with_acc (inlist, x::outlist) xs
      end
in
  with_acc ([], []) (List.rev thelist)
end

fun grule_term_names G grule = let
  fun suffix rr = (#term_name rr, SUFFIX (STD_suffix [rr]))
  fun prefix rr = (#term_name rr, PREFIX (STD_prefix [rr]))
  fun mkifix a rr = (#term_name rr, INFIX (STD_infix ([rr], a)))
  fun closefix rr = (#term_name rr, CLOSEFIX [rr])
in
  case grule of
    PREFIX (STD_prefix list) => map prefix list
  | PREFIX (BINDER list) =>
      map (fn b => (binder_to_string G b, PREFIX (BINDER [b]))) list
  | SUFFIX (STD_suffix list) => map suffix list
  | SUFFIX TYPE_annotation => []
  | INFIX (STD_infix(list, a)) => map (mkifix a) list
  | INFIX RESQUAN_OP => [(resquan_special, grule)]
  | CLOSEFIX lst => map closefix lst
  | FNAPP => [(fnapp_special, FNAPP)]
  | VSCONS => [(vs_cons_special, VSCONS)]
  | LISTRULE lspeclist => let
      fun process lspec = [(#cons lspec, LISTRULE [lspec]),
                           (#nilstr lspec, LISTRULE [lspec])]
    in
      List.concat (map process lspeclist)
    end
end

exception SimpleExit
exception DoneExit

fun symbolic s = List.all HOLsym (String.explode s)

fun has_name s tm =
  (is_const tm andalso #Name (dest_const tm) = s) orelse
  (is_var tm andalso #Name (dest_var tm) = s)


datatype bvar = Simple of term | Restricted of {Bvar : term, Restrictor : term}
fun bv2term (Simple t) = t | bv2term (Restricted {Bvar,...}) = Bvar

fun my_dest_abs tm =
  case dest_term tm of
    LAMB{Bvar, Body} => (Bvar, Body)
  | COMB{Rator, Rand} => let
      val _ =
        #Name (dest_const Rator)= "UNCURRY" orelse
        raise PP_ERR "my_dest_abs" "term not an abstraction"
      val (v1, body0) = my_dest_abs Rand
      val (v2, body) = my_dest_abs body0
    in
      (mk_pair{fst = v1, snd = v2}, body)
    end
  | _ => raise PP_ERR "my_dest_abs" "term not an abstraction"

fun my_is_abs tm = can my_dest_abs tm

fun strip_vstructs bnder res tm =
  case bnder of
    NONE => let
      fun strip vs t =
        if my_is_abs t then let
          val (bv, body) = my_dest_abs t
        in
          strip ((Simple bv)::vs) body
        end
        else
          case res of
            NONE => (List.rev vs, t)
          | SOME s => let
            in
              case dest_term t of
                COMB{Rator, Rand} => let
                in
                  case dest_term Rator of
                    COMB{Rator = rator1, Rand = rand1} =>
                      if has_name s rator1 andalso my_is_abs Rand then let
                        val (bv, body) = my_dest_abs Rand
                      in
                        strip
                        (Restricted{Bvar = bv, Restrictor = rand1}::vs)
                        body
                      end
                      else (List.rev vs, t)
                  | _ => (List.rev vs, t)
                end
              | _ => (List.rev vs, t)
            end
    in
      strip [] tm
    end
  | SOME s => let
      fun strip vs t =
        case (dest_term t) of
          COMB{Rator,Rand} => let
          in
            if has_name s Rator andalso my_is_abs Rand then let
              val (bv, body) = my_dest_abs Rand
            in
              strip ((Simple bv)::vs) body
            end
            else
              case res of
                NONE => (List.rev vs, t)
              | SOME s => let
                in
                  case (dest_term Rator) of
                    COMB{Rator = rator1, Rand = rand1} =>
                      if has_name s rator1 andalso my_is_abs Rand then let
                        val (bv, body) = my_dest_abs Rand
                      in
                        strip
                        (Restricted{Bvar = bv, Restrictor = rand1}::vs)
                        body
                      end
                      else (List.rev vs, t)
                  | _ => (List.rev vs, t)
                end
          end
        | _ => (List.rev vs, t)
    in
      strip [] tm
    end

fun rule_to_rr rule =
  case rule of
    INFIX (STD_infix (slist, _)) => slist
  | PREFIX (STD_prefix slist) => slist
  | SUFFIX (STD_suffix slist) => slist
  | CLOSEFIX slist => slist
  | _ => []

fun pp_term (G : grammar) TyG = let
  val {restr_binders,lambda,endbinding,type_intro,res_quanop} = specials G
  val overload_info = overload_info G
  val spec_table = let
    val toks = grammar_tokens G
    val table = Polyhash.mkPolyTable(50, Fail "")
  in
    app (fn s => Polyhash.insert table (s, ())) toks;
    table
  end
  val num_info = numeral_info G
  val rule_table = Polyhash.mkPolyTable(50, Fail "")
  fun insert (grule, n) = let
    val keys_n_rules = grule_term_names G grule
    fun myinsert t (k, v) = let
      val existing = Polyhash.peek t k
      val newvalue =
        case existing of
          NONE => [v]
        | SOME vs => v::vs
    in
      Polyhash.insert t (k, newvalue)
    end
  in
    app (fn (s,rule) => myinsert rule_table (s, (n, rule))) keys_n_rules;
    n + 1
  end
  val _ = foldl insert 0 (grammar_rules G)
  fun lookup_term s = Polyhash.peek rule_table s
  val comb_prec = #1 (hd (valOf (lookup_term fnapp_special)))
    handle Option =>
      raise PP_ERR "pp_term" "Grammar has no function application"
  val resquan_op_prec =
    case (lookup_term resquan_special) of
      SOME [] => raise Fail "term_pp : This really shouldn't happen"
    | SOME (x::xs) => SOME (#1 x)
    | NONE => NONE
  val vscons_prec = #1 (hd (valOf (lookup_term vs_cons_special)))
    handle Option =>
      raise PP_ERR "pp_term" "Grammar has no vstruct cons"
  val open_res_list_allowed =
    case resquan_op_prec of
      NONE => false
    | SOME p => p < vscons_prec
  fun pr_term binderp showtypes vars_seen pps tm pgrav lgrav rgrav depth = let
    val {fvars_seen, bvars_seen} = vars_seen
    val full_pr_term = pr_term
    val pr_term = pr_term binderp showtypes vars_seen pps
    val {add_string, add_break, begin_block, end_block,...} =
      with_ppstream pps
    fun block_by_style (rr, pgrav, fname, fprec) = let
      val needed =
        case #1 (#block_style rr) of
          AroundSameName => grav_name pgrav <> fname
        | AroundSamePrec => grav_prec pgrav <> fprec
        | AroundEachPhrase => true
      fun bblock() = uncurry begin_block (#2 (#block_style rr))
    in
      if needed then (bblock, end_block) else (I, I)
    end
    fun pbegin b = if b then add_string "(" else ()
    fun pend b = if b then add_string ")" else ()
    fun spacep b = if b then add_break(1, 0) else ()
    fun sizedbreak n = add_break(n, 0)
    fun pr_vstruct bv = let
      val pr_t =
        if showtypes then full_pr_term true true vars_seen pps
        else full_pr_term true false vars_seen pps
    in
      case bv of
        Simple tm => let
        in
          if (is_pair tm orelse is_var tm) then
            pr_t tm Top Top Top (depth - 1)
          else
            raise PP_ERR "pr_vstruct"
              "Can only handle pairs and vars as vstructs"
        end
      | Restricted{Bvar, Restrictor} => let
        in
          begin_block CONSISTENT 0;
          add_string "(";
          pr_vstruct (Simple Bvar);
          add_string (res_quanop);
          add_break(0,2);
          pr_term Restrictor Top Top Top (depth - 1);
          add_string ")";
          end_block ()
        end
    end

    (* this function is only called in circumstances when all of a
       vstruct list is restricted with the same term and when the
       relative precedences of the res_quan_op (traditionally "::") is
       less than that of VSCONS.  If this situation pertains, then we
       can print out all of the vstruct items in a row, and then
       finish off with a single :: <tm>. For example \x y z::Q.

       The accompanying can_print_vstructl function spots when the
       situation as described above pertains.  *)
    fun pr_res_vstructl restrictor res_op vsl = let
      val simples = map (Simple o bv2term) vsl
    in
      begin_block CONSISTENT 2;
      begin_block INCONSISTENT 2;
      pr_list pr_vstruct (fn () => ()) (fn () => add_break(1,0)) simples;
      end_block();
      add_string res_op;
      pr_term restrictor Top Top Top (depth - 1);
      end_block ()
    end
    fun can_print_vstructl vsl = let
      fun recurse acc [] = SOME acc
        | recurse acc ((Simple _)::_) = NONE
        | recurse acc (Restricted{Restrictor = t,...}::xs) = let
          in
            if t = acc then recurse acc xs else NONE
          end
    in
      case vsl of
        [] => raise PP_ERR "can_print_vstructl" "Empty list!"
      | (Simple _::xs) => NONE
      | (Restricted{Restrictor = t,...}::xs) => recurse t xs
    end

    (* the pr_vstructl function figures out which way to print a given
       list of vstructs *)
    fun pr_vstructl vsl =
      case can_print_vstructl vsl of
        SOME r => pr_res_vstructl r res_quanop vsl
      | _ => let
        in
          begin_block INCONSISTENT 2;
          pr_list pr_vstruct (fn () => ()) (fn () => add_break(1,0)) vsl;
          end_block ()
        end

    fun pr_abs tm = let
      val addparens = lgrav <> RealTop orelse rgrav <> RealTop
      val restr_binder =
        find_partial (fn (b,s) => if b = LAMBDA then SOME s else NONE)
        restr_binders
      val (bvars, body) = strip_vstructs NONE restr_binder tm
      val bvars_seen_here = List.concat (map (free_vars o bv2term) bvars)
      val old_seen = !bvars_seen
    in
      begin_block CONSISTENT 2; pbegin addparens;
      add_string lambda;
      pr_vstructl bvars;
      add_string endbinding; add_break (1,0);
      bvars_seen := bvars_seen_here @ old_seen;
      pr_term body Top Top Top (depth - 1);
      bvars_seen := old_seen;
      pend addparens; end_block()
    end

    fun atom_name tm = #Name (dest_var tm) handle _ => #Name (dest_const tm)
    fun can_pr_numeral stropt = List.exists (fn (k,s') => s' = stropt) num_info
    fun pr_numeral stropt tm =
      if #2 (hd num_info) = stropt then
        add_string (Arbnum.toString (Term.dest_numeral tm))
      else let
        val (k, _) = valOf (List.find (fn (_, s') => s' = stropt) num_info)
      in
        add_string (Arbnum.toString (Term.dest_numeral tm) ^ str k)
      end

    fun pr_comb tm t1 t2 = let
      val add_l =
        case lgrav of
           Prec (n, _) => (n >= comb_prec)
         | _ => false
      val add_r =
        case rgrav of
          Prec (n, _) => (n > comb_prec)
        | _ => false
      val addparens = add_l orelse add_r
      val _ =
        if is_numeral tm andalso can_pr_numeral NONE then
          (pr_numeral NONE tm; raise SimpleExit)
        else
          ()
      val _ =
        (if is_numeral t2 andalso can_pr_numeral (SOME (atom_name t1)) then
           (pr_numeral (SOME (atom_name t1)) t2; raise SimpleExit)
         else ()) handle SimpleExit => raise SimpleExit | _ => ()
      val _ =
        if my_is_abs tm then (pr_abs tm; raise SimpleExit)
        else ()
      val _ =
        if
          is_const t1 andalso #Name (dest_const t1) = "GSPEC" andalso
          my_is_abs t2 then let
            val (_, body) = my_dest_abs t2
            val {fst = l, snd = r} = dest_pair body
          in
            begin_block CONSISTENT 0;
            add_string "{"; begin_block CONSISTENT 0;
            pr_term l Top Top Top (depth - 1);
            spacep true; add_string "|"; spacep true;
            pr_term r Top Top Top (depth - 1);
            end_block(); add_string "}"; end_block(); raise SimpleExit
          end handle HOL_ERR _ => ()
        else ()
      val prec = Prec(comb_prec, fnapp_special)
      val lprec = if addparens then Top else lgrav
      val rprec = if addparens then Top else rgrav
    in
      begin_block INCONSISTENT 2;
      if addparens then add_string "(" else ();
      pr_term t1 prec lprec prec (depth - 1);
      add_break (1, 0);
      pr_term t2 prec prec rprec (depth - 1);
      if addparens then add_string ")" else ();
      end_block()
    end handle SimpleExit => ()

    fun pr_sole_name n rules = let
      fun check_rule rule =
        case rule of
          LISTRULE lrules => List.find (fn r => #nilstr r = n) lrules
        | _ => NONE
      val nilrule = find_partial check_rule rules
    in
      case nilrule of
        SOME r => add_string (#leftdelim r ^ #rightdelim r)
      | NONE => let
          (* if only rule is a list form rule and we've got to here, it
             will be a rule allowing this to the cons part of a list form.
             Such functions don't need to be dollar-ed *)
        in
          case rules of
            [LISTRULE _] => add_string n
          | _ =>
              if isSome (Polyhash.peek spec_table n) then add_string ("$"^n)
              else add_string n
        end
    end

    fun pr_comb_with_rule frule fterm args Rand = let
      val {fname,fprec,f} = fterm
      fun block_up_els acc els =
        case els of
          [] => List.rev acc
        | (e::es) => let
          in
            case e of
              EndInitialBlock bi =>
                block_up_els [PPBlock(List.rev acc, bi)] es
            | BeginFinalBlock bi => let
                val block_of_rest = block_up_els [] es
              in
                List.rev (PPBlock(block_of_rest, bi)::acc)
              end
            | x => block_up_els (x::acc) es
          end
      fun recurse_els (lprec, cprec, rprec) (els, args) = let
        val recurse = recurse_els (lprec, cprec, rprec)
      in
        case els of
          [] => args
        | (e :: es) => let
          in
            case e of
              PPBlock(more_els, (sty, ind)) => let
                val _ = begin_block sty ind
                val rest = recurse (more_els, args)
                val _ = end_block()
              in
                recurse (es, rest)
              end
            | HardSpace n => (add_string (string_of_nspaces n);
                              recurse (es, args))
            | BreakSpace (n, m) => (add_break(n,m); recurse (es, args))
            | RE (TOK s) => (add_string s; recurse (es, args))
            | RE TM => (pr_term (hd args) Top Top Top (depth - 1);
                        recurse (es, tl args))
            | FirstTM => (pr_term (hd args) cprec lprec cprec (depth - 1);
                          recurse (es, tl args))
            | LastTM => (pr_term (hd args) cprec cprec rprec (depth - 1);
                         recurse (es, tl args))
            | EndInitialBlock _ => raise Fail "term_pp - encountered EIB"
            | BeginFinalBlock _ => raise Fail "term_pp - encountered BFB"
          end
      end
    in
      case frule of
        INFIX(STD_infix(lst, fassoc)) => let
          val rr = hd lst
          val elements = #elements rr
          fun check_grav a grav =
            case grav of
              Prec(n, _) =>
                (n > fprec) orelse (n = fprec andalso a <> fassoc)
            | _ => false
          val parens_needed_outright =
            check_grav RIGHT lgrav orelse check_grav LEFT rgrav
          val parens_needed_by_style =
            pneeded_by_style(rr, pgrav, fname, fprec)
          val addparens = parens_needed_outright orelse parens_needed_by_style
          val prec = Prec(fprec, fname)
          val lprec = if addparens then Top else lgrav
          val rprec = if addparens then Top else rgrav
          val arg_terms = args @ [Rand]
          val pp_elements = block_up_els [] ((FirstTM::elements) @ [LastTM])
          val (begblock, endblock) = block_by_style(rr, pgrav, fname, fprec)
        in
          pbegin addparens; begblock();
          recurse_els (lprec, prec, rprec) (pp_elements, arg_terms);
          endblock (); pend addparens
        end
      | INFIX RESQUANOP => raise Fail "Res. quans shouldn't arise"
      | SUFFIX (STD_suffix lst) => let
          val rr = hd lst
          val elements = #elements rr
          val parens_needed_outright =
            case lgrav of
              Prec(n, _) => n > fprec
            | _ => false
          val parens_needed_by_style =
            pneeded_by_style (rr, pgrav, fname, fprec)
          val addparens = parens_needed_outright orelse parens_needed_by_style
          val lprec = if addparens then Top else lgrav
          val prec = Prec(fprec, fname)
          val real_args = args @ [Rand]
          val pp_elements = block_up_els [] (FirstTM :: elements)
          val (begblock, endblock) = block_by_style(rr, pgrav, fname, fprec)
        in
          begblock(); pbegin addparens;
          recurse_els (lprec, prec, Top) (pp_elements, real_args);
          pend addparens; endblock()
        end
      | SUFFIX TYPE_annotation =>
        raise Fail "Type annotation shouldn't arise"
      | PREFIX (STD_prefix lst) => let
          val rr = hd lst
          val elements = #elements rr
          val parens_needed_outright =
            case rgrav of
              Prec(n, _) => n > fprec
            | _ => false
          val addparens = parens_needed_outright orelse
            pneeded_by_style(rr, pgrav, fname, fprec)
          val rprec = if addparens then Top else rgrav
          val pp_elements = block_up_els [] (elements @ [LastTM])
          val real_args = args @ [Rand]
          val prec = Prec(fprec, fname)
          val (begblock, endblock) = block_by_style(rr, pgrav, fname, fprec)
        in
          begblock(); pbegin addparens;
          recurse_els (Top, prec, rprec) (pp_elements, real_args);
          pend addparens; endblock()
        end
      | PREFIX (BINDER _) => let
          fun find (BinderString bs, s) = if bs = fname then SOME s else NONE
            | find _ = NONE
          val restr_binder = find_partial find restr_binders
          val (bvs, body) = strip_vstructs (SOME fname) restr_binder tm
          val bvars_seen_here = List.concat (map (free_vars o bv2term) bvs)
          val old_seen = !bvars_seen
          val addparens =
            case rgrav of
              Prec(n, _) => n > fprec
            | _ => false
        in
          begin_block INCONSISTENT 2; pbegin addparens;
          add_string fname;
          spacep (not (symbolic fname));
          pr_vstructl bvs;
          add_string endbinding; spacep true;
          begin_block CONSISTENT 0;
          bvars_seen := bvars_seen_here @ old_seen;
          pr_term body Top Top Top (depth - 1);
          bvars_seen := old_seen;
          end_block ();
          pend addparens;
          end_block()
        end
      | CLOSEFIX lst => let
          val rr = hd lst
          val elements = #elements rr
        in
          uncurry begin_block (#2 (#block_style rr)) ;
          recurse_els (Top, Top, Top) (elements, args @ [Rand]);
          end_block()
        end
      | LISTRULE lrules => let
          val (r as {nilstr, cons, ...}) =
            valOf (List.find (fn r => #cons r = fname) lrules)
          val sep = #separator r
          val rdelim = #rightdelim r
          val ldelim = #leftdelim r
          (* list will never be empty *)
          fun pr_list tm = let
            fun recurse tm = let
              val (_, args) = strip_comb tm
              val head = hd args
              val tail = List.nth(args, 1)
            in
              if has_name nilstr tail then
                (* last element *)
                pr_term head Top Top Top (depth - 1)
              else let
              in
                pr_term head Top Top Top (depth - 1);
                add_string sep; spacep true;
                recurse tail
              end
            end
          in
            add_string ldelim; begin_block INCONSISTENT 0;
            recurse tm;
            end_block(); add_string rdelim
          end
        in
          pr_list tm
        end
      | FNAPP => raise PP_ERR "pr_term" "fn apps can't arise"
      | VSCONS => raise PP_ERR "pr_term" "vs cons can't arise"
    end

    fun pr_let lgrav rgrav tm = let
      fun find_base acc tm =
        if is_let tm then let
          val (let_tm, args) = strip_comb tm
        in
          find_base (List.nth(args, 1)::acc) (hd args)
        end
        else (acc, tm)
      fun pr_leteq (bv, tm2) = let
        val (args, rhs_t) = strip_vstructs NONE NONE tm2
        val bvars_seen_here = List.concat (map (free_vars o bv2term) args)
        val old_seen = (free_vars (bv2term bv)) @ (!bvars_seen)
      in
        pr_vstruct bv; spacep true;
        pr_list pr_vstruct (fn () => ()) (fn () => spacep true) args;
        bvars_seen := bvars_seen_here @ old_seen;
        spacep (not (null args));
        add_string "="; spacep true;
        pr_term rhs_t Top Top Top (depth - 1);
        bvars_seen := old_seen
      end
      val (values, abstraction) = find_base [] tm
      val (varnames, body) = strip_vstructs NONE NONE abstraction
    in
      if length varnames = length values then let
        val name_value_pairs = ListPair.zip (varnames, values)
        val addparens = lgrav <> RealTop orelse rgrav <> RealTop
        val old_bvars_seen = !bvars_seen
      in
        pbegin addparens; begin_block INCONSISTENT 2;
        add_string "let"; spacep true;
        begin_block INCONSISTENT 0;
        pr_list pr_leteq (fn () => (spacep true; add_string "and"))
                (fn () => spacep true) name_value_pairs;
        end_block();
        spacep true; add_string "in"; spacep true;
        (* a lie! but it works *)
        pr_term body RealTop RealTop RealTop (depth - 1);
        bvars_seen := old_bvars_seen;
        end_block(); pend addparens
      end
      else
        uncurry (pr_comb tm) ((fn {Rator,Rand} => (Rator,Rand)) (dest_comb tm))
    end
    fun print_ty_antiq tm = let
      val ty = dest_ty_antiq tm
    in
      begin_block CONSISTENT 2;
      add_string "(ty_antiq(";
      add_break(0,0);
      add_string "`:";
      type_pp.pp_type_with_depth TyG pps (depth - 1) ty;
      add_string "`))";
      end_block()
    end

    val _ = if is_ty_antiq tm then (print_ty_antiq tm; raise SimpleExit)
            else ()
  in
    if depth = 0 then add_string "..."
    else
      case (dest_term tm) of
        VAR{Name = vname, Ty} => let
          val vrule = lookup_term vname
          fun add_type () = let
          in
            add_string (" "^type_intro); add_break (0,0);
            type_pp.pp_type_with_depth TyG pps (depth - 1) Ty
          end
          val new_freevar =
            showtypes andalso (not (mem tm (!fvars_seen))) andalso
            not (mem tm (!bvars_seen)) andalso not binderp
          val _ = if new_freevar then fvars_seen := tm :: (!fvars_seen) else ()
          val print_type =
            showtypes andalso (binderp orelse new_freevar)
        in
          begin_block INCONSISTENT 2; pbegin print_type;
          if isSome vrule then pr_sole_name vname (map #2 (valOf vrule))
          else
            if isSome (Polyhash.peek spec_table vname) then
              add_string ("$"^vname)
            else
              add_string vname;
          if print_type then add_type() else ();
          pend print_type; end_block()
        end
      | CONST{Name = cname0, ...} => let
          val cname =
            case Overload.overloading_of_term overload_info tm of
              SOME s => s
            | NONE => cname0
          val crules = lookup_term cname
          fun print_string_literal s = let
            val contents0 = String.substring(s, 1, size s - 2)
            fun tr #"\\" = "\\\\"
              | tr #"\"" = "\\\""
              | tr #"\n" = "\\n"
              | tr c = str c
            val contents = String.translate tr contents0
          in
            add_string "\""; add_string contents; add_string "\""
          end
        in
          if isSome crules then pr_sole_name cname (map #2 (valOf crules))
          else
            if cname = "ZERO" andalso can_pr_numeral NONE then
              pr_numeral NONE tm
            else
              if Lexis.is_string_literal cname then
                print_string_literal cname
              else add_string cname
        end
      | COMB{Rator, Rand} => let
          val (f, args) = strip_comb Rator
          fun is_atom tm = is_const tm orelse is_var tm
          fun dest_atom tm = dest_var tm handle HOL_ERR _ => dest_const tm
          fun pr_atomf fname = let
            val candidate_rules = lookup_term fname
            fun is_list (r as {nilstr, cons, ...}) tm =
              (has_name nilstr tm) orelse
              is_comb tm andalso
              let
                val {Rator = t0, Rand = tail} = dest_comb tm
              in
                is_list r tail andalso is_comb t0 andalso
                has_name cons (#Rator (dest_comb t0))
              end
            val restr_binder =
              find_partial (fn (b,s) => if s = fname then SOME b else NONE)
              restr_binders
            val restr_binder_rule = let
              val condition =
                isSome restr_binder andalso length args = 1 andalso
                my_is_abs Rand
            in
              if condition then let
                val optrule =
                  lookup_term (binder_to_string G (valOf restr_binder))
                fun ok_rule (_, r) =
                  case r of PREFIX(BINDER _) => true | _ => false
              in
                case optrule of
                  SOME rule_list => List.find ok_rule rule_list
                | _ => NONE
              end
              else
                NONE
            end
          in
            case candidate_rules of
              NONE =>
                if is_let tm then pr_let lgrav rgrav tm
                else let
                in
                  case restr_binder of
                    NONE => pr_comb tm Rator Rand
                  | SOME LAMBDA =>
                      if isSome restr_binder_rule then pr_abs tm
                      else pr_comb tm Rator Rand
                  | SOME (BinderString bs) =>
                      if isSome restr_binder_rule then
                        pr_comb_with_rule (#2 (valOf restr_binder_rule))
                        {fprec = #1 (valOf restr_binder_rule),
                         fname = binder_to_string G (valOf restr_binder),
                         f = f} args Rand
                      else pr_comb tm Rator Rand
                end
            | SOME crules0 => let
                fun suitable_rule rule =
                  case rule of
                    INFIX(STD_infix(rrlist, _)) =>
                      numTMs (rule_elements (#elements (hd rrlist))) + 1 =
                      length args
                  | INFIX RESQUAN_OP => raise Fail "Can't happen 90212"
                  | PREFIX (STD_prefix list) =>
                      numTMs (rule_elements (#elements (hd list))) =
                      length args
                  | PREFIX (BINDER _) => my_is_abs Rand andalso length args = 0
                  | SUFFIX (STD_suffix list) =>
                      numTMs (rule_elements (#elements (hd list))) =
                      length args
                  | SUFFIX Type_annotation => raise Fail "Can't happen 90210"
                  | CLOSEFIX list =>
                      numTMs (rule_elements (#elements (hd list))) - 1 =
                      length args
                  | FNAPP => raise Fail "Can't happen 90211"
                  | VSCONS => raise Fail "Can't happen 90213"
                  | LISTRULE list => is_list (hd list) tm
                val crules = List.filter (suitable_rule o #2) crules0
                fun is_lrule (LISTRULE _) = true | is_lrule _ = false
                fun is_binder_rule (PREFIX (BINDER s)) = true
                  | is_binder_rule _ = false
                val (lrules, others0) = splitP (is_lrule o #2) crules
                val (brules, others) = splitP (is_binder_rule o #2) others0
              in
                if not (null brules) then
                  pr_comb_with_rule (#2 (hd brules)) {fprec = #1 (hd brules),
                                                      fname = fname,
                                                      f = f}
                  args Rand
                else
                  if not (null lrules) then
                    pr_comb_with_rule (#2 (hd lrules)) {fprec = #1 (hd lrules),
                                                        fname = fname, f = f}
                    args Rand
                  else
                    if not (null others) then let
                      val preferred =
                        List.find (#preferred o hd o rule_to_rr o #2) others
                    in
                      case preferred of
                        SOME (p,r) =>
                          pr_comb_with_rule r {fprec = p, fname = fname, f = f}
                          args Rand
                      | NONE => pr_comb tm Rator Rand
                    end
                    else
                      pr_comb tm Rator Rand
              end
          end
        in
          if (is_atom f) then let
            val name_to_use =
              case (Overload.overloading_of_term overload_info f) of
                SOME s => s
              | NONE => #Name (dest_atom f)
          in
            pr_atomf name_to_use
          end
          else pr_comb tm Rator Rand
        end
      | LAMB{Bvar, Body} => pr_abs tm
  end handle SimpleExit => ()
  fun start_names() = {fvars_seen = ref [], bvars_seen = ref []}
in
  (fn pps => fn t => let
  in
    Portable.begin_block pps CONSISTENT 0;
    pr_term false (!Globals.show_types) (start_names())
    pps t RealTop RealTop RealTop (!Globals.max_print_depth);
    Portable.end_block pps
  end)
end

(* testing
use "term_pp.sml";
val G = let
  open term_grammar
  infix Gmerge
in
  stdhol Gmerge simple_arith Gmerge semantics_rules
end
fun p tm =
  Portable.pp_to_string 75
   (fn pp => fn tm => pp_term G parse_type.BaseHOLgrammar pp tm) tm;
fun pr q = print (p (Term q) ^ "\n")

new_type {Name = "fmap", Arity = 2};

val G' = [(0, parse_type.INFIX("->", "fun", parse_type.RIGHT)),
     (1, parse_type.INFIX("=>", "fmap", parse_type.NONASSOC)),
     (2, parse_type.INFIX("+", "sum", parse_type.LEFT)),
     (3, parse_type.INFIX("#", "prod", parse_type.RIGHT)),
     (100, parse_type.SUFFIX("list", true)),
     (101, parse_type.SUFFIX("fun", false)),
     (102, parse_type.SUFFIX("prod", false)),
     (103, parse_type.SUFFIX("sum", false))];
fun p ty =
  Portable.pp_to_string 75
   (fn pp => fn ty => type_pp.pp_type G' pp ty type_pp.Top 100) ty;

p (Type`:(bool,num)fmap`)

*)
