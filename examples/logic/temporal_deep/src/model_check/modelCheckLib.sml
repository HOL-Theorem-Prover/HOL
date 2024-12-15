structure modelCheckLib :> modelCheckLib =
struct

open HolKernel boolLib bossLib
    full_ltlTheory arithmeticTheory automaton_formulaTheory xprop_logicTheory prop_logicTheory
     infinite_pathTheory tuerk_tacticsLib symbolic_semi_automatonTheory listTheory pred_setTheory
     temporal_deep_mixedTheory pred_setTheory rich_listTheory set_lemmataTheory pairTheory pred_setSyntax
     ltl_to_automaton_formulaTheory numLib listLib listSyntax translationsLibTheory
     rltl_to_ltlTheory rltlTheory computeLib congLib temporal_deep_simplificationsLib
     Trace symbolic_kripke_structureTheory Varmap psl_lemmataTheory ProjectionTheory psl_to_rltlTheory
     translationsLib temporalLib ctl_starTheory;

(* this is Moscow ML only *)
open bdd;

(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)


val model_check_temp_file = ref "smv_file.smv";


val _ = init 10000000 1000000;

local
  fun get_const t =
      if (is_const t) then dest_const t else get_const (rator t)


  (*Translates a prop_logic formula that may contain only basic operators
    to an sml string. Thefore it uses the mapping of propositional variables
    to numbers given by the map parameter. Additionally this map is
    extended if new propositional variables are found.*)

  exception translation2smv_exp

  fun get_arg_num (map, maxindex) term =
    let
      val num_option = Binarymap.peek (map, term);
    in
      if (isSome num_option) then
        (valOf num_option, (map, maxindex))
      else
        let
          val map = Binarymap.insert (map, term, maxindex+1);
        in
          (maxindex+1, (map, maxindex+1))
        end
    end;

  fun get_arg_var uv term =
    let
      val (num, uv) = get_arg_num uv term
      val s = "x"^(int_to_string num);
    in
      (s, uv)
    end;


  fun prop_list_to_var_list uv [] = ([], uv) |
      prop_list_to_var_list uv (e::l) =
        let
          val (num, uv) = get_arg_num uv e;
          val _ = if (getVarnum () < (2*num+2)) then setVarnum (2*num+2) else ();
          val (l, uv) = prop_list_to_var_list uv l;
        in
          ((2*num)::l, uv)
        end;

  fun xprop_prop_logic_to_bdd (uv:((term, int) Binarymap.dict * int)) term =
    let
      val (f, _) = get_const term;
    in
      if ((f = "XP_TRUE") orelse (f = "P_TRUE")) then (TRUE, uv) else
      if ((f = "XP_FALSE") orelse (f = "P_FALSE")) then (FALSE, uv) else
      if ((f = "XP_PROP") orelse (f = "P_PROP")) then
        let
          val arg = rand term;
          val (num, uv) = get_arg_num uv arg
          val _ = if (getVarnum () < (2*num+2)) then setVarnum (2*num+2) else ();
          val s = ithvar (2*num);
        in
          (s, uv)
        end else
      if (f = "XP_NEXT_PROP") then
        let
          val arg = rand term;
          val (num, uv) = get_arg_num uv arg
          val _ = if (getVarnum() < (2*num+1)) then setVarnum (2*num+2) else ();
          val s = ithvar (2*num+1);
        in
          (s, uv)
        end else
      if ((f = "XP_NOT") orelse (f = "P_NOT")) then
        let
          val arg = rand term;
          val (s, uv) = xprop_prop_logic_to_bdd uv arg
        in
          (NOT s, uv)
        end else
      if ((f = "XP_AND") orelse (f = "P_AND")) then
        let
          val (arg1,arg2) = dest_pair (rand term);
          val (s1, uv) = xprop_prop_logic_to_bdd uv arg1
          val (s2, uv) = xprop_prop_logic_to_bdd uv arg2
        in
          (AND (s1, s2), uv)
        end else
      if ((f = "XP_OR") orelse (f = "P_OR")) then
        let
          val (arg1,arg2) = dest_pair (rand term);
          val (s1, uv) = xprop_prop_logic_to_bdd uv arg1
          val (s2, uv) = xprop_prop_logic_to_bdd uv arg2
        in
          (OR (s1, s2), uv)
        end else
      if ((f = "XP_IMPL") orelse (f = "P_IMPL")) then
        let
          val (arg1,arg2) = dest_pair (rand term);
          val (s1, uv) = xprop_prop_logic_to_bdd uv arg1
          val (s2, uv) = xprop_prop_logic_to_bdd uv arg2
        in
          (IMP (s1, s2), uv)
        end else
      if ((f = "XP_EQUIV") orelse (f = "P_EQUIV"))then
        let
          val (arg1,arg2) = dest_pair (rand term);
          val (s1, uv) = xprop_prop_logic_to_bdd uv arg1
          val (s2, uv) = xprop_prop_logic_to_bdd uv arg2
        in
          (BIIMP (s1, s2), uv)
        end else
      if ((f = "XP_COND") orelse (f = "P_COND")) then
        let
          val arg_list = strip_pair (rand term);
          val (arg1,arg2, arg3) = (el 1 arg_list, el 2 arg_list, el 3 arg_list);
          val (s1, uv) = xprop_prop_logic_to_bdd uv arg1
          val (s2, uv) = xprop_prop_logic_to_bdd uv arg2
          val (s3, uv) = xprop_prop_logic_to_bdd uv arg3
        in
          (ITE s1 s2 s3, uv)
        end else
      if ((f = "XP_CURRENT_EXISTS") orelse (f = "P_EXISTS")) then
        let
          val p = rand term;
          val l = fst (dest_list (rand (rator term)));
          val (s, uv) = xprop_prop_logic_to_bdd uv p
          val (l', uv) = prop_list_to_var_list uv l
        in
          (bdd.exist (bdd.makeset l') s, uv)
        end else
      if ((f = "XP_CURRENT_FORALL") orelse (f = "P_FORALL")) then
        let
          val p = rand term;
          val l = fst (dest_list (rand (rator term)));
          val (s, uv) = xprop_prop_logic_to_bdd uv p
          val (l', uv) = prop_list_to_var_list uv l
        in
          (bdd.forall (bdd.makeset l') s, uv)
        end else
      if ((f = "XP_NEXT_EXISTS")) then
        let
          val p = rand term;
          val l = fst (dest_list (rand (rator term)));
          val (s, uv) = xprop_prop_logic_to_bdd uv p
          val (l', uv) = prop_list_to_var_list uv l
          val l' = map (fn x => x + 1) l';
        in
          (bdd.exist (bdd.makeset l') s, uv)
        end else
      if ((f = "XP_NEXT_FORALL")) then
        let
          val p = rand term;
          val l = fst (dest_list (rand (rator term)));
          val (s, uv) = xprop_prop_logic_to_bdd uv p
          val (l', uv) = prop_list_to_var_list uv l
          val l' = map (fn x => x + 1) l';
        in
          (bdd.forall (bdd.makeset l') s, uv)
        end else
          let
            val _ = print ("\n\nERROR!!! UNKNOWN LOGIC TERM "^f^"\n");
            val _ = print_term term;
            val _ = print "\n\n";
          in
            raise translation2smv_exp
          end
    end;

(*
val t = ``XP_NEXT_EXISTS [2] (XP_COND (XP_NEXT_PROP 1, XP_NEXT_PROP 2, XP_PROP 3))``;
val t = ``P_COND (P_PROP 1, P_PROP 2, P_PROP 3)``;
dest_pair (rator t)

val uv = ((Binarymap.mkDict compare):(term, int) Binarymap.dict, 0);
val (b, _) = xprop_prop_logic_to_bdd uv t

printset b
val set = Intset.empty
help "intset"

hash b
definitions_of_bdd TextIO.stdOut b Intset.empty

val t = ``P_COND (P_PROP 1, P_PROP 2, P_PROP 3)``;
dest_pair (rator t)

val uv = ((Binarymap.mkDict compare):(term, int) Binarymap.dict, 0);
val (b, _) = xprop_prop_logic_to_bdd uv t

val set = Intset.empty
help "intset"

*)

  fun num_to_var_string n =
    let
      val next_var = (n mod 2 = 1);
      val var_s = "x"^(int_to_string (n div 2))
      val var_s = if (next_var) then "next("^var_s^")" else var_s;
    in
      var_s
    end;

  fun bdd_to_definition b =
    if (bdd.hash b = 1) then "1" else
    if (bdd.hash b = 0) then "0" else
    if (((bdd.hash (bdd.high b) = 1) andalso (bdd.hash (bdd.low b) = 0))) then (num_to_var_string (bdd.var b)) else
    if (((bdd.hash (bdd.high b) = 0) andalso (bdd.hash (bdd.low b) = 1))) then ("!"^(num_to_var_string (bdd.var b))) else
    "def_"^(int_to_string (hash b));



  fun add_def file_st b =
    let
      val def = bdd_to_definition b;
    in
      if (String.isPrefix "def_" def) then
        let
          val var_s = num_to_var_string (bdd.var b);

          val res = if ((bdd.hash (bdd.high b) = 1)) then
                        ("("^(num_to_var_string (bdd.var b))^" | "^bdd_to_definition (low b)^")") else
                    if ((bdd.hash (bdd.low b) = 1)) then
                        ("(!"^(num_to_var_string (bdd.var b))^" | "^bdd_to_definition (high b)^")") else
                    if ((bdd.hash (bdd.high b) = 0)) then
                        ("(!"^(num_to_var_string (bdd.var b))^" & "^bdd_to_definition (low b)^")") else
                    if ((bdd.hash (bdd.low b) = 0)) then
                        ("("^(num_to_var_string (bdd.var b))^" & "^bdd_to_definition (high b)^")") else
                    "("^ var_s ^" & "^(bdd_to_definition (high b))^") | (!"^var_s^" & "^(bdd_to_definition (low b)) ^")";
          val res = def ^ " := " ^ res ^";\n";
          val _ = TextIO.output(file_st,res);
          val _ = TextIO.flushOut file_st;
        in
          ()
        end
      else
        ()
    end;


  fun definitions_of_bdd file_st s [] = () |
      definitions_of_bdd file_st s (b::bl) =

    let
      val (s, bl) =
        if (bdd.hash b = 1) then (s, bl) else
        if (bdd.hash b = 0) then (s, bl) else
        if (Intset.member (s,(hash b))) then (s, bl) else
        let
          val s = Intset.add (s, (hash b));
          val _ = add_def file_st b;
          val bl = (high b)::(low b)::bl;
        in
          (s, bl)
        end;
    in
      definitions_of_bdd file_st s bl
    end;


  fun ctl_to_smv uv term =
    let
      val (f, _) = get_const term;
    in
      if (f = "CTL_TRUE") then ("TRUE", uv, []) else
      if (f = "CTL_FALSE") then ("FALSE", uv, []) else
      if (f = "CTL_PROP") then
        let
          val p_term = rand term;
          val (p_bdd, uv) = xprop_prop_logic_to_bdd uv p_term;
          val p_string = bdd_to_definition p_bdd;
        in
          (p_string, uv, [p_bdd])
        end else
      if (f = "CTL_NOT") then
        let
          val arg = rand term;
          val (arg_string, uv, bdds) =  ctl_to_smv uv arg;
        in
          ("!("^arg_string^")", uv, bdds)
        end else
      if (f = "CTL_AND") then
        let
          val (arg1,arg2) = dest_pair (rand term);
          val (arg1_string, uv, bdds1) =  ctl_to_smv uv arg1;
          val (arg2_string, uv, bdds2) =  ctl_to_smv uv arg2;
        in
          ("("^arg1_string^") & ("^arg2_string^")", uv, bdds1 @ bdds2)
        end else
      if (f = "CTL_OR") then
        let
          val (arg1,arg2) = dest_pair (rand term);
          val (arg1_string, uv, bdds1) =  ctl_to_smv uv arg1;
          val (arg2_string, uv, bdds2) =  ctl_to_smv uv arg2;
        in
          ("("^arg1_string^") | ("^arg2_string^")", uv, bdds1 @ bdds2)
        end else
      if (f = "CTL_IMPL") then
        let
          val (arg1,arg2) = dest_pair (rand term);
          val (arg1_string, uv, bdds1) =  ctl_to_smv uv arg1;
          val (arg2_string, uv, bdds2) =  ctl_to_smv uv arg2;
        in
          ("("^arg1_string^") -> ("^arg2_string^")", uv, bdds1 @ bdds2)
        end else
      if (f = "CTL_EQUIV") then
        let
          val (arg1,arg2) = dest_pair (rand term);
          val (arg1_string, uv, bdds1) =  ctl_to_smv uv arg1;
          val (arg2_string, uv, bdds2) =  ctl_to_smv uv arg2;
        in
          ("("^arg1_string^") <-> ("^arg2_string^")", uv, bdds1 @ bdds2)
        end else
      if (f = "CTL_E_NEXT") then
        let
          val arg = rand term;
          val (arg_string, uv, bdds) =  ctl_to_smv uv arg;
        in
          ("EX ("^arg_string^")", uv, bdds)
        end else
      if (f = "CTL_A_NEXT") then
        let
          val arg = rand term;
          val (arg_string, uv, bdds) =  ctl_to_smv uv arg;
        in
          ("AX ("^arg_string^")", uv, bdds)
        end else
      if (f = "CTL_E_ALWAYS") then
        let
          val arg = rand term;
          val (arg_string, uv, bdds) =  ctl_to_smv uv arg;
        in
          ("EG ("^arg_string^")", uv, bdds)
        end else
      if (f = "CTL_A_ALWAYS") then
        let
          val arg = rand term;
          val (arg_string, uv, bdds) =  ctl_to_smv uv arg;
        in
          ("AG ("^arg_string^")", uv, bdds)
        end else
      if (f = "CTL_E_EVENTUAL") then
        let
          val arg = rand term;
          val (arg_string, uv, bdds) =  ctl_to_smv uv arg;
        in
          ("EF ("^arg_string^")", uv, bdds)
        end else
      if (f = "CTL_A_EVENTUAL") then
        let
          val arg = rand term;
          val (arg_string, uv, bdds) =  ctl_to_smv uv arg;
        in
          ("AF ("^arg_string^")", uv, bdds)
        end else
      if (f = "CTL_E_SUNTIL") then
        let
          val (arg1,arg2) = dest_pair (rand term);
          val (arg1_string, uv, bdds1) =  ctl_to_smv uv arg1;
          val (arg2_string, uv, bdds2) =  ctl_to_smv uv arg2;
        in
          ("E (("^arg1_string^") U ("^arg1_string^"))", uv, bdds1 @ bdds2)
        end else
      if (f = "CTL_E_UNTIL") then
        let
          val (arg1,arg2) = dest_pair (rand term);
          val (arg1_string, uv, bdds1) =  ctl_to_smv uv arg1;
          val (arg2_string, uv, bdds2) =  ctl_to_smv uv arg2;
        in
          ("(E (("^arg1_string^") U ("^arg2_string^"))) | (EG ("^arg1_string^"))", uv, bdds1 @ bdds2)
        end else
      let
        val _ = print ("\n\nERROR!!! UNKNOWN TERM "^f^"\n");
        val _ = print_term term;
        val _ = print "\n\n";
      in
        raise translation2smv_exp
      end
    end

  in

  fun ctl_ks_fair2smv_string ks_term file_st =
      let
        val p_term = rand (rator (rand (rator ((rator (ks_term))))))
        val xp_term = rand (rand (rator (rator (ks_term))))
        val (fc, _) = dest_list (rand ks_term)
        val ctl = rand (rator (ks_term))

        val uv = ((Binarymap.mkDict compare):(term, int) Binarymap.dict, 0);


        val (p_bdd, uv) = xprop_prop_logic_to_bdd uv p_term;
        val p_string = bdd_to_definition p_bdd;
        val (xp_bdd, uv) = xprop_prop_logic_to_bdd uv xp_term
        val xp_string = bdd_to_definition xp_bdd;
        val (ctl_string, uv, ctl_bdds) = ctl_to_smv uv ctl

        fun fairness_string uv [] = ("", uv, []) |
            fairness_string uv (e::l) =
              let
                val (fc_bdd, uv) = xprop_prop_logic_to_bdd uv e
                val fc_string = bdd_to_definition fc_bdd;

                val (FC_string, uv, bdds) = fairness_string uv l;
              in
                ("FAIRNESS ("^fc_string^")\n"^FC_string, uv, fc_bdd::bdds)
              end;
        val (fc_string, uv, fc_bdds) = fairness_string uv fc;



        fun used_vars_add s b =
          Vector.foldl (fn (n, s) => Intset.add (s, n div 2)) s (scanset (support b));

        val vars = Intset.empty;
        val vars = used_vars_add vars p_bdd;
        val vars = used_vars_add vars xp_bdd;
        val vars = foldl (fn (b, s) => used_vars_add s b) vars (fc_bdds@ctl_bdds);

        fun varstring 0 = "" |
            varstring n =
              if (Intset.member (vars, n)) then
                (varstring (n-1))^"   x"^(int_to_string n)^": boolean;\n"
              else
                (varstring (n-1));


        val ks_string = term_to_string ks_term;
        val ks_string_list = String.fields (fn x=> (x = #"\n")) ks_string
        val _ = map (fn x => TextIO.output(file_st, "-- "^x^"\n")) ks_string_list;
        val _ = TextIO.output(file_st, "\n\n");
        val _ = TextIO.output(file_st, "-- used variables\n\n");
        val _ = TextIO.flushOut file_st;

        fun varrenaming_foldr ((term, var), s) =
          let
            val x = "x"^(int_to_string var);
            val t = term_to_string term;
            val line = x^": "^t^"\n";
            val _ = TextIO.output(file_st, "-- "^line);
            val _ = TextIO.flushOut file_st;
          in
            (s^line)
          end;
        val varrenaming_list = Binarymap.listItems (fst uv);
        val varrenaming_list = sort (fn (_, x) => fn (_, y) => (x > y)) varrenaming_list;

        val varrenaming_string = foldr varrenaming_foldr "" varrenaming_list;

        val _ = TextIO.output(file_st,"MODULE main\n\n"^
                     "VAR\n"^(varstring (#2 uv))^"\n"^
                     "INIT \n"^(p_string)^"\n\n"^
                     "TRANS \n"^(xp_string)^"\n\n"^
                     (fc_string)^"\n\n"^
                     "DEFINE\n");
        val _ = TextIO.flushOut file_st;


        val s = Intset.empty;
        val bl = p_bdd::xp_bdd::(fc_bdds@ctl_bdds);
        val _ = definitions_of_bdd file_st s bl;

        val _ = TextIO.output(file_st,"\n\nCTLSPEC "^ctl_string^"\n\n");
        val _ = TextIO.flushOut file_st;

      in
        varrenaming_string
      end;
  end;


fun fair_empty_ks2smv_string term file_st =
  let
    val ks_term = rhs (concl (REWRITE_CONV [IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE___TO___CTL_KS_FAIR_SEM] term));
  in
    ctl_ks_fair2smv_string ks_term file_st
  end;


fun modelCheckFairEmptyness ks_term thm =
  let
    val file_st = TextIO.openOut(!model_check_temp_file);
    val vars = fair_empty_ks2smv_string ks_term file_st;
    val _ = TextIO.closeOut file_st;
    val res = SMV_RUN_FILE (!model_check_temp_file);

  in
    if (res) then true else
    let
      val _ = print vars;
      val _ = print "===============================================\n";
      val _ = print_thm thm;
      val _ = print "\n===============================================\n";
    in
      false
    end
  end;


fun model_check___ks_fair_emptyness thm =
    let
      val ks_term = rhs (rand (body (rand (concl thm))))
      val eq_term = lhs (rand (body (rand (concl thm))))
      val erg = modelCheckFairEmptyness ks_term thm;
      val thm = if erg then (SOME (mk_oracle_thm "SMV" ([], eq_term))) else NONE
    in
      thm
    end


fun model_check___ltl_contradiction f =
    let
      val thm = ltl_contradiction2ks_fair_emptyness true f
    in
      model_check___ks_fair_emptyness thm
    end

fun model_check___ltl_equivalent l1 l2 =
    let
      val thm = ltl_equivalent2ks_fair_emptyness true l1 l2
    in
      model_check___ks_fair_emptyness thm
    end

fun model_check___ltl_equivalent_initial l1 l2 =
    let
      val thm = ltl_equivalent_initial2ks_fair_emptyness true l1 l2
    in
      model_check___ks_fair_emptyness thm
    end

fun model_check___ltl_ks_sem l M =
    let
      val thm = ltl_ks_sem2ks_fair_emptyness true l M
    in
      model_check___ks_fair_emptyness thm
    end

fun model_check___psl_contradiction f =
    let
      val thm = psl_contradiction2ks_fair_emptyness true f
    in
      model_check___ks_fair_emptyness thm
    end

fun model_check___psl_equivalent f1 f2 =
    let
      val thm = psl_equivalent2ks_fair_emptyness true f1 f2
    in
      model_check___ks_fair_emptyness thm
    end

fun model_check___psl_ks_sem f M =
    let
      val thm = psl_ks_sem2ks_fair_emptyness true f M
    in
      model_check___ks_fair_emptyness thm
    end

(* examples:

val ltl1 = ``LTL_SUNTIL (LTL_PROP (P_PROP a), LTL_PROP (P_PROP b))``;

val ltl2 = ``LTL_EVENTUAL (LTL_AND (LTL_PROP (P_PROP b),
                                    LTL_PNEXT (LTL_PALWAYS (LTL_PROP (P_PROP a)))))``;

(* SOME thm *)
model_check___ltl_equivalent_initial ltl1 ltl2;

(* NONE *)
model_check___ltl_equivalent ltl1 ltl2;

*)

end
