(****************************************************************************)
(* FILE          : cong_types.sml                                           *)
(* DESCRIPTION   : Deciding the equational theory of recursively defined    *)
(*                 types using congruence closure.                          *)
(*                 Also handles uninterpreted function symbols.             *)
(*                                                                          *)
(* AUTHOR        : R.J.Boulton                                              *)
(* DATE          : 10th March 1995                                          *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 19th August 1996                                         *)
(****************************************************************************)

structure CongruenceClosureTypes =
struct

local

open Exception Lib Term Dsyntax Drule Psyntax 
     DecisionConv DecisionSupport DecisionNormConvs Decide
     CongruenceClosure HOLTypeInfo LazyThm LazyRules;

fun failwith function =
   raise HOL_ERR{origin_structure = "CongruenceClosureTypes",
                 origin_function = function,
                 message = ""};

type thm = LazyThm.pre_thm;

fun EXISTS_HYP vars tm =
   let fun process_hyps rs [] = rs @ [list_mk_exists (vars,tm)]
         | process_hyps rs (h :: hs) =
          if (h = tm)
          then if (null (intersect vars (free_varsl hs)))
               then rs @ (rev hs) @ [list_mk_exists (vars,h)]
               else failwith "EXISTS_HYP"
          else if (null (intersect vars (free_vars h)))
               then process_hyps (h :: rs) hs
               else failwith "EXISTS_HYP"
       fun exists_hyp (hyps,conc) =
          if (null (intersect vars (free_vars conc)))
          then (process_hyps [] hyps,
                list_mk_forall (subtract vars (free_vars tm),conc))
          else failwith "EXISTS_HYP"
   in  apply_rule1 (exists_hyp,HOLTypeInfo.EXISTS_HYP vars tm)
   end;

in

(*--------------------------------------------------------------------------*)
(* INJECTIVE_REDUCTION : (string * conv) list -> thm -> thm list            *)
(*                                                                          *)
(* Splits a theorem of the form |- C x_1 ... x_n = C y_1 ... y_n where C is *)
(* a type constructor into n theorems |- x_1 = y_1, ..., |- x_n = y_n which *)
(* are then processed recursively. If the theorem is not of the specified   *)
(* form it is returned unchanged in a one-element list.                     *)
(*                                                                          *)
(* The first argument is an association list of constructor names and       *)
(* injectivity theorems for the constructors, where the theorems are given  *)
(* as conversions.                                                          *)
(*--------------------------------------------------------------------------*)

fun INJECTIVE_REDUCTION injectivity_convs th =
   let val eq = concl th
       val (l,r) = dest_eq eq
       val lname = name_of_operator l
       and rname = name_of_operator r
       val lconv = assoc lname injectivity_convs
       and rconv = assoc rname injectivity_convs
   in  if (lname = rname)
       then flat (map (INJECTIVE_REDUCTION injectivity_convs)
                     (CONJUNCTS (EQ_MP (lconv eq) th)))
       else [th]
   end
   handle HOL_ERR _ => [th];

(*--------------------------------------------------------------------------*)
(* choose_new_vars : term -> (thm -> thm) * thm                             *)
(*                                                                          *)
(* Chooses new unique variables for an existentially quantified equation.   *)
(*                                                                          *)
(* The argument should be a term of the form ?x_1 ... x_n. l[x_i] = r[x_i]. *)
(* The result is a pair. The second component is a theorem of the form:     *)
(*                                                                          *)
(*    l[v_i] = r[v_i] |- l[v_i] = r[v_i]                                    *)
(*                                                                          *)
(* where the v_i's are new unique variables corresponding to the x_i's.     *)
(*                                                                          *)
(* The first component of the result is a function that given a theorem:    *)
(*                                                                          *)
(*    l[v_i] = r[v_i] |- F                                                  *)
(*                                                                          *)
(* returns:                                                                 *)
(*                                                                          *)
(*    ?v_1 ... v_n. l[v_i] = r[v_i] |- F                                    *)
(*                                                                          *)
(* Thus, the intention is for the second component to be used in deriving   *)
(* false, and the first to make the hypothesis alpha-equivalent to the      *)
(* argument term.                                                           *)
(*--------------------------------------------------------------------------*)

fun choose_new_vars tm =
   let val (vars,eq) = strip_exists tm
       val newvars = map (genvar o type_of) vars
       val neweq = subst (zip newvars vars) eq
       val newtm = list_mk_exists (newvars,neweq)
   in  (fn falseth => EXISTS_HYP newvars neweq falseth,ASSUME neweq)
   end;

(*--------------------------------------------------------------------------*)
(* ELIMINATE_DISCRIMINATOR :                                                *)
(*    thm hol_discriminator_info list -> thm -> (thm -> thm) * thm          *)
(*                                                                          *)
(* Eliminates an application of a type discriminator.                       *)
(*                                                                          *)
(* The first argument is a list of information about discriminators (see    *)
(* the documentation elsewhere). The second should be a theorem of the form *)
(* A |- D_i x. The result is a pair, the second component of which is a     *)
(* theorem of the form:                                                     *)
(*                                                                          *)
(*    x = C_i vars |- x = C_i vars                                          *)
(*                                                                          *)
(* where C_i is the constructor recognised by D_i, and vars are new unique  *)
(* variables.                                                               *)
(*                                                                          *)
(* The first component of the result is a function that given a theorem:    *)
(*                                                                          *)
(*    A, x = C_i vars |- F                                                  *)
(*                                                                          *)
(* returns:                                                                 *)
(*                                                                          *)
(*    A |- F                                                                *)
(*--------------------------------------------------------------------------*)

fun ELIMINATE_DISCRIMINATOR
       (discr_infos : thm hol_discriminator_info list) th =
   let val discr_info =
          gen_assoc #name (name_of_operator (concl th)) discr_infos
       val elim = #conversion (#positive_elimination discr_info)
       val th' = CONV_RULE elim th
       val tm' = concl th'
       val (f,eqth) = choose_new_vars tm'
   in  (fn falseth => MP (DISCH tm' (f falseth)) th',eqth)
   end;

(*--------------------------------------------------------------------------*)
(* ELIMINATE_NEGATED_DISCRIMINATOR :                                        *)
(*    thm hol_discriminator_info list -> thm ->                             *)
(*    (thm list -> thm) * thm list                                          *)
(*                                                                          *)
(* Eliminates a negated application of a type discriminator.                *)
(*                                                                          *)
(* The first argument is a list of information about discriminators (see    *)
(* the documentation elsewhere). The second should be a theorem of the form *)
(* A |- ~(D_i x). The result is a pair, the second component of which is a  *)
(* list of theorems:                                                        *)
(*                                                                          *)
(*    x = C_1 vars_1 |- x = C_1 vars_1                                      *)
(*    ...                                                                   *)
(*    x = C_i-1 vars_i-1 |- x = C_i-1 vars_i-1                              *)
(*    x = C_i+1 vars_i+1 |- x = C_i+1 vars_i+1                              *)
(*    ...                                                                   *)
(*    x = C_n vars_n |- x = C_n vars_n                                      *)
(*                                                                          *)
(* where the C's are the constructors of the type that are NOT recognised   *)
(* by D_i, and the vars are new unique variables.                           *)
(*                                                                          *)
(* The first component of the result is a function that given a list of     *)
(* theorems:                                                                *)
(*                                                                          *)
(*    A, x = C_1 vars_1 |- F                                                *)
(*    ...                                                                   *)
(*    A, x = C_i-1 vars_i-1 |- F                                            *)
(*    A, x = C_i+1 vars_i+1 |- F                                            *)
(*    ...                                                                   *)
(*    A, x = C_n vars_n |- F                                                *)
(*                                                                          *)
(* returns:                                                                 *)
(*                                                                          *)
(*    A |- F                                                                *)
(*--------------------------------------------------------------------------*)

fun ELIMINATE_NEGATED_DISCRIMINATOR
       (discr_infos : thm hol_discriminator_info list) th =
   let val discr_info =
          gen_assoc #name (name_of_operator (dest_neg (concl th))) discr_infos
       val elim = #conversion (#negative_elimination discr_info)
       val th' = CONV_RULE elim th
       val tm' = concl th'
   in  if (is_F tm')
       then (fn _ => th',[])
       else let val (fs,eqths) = unzip (map choose_new_vars (strip_disj tm'))
            in  (fn falseths => Decide.LIST_DISJ_CASES th'
                                   (map2 (fn f => fn x => f x) fs falseths),
                 eqths)
            end
   end;

(*--------------------------------------------------------------------------*)
(* refute_distinct : (term -> bool) ->                                      *)
(*                   (string -> string * string -> thm) ->                  *)
(*                   equivalence ->                                         *)
(*                   thm                                                    *)
(*                                                                          *)
(* Proves false from an equivalence class that contains terms headed by     *)
(* distinct type constructors.                                              *)
(*                                                                          *)
(* The first argument is a predicate that returns true when given a term    *)
(* headed by a constructor. The second is a function that when given a type *)
(* (the name of the HOL type associated with the terms in the equivalence   *)
(* class, e.g., "list") and the names of two (distinct) constructors        *)
(* returns a theorem stating that applications of the constructors are not  *)
(* equal. The third argument is the equivalence class.                      *)
(*--------------------------------------------------------------------------*)

fun refute_distinct is_constructor
       (distinctf : string -> string * string -> thm * thm eqthm_info) equiv =
   let fun head ((_,f),_) = f
       and index ((i,_),_) = i
       val is_constructor_node = is_constructor o head
       val constr_nodes = filter_equivalence is_constructor_node equiv
       val named_nodes =
          map (fn node => (name_of_const (head node),node)) constr_nodes
       fun distinct_nodes _ [] = failwith ""
         | distinct_nodes
              (name1,((i1,_),tm1)) ((node as (name2,((i2,_),_)))::nodes) =
          if (name2 = name1)
          then distinct_nodes node nodes
          else ((i1,i2),(name1,name2),
                (#Tyop o Rsyntax.dest_type o type_of) tm1)
   in  if (null constr_nodes)
       then failwith ""
       else let val (is,names,tyname) =
                   distinct_nodes (hd named_nodes) (tl named_nodes)
                val eqth = equal_to is equiv
                val diseqconv = (#conversion o #2 o distinctf tyname) names
            in  CONV_RULE diseqconv eqth
            end
   end
   handle _ => failwith "refute_distinct";

(*--------------------------------------------------------------------------*)
(* refute_distincts : (term -> bool) ->                                     *)
(*                    (string -> string * string -> thm) ->                 *)
(*                    equivalence list ->                                   *)
(*                    thm                                                   *)
(*                                                                          *)
(* Proves false from a list of equivalence classes if any of them contain   *)
(* two terms headed by distinct type constructors.                          *)
(*                                                                          *)
(* First and second arguments are as for `refute_distinct'.                 *)
(*--------------------------------------------------------------------------*)

fun refute_distincts is_constructor distinctf [] = failwith "refute_distincts"
  | refute_distincts is_constructor distinctf (equiv::equivs) = 
   (refute_distinct is_constructor distinctf equiv handle HOL_ERR _ =>
    refute_distincts is_constructor distinctf equivs);

(*--------------------------------------------------------------------------*)
(* REC_TYPE_CONV : thm hol_type_info list -> conv                           *)
(*                                                                          *)
(* Proves false from an unsatisfiable conjunction of literals from the      *)
(* equational theories of recursive types and uninterpreted function        *)
(* symbols. Multiple types may appear.                                      *)
(*                                                                          *)
(* The first argument is a list of information about the types involved in  *)
(* the input term (see documentation elsewhere). The second argument is the *)
(* conjunction (a term). If successful, the result is a theorem stating     *)
(* that the conjunction is equal to false. Each conjunct must have one of   *)
(* the following forms:                                                     *)
(*                                                                          *)
(*    l = r   ~(l = r)   P x   ~(P x)   D x   ~(D x)                        *)
(*                                                                          *)
(* where P is an uninterpreted predicate symbol and D is a discriminator,   *)
(* i.e., a function that is true for an application of one constructor of a *)
(* type and false for all others. The l, r, and x are terms involving       *)
(* variables, applications of type constructors and/or selectors, and       *)
(* applications of uninterpreted function symbols.                          *)
(*                                                                          *)
(* The procedure reformulates (P x) as (P x = T) and ~(P x) as ~(P x = T).  *)
(*                                                                          *)
(* An outline of the algorithm is:                                          *)
(*                                                                          *)
(* 0. Eliminate applications of discriminators in favour of equations       *)
(*    between the argument and a constructor application. Each positive     *)
(*    application of a discriminator gives rise to one equation and each    *)
(*    negative application gives rise to a list of equations.               *)
(*    (See the documentation for the elimination procedures.)               *)
(*                                                                          *)
(*    Recursively apply injectivity theorems to any of the original and new *)
(*    equations that are of the form (C x_1 ... x_n = C y_1 ... y_n) where  *)
(*    C is a type constructor. This produces new equations x_1 = y_1, etc.  *)
(*                                                                          *)
(* 1. Build a graph from the left and right-hand sides of all the equations *)
(*    and disequations obtained after step 0. The nodes of the graph are    *)
(*    functions, predicates, variables, etc. The graph forms the basis for  *)
(*    equivalence classes of terms. Use congruence closure to merge         *)
(*    equivalence classes according to the equations derived from equations *)
(*    in the original conjunction and positive applications of              *)
(*    discriminators.                                                       *)
(*                                                                          *)
(* 2. For each term C x_1 ... x_n represented in the graph, and for each    *)
(*    selector S_i of C, add an equation x_i = S_i (C x_1 ... x_n).         *)
(*    Merge equivalence classes. The code is constructed so that any new    *)
(*    terms introduced are included in the graph when it is first built.    *)
(*                                                                          *)
(* 3. For each list of equations obtained from the negated applications of  *)
(*    discriminators do a case-split. Add each case separately to the graph *)
(*    and attempt to derive false. False can be derived if:                 *)
(*                                                                          *)
(*    (a) the left and right-hand sides of any disequation are in the same  *)
(*        equivalence class;                                                *)
(*    (b) any equivalence class contains two terms with different           *)
(*        constructors at their heads.                                      *)
(*                                                                          *)
(*    If false can be derived for all cases then the original conjunction   *)
(*    is unsatisfiable.                                                     *)
(*                                                                          *)
(* The function does not yet prove acyclicity properties.                   *)
(*--------------------------------------------------------------------------*)

fun REC_TYPE_CONV (type_infos : thm hol_type_info list) (*type_selector*) tm =
   let fun injectivity_convs ([] : thm hol_constructor_info list) = []
         | injectivity_convs (info::infos) =
          (case (#one_one info)
           of NONE => injectivity_convs infos
            | SOME eqthm_info =>
                 (#name info,#conversion eqthm_info) ::
                 injectivity_convs infos)
       fun apply_constant name tm =
          let val const = #const (const_decl name)
              val ty_subst =
                 match_type ((hd o #Args o Rsyntax.dest_type o type_of) const)
                    (type_of tm)
          in  mk_comb (inst ty_subst const,tm)
          end

       val constr_infos = flat (map #constructors type_infos)
       fun is_constructor tm =
          exists (fn info => (#name info = name_of_operator tm
                              handle HOL_ERR _ => false)) constr_infos
       fun mk_selections tm =
          let val info = gen_assoc #name (name_of_operator tm) constr_infos
          in  map (fn (name,_) => apply_constant name tm) (#selectors info)
          end
       val discr_infos = flat (map #discriminators type_infos)
       fun is_discriminator tm =
          exists (fn info => (#name info = name_of_operator tm
                              handle HOL_ERR _ => false)) discr_infos
       fun distinctf tyname = #distinct (gen_assoc #name tyname type_infos)

       val ths = CONJUNCTS (ASSUME tm)
       val posths =
          filter
            ((fn tm => not (is_neg tm orelse is_discriminator tm)) o concl) ths
       and posdiscths = filter (is_discriminator o concl) ths
       and negths =
          filter ((fn tm => is_neg tm andalso
                            (not o is_discriminator o dest_neg) tm) o
                  concl) ths
       and negdiscths =
          filter ((fn tm => is_neg tm andalso
                            (is_discriminator o dest_neg) tm) o
                  concl) ths
       val eqths =
          map (fn th => if (is_eq o concl) th then th else EQT_INTRO th) posths
       val diseqths =
          map (fn th => if (is_eq o dest_neg o concl) th
                        then th
                        else NOT_EQT_INTRO th) negths
       val (posdiscfns,posdisceqths) =
          unzip (map (ELIMINATE_DISCRIMINATOR discr_infos) posdiscths)
       val eqths' =
          flat (map (INJECTIVE_REDUCTION (injectivity_convs constr_infos))
                   (posdisceqths @ eqths))
       val (negdiscfns,negdisceqthss) =
          unzip (map (ELIMINATE_NEGATED_DISCRIMINATOR discr_infos) negdiscths)
       val negdisceqthsss =
          map (map (INJECTIVE_REDUCTION (injectivity_convs constr_infos)))
                  negdisceqthss
       val negdisctmsss = map (map (map concl)) negdisceqthsss
       (* Build one graph for all possible case-splits *)
       val tms = itlist (fn eq => fn tms => lhs eq :: rhs eq :: tms)
                    (map concl eqths' @ map (dest_neg o concl) diseqths @
                     flat (map flat negdisctmsss)) []
       fun selections tm =
          if (is_constructor tm) then (mk_selections tm) else []
       val (graph,equivs,label_for_term,extras) =
          construct_congruence selections tms
       val equivs' = congruence_closure (graph,label_for_term) equivs eqths'
       fun extrath (_,tm) =
          let val selector = name_of_operator tm
              and constructor = name_of_operator (rand tm)
              val constr_info = gen_assoc #name constructor constr_infos
          in  #conversion (assoc selector (#selectors constr_info)) tm
          end
       val equivs'' = congruence_closure (graph,label_for_term) equivs'
                         (map extrath extras)
       (* Considers all combinations of cases:                             *)
       (* exponential in the number of negatively occurring discriminators *)
       fun refute [] equivs =
          (refute_diseqs (equivs,label_for_term) diseqths handle HOL_ERR _ =>
           refute_distincts is_constructor distinctf equivs)
         | refute ((negdiscfn,negdisceqthss)::cases) equivs =
          let val equivss =
                 map (fn eqths => congruence_closure (graph,label_for_term)
                                     equivs eqths)
                    negdisceqthss
          in  negdiscfn (map (refute cases) equivss)
          end
       val falseth = refute (zip negdiscfns negdisceqthsss) equivs''
   in  IMP_F_EQ_F_RULE (DISCH tm (foldl (fn (f,x) => f x) falseth posdiscfns))
   end
   handle HOL_ERR _ => failwith "REC_TYPE_CONV";

end;

end; (* CongruenceClosureTypes *)
