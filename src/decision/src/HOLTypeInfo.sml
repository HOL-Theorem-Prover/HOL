(****************************************************************************)
(* FILE          : type_info.sml                                            *)
(* DESCRIPTION   : Storage and retrieval of information about defined types.*)
(*                 (Based on shells.sml in contrib/boyer-moore/.)           *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 8th May 1991                                             *)
(*                                                                          *)
(* TRANSLATED BY : R.J.Boulton                                              *)
(* DATE          : 2nd October 1995                                         *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 19th August 1996                                         *)
(****************************************************************************)

structure HOLTypeInfo =
struct

local

open HolKernel boolTheory Parse Datatype Psyntax
     Drule Conv Rewrite Prim_rec
     DecisionSupport DecisionNormConvs;
open Prim_rec_Compat;

infix ## THENC ORELSEC -->;

fun failwith function =
   raise HOL_ERR {origin_structure = "HOLTypeInfo",
                  origin_function = function,
                  message = ""};

in

(*--------------------------------------------------------------------------*)
(* ML types for holding information about a recursive logical type.         *)
(*--------------------------------------------------------------------------*)

type 'thm eqthm_info =
   {generalized : 'thm,specialized : 'thm,conversion : term -> 'thm};

type 'thm hol_constructor_info =
   {name : string,                       (* Name of the constructor *)
    arg_types : hol_type list,           (* Argument types          *)
    selectors :                          (* Selector functions      *)
       (string * 'thm eqthm_info) list,
    one_one : 'thm eqthm_info option};   (* Constructor is one-one  *)

type 'thm hol_discriminator_info =
   {name : string,                   (* Name of the discriminator           *)
    true_constructor :               (* Name of constructor recognized by   *)
       string * 'thm,                (*   the discriminator and the theorem *)
    false_constructors :             (* The other constructors and theorems *)
       (string * 'thm) list,
    positive_elimination :           (* Elimination of discriminator *)
       'thm eqthm_info,
    negative_elimination :           (* and of negated discriminator *)
       'thm eqthm_info};

type 'thm hol_type_info =
   {name : string,                   (* Name of the type                    *)
    arg_types : hol_type list,       (* Argument types for type constructor *)
    constructors :                   (* Constructors for the type           *)
       'thm hol_constructor_info list,
    discriminators :                 (* Discriminators for the type         *)
       'thm hol_discriminator_info list,
    axiom : 'thm,                    (* Type axiom                          *)
    induct : 'thm,                   (* Induction theorem                   *)
    cases : 'thm,                    (* Cases theorem                       *)
    distinct :                       (* Constructors distinct               *)
       string * string ->            (*    as a function of the names       *)
       'thm *                        (*    |- !... . ~(... = ...)           *)
       'thm eqthm_info};             (*    |- !... . (... = ...) = F, etc.  *)

(*--------------------------------------------------------------------------*)
(* Exceptions for information extraction.                                   *)
(*--------------------------------------------------------------------------*)

exception NotDistinct;
exception NotOneOne;

(*--------------------------------------------------------------------------*)
(* Function to extract details of a named constructor from type             *)
(* information.                                                             *)
(*--------------------------------------------------------------------------*)

fun hol_constructor con_name (info : 'thm hol_type_info) =
   let fun constructor_of con_name [] = failwith "hol_constructor"
         | constructor_of con_name
              ((con_info as {name,arg_types,selectors,one_one}) ::
               constructors) =
          if (name = con_name)
          then con_info
          else constructor_of con_name constructors
   in  constructor_of con_name (#constructors info) : 'thm hol_constructor_info
   end;

(*--------------------------------------------------------------------------*)
(* Functions to extract from type information the argument types, selector  *)
(* functions, and injectivity theorem for a particular constructor.         *)
(*--------------------------------------------------------------------------*)

fun hol_constructor_arg_types name info =
   #arg_types (hol_constructor name info)
and hol_constructor_selectors name info =
   #selectors (hol_constructor name info)
and hol_constructor_one_one name info =
   case (#one_one (hol_constructor name info))
   of NONE => raise NotOneOne
    | SOME eqthm_info => eqthm_info;

(*--------------------------------------------------------------------------*)
(* Function to construct the theorem of the form |- !... . (... = ...) = F  *)
(* (and its specialized version and its conversion) from a distinctness     *)
(* theorem and put this information in a record structure suitable for use  *)
(* in type info.                                                            *)
(*--------------------------------------------------------------------------*)

fun construct_distinct th =
   let val thF = EQF_INTRO (SPEC_ALL th)
   in  (th,{generalized = GEN_ALL thF,
            specialized = thF,
            conversion = REWR_CONV thF})
   end;

(*--------------------------------------------------------------------------*)
(* Functions to change the thm type in info.                                *)
(*--------------------------------------------------------------------------*)

local

fun app2 f (x,y) = (x,f y);

in

fun transform_eqthm_info f
       ({generalized,specialized,conversion} : 'thm eqthm_info) =
   {generalized = f generalized,
    specialized = f specialized,
    conversion = f o conversion} : 'thm' eqthm_info;

fun transform_constructor_info f
       ({name,arg_types,selectors,one_one} : 'thm hol_constructor_info) =
   {name = name,arg_types = arg_types,
    selectors = map (app2 (transform_eqthm_info f)) selectors,
    one_one = case one_one of NONE => NONE
                            | SOME info => SOME (transform_eqthm_info f info)}
   : 'thm' hol_constructor_info;

fun transform_discriminator_info f
       ({name,true_constructor,false_constructors,positive_elimination,
         negative_elimination} : 'thm hol_discriminator_info) =
   {name = name,
    true_constructor = app2 f true_constructor,
    false_constructors = map (app2 f) false_constructors,
    positive_elimination = transform_eqthm_info f positive_elimination,
    negative_elimination = transform_eqthm_info f negative_elimination}
   : 'thm' hol_discriminator_info;

fun transform_type_info f
       ({name,arg_types,constructors,discriminators,
         axiom,induct,cases,distinct} : 'thm hol_type_info) =
   {name = name,
    arg_types = arg_types,
    constructors = map (transform_constructor_info f) constructors,
    discriminators = map (transform_discriminator_info f) discriminators,
    axiom = f axiom,
    induct = f induct,
    cases = f cases,
    distinct = (f ## transform_eqthm_info f) o distinct} : 'thm' hol_type_info;

end;

(*--------------------------------------------------------------------------*)
(* EXISTS_HYP : term list -> term -> thm -> thm                             *)
(*                                                                          *)
(* Existentially quantifies the specified variables in the specified        *)
(* assumption provided they are not free elsewhere.                         *)
(*                                                                          *)
(*     A u {h} |- t                                                         *)
(*    --------------------------  EXISTS_HYP [`v1`,...,`vn`] `h`            *)
(*     A u {?v1 ... vn. h} |- t   provided v1,...,vn are not free in A or t *)
(*                                                                          *)
(* Assumes the v's are free in h. If not, FORALL_IMP_CONV causes t to       *)
(* become universally quantified by them.                                   *)
(*--------------------------------------------------------------------------*)

fun EXISTS_HYP vars tm th =
   let fun LIST_FORALL_IMP_CONV [] = ALL_CONV
         | LIST_FORALL_IMP_CONV (_::vs) =
          BINDER_CONV (LIST_FORALL_IMP_CONV vs) THENC FORALL_IMP_CONV
   in  (UNDISCH o CONV_RULE (LIST_FORALL_IMP_CONV vars) o GENL vars o DISCH tm)
       th
   end
   handle HOL_ERR _ => failwith "EXISTS_HYP";

(*--------------------------------------------------------------------------*)

local
   open LazyThm
in

fun LIST_DISJ_CASES disjth ths =
   prove_pre_thm (Decide.LIST_DISJ_CASES (mk_proved_pre_thm disjth)
                     (map mk_proved_pre_thm ths));

end;

(*--------------------------------------------------------------------------*)

local

val refl_conv = REWR_CONV REFL_CLAUSE
and not_conv = REWRITES_CONV (add_rewrites empty_rewrites [NOT_CLAUSES])
and or_conv = REWRITES_CONV (add_rewrites empty_rewrites [OR_CLAUSES]);

fun distinct_conv distinctf tm =
   let val (l,r) = dest_eq tm
       val lname = name_of_operator l
       and rname = name_of_operator r
   in  #conversion ((snd o distinctf) (lname,rname) : 'thm eqthm_info) tm
   end
   handle NotDistinct => failwith "";

fun constrs_dis_conv distinctf =
   DEPTH_EXISTS_CONV (distinct_conv distinctf) THENC REPEATC EXISTS_SIMP_CONV;

fun constrs_eq_conv vars =
   let fun list_exists tm =
          let val (var,body) = dest_exists tm
              val v = assoc var vars
          in  EXISTS (tm,v) (list_exists (subst [(v,var)] body))
          end
          handle HOL_ERR _ => REFL (lhs tm)
   in  EQT_INTRO o list_exists
   end;

fun rewrite_conv ths = REWRITES_CONV (add_rewrites empty_rewrites ths);

fun generalise_case tm =
   let val (vars,eq) = strip_exists tm
       val newvars = map (genvar o type_of) vars
       val neweq = subst (zip newvars vars) eq
   in  (zip vars newvars,neweq)
   end;

fun prove_discrim_elim conv casesth tm =
   let val (_,casedisj) = dest_forall (concl casesth)
       val cases = map generalise_case (strip_disj casedisj)
       val ths = map (fn (vars,eq) =>
                         EXISTS_HYP (map #2 vars) eq
                            (EQT_ELIM (conv vars (REWR_CONV (ASSUME eq)) tm)))
                    cases
   in  LIST_DISJ_CASES (SPEC_ALL casesth) ths
   end;

in

(*--------------------------------------------------------------------------*)
(* PROVE_DISCRIM_ELIM :                                                     *)
(*    thm -> (string * string -> thm) -> thm * thm list -> thm              *)
(*                                                                          *)
(* Proves a theorem stating that an application of a discriminator D_i is   *)
(* equivalent to asserting that the argument is an application of the       *)
(* corresponding constructor C_i, i.e.: |- D_i x = (?vars. x = C_i vars)    *)
(*                                                                          *)
(* Arguments:                                                               *)
(*                                                                          *)
(*  * Cases theorem:                                                        *)
(*    |- !x. (?vars_1. x = C_1 vars_1) \/ ... \/ (?vars_n. x = C_n vars_n)  *)
(*  * Distinctness:                                                         *)
(*    fn ("C_i","C_j") =>                                                   *)
(*       |- !vars_i vars_j. ~(C_i vars_i = C_j vars_j)            (j =/= i) *)
(*  * Discriminator definitions: |- !vars. D_i (C_i vars) = T               *)
(*                               |- !vars. D_i (C_j vars) = F     (j =/= i) *)
(*--------------------------------------------------------------------------*)

fun PROVE_DISCRIM_ELIM casesth distinctf (tdef,fdefs) =
   let fun CONV vars conv =
          LEFT_CONV (RAND_CONV conv THENC rewrite_conv (tdef :: fdefs)) THENC
          RIGHT_CONV
             (DEPTH_EXISTS_CONV (LEFT_CONV conv) THENC
              (constrs_dis_conv distinctf ORELSEC constrs_eq_conv vars)) THENC
          refl_conv
       val v = #1 (dest_forall (concl casesth))
       val (vars,body) = strip_forall (concl tdef)
       val (disc,arg) = dest_comb (lhs body)
       val tm = mk_eq (mk_comb (disc,v),list_mk_exists (vars,mk_eq (v,arg)))
   in  prove_discrim_elim CONV casesth tm
   end
   handle HOL_ERR _ => failwith "PROVE_DISCRIM_ELIM";

(*--------------------------------------------------------------------------*)
(* PROVE_NEG_DISCRIM_ELIM :                                                 *)
(*    thm -> (string * string -> thm) -> thm * thm list -> thm              *)
(*                                                                          *)
(* Proves a theorem stating that the negation of a discriminator D_i is     *)
(* equivalent to asserting that the argument is an application of one of    *)
(* the constructors C_j where j =/= i, i.e.:                                *)
(*                                                                          *)
(*    |- ~(D_i x) = (?vars_1. x = C_1 vars_1) \/                            *)
(*                  ... \/                                                  *)
(*                  (?vars_i-1. x = C_i-1 vars_i-1) \/                      *)
(*                  (?vars_i+1. x = C_i+1 vars_i+1) \/                      *)
(*                  ... \/                                                  *)
(*                  (?vars_n. x = C_n vars_n)                               *)
(*                                                                          *)
(* Arguments:                                                               *)
(*                                                                          *)
(*  * Cases theorem:                                                        *)
(*    |- !x. (?vars_1. x = C_1 vars_1) \/ ... \/ (?vars_n. x = C_n vars_n)  *)
(*  * Distinctness:                                                         *)
(*    fn ("C_i","C_j") =>                                                   *)
(*       |- !vars_i vars_j. ~(C_i vars_i = C_j vars_j)            (j =/= i) *)
(*  * Discriminator definitions: |- !vars. D_i (C_i vars) = T               *)
(*                               |- !vars. D_i (C_j vars) = F     (j =/= i) *)
(*--------------------------------------------------------------------------*)

fun PROVE_NEG_DISCRIM_ELIM casesth distinctf (tdef,fdefs) =
   let fun CONV vars conv =
          LEFT_CONV
             (RAND_CONV
                 (RAND_CONV conv THENC rewrite_conv (tdef :: fdefs)) THENC
              not_conv) THENC
          TRY_CONV
             (RIGHT_CONV
                 (DEPTH_DISJ_CONV
                     (DEPTH_EXISTS_CONV (LEFT_CONV conv) THENC
                      (constrs_dis_conv distinctf ORELSEC
                       constrs_eq_conv vars)) THENC
                  DEPTH_CONV or_conv)) THENC
          refl_conv
       val v = #1 (dest_forall (concl casesth))
       val disc = (rator o lhs o #2 o strip_forall o concl) tdef
       fun construct_disj th =
          let val (vars,body) = strip_forall (concl th)
              val (_,arg) = dest_comb (lhs body)
          in  list_mk_exists (vars,mk_eq (v,arg))
          end
       val disjs = map construct_disj fdefs
       val tm = mk_eq (mk_neg (mk_comb (disc,v)),
                       list_mk_disj disjs handle HOL_ERR _ => F)
   in  prove_discrim_elim CONV casesth tm
   end
   handle HOL_ERR _ => failwith "PROVE_NEG_DISCRIM_ELIM";

end;

(*--------------------------------------------------------------------------*)
(* Type information for natural numbers.                                    *)
(*--------------------------------------------------------------------------*)

val num_type_info : thm hol_type_info =
   {name = "num",
    arg_types = [],
    constructors =
       [{name = "0",arg_types = [],selectors = [],one_one = NONE},
        {name = "SUC",
         arg_types = [(==`:num`==)],
         selectors = [("PRE",
                       let val PRE = CONJUNCT2 (prim_recTheory.PRE)
                       in  {generalized = PRE,
                            specialized = SPEC_ALL PRE,
                            conversion = REWR_CONV PRE}
                       end)],
         one_one = let val th = prim_recTheory.INV_SUC_EQ
                   in  SOME {generalized = th,
                             specialized = SPEC_ALL th,
                             conversion = REWR_CONV th}
                   end}],
    discriminators = [],
    axiom = prim_recTheory.num_Axiom,
    induct = numTheory.INDUCTION,
    cases = arithmeticTheory.num_CASES,
    distinct = fn ("0","SUC") =>
                     construct_distinct (arithmeticTheory.SUC_NOT)
                | ("SUC","0") => construct_distinct (numTheory.NOT_SUC)
                | _ => raise NotDistinct};

(*--------------------------------------------------------------------------*)
(* Type information for lists.                                              *)
(*--------------------------------------------------------------------------*)

val list_type_info : thm hol_type_info =
   let val cases = listTheory.list_CASES
       val distinct = fn ("NIL","CONS") =>
                            construct_distinct (listTheory.NOT_NIL_CONS)
                       | ("CONS","NIL") =>
                            construct_distinct (listTheory.NOT_CONS_NIL)
                       | _ => raise NotDistinct
   in
   {name = "list",
    arg_types = [(==`:'a`==)],
    constructors =
       [{name = "NIL",arg_types = [],selectors = [],one_one = NONE},
        {name = "CONS",
         arg_types = [(==`:'a`==),(==`:('a)list`==)],
         selectors = [("HD",
                       let val HD = listTheory.HD
                       in  {generalized = HD,
                            specialized = SPEC_ALL HD,
                            conversion = REWR_CONV HD}
                       end),
                      ("TL",
                       let val TL = listTheory.TL
                       in  {generalized = TL,
                            specialized = SPEC_ALL TL,
                            conversion = REWR_CONV TL}
                       end)],
         one_one = let val th = listTheory.CONS_11
                   in  SOME {generalized = th,
                             specialized = SPEC_ALL th,
                             conversion = REWR_CONV th}
                   end}],
    discriminators =
       [let val true_constructor =
               ("NIL",CONJUNCT1 (listTheory.NULL_DEF))
            and false_constructors =
               [("CONS",CONJUNCT2 (listTheory.NULL_DEF))]
            val pos_elim = PROVE_DISCRIM_ELIM cases distinct
                              (#2 true_constructor,map #2 false_constructors)
            and neg_elim = PROVE_NEG_DISCRIM_ELIM cases distinct
                              (#2 true_constructor,map #2 false_constructors)
        in
        {name = "NULL",
         true_constructor = true_constructor,
         false_constructors = false_constructors,
         positive_elimination = {generalized = GEN_ALL pos_elim,
                                 specialized = pos_elim,
                                 conversion = REWR_CONV pos_elim},
         negative_elimination =  {generalized = GEN_ALL neg_elim,
                                 specialized = neg_elim,
                                 conversion = REWR_CONV neg_elim}}
        end],
    axiom = listTheory.list_Axiom,
    induct = listTheory.list_INDUCT,
    cases = cases,
    distinct = distinct}
   end;

(*--------------------------------------------------------------------------*)
(* define_type_info : {name : string,                                       *)
(*                     type_spec : term frag list,                          *)
(*                     fixities : fixity list,                              *)
(*                     selectors : (string * string list) list} ->          *)
(*                     discriminators : (string * string) list} ->          *)
(*                    thm hol_type_info                                     *)
(*                                                                          *)
(* Function for defining a new HOL type together with selector and          *)
(* discriminator functions, and making a new type info. record from these   *)
(* definitions. If the type already exists the function attempts to load    *)
(* the corresponding theorems from the current theory hierarchy and use     *)
(* them to make the info.                                                   *)
(*                                                                          *)
(* The first three fields of the argument correspond to those taken by      *)
(* `define_type' and the fourth and fifth specify the names of the selector *)
(* and discriminator functions. The function assumes that there are no      *)
(* selectors for a constructor that doesn't appear in the list, so it is    *)
(* not necessary to include an entry for a nullary constructor. For other   *)
(* constructors there must be one selector name for each argument and they  *)
(* should be given in the correct order. The function ignores any item in   *)
(* the list with a constructor name that does not belong to the type.       *)
(* The discriminators are optional.                                         *)
(*                                                                          *)
(* The constructor, selector and discriminator names must all be distinct   *)
(* and must not be the names of existing constants.                         *)
(*                                                                          *)
(* Example:                                                                 *)
(*                                                                          *)
(*    define_type_info                                                      *)
(*       {name = "sexp",                                                    *)
(*        type_spec = `sexp = Nil | Atom of 'a | Cons of sexp => sexp`,     *)
(*        fixities = [Prefix,Prefix,Prefix],                                *)
(*        selectors = [("Atom",["Tok"]),("Cons",["Car","Cdr"])],            *)
(*        discriminators =                                                  *)
(*           [("Nil","Nilp"),("Atom","Atomp"),("Cons","Consp")]};           *)
(*                                                                          *)
(* This results in the following theorems being stored in the current       *)
(* theory (or these are the theorems the function would expect to find in   *)
(* the theory hierarchy if the type already exists):                        *)
(*                                                                          *)
(*    sexp               (type axiom)                                       *)
(*    sexp_Induct        (induction theorem)                                *)
(*    sexp_one_one       (injectivity of constructors)                      *)
(*    sexp_distinct      (distinctness of constructors)                     *)
(*    sexp_cases         (cases theorem)                                    *)
(*                                                                          *)
(* The following definitions for the selector and discriminator functions   *)
(* are also stored:                                                         *)
(*                                                                          *)
(*    Tok                |- !x. Tok (Atom x) = x                            *)
(*    Car                |- !s1 s2. Car (Cons s1 s2) = s1                   *)
(*    Cdr                |- !s1 s2. Cdr (Cons s1 s2) = s2                   *)
(*                                                                          *)
(*    Nilp               |- (Nilp Nil = T) /\                               *)
(*                          (!x. Nilp (Atom x) = F) /\                      *)
(*                          (!s2 s1. Nilp (Cons s1 s2) = F)                 *)
(*    Atomp              |- (Atomp Nil = F) /\                              *)
(*                          (!x. Atomp (Atom x) = T) /\                     *)
(*                          (!s2 s1. Atomp (Cons s1 s2) = F)                *)
(*    Consp              |- (Consp Nil = F) /\                              *)
(*                          (!x. Consp (Atom x) = F) /\                     *)
(*                          (!s2 s1. Consp (Cons s1 s2) = T)                *)
(*                                                                          *)
(* In certain cases the distinctness or injectivity theorems may not exist, *)
(* when nothing is saved for them.                                          *)
(*--------------------------------------------------------------------------*)

(* Should check stuff pulled in from disk is consistent with user's spec.   *)

(* Does not work for mutual and nested mutual type definitions.             *)

fun define_type_info {name,type_spec,fixities,selectors,discriminators} =
   let fun define_function axiom (name,tm) =
          (name,Prim_rec.new_recursive_definition
                   {name=name,rec_axiom=axiom, def=tm})
       fun mk_def_eq (name,comb,arg) =
          let val ty = type_of comb --> type_of arg
          in  mk_eq (mk_comb (Rsyntax.mk_var {Name = name,Ty = ty},comb),arg)
          end
       fun define_selectors axiom (comb,specs) =
          map (fn (name,arg) =>
                  define_function axiom (name,mk_def_eq (name,comb,arg)))
             specs
       fun define_discriminator axiom constrs_and_combs c name =
          let fun mk_case (constr,comb) =
                 mk_def_eq (name,comb,if (constr = c) then T else F)
          in  define_function axiom
                 (name,list_mk_conj (map mk_case constrs_and_combs))
          end
       val _ = if (is_type name)
               then failwith("define_type_info -- type "^ Lib.quote name
                            ^" already exists.")
                else ()
       val _ = Datatype.Hol_datatype type_spec
       val SOME tyinfo = TypeBase.read name
       val name_Axiom = TypeBase.axiom_of tyinfo
       val name_Induct = TypeBase.induction_of tyinfo
       val name_one_ones = 
           case TypeBase.one_one_of tyinfo
            of NONE => []
             | SOME th => CONJUNCTS th
       val name_distincts =
           case TypeBase.distinct_of tyinfo
            of NONE => []
             | SOME th => CONJUNCTS th
       val name_cases = TypeBase.nchotomy_of tyinfo
       val ty = (type_of o #1 o dest_forall o concl) name_cases
       val ty_args = #Args (Rsyntax.dest_type ty)
       val cases = (strip_disj o #2 o dest_forall o concl) name_cases
       val combs = map (rhs o #2 o strip_exists) cases
       val constrs_and_args = map ((name_of_const ## I) o strip_comb) combs
       val (constrs,arg_types) =
          split (map (I ## map type_of) constrs_and_args)
       val constrs_and_combs = combine (constrs,combs)
       val sel_specs =
          map (fn (c,args) =>
                  (combine (assoc c selectors handle NOT_FOUND => [],args)
                   handle HOL_ERR _ =>
                   failwith
                      ("define_type_info -- " ^
                       "incorrect number of selectors for constructor " ^ c)))
             constrs_and_args
       val sel_defs =
          let val sels =
             map (define_selectors name_Axiom) (combine (combs,sel_specs))
          in  map (map (fn (s,th) => (s,{generalized = th,
                                         specialized = SPEC_ALL th,
                                         conversion = REWR_CONV th}))) sels
          end
       val disc_defs =
          map (fn (c,disc) =>
                  define_discriminator name_Axiom constrs_and_combs c disc)
             (filter (fn (c,_) => member c constrs) discriminators)
       fun constr_and_bool th =
          let val (l,r) = (dest_eq o #2 o strip_forall o concl) th
          in  (name_of_operator (rand l),(r = T))
          end
       val one_ones =
          map (fn th => ((name_of_operator o lhs o lhs o
                          #2 o strip_forall o concl) th,th))
             name_one_ones
       val half_distincts =
          map (fn th => (((name_of_operator ## name_of_operator) o dest_eq o
                          dest_neg o #2 o strip_forall o concl) th,th))
             name_distincts
       val distincts =
          map (I ## construct_distinct) half_distincts @
          (map (fn ((c1,c2),th) => ((c2,c1),construct_distinct (GSYM th)))
              half_distincts)
       val distinctf = fn cpair => (assoc cpair distincts
                                    handle HOL_ERR _ => raise NotDistinct)
       val type_info =
          {name = name,
           arg_types = ty_args,
           constructors =
              map (fn (n,(t,s)) =>
                      {name = n,arg_types = t,selectors = s,
                       one_one = SOME (let val th = assoc n one_ones
                                       in  {generalized = th,
                                            specialized = SPEC_ALL th,
                                            conversion = REWR_CONV th}
                                       end)
                                 handle HOL_ERR _ => NONE})
                 (combine (constrs,combine (arg_types,sel_defs))),
           discriminators =
              map (fn (n,th) =>
                      let val ths = CONJUNCTS th
                          val (cs,bs) = split (map constr_and_bool ths)
                          val bdefs = combine (bs,combine (cs,ths))
                          val tdef = assoc true bdefs
                          and fdefs = map #2 (filter (not o #1) bdefs)
                          val pos_elim =
                             PROVE_DISCRIM_ELIM name_cases distinctf
                                (#2 tdef,map #2 fdefs)
                          and neg_elim =
                             PROVE_NEG_DISCRIM_ELIM name_cases distinctf
                                (#2 tdef,map #2 fdefs)
                      in  {name = n,
                           true_constructor = tdef,
                           false_constructors = fdefs,
                           positive_elimination =
                              {generalized = GEN_ALL pos_elim,
                               specialized = pos_elim,
                               conversion = REWR_CONV pos_elim},
                           negative_elimination =
                              {generalized = GEN_ALL neg_elim,
                               specialized = neg_elim,
                               conversion = REWR_CONV neg_elim}}
                      end)
                 disc_defs,
           axiom = name_Axiom,induct = name_Induct,cases = name_cases,
           distinct = distinctf}
   in  type_info : thm hol_type_info
   end;


(*---------------------------------------------------------------------------
  Original version -- does not work under theories-as-modules approach,
   since "define_type_info" treats theories as first-class ML values,
   e.g., "can (theorem thy)". Therefore, we will only allow datatypes
   to be built using this call, and not brought in from ancestor theories
   by first class operations. (Trying to bring things in from ancestor
   theories by name is fragile -- maybe we can fix this by having
   a central repository of datatype facts.)

fun define_type_info {name,type_spec,fixities,selectors,discriminators} =
   let fun find_theory s =
          let fun f s [] = failwith "find_theory"
                | f s (thy::thys) =
                 if can (theorem thy) s
                 then thy
                 else f s thys
          in  f s (current_theory () :: ancestry "-")
          end
       fun define_function axiom (name,tm) =
          (name,Rsyntax.new_recursive_definition
                   {name = name,fixity = Prefix,rec_axiom = axiom,def = tm})
       fun mk_def_eq (name,comb,arg) =
          let val ty = mk_type ("fun",[type_of comb,type_of arg])
          in  mk_eq (mk_comb (Rsyntax.mk_var {Name = name,Ty = ty},comb),arg)
          end
       fun define_selectors axiom (comb,specs) =
          map (fn (name,arg) =>
                  define_function axiom (name,mk_def_eq (name,comb,arg)))
             specs
       fun define_discriminator axiom constrs_and_combs c name =
          let fun mk_case (constr,comb) =
                 mk_def_eq (name,comb,if (constr = c) then T else F)
          in  define_function axiom
                 (name,list_mk_conj (map mk_case constrs_and_combs))
          end
       val defined = is_type name
       val theory =
          if defined
          then (find_theory name handle HOL_ERR _ =>
                failwith
                   ("define_type_info -- no axiom found for type " ^ name))
          else current_theory ()
       val name_Axiom =
          if defined
          then theorem theory name
          else define_type
                  {name = name,fixities = fixities,type_spec = type_spec}
       val name_Induct =
          if defined
          then theorem theory (name ^ "_Induct")
          else save_thm (name ^ "_Induct",prove_induction_thm name_Axiom)
       and name_one_ones =
          if defined
          then (CONJUNCTS (theorem theory (name ^ "_one_one"))
                handle e as HOL_ERR _ =>
                   if (can prove_constructors_one_one name_Axiom)
                   then raise e
                   else [])
          else ((CONJUNCTS o save_thm)
                   ((name ^ "_one_one"),prove_constructors_one_one name_Axiom)
                handle HOL_ERR _ => [])
       and name_distincts =
          if defined
          then (CONJUNCTS (theorem theory (name ^ "_distinct"))
                handle e as HOL_ERR _ =>
                     if (can prove_constructors_distinct name_Axiom)
                     then raise e
                     else [])
          else ((CONJUNCTS o save_thm)
                   (name ^ "_distinct",prove_constructors_distinct name_Axiom)
                handle HOL_ERR _ => [])
       val name_cases =
          if defined
          then theorem theory (name ^ "_cases")
          else save_thm (name ^ "_cases",prove_cases_thm name_Induct)
       val ty = (type_of o #1 o dest_forall o concl) name_cases
       val ty_args = #Args (Rsyntax.dest_type ty)
       val cases = (strip_disj o #2 o dest_forall o concl) name_cases
       val combs = map (rhs o #2 o strip_exists) cases
       val constrs_and_args = map ((name_of_const ## I) o strip_comb) combs
       val (constrs,arg_types) =
          split (map (I ## map type_of) constrs_and_args)
       val constrs_and_combs = combine (constrs,combs)
       val sel_specs =
          map (fn (c,args) =>
                  (combine (assoc c selectors handle HOL_ERR _ => [],args)
                   handle HOL_ERR _ =>
                   failwith
                      ("define_type_info -- " ^
                       "incorrect number of selectors for constructor " ^ c)))
             constrs_and_args
       val sel_defs =
          let val sels =
             if defined
             then map (map ((fn sel => (sel,definition theory sel)) o #1))
                     sel_specs
             else map (define_selectors name_Axiom) (combine (combs,sel_specs))
          in  map (map (fn (s,th) => (s,{generalized = th,
                                         specialized = SPEC_ALL th,
                                         conversion = REWR_CONV th}))) sels
          end
       val disc_defs =
          map (fn (c,disc) =>
                  ((disc,definition theory disc) handle HOL_ERR _ =>
                   define_discriminator name_Axiom constrs_and_combs c disc))
             (filter (fn (c,_) => member c constrs) discriminators)
       fun constr_and_bool th =
          let val (l,r) = (dest_eq o #2 o strip_forall o concl) th
          in  (name_of_operator (rand l),(r = T))
          end
       val one_ones =
          map (fn th => ((name_of_operator o lhs o lhs o
                          #2 o strip_forall o concl) th,th))
             name_one_ones
       val half_distincts =
          map (fn th => (((name_of_operator ## name_of_operator) o dest_eq o
                          dest_neg o #2 o strip_forall o concl) th,th))
             name_distincts
       val distincts =
          map (I ## construct_distinct) half_distincts @
          (map (fn ((c1,c2),th) => ((c2,c1),construct_distinct (GSYM th)))
              half_distincts)
       val distinctf = fn cpair => (assoc cpair distincts
                                    handle HOL_ERR _ => raise NotDistinct)
       val type_info =
          {name = name,
           arg_types = ty_args,
           constructors =
              map (fn (n,(t,s)) =>
                      {name = n,arg_types = t,selectors = s,
                       one_one = SOME (let val th = assoc n one_ones
                                       in  {generalized = th,
                                            specialized = SPEC_ALL th,
                                            conversion = REWR_CONV th}
                                       end)
                                 handle NOT_FOUND => NONE})
                 (combine (constrs,combine (arg_types,sel_defs))),
           discriminators =
              map (fn (n,th) =>
                      let val ths = CONJUNCTS th
                          val (cs,bs) = split (map constr_and_bool ths)
                          val bdefs = combine (bs,combine (cs,ths))
                          val tdef = assoc true bdefs
                          and fdefs = map #2 (filter (not o #1) bdefs)
                          val pos_elim =
                             PROVE_DISCRIM_ELIM name_cases distinctf
                                (#2 tdef,map #2 fdefs)
                          and neg_elim =
                             PROVE_NEG_DISCRIM_ELIM name_cases distinctf
                                (#2 tdef,map #2 fdefs)
                      in  {name = n,
                           true_constructor = tdef,
                           false_constructors = fdefs,
                           positive_elimination =
                              {generalized = GEN_ALL pos_elim,
                               specialized = pos_elim,
                               conversion = REWR_CONV pos_elim},
                           negative_elimination =
                              {generalized = GEN_ALL neg_elim,
                               specialized = neg_elim,
                               conversion = REWR_CONV neg_elim}}
                      end)
                 disc_defs,
           axiom = name_Axiom,induct = name_Induct,cases = name_cases,
           distinct = distinctf}
   in  type_info : thm hol_type_info
   end;
 *---------------------------------------------------------------------------*)

end;

end; (* HOLTypeInfo *)
