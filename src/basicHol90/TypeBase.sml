(*---------------------------------------------------------------------------*
 * Building records of facts about datatypes. This is all purely functional, *
 * i.e., there are no side-effects happening anywhere in this file.          *
 *---------------------------------------------------------------------------*)

structure TypeBase :> TypeBase =
struct

open HolKernel Drule Tactic Tactical Conv Prim_rec Parse;
infix THEN THENL ## |->;

 type term = Term.term
 type thm = Thm.thm
 type ppstream = Portable_PrettyPrint.ppstream


fun ERR f s = 
  HOL_ERR{origin_structure = "TypeBase", 
          origin_function=f,message = s};


datatype tyinfo =
  FACTS of string * {axiom : thm, 
                     case_const : term, 
                     case_def : thm, 
                     case_cong : thm,
                     constructors : term list,
                     induction : thm,
                     nchotomy : thm, 
                     size : (term * thm) option,
                     distinct : thm option, 
                     one_one : thm option, 
                     simpls : thm list};

(*---------------------------------------------------------------------------
      Projections.
 ---------------------------------------------------------------------------*)
fun constructors_of (FACTS(_, {constructors,...})) = constructors
fun case_const_of (FACTS(_,{case_const,...})) = case_const
fun case_cong_of (FACTS(_,{case_cong,...})) = case_cong
fun case_def_of (FACTS(_,{case_def,...})) = case_def
fun induction_of (FACTS(_,{induction,...})) = induction
fun nchotomy_of (FACTS(_,{nchotomy,...})) = nchotomy
fun distinct_of (FACTS(_,{distinct,...})) = distinct
fun one_one_of (FACTS(_,{one_one,...})) = one_one
fun simpls_of (FACTS(_,{simpls,...})) = simpls
fun axiom_of (FACTS(_,{axiom,...})) = axiom
fun size_of (FACTS(_,{size,...})) = size
fun ty_name_of (FACTS(s,_)) = s


(*---------------------------------------------------------------------------
         Making alterations.
 ---------------------------------------------------------------------------*)
fun put_nchotomy th (FACTS(s,
 {axiom, case_const,case_cong,case_def,constructors,
  induction, nchotomy, distinct, one_one, simpls, size}))
  =
  FACTS(s, {axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def, constructors=constructors,
            induction=induction, nchotomy=th, distinct=distinct, 
            one_one=one_one, simpls=simpls, size=size})

fun put_induction th (FACTS(s,
 {axiom, case_const,case_cong,case_def,constructors,
  induction, nchotomy, distinct, one_one, simpls, size}))
  =
  FACTS(s, {axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def, constructors=constructors,
            induction=th, nchotomy=nchotomy, distinct=distinct, 
            one_one=one_one, simpls=simpls, size=size})

fun put_simpls thl (FACTS(s,
 {axiom, case_const, case_cong, case_def, constructors,
  induction, nchotomy, distinct, one_one, simpls, size}))
  =
  FACTS(s, {axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def,constructors=constructors,
            induction=induction, nchotomy=nchotomy, distinct=distinct, 
            one_one=one_one, simpls=thl, size=size});


fun put_size (size_tm,size_rw) (FACTS(s,
 {axiom, case_const,case_cong,case_def,constructors,
  induction, nchotomy, distinct, one_one, simpls, size}))
  =
  FACTS(s, {axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def,constructors=constructors,
            induction=induction, nchotomy=nchotomy, distinct=distinct, 
            one_one=one_one, simpls=simpls, size=SOME(size_tm,size_rw)});


(*---------------------------------------------------------------------------*
 * Returns the datatype name and the constructors. The code is a copy of     *
 * the beginning of "Datatype.define_case".                                  *
 *---------------------------------------------------------------------------*)
fun ax_info ax = 
  let val exu = snd(strip_forall(concl ax))
      val {Rator,Rand} = dest_comb exu
      val {Name = "?!",...} = dest_const Rator
      val {Bvar,Body} = dest_abs Rand
      val (dty,_) = Type.dom_rng (type_of Bvar)
      val {Tyop,Args} = dest_type dty
      val clist = map (rand o lhs o #2 o strip_forall) (strip_conj Body)
  in
   (Tyop,  map (fst o strip_comb) clist)
  end;

val defn_const = 
  #1 o strip_comb o lhs o #2 o strip_forall o hd o strip_conj o concl;


(*---------------------------------------------------------------------------*
 * The 11 theorem and distinctness theorem have to be given (currently)      *
 * because the routines for proving them use numbers, which might be         *
 * unnecessary in some formalizations. The size field is not filled by       *
 * mk_tyinfo, since that operation requires access to the current fact       *
 * database, and also assumes that numbers are in the context, which is not  *
 * necessarily true.                                                         *
 *---------------------------------------------------------------------------*)

fun mk_tyinfo {ax,case_def,case_cong,induction,
               nchotomy,size,one_one,distinct} =
  let val (ty_name,constructors) = ax_info ax
      val inj = case one_one of NONE => [] | SOME x => [x]
      val D = case distinct of NONE => [] | SOME x => CONJUNCTS x
  in
   FACTS(ty_name,
     {constructors = constructors,
      case_const   = defn_const case_def,
      case_def     = case_def,
      case_cong    = case_cong,
      induction    = induction,
      nchotomy     = nchotomy, 
      one_one      = one_one,
      distinct     = distinct,
      simpls       = case_def :: (D@map GSYM D@inj),
      size         = size,
      axiom        = ax})
  end;


fun pp_tyinfo ppstrm (FACTS(ty_name,recd)) =
 let open Portable_PrettyPrint
     val {add_string,add_break,begin_block,end_block,...}
          = with_ppstream ppstrm
     val pp_term = Term.pp_term ppstrm
     val pp_thm = Thm.pp_thm ppstrm
     val {constructors, case_const, case_def, case_cong, induction, 
          nchotomy, one_one, distinct, simpls, size, axiom} = recd
 in 
   begin_block CONSISTENT 0;
     begin_block INCONSISTENT 0; 
        add_string "-----------------------"; add_newline ppstrm; 
        add_string "-----------------------"; add_newline ppstrm; 
        add_string "HOL datatype:"; add_break(1,0);
        add_string (Lib.quote ty_name); end_block();
   add_break(1,0);
   begin_block CONSISTENT 1;
   add_string "Characterization:"; add_break (1,0); pp_thm axiom; end_block();
   add_break(1,0);
   begin_block CONSISTENT 1; add_string "Case analysis:"; 
                             add_break (1,0); pp_thm case_def; end_block();
   add_break(1,0);
   case size 
    of NONE => ()
     | SOME (tm,size_def) =>
        (begin_block CONSISTENT 1;
         add_string "Size:"; add_break (1,0); 
         if is_const tm then pp_thm size_def else pp_term tm; end_block();
         add_break(1,0));

   begin_block CONSISTENT 1;
   add_string "Induction:"; add_break (1,0); pp_thm induction; end_block();
   add_break(1,0);
   begin_block CONSISTENT 1; add_string "Case completeness:"; 
   add_break (1,0); pp_thm nchotomy; end_block();

   let fun do11 thm = 
            (begin_block CONSISTENT 1; add_string "One-to-one:"; 
             add_break (1,0); pp_thm thm; end_block());
       fun do_distinct thm =
            (begin_block CONSISTENT 1; add_string "Distinctness:"; 
             add_break (1,0); pp_thm thm; end_block())
   in
     case (one_one,distinct)
      of (NONE,NONE) => ()
       | (NONE,SOME thm) => (add_break(1,0); do_distinct thm)
       | (SOME thm,NONE) => (add_break(1,0); do11 thm)
       | (SOME thm1,SOME thm2) => (add_break(1,0); do11 thm1;
                                   add_break(1,0); do_distinct thm2)
   end;
   end_block()
end;


fun gen_tyinfo {ax, case_def, one_one, distinct} =
  let val induct_thm = prove_induction_thm ax
      val nchotomy   = prove_cases_thm induct_thm
      val case_cong  = case_cong_thm nchotomy case_def
  in
    mk_tyinfo {ax=ax,case_def=case_def,case_cong=case_cong,
               induction=induct_thm,nchotomy=nchotomy, size = NONE,
               one_one=one_one,distinct=distinct}
               
  end;

(*---------------------------------------------------------------------------*
 * Databases of facts.                                                       *
 *---------------------------------------------------------------------------*)
type typeBase = tyinfo Binaryset.set

val empty = 
   Binaryset.empty (fn (f1,f2) => 
       String.compare (ty_name_of f1, ty_name_of f2));

fun get db s = Binaryset.find (fn f => (s = ty_name_of f)) db;
fun add db f = Binaryset.add(db,f);
val listItems = Binaryset.listItems;


(*---------------------------------------------------------------------------*
 * Create the database.                                                      *
 *---------------------------------------------------------------------------*)

local val dBase = ref empty	
in
  fun theTypeBase() = !dBase;

  fun write facts = (dBase := add (theTypeBase()) facts);
end;

fun read s = get (theTypeBase()) s;
val elts = listItems o theTypeBase;


(*---------------------------------------------------------------------------*
 * Install datatype facts for booleans into theTypeBase.                     *
 *---------------------------------------------------------------------------*)

open boolTheory;

val boolAxiom = prove(Term`!(e0:'a) e1. ?!fn. (fn T = e0) /\ (fn F = e1)`,
SUBST_TAC[INST_TYPE[Type`:'a` |-> Type`:bool -> 'a`] EXISTS_UNIQUE_DEF]
  THEN BETA_TAC THEN BETA_TAC THEN REPEAT GEN_TAC THEN CONJ_TAC THENL
  [EXISTS_TAC(Term`\x. (x=T) => (e0:'a) | e1`) THEN BETA_TAC
     THEN SUBST_TAC[EQT_INTRO(REFL(Term`T`)),
                    EQF_INTRO(CONJUNCT2(BOOL_EQ_DISTINCT))]
     THEN SUBST_TAC(CONJUNCTS (SPECL [Term`e0:'a`, Term`e1:'a`] COND_CLAUSES))
     THEN CONJ_TAC THEN REFL_TAC,
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN REPEAT STRIP_TAC 
     THEN BOOL_CASES_TAC(Term`b:bool`)
     THEN REPEAT (POP_ASSUM SUBST1_TAC) THEN REFL_TAC]);

val bool_case_def = 
  let val [x,y,_] = #1(strip_forall(concl boolTheory.bool_case_DEF))
      val thm  = SPEC y (SPEC x boolTheory.bool_case_DEF)
      val thmT = SPEC (Term`T`) thm
      val thmF = SPEC (Term`F`) thm
      val CC   = SPECL [Term`x:'a`, Term`y:'a`] COND_CLAUSES
      val thmT' = SUBS [CONJUNCT1 CC] thmT
      val thmF' = SUBS [CONJUNCT2 CC] thmF
      fun gen th = GEN x (GEN y th)
  in
   CONJ (gen thmT') (gen thmF')
  end;

val bool_info = 
   gen_tyinfo
        {ax = boolAxiom,
         case_def = bool_case_def,
         distinct = SOME (CONJUNCT1 BOOL_EQ_DISTINCT),
         one_one = (NONE:thm option)};

val _ = write bool_info;

end;
