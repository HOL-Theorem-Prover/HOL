(*---------------------------------------------------------------------------*
 * Building records of facts about datatypes.                                *
 *---------------------------------------------------------------------------*)

structure TypeBase :> TypeBase =
struct

open HolKernel boolSyntax Rsyntax Drule Conv Prim_rec;

type ppstream = Portable.ppstream


val ERR = mk_HOL_ERR "TypeBase";


datatype shared_thm 
    = ORIG of thm 
    | COPY of string * thm;

fun thm_of (ORIG x)     = x
  | thm_of (COPY (s,x)) = x;


datatype tyinfo =
  FACTS of string * {axiom        : shared_thm,
                     induction    : shared_thm,
                     case_def     : thm,
                     case_cong    : thm,
                     nchotomy     : thm,
                     case_const   : term,
                     constructors : term list,
                     size         : (term * shared_thm) option,
                     distinct     : thm option,
                     one_one      : thm option,
                     simpls       : thm list};

(*---------------------------------------------------------------------------
                  Projections
 ---------------------------------------------------------------------------*)

fun constructors_of (FACTS(_, {constructors,...})) = constructors
fun case_const_of (FACTS(_,{case_const,...})) = case_const
fun case_cong_of (FACTS(_,{case_cong,...})) = case_cong
fun case_def_of (FACTS(_,{case_def,...})) = case_def
fun induction_of0 (FACTS(_,{induction,...})) = induction
fun induction_of (FACTS(_,{induction,...})) = thm_of induction
fun nchotomy_of (FACTS(_,{nchotomy,...})) = nchotomy
fun distinct_of (FACTS(_,{distinct,...})) = distinct
fun one_one_of (FACTS(_,{one_one,...})) = one_one
fun simpls_of (FACTS(_,{simpls,...})) = simpls
fun axiom_of0 (FACTS(_,{axiom,...})) = axiom
fun axiom_of (FACTS(_,{axiom,...})) = thm_of axiom
fun ty_name_of (FACTS(s,_)) = s

fun size_of0 (FACTS(_,{size,...})) = size;
fun size_of (FACTS(_,{size=NONE,...})) = NONE
  | size_of (FACTS(_,{size=SOME(tm,def),...})) = SOME(tm,thm_of def);


(*---------------------------------------------------------------------------
                    Making alterations
 ---------------------------------------------------------------------------*)

fun put_nchotomy th (FACTS(s,
 {axiom, case_const,case_cong,case_def,constructors,
  induction, nchotomy, distinct, one_one, simpls, size}))
  =
  FACTS(s, {axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def, constructors=constructors,
            induction=induction, nchotomy=th, distinct=distinct,
            one_one=one_one, simpls=simpls, size=size})

fun put_simpls thl (FACTS(s,
 {axiom, case_const, case_cong, case_def, constructors,
  induction, nchotomy, distinct, one_one, simpls, size}))
  =
  FACTS(s, {axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def,constructors=constructors,
            induction=induction, nchotomy=nchotomy, distinct=distinct,
            one_one=one_one, simpls=thl, size=size});

fun put_induction th (FACTS(s,
 {axiom, case_const,case_cong,case_def,constructors,
  induction, nchotomy, distinct, one_one, simpls, size}))
  =
  FACTS(s, {axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def, constructors=constructors,
            induction=th, nchotomy=nchotomy, distinct=distinct,
            one_one=one_one, simpls=simpls, size=size})

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

fun basic_info case_def =
 let val clauses = (strip_conj o concl) case_def
     val lefts   = map (#lhs o dest_eq o #2 o strip_forall) clauses
     val constrs = map (#1 o strip_comb o rand) lefts
     val ty      = type_of (rand (Lib.trye hd lefts))
 in
   (#Tyop(dest_type ty), constrs)
 end
 handle HOL_ERR _ => raise ERR "basic_info" "";


val defn_const =
  #1 o strip_comb o lhs o #2 o strip_forall o hd o strip_conj o concl;


(*---------------------------------------------------------------------------*
 * The size field is not filled by mk_tyinfo, since that operation           *
 * requires access to the current fact database, and also assumes that       *
 * numbers are in the context, which is not necessarily true.                *
 *---------------------------------------------------------------------------*)

fun mk_tyinfo {ax,case_def,case_cong,induction,
               nchotomy,size,one_one,distinct} =
  let val (ty_name,constructors) = basic_info case_def
      val inj = case one_one of NONE => [] | SOME x => [x]
      val D  = case distinct of NONE => [] | SOME x => CONJUNCTS x
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


local fun mk_ti (n,ax,ind) 
                (cdef::cds) (ccong::cgs) (oo::oos) (d::ds) (nch::nchs) =
            mk_tyinfo{ax=COPY(n,ax), induction=COPY(n,ind), case_def=cdef, 
                      case_cong=ccong, nchotomy=nch, size=NONE, 
                      one_one=oo, distinct=d}
            :: mk_ti (n,ax,ind) cds cgs oos ds nchs
        | mk_ti _ [] [] [] [] [] = []
        | mk_ti _ [] _ _ _ _ = raise ERR "gen_tyinfo" "Too few case defns"
        | mk_ti _ _ _ _ _ _  = raise ERR "gen_tyinfo" "Too many case defns"
in
fun gen_tyinfo {ax, ind, case_defs} = 
 let val nchotomyl  = prove_cases_thm ind
     val case_congs = map2 case_cong_thm nchotomyl case_defs
     val one_ones   = prove_constructors_one_one ax
     val distincts  = prove_constructors_distinct ax
     val _ = (length nchotomyl  = length case_congs andalso
              length case_congs = length one_ones   andalso
              length one_ones   = length distincts) 
        orelse raise ERR "gen_tyinfo"
                 "Number of theorems automatically proved doesn't match up"
     val tyinfo_1 = mk_tyinfo
           {ax=ORIG ax, induction=ORIG ind, 
            case_def=hd case_defs, case_cong=hd case_congs, 
            nchotomy=hd nchotomyl, size=NONE, 
            one_one=hd one_ones, distinct=hd distincts}
 in
   if length nchotomyl = 1 then [tyinfo_1]
   else let val tyname = ty_name_of tyinfo_1
        in tyinfo_1 :: mk_ti (tyname,ax,ind)
                          (tl case_defs) (tl case_congs) 
                          (tl one_ones) (tl distincts) (tl nchotomyl)
        end
 end
end;


fun pp_tyinfo ppstrm (FACTS(ty_name,recd)) =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...}
          = with_ppstream ppstrm
     val pp_term = Parse.pp_term ppstrm
     val pp_thm = Parse.pp_thm ppstrm
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
   add_string "Primitive recursion:"; add_break (1,0); 
       (case axiom 
         of ORIG thm  => pp_thm thm
          | COPY(s,_) => add_string ("see "^Lib.quote s)); end_block();
   add_break(1,0);
   begin_block CONSISTENT 1; add_string "Case analysis:";
                             add_break (1,0); pp_thm case_def; end_block();
   add_break(1,0);
   case size
    of NONE => ()
     | SOME (tm,size_def) =>
        (begin_block CONSISTENT 1;
         add_string "Size:"; add_break (1,0);
         (case size_def
           of COPY(s,th) => add_string ("see "^Lib.quote s)
            | ORIG th    => if is_const tm 
                            then pp_thm th else pp_term tm); end_block();
         add_break(1,0));

   begin_block CONSISTENT 1;
   add_string "Induction:"; add_break (1,0); 
       (case induction 
         of ORIG thm  => pp_thm thm
          | COPY(s,_) => add_string ("see "^Lib.quote s)); end_block();
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


(*---------------------------------------------------------------------------
       Computing the size of a type as a term. "tysize" is the more
       general function. It takes a couple of environments
       (theta,gamma); theta maps type variables to size functions, and
       gamma maps type operators to size functions.
 ---------------------------------------------------------------------------*)

local fun drop [] ty = fst(dom_rng ty)
        | drop (_::t) ty = drop t (snd(dom_rng ty));
      fun num() = mk_thy_type{Tyop="num",Thy="num",Args=[]}
      fun Zero() = mk_thy_const{Name="0",Thy="num", Ty=num()}
        handle HOL_ERR _ => raise ERR "type_size.Zero()" "Numbers not declared"
      fun K0 ty = mk_abs{Bvar=mk_var{Name="v",Ty=ty}, Body=Zero()};
      fun join f g x =
        case (g x)
         of NONE => NONE
          | SOME y => (case f y
                        of NONE => NONE
                         | SOME(x,_) => SOME x)
      fun tysize_env db = join size_of (get db)
in
fun tysize (theta,gamma) ty  =
   case theta ty
    of SOME fvar => fvar
     | NONE =>
        let val {Tyop,Args} = dest_type ty
        in case gamma Tyop
            of SOME f =>
                let val vty = drop Args (type_of f)
                    val sigma = match_type vty ty
                in list_mk_comb(inst sigma f,
                                map (tysize (theta,gamma)) Args)
                end
             | NONE => K0 ty
        end

fun type_size db ty =
  let fun theta ty = if is_vartype ty then SOME (K0 ty) else NONE
  in tysize (theta,tysize_env db) ty
  end
end;

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

val [bool_info] = gen_tyinfo {ax=boolTheory.boolAxiom, 
                              ind=boolTheory.bool_INDUCT,
                              case_defs = [boolTheory.bool_case_thm]};

val _ = write bool_info;

end;
