(*---------------------------------------------------------------------------*
 * Building records of facts about datatypes.                                *
 *---------------------------------------------------------------------------*)

structure TypeBasePure :> TypeBasePure =
struct

open HolKernel boolSyntax Drule Conv Prim_rec;

type ppstream = Portable.ppstream

val ERR = mk_HOL_ERR "TypeBasePure";

type simpfrag = simpfrag.simpfrag

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
                     encode       : (term * shared_thm) option,
                     lift         : term option,
                     distinct     : thm option,
                     one_one      : thm option,
                     simpls       : simpfrag};

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

fun encode_of0(FACTS(_,{encode,...})) = encode;
fun encode_of(FACTS(_,{encode=NONE,...})) = NONE
  | encode_of(FACTS(_,{encode=SOME(tm,def),...})) = SOME(tm,thm_of def)

fun lift_of(FACTS(_,{lift,...})) = lift;

(*---------------------------------------------------------------------------
                    Making alterations
 ---------------------------------------------------------------------------*)

fun put_nchotomy th (FACTS(s,
 {axiom, case_const,case_cong,case_def,constructors,
  induction, nchotomy, distinct, one_one, simpls, 
  size, encode, lift}))
  =
  FACTS(s, {axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def, constructors=constructors,
            induction=induction, nchotomy=th, distinct=distinct,
            one_one=one_one, simpls=simpls, 
            size=size, encode=encode,lift=lift})

fun put_simpls thl (FACTS(s,
 {axiom, case_const, case_cong, case_def, constructors,
  induction, nchotomy, distinct, one_one, simpls, size, encode,lift}))
  =
  FACTS(s, {axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def,constructors=constructors,
            induction=induction, nchotomy=nchotomy, distinct=distinct,
            one_one=one_one, simpls=thl, 
            size=size, encode=encode,lift=lift});

fun put_induction th (FACTS(s,
 {axiom, case_const,case_cong,case_def,constructors,
  induction, nchotomy, distinct, one_one, simpls, size, encode,lift}))
  =
  FACTS(s, {axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def, constructors=constructors,
            induction=th, nchotomy=nchotomy, distinct=distinct,
            one_one=one_one, simpls=simpls, 
            size=size, encode=encode,lift=lift})

fun put_size (size_tm,size_rw) (FACTS(s,
 {axiom, case_const,case_cong,case_def,constructors,
  induction, nchotomy, distinct, one_one, simpls, size, encode,lift}))
  =
  FACTS(s, {axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def,constructors=constructors,
            induction=induction, nchotomy=nchotomy, distinct=distinct,
            one_one=one_one, simpls=simpls, size=SOME(size_tm,size_rw),
            encode=encode,lift=lift});

fun put_encode (encode_tm,encode_rw) (FACTS(s,
 {axiom, case_const,case_cong,case_def,constructors,
  induction, nchotomy, distinct, one_one, simpls, size, encode,lift}))
  =
  FACTS(s, {axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def,constructors=constructors,
            induction=induction, nchotomy=nchotomy, distinct=distinct,
            one_one=one_one, simpls=simpls,
            size=size, encode=SOME(encode_tm,encode_rw), lift=lift});

fun put_lift lift_tm (FACTS(s,
 {axiom, case_const,case_cong,case_def,constructors,
  induction, nchotomy, distinct, one_one, simpls, size, encode, lift}))
  =
  FACTS(s, {axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def,constructors=constructors,
            induction=induction, nchotomy=nchotomy, distinct=distinct,
            one_one=one_one, simpls=simpls,
            size=size, encode=encode, lift=SOME lift_tm});


(*---------------------------------------------------------------------------*
 * Returns the datatype name and the constructors. The code is a copy of     *
 * the beginning of "Datatype.define_case".                                  *
 *---------------------------------------------------------------------------*)

fun basic_info case_def =
 let val clauses = (strip_conj o concl) case_def
     val lefts   = map (fst o dest_eq o #2 o strip_forall) clauses
     val constrs = map (#1 o strip_comb o rand) lefts
     val ty      = type_of (rand (Lib.trye hd lefts))
 in
   (fst(dest_type ty), constrs)
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
               nchotomy,size,encode,lift,one_one,distinct} =
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
      simpls       = {rewrs = case_def :: (D@map GSYM D@inj), convs = []},
      size         = size,
      encode       = encode,
      lift         = lift,
      axiom        = ax})
  end;


local fun mk_ti (n,ax,ind)
                (cdef::cds) (ccong::cgs) (oo::oos) (d::ds) (nch::nchs) =
            mk_tyinfo{ax=COPY(n,ax), induction=COPY(n,ind), case_def=cdef,
                      case_cong=ccong, nchotomy=nch, one_one=oo, distinct=d,
                      size=NONE, encode=NONE,lift=NONE}
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
            nchotomy=hd nchotomyl, size=NONE, encode=NONE, lift=NONE,
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
          nchotomy,one_one,distinct,simpls,size,encode,lift,axiom} = recd
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
                            then pp_thm th else pp_term tm)
         ; end_block(); add_break(1,0));

(*   add_break(1,0); *)
   case encode
    of NONE => ()
     | SOME (tm,encode_def) =>
        (begin_block CONSISTENT 1;
         add_string "Encoder:"; add_break (1,0);
         (case encode_def
           of COPY(s,th) => add_string ("see "^Lib.quote s)
            | ORIG th    => if is_const tm
                            then pp_thm th else pp_term tm);
          end_block();
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
      General facility for interpreting types as terms. It takes a
      couple of environments (theta,gamma); theta maps type variables
      to (term) functions on those type variables, and gamma maps
      type operators to (term) functions on elements of the given type.
      The interpretation is partial: for types that are not mapped,
      the supplied function undef is applied.
 ---------------------------------------------------------------------------*)

local fun drop [] ty = fst(dom_rng ty)
        | drop (_::t) ty = drop t (snd(dom_rng ty))
in
fun typeValue (theta,gamma,undef) =
 let fun tyValue ty =
      case theta ty
       of SOME fvar => fvar
        | NONE =>
          let val (Tyop,Args) = dest_type ty
          in case gamma Tyop
              of SOME f =>
                  let val vty = drop Args (type_of f)
                      val sigma = match_type vty ty
                  in list_mk_comb(inst sigma f, map tyValue Args)
                  end
               | NONE => undef ty
          end
  in tyValue
  end
end

(*---------------------------------------------------------------------------
    Map a HOL type (ty) into a term having type :ty -> num.
 ---------------------------------------------------------------------------*)

local fun num() = mk_thy_type{Tyop="num",Thy="num",Args=[]}
      fun Zero() = mk_thy_const{Name="0",Thy="num", Ty=num()}
        handle HOL_ERR _ => raise ERR "type_size.Zero()" "Numbers not declared"
      fun K0 ty = mk_abs(mk_var("v",ty),Zero())
      fun tysize_env db = Option.map fst o
                          Option.composePartial (size_of,get db)
in
fun type_size db ty =
   let fun theta ty = if is_vartype ty then SOME (K0 ty) else NONE
   in typeValue (theta,tysize_env db,K0) ty
   end
end

(*---------------------------------------------------------------------------
    Encoding: map a HOL type (ty) into a term having type :ty -> bool list
 ---------------------------------------------------------------------------*)

local
  fun tyencode_env db =
    Option.map fst o Option.composePartial (encode_of, get db)
  fun undef _ = raise ERR "type_encode" "unknown type"
  fun theta ty =
    if is_vartype ty then raise ERR "type_encode" "type variable" else NONE
in
fun type_encode db = typeValue (theta, tyencode_env db, undef)
end;

(*---------------------------------------------------------------------------*)
(* Lifters are a bit different, since they are ML-level definitions.         *)
(*                                                                           *)
(* Build a HOL term that represents an ML expression that will construct a   *)
(* compound HOL type.                                                        *)
(*---------------------------------------------------------------------------*)

local 
  val string_tyv = mk_vartype "'string"
  val type_tyv   = mk_vartype "'type"
  val typelist_tyv = mk_vartype "'typelist"
  val stringXtypelist_tyv = mk_vartype "'string_X_typelist"
  val mk_type_var = mk_var("mk_type", stringXtypelist_tyv --> type_tyv)
  val cons_var  = mk_var ("cons",type_tyv --> typelist_tyv --> typelist_tyv)
  val nil_var   = mk_var ("nil",typelist_tyv)
  val comma_var = mk_var (",",string_tyv --> typelist_tyv 
                                          --> stringXtypelist_tyv)
  val mk_vartype_var = mk_var("mk_vartype",string_tyv --> type_tyv)
  fun Cons x y = list_mk_comb(cons_var,[x,y])
  fun to_list alist = itlist Cons alist nil_var
  fun tyop_var tyop = mk_var(Lib.quote tyop,string_tyv)
  fun Pair x y = list_mk_comb(comma_var,[x,y])
  val bool_var = mk_var("bool",type_tyv)
in
fun enc_type ty =
  if is_vartype ty 
  then mk_comb(mk_vartype_var,
               mk_var(Lib.quote (dest_vartype ty),string_tyv))
  else
  if ty = Type.bool then bool_var
  else
  let val (tyop,args) = dest_type ty
      val enc_args = to_list(map enc_type args)
      val enc_tyop = tyop_var tyop
      val pair = Pair enc_tyop enc_args
  in 
    mk_comb(mk_type_var,pair)
  end
end;

(*---------------------------------------------------------------------------*)
(* Implements the interpretation of a type, which yields a function to be    *)
(* applied to a term. (Except that in this case, it is applied to an ML      *)
(* value.)                                                                   *)
(*                                                                           *)
(*    [| v |] = Theta(v), where v is a type variable                         *)
(*   [| ty |] = Gamma(c) ty [| t1 |] ... [| tn |], where ty is (t1,...,tn)c  *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

local fun drop [] ty = fst(dom_rng ty)
        | drop (_::t) ty = drop t (snd(dom_rng ty))
in
fun tyValue (theta,gamma,undef) =
 let fun tyVal ty = 
      case theta ty  (* map type variable *)
       of SOME x => x
        | NONE =>    (* map compound type *)
          let val (Tyop,Args) = dest_type ty
          in case gamma Tyop
              of SOME f =>
                  let val vty = drop (alpha::Args) (type_of f)
                      val sigma = match_type vty ty
                  in list_mk_comb(inst sigma f, 
                                  enc_type ty::map tyVal Args)
                  end
               | NONE => undef Tyop
          end
  in tyVal
  end
end

fun Undef tyop = raise ERR "Undef"
                           (Lib.quote tyop^" is an unknown type operator");

(*---------------------------------------------------------------------------*)
(* Used to synthesize lifters                                                *)
(*---------------------------------------------------------------------------*)

local fun mk_K_1(tm,ty) = 
        let val ty1 = type_of tm
            val K = mk_thy_const{Name="K",Thy="combin",
                                 Ty = ty1 --> ty --> ty1}
        in mk_comb(K,tm)
        end
in
fun type_lift db ty =
  let val TYV = type_vars ty
      val tyv_fns = map (fn tyv => mk_K_1(boolSyntax.mk_arb tyv, tyv)) TYV
      val Theta = C assoc (zip TYV tyv_fns)
      val Gamma = Option.composePartial (lift_of, get db)
  in 
     tyValue (total Theta, Gamma, Undef) ty
  end
end;

(*---------------------------------------------------------------------------*)
(* Instantiate a constructor to a type. Used in lifting (see                 *)
(* datatype/Lift.sml                                                         *)
(*---------------------------------------------------------------------------*)

fun cinst ty c =
  let val cty = snd(strip_fun(type_of c))
      val theta = match_type cty ty
  in inst theta c
  end

(*---------------------------------------------------------------------------*)
(* Syntax operations on the (extensible) set of case expressions.            *)
(*---------------------------------------------------------------------------*)

fun mk_case tybase (exp, plist) =
  case get tybase (fst(dest_type (type_of exp)))
   of NONE => raise ERR "mk_case" "unable to analyze type"
    | SOME tyinfo =>
       let val c = case_const_of tyinfo
           val fns = map (fn (p,R) => list_mk_abs(snd(strip_comb p),R)) plist
           val ty' = list_mk_fun (map type_of fns@[type_of exp],
                                  type_of (snd (hd plist)))
           val theta = match_type (type_of c) ty'
       in list_mk_comb(inst theta c,fns@[exp])
       end;
                         

local fun build_case_clause(constr,rhs) =
 let val (args,r) = strip_fun (type_of constr)
     fun peel [] N = ([],N)
       | peel (_::tys) N = 
           let val (v,M) = dest_abs N
               val (V,M') = peel tys M
           in (v::V,M')
           end
     val (V,rhs') = peel args rhs
     val theta = match_type (list_mk_fun (args,ind))
                            (list_mk_fun (map type_of V, ind))
     val constr' = inst theta constr
  in (list_mk_comb(constr',V), rhs')
  end
in
fun dest_case tybase M = 
  let val (c,args) = strip_comb M
      val (cases,arg) = front_last args
      val tyop = fst(dest_type (type_of arg))
  in case get tybase tyop
      of NONE => raise ERR "dest_case" "unable to destruct case expression"
       | SOME tyinfo => 
          let val d = case_const_of tyinfo
          in if same_const c d
           then let val constrs = constructors_of tyinfo
                in (c, arg, map build_case_clause (zip constrs cases))
                end
           else raise ERR "dest_case" "unable to destruct case expression"
          end
  end
end

fun is_case tybase M = 
  let val (c,args) = strip_comb M
      val tyop = fst(dest_type (type_of (last args)))
  in case get tybase tyop
      of NONE => raise ERR "is_case" ("unknown type operator: "^Lib.quote tyop)
       | SOME tyinfo => same_const c (case_const_of tyinfo) 
  end 
  handle HOL_ERR _ => false;

fun is_constructor tybase c =
  let val (_,ty) = strip_fun (type_of c)
      val {Tyop,...} = dest_thy_type ty
  in case get tybase Tyop
     of NONE => false
      | SOME tyinfo => op_mem same_const c (constructors_of tyinfo)
  end handle HOL_ERR _ => false;


end
