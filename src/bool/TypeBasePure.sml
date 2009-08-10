(*---------------------------------------------------------------------------*
 * Building records of facts about datatypes.                                *
 *---------------------------------------------------------------------------*)

structure TypeBasePure :> TypeBasePure =
struct

open HolKernel boolSyntax Drule Conv Prim_rec;
type ppstream = Portable.ppstream

val ERR = mk_HOL_ERR "TypeBasePure";

fun type_names ty =
  let val {Thy,Tyop,Args} = Type.dest_thy_type ty
  in (Thy,Tyop)
  end;

type simpfrag = simpfrag.simpfrag

datatype shared_thm
    = ORIG of thm
    | COPY of (string * string) * thm;

fun thm_of (ORIG x)     = x
  | thm_of (COPY (s,x)) = x;

(*---------------------------------------------------------------------------*)
(* Support both constructor-style datatypes and other types as well.         *)
(*---------------------------------------------------------------------------*)

type dtyinfo =
           {ty           : hol_type,
            axiom        : shared_thm,
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
            fields       : (string * hol_type) list,
            accessors    : thm list,
            updates      : thm list,
            simpls       : simpfrag} ;

type ntyinfo = hol_type *
          {nchotomy : thm option,
           size : (term * thm) option,
           encode : (term * thm) option};

datatype tyinfo = DFACTS of dtyinfo
                | NFACTS of ntyinfo;


(*---------------------------------------------------------------------------
                  Projections
 ---------------------------------------------------------------------------*)

fun ty_of (DFACTS {ty,...}) = ty
  | ty_of (NFACTS(ty,_)) = ty;

fun dollarty ty =
  let val {Thy,Tyop,Args} = dest_thy_type ty
  in Lib.quote (Thy ^ "$" ^ Tyop)
  end;

val ty_name_of = type_names o ty_of

fun constructors_of (DFACTS {constructors,...}) = constructors
  | constructors_of (NFACTS _) = [];

fun case_const_of (DFACTS {case_const,...}) = case_const
  | case_const_of (NFACTS (ty,_)) =
      raise ERR "case_const_of" (dollarty ty^" is not a datatype");

fun case_cong_of (DFACTS {case_cong,...}) = case_cong
  | case_cong_of (NFACTS (ty,_)) =
       raise ERR "case_cong_of" (dollarty ty^" is not a datatype");

fun case_def_of (DFACTS {case_def,...}) = case_def
  | case_def_of (NFACTS (ty,_)) =
       raise ERR "case_def_of" (dollarty ty^" is not a datatype");

fun induction_of0 (DFACTS {induction,...}) = induction
  | induction_of0 (NFACTS (ty,_)) =
        raise ERR "induction_of0" (dollarty ty^" is not a datatype");

fun induction_of (DFACTS {induction,...}) = thm_of induction
  | induction_of (NFACTS (ty,_)) =
        raise ERR "induction_of" (dollarty ty^" is not a datatype");

fun nchotomy_of (DFACTS {nchotomy,...}) = nchotomy
  | nchotomy_of (NFACTS(_,{nchotomy=SOME th,...})) = th
  | nchotomy_of (NFACTS(ty,{nchotomy=NONE,...})) =
        raise ERR "nchotomy_of" (dollarty ty^" no cases theorem available");

fun distinct_of (DFACTS {distinct,...}) = distinct
  | distinct_of (NFACTS (ty,_)) =
        raise ERR "distinct_of" (dollarty ty^" is not a datatype");

fun one_one_of (DFACTS {one_one,...}) = one_one
  | one_one_of (NFACTS (ty,_)) =
        raise ERR "one_one_of" (dollarty ty^" is not a datatype");

fun fields_of (DFACTS {fields,...}) = fields
  | fields_of (NFACTS _) = [];

fun accessors_of (DFACTS {accessors,...}) = accessors
  | accessors_of (NFACTS _) = [];

fun updates_of (DFACTS {updates,...}) = updates
  | updates_of (NFACTS _) = [];

fun simpls_of (DFACTS {simpls,...}) = simpls
  | simpls_of (NFACTS _) = simpfrag.empty_simpfrag;

fun axiom_of0 (DFACTS {axiom,...}) = axiom
  | axiom_of0 (NFACTS (ty,_)) =
      raise ERR "axiom_of0" (dollarty ty^" is not a datatype");

fun axiom_of (DFACTS {axiom,...}) = thm_of axiom
  | axiom_of (NFACTS (ty,_)) =
      raise ERR "axiom_of" (dollarty ty^" is not a datatype");

fun size_of0 (DFACTS {size,...}) = size
  | size_of0 (NFACTS (ty,_)) =
      raise ERR "size_of0" (dollarty ty^" is not a datatype");

fun size_of (DFACTS {size=NONE,...}) = NONE
  | size_of (DFACTS {size=SOME(tm,def),...}) = SOME(tm,thm_of def)
  | size_of (NFACTS(_,{size,...})) = size;

fun encode_of0(DFACTS {encode,...}) = encode
  | encode_of0(NFACTS (ty,_)) =
       raise ERR "encode_of0" (dollarty ty^" is not a datatype")

fun encode_of(DFACTS {encode=NONE,...}) = NONE
  | encode_of(DFACTS {encode=SOME(tm,def),...}) = SOME(tm,thm_of def)
  | encode_of(NFACTS(_,{encode,...})) = encode;

fun lift_of(DFACTS {lift,...}) = lift
  | lift_of(NFACTS (ty,_)) =
       raise ERR "lift_of" (dollarty ty^" is not a datatype")
;

(*---------------------------------------------------------------------------
                    Making alterations
 ---------------------------------------------------------------------------*)

fun put_nchotomy th (DFACTS
      {ty,axiom, case_const,case_cong,case_def, constructors,
       induction, nchotomy, distinct, one_one, fields,
        accessors, updates, simpls, size, encode, lift})
    = DFACTS{ty=ty,axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def, constructors=constructors,
            induction=induction, nchotomy=th, distinct=distinct,
            one_one=one_one, fields=fields,
            accessors=accessors, updates=updates, simpls=simpls,
            size=size, encode=encode,lift=lift}
  | put_nchotomy th (NFACTS(ty,{nchotomy,size,encode})) =
      NFACTS(ty,{nchotomy=SOME th,size=size,encode=encode});

fun put_simpls thl (DFACTS
 {ty,axiom, case_const, case_cong, case_def, constructors,
  induction, nchotomy, distinct, one_one, fields,
  accessors, updates, simpls, size, encode,lift})
  =
  DFACTS {ty=ty,axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def,constructors=constructors,
            induction=induction, nchotomy=nchotomy, distinct=distinct,
            one_one=one_one, fields=fields, accessors=accessors, updates=updates,
            simpls=thl, size=size, encode=encode,lift=lift}
 | put_simpls _ _ = raise ERR "put_simpls" "not a datatype";

fun put_induction th (DFACTS
 {ty,axiom, case_const,case_cong,case_def,constructors,
  induction, nchotomy, distinct, one_one, fields,
  accessors, updates, simpls, size, encode,lift})
  =
  DFACTS {ty=ty,axiom=axiom, case_const=case_const,
          case_cong=case_cong,case_def=case_def, constructors=constructors,
          induction=th, nchotomy=nchotomy, distinct=distinct,
          one_one=one_one, fields=fields, accessors=accessors, updates=updates,
          simpls=simpls, size=size, encode=encode,lift=lift}
 | put_induction _ _ = raise ERR "put_induction" "not a datatype";

fun put_size (size_tm,size_rw) (DFACTS
       {ty,axiom, case_const,case_cong,case_def,constructors,
        induction, nchotomy, distinct, one_one, fields,
        accessors, updates, simpls, size, encode,lift})
    =
    DFACTS {ty=ty,axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def,constructors=constructors,
            induction=induction, nchotomy=nchotomy, distinct=distinct,
            one_one=one_one, fields=fields,
            accessors=accessors, updates=updates, simpls=simpls,
            size=SOME(size_tm,size_rw), encode=encode,lift=lift}
  | put_size (size_tm,size_rw) (NFACTS(ty,{nchotomy,size,encode})) =
      NFACTS(ty,{nchotomy=nchotomy,size=SOME(size_tm,thm_of size_rw),
                 encode=encode});

fun put_encode (encode_tm,encode_rw) (DFACTS
       {ty,axiom, case_const,case_cong,case_def,constructors,
        induction, nchotomy, distinct, one_one, fields,
        accessors, updates, simpls, size, encode,lift})
     =
     DFACTS{ty=ty,axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def,constructors=constructors,
            induction=induction, nchotomy=nchotomy, distinct=distinct,
            one_one=one_one, fields=fields,
            accessors=accessors, updates=updates, simpls=simpls,
            size=size, encode=SOME(encode_tm,encode_rw), lift=lift}
  | put_encode (encode_tm,encode_rw) (NFACTS(ty,{nchotomy,size,encode})) =
     NFACTS(ty,{nchotomy=nchotomy,size=size,encode=SOME(encode_tm,thm_of encode_rw)});

fun put_lift lift_tm (DFACTS
 {ty,axiom, case_const,case_cong,case_def,constructors,
  induction, nchotomy, distinct, one_one, fields,
  accessors, updates, simpls, size, encode, lift})
  =
  DFACTS {ty=ty,axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def,constructors=constructors,
            induction=induction, nchotomy=nchotomy, distinct=distinct,
            one_one=one_one, fields=fields,
            accessors=accessors, updates=updates, simpls=simpls,
            size=size, encode=encode, lift=SOME lift_tm}
 | put_lift _ _ = raise ERR "put_lift" "not a datatype";

fun put_fields flds (DFACTS
 {ty,axiom, case_const,case_cong,case_def,constructors,
  induction, nchotomy, distinct, one_one, fields,
  accessors, updates, simpls, size, encode, lift})
  =
  DFACTS {ty=ty,axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def,constructors=constructors,
            induction=induction, nchotomy=nchotomy, distinct=distinct,
            one_one=one_one, fields=flds,
            accessors=accessors, updates=updates, simpls=simpls,
            size=size, encode=encode, lift=lift}
 | put_fields _ _ = raise ERR "put_fields" "not a datatype";

fun put_accessors thl (DFACTS
 {ty,axiom, case_const,case_cong,case_def,constructors,
  induction, nchotomy, distinct, one_one, fields,
  accessors, updates, simpls, size, encode, lift})
  =
  DFACTS {ty=ty,axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def,constructors=constructors,
            induction=induction, nchotomy=nchotomy, distinct=distinct,
            one_one=one_one, fields=fields,
            accessors=thl, updates=updates, simpls=simpls,
            size=size, encode=encode, lift=lift}
 | put_accessors _ _ = raise ERR "put_accessors" "not a datatype";

fun put_updates thl (DFACTS
 {ty,axiom, case_const,case_cong,case_def,constructors,
  induction, nchotomy, distinct, one_one, fields,
  accessors, updates, simpls, size, encode, lift})
  =
  DFACTS {ty=ty,axiom=axiom, case_const=case_const,
            case_cong=case_cong,case_def=case_def,constructors=constructors,
            induction=induction, nchotomy=nchotomy, distinct=distinct,
            one_one=one_one, fields=fields,
            accessors=accessors, updates=thl, simpls=simpls,
            size=size, encode=encode, lift=lift}
 | put_updates _ _ = raise ERR "put_updates" "not a datatype";

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
   (ty, type_names ty, constrs)
 end
 handle HOL_ERR _ => raise ERR "basic_info" "";


val defn_const =
  #1 o strip_comb o lhs o #2 o strip_forall o hd o strip_conj o concl;


(*---------------------------------------------------------------------------*
 * The size field is not filled by mk_tyinfo, since that operation           *
 * requires access to the current fact database, and also assumes that       *
 * numbers are in the context, which is not necessarily true.                *
 *---------------------------------------------------------------------------*)

fun mk_datatype_info {ax,case_def,case_cong,induction,
                      nchotomy,size,encode,lift,one_one,
                      fields, accessors, updates, distinct} =
  let val (ty,ty_names,constructors) = basic_info case_def
      val inj = case one_one of NONE => [] | SOME x => [x]
      val D  = case distinct of NONE => [] | SOME x => CONJUNCTS x
  in
   DFACTS
     {ty           = ty,
      constructors = constructors,
      case_const   = defn_const case_def,
      case_def     = case_def,
      case_cong    = case_cong,
      induction    = induction,
      nchotomy     = nchotomy,
      one_one      = one_one,
      distinct     = distinct,
      fields       = fields,
      accessors    = accessors,
      updates      = updates,
      simpls       = {rewrs = case_def :: (D@map GSYM D@inj), convs = []},
      size         = size,
      encode       = encode,
      lift         = lift,
      axiom        = ax}
  end;


local fun mk_ti (n,ax,ind)
                (cdef::cds) (ccong::cgs) (oo::oos) (d::ds) (nch::nchs) =
            mk_datatype_info{ax=COPY(n,ax), induction=COPY(n,ind),
                      case_def=cdef,case_cong=ccong, nchotomy=nch,
                      one_one=oo, distinct=d,size=NONE, encode=NONE,
                      lift=NONE, fields=[], accessors=[],updates=[]}
            :: mk_ti (n,ax,ind) cds cgs oos ds nchs
        | mk_ti _ [] [] [] [] [] = []
        | mk_ti _ [] _ _ _ _ = raise ERR "gen_tyinfo" "Too few case defns"
        | mk_ti _ _ _ _ _ _  = raise ERR "gen_tyinfo" "Too many case defns"
in
fun gen_datatype_info {ax, ind, case_defs} =
 let val nchotomyl  = prove_cases_thm ind
     val case_congs = map2 case_cong_thm nchotomyl case_defs
     val one_ones   = prove_constructors_one_one ax
     val distincts  = prove_constructors_distinct ax
     val _ = (length nchotomyl  = length case_congs andalso
              length case_congs = length one_ones   andalso
              length one_ones   = length distincts)
        orelse raise ERR "gen_tyinfo"
                 "Number of theorems automatically proved doesn't match up"
     val tyinfo_1 = mk_datatype_info
           {ax=ORIG ax, induction=ORIG ind,
            case_def = hd case_defs, case_cong = hd case_congs,
            nchotomy = hd nchotomyl,
            size=NONE, encode=NONE, lift=NONE,
            fields=[], accessors=[],updates=[],
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

fun mk_nondatatype_info (ty,record) = NFACTS(ty,record);


fun name_pair(s1,s2) = s1^"$"^s2;

fun pp_tyinfo ppstrm (d as DFACTS recd) =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...}
          = with_ppstream ppstrm
     val pp_term = Parse.pp_term ppstrm
     val pp_thm = Parse.pp_thm ppstrm
     val {ty,constructors, case_const, case_def, case_cong, induction,
          nchotomy,one_one,distinct,simpls,size,encode,lift,axiom,
          fields, accessors, updates} = recd
     val ty_namestring = name_pair (ty_name_of d)
 in
   begin_block CONSISTENT 0;
     begin_block INCONSISTENT 0;
        add_string "-----------------------"; add_newline ppstrm;
        add_string "-----------------------"; add_newline ppstrm;
        add_string "HOL datatype:"; add_break(1,0);
        add_string (Lib.quote ty_namestring); end_block();
   add_break(1,0);
   begin_block CONSISTENT 1;
   add_string "Primitive recursion:"; add_break (1,0);
       (case axiom
         of ORIG thm  => pp_thm thm
          | COPY(sp,_) => add_string ("see "^Lib.quote (name_pair sp)));
        end_block();
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
           of COPY(sp,th) => add_string ("see "^Lib.quote (name_pair sp))
            | ORIG th    => if is_const tm
                            then pp_thm th else pp_term tm)
         ; end_block(); add_break(1,0));

   (* add_break(1,0); *)
   case encode
    of NONE => ()
     | SOME (tm,encode_def) =>
        (begin_block CONSISTENT 1;
         add_string "Encoder:"; add_break (1,0);
         (case encode_def
           of COPY(sp,th) => add_string ("see "^Lib.quote (name_pair sp))
            | ORIG th    => if is_const tm
                            then pp_thm th else pp_term tm);
          end_block();
          add_break(1,0));

   begin_block CONSISTENT 1;
   add_string "Induction:"; add_break (1,0);
    (case induction
      of ORIG thm  => pp_thm thm
       | COPY(sp,_) => add_string ("see "^Lib.quote (name_pair sp)));
   end_block();
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
 end
 | pp_tyinfo ppstrm (NFACTS(ty,recd)) =
   let open Portable
     val {add_string,add_break,begin_block,end_block,...}
           = with_ppstream ppstrm
     val pp_type = Parse.pp_type ppstrm
     val pp_term = Parse.pp_term ppstrm
     val pp_thm = Parse.pp_thm ppstrm
     val {nchotomy,size,encode} = recd
   in
    begin_block CONSISTENT 0;
     begin_block INCONSISTENT 0;
        add_string "-----------------------"; add_newline ppstrm;
        add_string "-----------------------"; add_newline ppstrm;
        add_string "HOL type:";
        add_break(1,0);
        pp_type ty;
     end_block();
    add_break(1,0);
     begin_block CONSISTENT 1;
       add_string "Case completeness:"; add_break (1,0);
       (case nchotomy
         of NONE => add_string "none"
          | SOME thm => pp_thm thm);
     end_block();
    end_block()
  end;



(*---------------------------------------------------------------------------*)
(* Database of facts.                                                        *)
(*---------------------------------------------------------------------------*)

type typeBase = tyinfo TypeNet.typenet

val empty : typeBase = TypeNet.empty

fun next_ty ty = mk_vartype(Lexis.tyvar_vary (dest_vartype ty))

(*---------------------------------------------------------------------------*)
(* Rename type variables in a type so that they occur in alphabetical order, *)
(* from left-to-right, and start from 'a. Example:                           *)
(*                                                                           *)
(*  normalise_ty ``:('k#'a) list`` = ``:('a#'b) list                         *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun normalise_ty ty = let
  fun recurse (acc as (dict,usethis)) tylist =
      case tylist of
        [] => acc
      | ty :: rest => let
        in
          if is_vartype ty then
            case Binarymap.peek(dict,ty) of
                NONE => recurse (Binarymap.insert(dict,ty,usethis),
                                 next_ty usethis)
                                rest
              | SOME _ => recurse acc rest
          else let
              val {Args,...} = dest_thy_type ty
            in
              recurse acc (Args @ rest)
            end
        end
  val (inst0, _) = recurse (Binarymap.mkDict Type.compare, Type.alpha) [ty]
  val inst = Binarymap.foldl (fn (tyk,tyv,acc) => (tyk |-> tyv)::acc)
                             []
                             inst0
in
  Type.type_subst inst ty
end

fun prim_get (db:typeBase) (thy,tyop) =
    case Type.op_arity {Thy = thy, Tyop = tyop} of
      NONE => NONE
    | SOME i => let
        fun genargs (acc,nextty) n = if n = 0 then List.rev acc
                                 else genargs (nextty :: acc, next_ty nextty)
                                              (n - 1)
        val ty = mk_thy_type {Thy = thy, Tyop = tyop,
                              Args = genargs ([], alpha) i}
      in
        TypeNet.peek (db, ty)
      end

fun add db (d as DFACTS x) = TypeNet.insert(db, normalise_ty (ty_of d), d)
  | add db (NFACTS _) = raise ERR "add" "not a datatype"

fun listItems db = map #2 (TypeNet.listItems db)

fun get db s = let
  fun foldthis (ty,tyi as DFACTS _,acc) =
      if #2 (type_names ty) = s then tyi::acc else acc
    | foldthis (ty, _, acc) = acc
in
  TypeNet.fold foldthis [] db
end

(*---------------------------------------------------------------------------*)
(* If ty1 is an instance of ty2, then return the record                      *)
(*---------------------------------------------------------------------------*)

fun tysize ty =
    if Type.is_vartype ty then 1
    else let
        val {Args,...} = Type.dest_thy_type ty
      in
        1 + List.foldl (fn (ty,acc) => tysize ty + acc) 0 Args
      end

fun mymatch pat ty = let
  val (i, sames) = Type.raw_match_type pat ty ([], [])
in
  i @ (map (fn ty => ty |-> ty) sames)
end

fun instsize i =
    List.foldl (fn ({redex,residue},acc) => tysize residue + acc) 0 i

fun check_match ty (pat, data) =
    SOME(instsize (mymatch pat ty), data) handle HOL_ERR _ => NONE

fun fetch tbase ty =
    case TypeNet.match (tbase, ty) of
      [] => NONE
    | matches0 => let
        val matches = List.mapPartial (check_match ty) matches0
        val sorted = Listsort.sort (measure_cmp fst) matches
      in
        SOME (#2 (hd sorted))
      end

fun insert dbs (x as DFACTS _) = add dbs x
  | insert db (x as NFACTS _) = TypeNet.insert(db,normalise_ty (ty_of x),x)


(*---------------------------------------------------------------------------
      General facility for interpreting types as terms. It takes a
      couple of environments (theta,gamma); theta maps type variables
      to (term) functions on those type variables, and gamma maps
      type operators to (term) functions on elements of the given type.
      The interpretation is partial: for types that are not mapped,
      the supplied function undef is applied.
 ---------------------------------------------------------------------------*)

(*
local fun drop [] ty = fst(dom_rng ty)
        | drop (_::t) ty = drop t (snd(dom_rng ty))
in
fun typeValue (theta,gamma,undef) =
 let fun tyValue ty =
      case theta ty
       of SOME fvar => fvar
        | NONE =>
          let val {Thy,Tyop,Args} = dest_thy_type ty
          in case gamma (Thy,Tyop)
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
*)

(* Not sure this will work ... *)
fun typeValue (theta,gamma,undef) =
 let fun tyValue ty =
      case theta ty
       of SOME fvar => fvar
        | NONE =>
           case gamma ty
              of SOME f =>
                  let val (tys,rng) = strip_fun (type_of f)
                      val vty = last tys
                      val sigma = match_type vty ty handle HOL_ERR _ => []
                      val args = snd(dest_type ty)
                  in list_mk_comb(inst sigma f, map tyValue args)
                  end
               | NONE => undef ty
 in tyValue
 end

(*---------------------------------------------------------------------------
    Map a HOL type (ty) into a term having type :ty -> num.
 ---------------------------------------------------------------------------*)

local fun num() = mk_thy_type{Tyop="num",Thy="num",Args=[]}
      fun Zero() = mk_thy_const{Name="0",Thy="num", Ty=num()}
        handle HOL_ERR _ => raise ERR "type_size.Zero()" "Numbers not declared"
      fun K0 ty = mk_abs(mk_var("v",ty),Zero())
      fun tysize_env db = Option.map fst o
                          Option.composePartial (size_of,fetch db)
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
    Option.map fst o Option.composePartial (encode_of, fetch db)
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
          let val {Thy,Tyop,Args} = dest_thy_type ty
          in case gamma ty
              of SOME f =>
                  let val vty = drop (alpha::Args) (type_of f)
                      val sigma = match_type vty ty
                  in list_mk_comb(inst sigma f,
                                  enc_type ty::map tyVal Args)
                  end
               | NONE => undef ty
          end
  in tyVal
  end
end

fun Undef ty =
    raise ERR "Undef"
              (Lib.quote (Parse.type_to_string ty)^" is an unknown type");

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
      val Gamma = Option.composePartial (lift_of, fetch db)
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
(* Is a constant a constructor for some datatype.                            *)
(*---------------------------------------------------------------------------*)

fun is_constructor tybase c =
  let val (_,ty) = strip_fun (type_of c)
  in case prim_get tybase (type_names ty)
     of NONE => false
      | SOME tyinfo => op_mem same_const c (constructors_of tyinfo)
  end handle HOL_ERR _ => false;

fun is_constructor_pat tybase tm =
    is_constructor tybase (fst (strip_comb tm))

fun is_constructor_var_pat tybase tm =
    is_var tm orelse is_constructor_pat tybase tm

(*---------------------------------------------------------------------------*)
(* Syntax operations on the (extensible) set of case expressions.            *)
(*---------------------------------------------------------------------------*)

fun mk_case1 tybase (exp, plist) =
  case prim_get tybase (type_names (type_of exp))
   of NONE => raise ERR "mk_case" "unable to analyze type"
    | SOME tyinfo =>
       let val c = case_const_of tyinfo
           val fns = map (fn (p,R) => list_mk_abs(snd(strip_comb p),R)) plist
           val ty' = list_mk_fun (map type_of fns@[type_of exp],
                                  type_of (snd (hd plist)))
           val theta = match_type (type_of c) ty'
       in list_mk_comb(inst theta c,fns@[exp])
       end;

fun mk_case2 v (exp, plist) =
       let fun mk_switch [] = raise ERR "mk_case" "null patterns"
             | mk_switch [(p,R)] = R
             | mk_switch ((p,R)::rst) =
                  mk_bool_case(R, mk_switch rst, mk_eq(v,p))
           val switch = mk_switch plist
       in if v = exp then switch
                     else mk_literal_case(mk_abs(v,switch),exp)
       end;

fun mk_case tybase (exp, plist) =
  let val col0 = map fst plist
  in if all (is_constructor_var_pat tybase) col0
        andalso not (all is_var col0)
     then (* constructor patterns *)
          mk_case1 tybase (exp, plist)
     else (* literal patterns *)
          mk_case2 (last col0) (exp, plist)
  end


(*---------------------------------------------------------------------------*)
(* dest_case destructs one level of pattern matching. To deal with nested    *)
(* patterns, use strip_case.                                                 *)
(*---------------------------------------------------------------------------*)

local fun build_case_clause((ty,constr),rhs) =
 let val (args,tau) = strip_fun (type_of constr)
     fun peel  [] N = ([],N)
       | peel (_::tys) N =
           let val (v,M) = dest_abs N
               val (V,M') = peel tys M
           in (v::V,M')
           end
     val (V,rhs') = peel args rhs
     val theta = match_type (type_of constr) (list_mk_fun (map type_of V, ty))
     val constr' = inst theta constr
 in
   (list_mk_comb(constr',V), rhs')
  end
in
fun dest_case1 tybase M =
  let val (c,args) = strip_comb M
      val (cases,arg) = front_last args
  in case prim_get tybase (type_names (type_of arg))
      of NONE => raise ERR "dest_case" "unable to destruct case expression"
       | SOME tyinfo =>
          let val d = case_const_of tyinfo
          in if same_const c d
           then let val constrs = constructors_of tyinfo
                    val constrs_type = map (pair (type_of arg)) constrs
                in (c, arg, map build_case_clause (zip constrs_type cases))
                end
           else raise ERR "dest_case" "unable to destruct case expression"
          end
  end
end

fun dest_case tybase M =
  if is_literal_case M then
  let val (lcf, e)  = dest_comb M
      val (lit_cs, f) = dest_comb lcf
      val (x, M')  = dest_abs f
  in (lit_cs, e, [(x,M')])
  end
  else dest_case1 tybase M

fun is_case1 tybase M =
  let val (c,args) = strip_comb M
      val (tynames as (_,tyop)) = type_names (type_of (last args))
  in case prim_get tybase tynames
      of NONE => raise ERR "is_case" ("unknown type operator: "^Lib.quote tyop)
       | SOME tyinfo => same_const c (case_const_of tyinfo)
  end
  handle HOL_ERR _ => false;

fun is_case tybase M = is_literal_case M orelse is_case1 tybase M

local fun dest tybase (pat,rhs) =
 let val patvars = free_vars pat
 in if is_case tybase rhs
    then let val (case_tm,exp,clauses) = dest_case tybase rhs
             val (pats,rhsides) = unzip clauses
         in if is_eq exp
            then let val (v,e) = dest_eq exp
                     val fvs = free_vars v
                     val pat0 = if is_var v then subst [v |-> e] pat
                                else e (* fails if pat ~= v *)
                  (* val theta = fst (match_term v e) handle HOL_ERR _ => [] *)
                  in if null (subtract fvs patvars)
                  (* andalso null_intersection fvs (free_vars (hd rhsides)) *)
                     then flatten (map (dest tybase)
                                       (zip [pat0, pat] rhsides))
                     else [(pat,rhs)]
                  end
             else let val fvs = free_vars exp
                  in if null (subtract fvs patvars) andalso
                        null_intersection fvs (free_varsl rhsides)
                     then flatten
                            (map (dest tybase)
                               (zip (map (fn p =>
                                      subst (fst (match_term exp p)) pat) pats)
                                    rhsides))
                     else [(pat,rhs)]
                  end
                  handle HOL_ERR _ => [(pat,rhs)] (* catch from match_term *)
          end
     else [(pat,rhs)]
  end
  handle e => raise Feedback.wrap_exn "TypeBasePure" "strip_case(dest)" e
in
fun strip_case1 tybase M =
 (case total (dest_case1 tybase) M
   of NONE => (M,[])
    | SOME(case_tm,exp,cases) =>
         if is_eq exp
         then let val (v,e) = dest_eq exp
              in (v, flatten (map (dest tybase)
                               (zip [e, v] (map snd cases))))
              end
         else (exp, flatten (map (dest tybase) cases)))
 handle e => raise (Feedback.wrap_exn "TypeBasePure" "strip_case" e)
end;

fun strip_case tybase M =
  if is_literal_case M then
  let val (lcf, e) = dest_comb M
      val (lit_cs, f) = dest_comb lcf
      val (x, M') = dest_abs f
      val (exp, cases) = if is_case1 tybase M'
                         then strip_case1 tybase M'
                         else (x, [(x, M')])
  in (e, cases)
  end
  else strip_case1 tybase M


(*---------------------------------------------------------------------------*)
(* Syntax operations for record types.                                       *)
(*---------------------------------------------------------------------------*)

fun is_record_type tybase ty =
  (case prim_get tybase (type_names ty)
   of NONE => false
    | SOME tyinfo => not (null (fields_of tyinfo)))
  handle HOL_ERR _ => false;

fun has_record_type tybase M = is_record_type tybase (type_of M);

(*---------------------------------------------------------------------------*)
(* The function                                                              *)
(*                                                                           *)
(*   dest_record : tyBase -> term -> (string * hol_type) list                *)
(*                                                                           *)
(* needs to know about the TypeBase in order to tell if the term is an       *)
(* element of a record type.                                                 *)
(*---------------------------------------------------------------------------*)

fun mk_K_1 (tm,ty) =
  let val K_tm = prim_mk_const{Name="K",Thy="combin"}
  in mk_comb(inst [alpha |-> type_of tm, beta |-> ty] K_tm,tm)
  end;
fun dest_K_1 tm =
  let val K_tm = prim_mk_const{Name="K",Thy="combin"}
  in dest_monop K_tm (ERR "dest_K_1" "not a K-term") tm
  end;

fun get_field_name s1 s2 =
  let val prefix = String.extract(s2,0,SOME(String.size s1))
      val rest = String.extract(s2,String.size s1 + 1, NONE)
      val middle = String.extract(rest,0,SOME(String.size rest - 5))
      val suffix = String.extract(rest,String.size middle, NONE)
  in
    if prefix = s1 andalso suffix = "_fupd"
      then middle
      else raise ERR "get_field" ("unable to parse "^Lib.quote s2)
  end;

(*---------------------------------------------------------------------------*)
(* A record looks like `fupd arg_1 (fupd arg_2 ... (fupd arg_n ARB) ...)`    *)
(* where each arg_i is a (name,type) pair showing how the ith field should   *)
(* be declared.                                                              *)
(*---------------------------------------------------------------------------*)

fun dest_field tm =
  let val (ty,_) = dom_rng (type_of tm)
      val tyname = fst(dest_type ty)
      val (updf,arg) = dest_comb tm
      val (name0,ty) = dest_const updf
      val name = get_field_name tyname name0
  in
    (name,dest_K_1 arg)
  end
  handle HOL_ERR _ => raise ERR "dest_field" "unexpected term structure";


fun dest_record tybase tm =
  let fun dest tm =
       if is_arb tm then []
       else let val (f,a) = dest_comb tm
            in dest_field f::dest a
            end
       handle HOL_ERR _ => raise ERR "dest_record" "unexpected term structure"
  in
   if has_record_type tybase tm
     then (type_of tm, dest tm)
     else raise ERR "dest_record" "not a record"
  end;

fun is_record tybase = can (dest_record tybase);

fun mk_record tybase (ty,fields) =
 if is_record_type tybase ty
 then let val (Thy,Tyop) = type_names ty
        val fupds = map (fn p => String.concat[Tyop,"_",fst p,"_fupd"]) fields
        val updfns = map (fn n => prim_mk_const{Name=n,Thy=Thy}) fupds
        fun ifn c = let val (_,ty') = strip_fun (type_of c)
                        val theta = match_type ty' ty
                    in inst theta c
                    end
        val updfns' = map ifn updfns
        fun mk_field (updfn,v) tm =
              mk_comb(mk_comb(updfn, mk_K_1(v,type_of v)),tm)
       in
         itlist mk_field (zip updfns' (map snd fields)) (mk_arb ty)
       end
  else raise ERR "mk_record" "first arg. not a record type";

end
