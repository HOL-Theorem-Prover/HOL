(*---------------------------------------------------------------------------*
 * Building records of facts about datatypes.                                *
 *---------------------------------------------------------------------------*)

structure TypeBasePure :> TypeBasePure =
struct

open HolKernel boolSyntax Drule Conv Prim_rec;
type simpfrag = simpfrag.simpfrag
type rcd_fieldinfo = {ty: hol_type, accessor: term, fupd : term}

val ERR = mk_HOL_ERR "TypeBasePure";
val WARN = HOL_WARNING "TypeBasePure";

fun type_names ty =
  let val {Thy,Tyop,Args} = Type.dest_thy_type ty
  in (Thy,Tyop)
  end;

fun mk_recordtype_constructor s = "recordtype." ^ s
fun mk_recordtype_fieldsel {tyname=ty,fieldname=s} =
    String.concatWith "." ["recordtype",ty,"seldef",s]
fun mk_recordtype_fieldfupd r = mk_recordtype_fieldsel r ^ "_fupd"

datatype shared_thm
    = ORIG of thm
    | COPY of (string * string) * thm;

   type mk_datatype_record =
        {ax        : shared_thm,
         induction : shared_thm,
         case_def  : thm,
         case_cong : thm,
         case_eq   : thm,
         case_elim : thm,
         nchotomy  : thm,
         size      : (term * shared_thm) option,
         encode    : (term * shared_thm) option,
         lift      : term option,
         one_one   : thm option,
         distinct  : thm option,
         fields    : (string * rcd_fieldinfo) list,
         accessors : thm list,
         updates   : thm list,
         destructors : thm list,
         recognizers : thm list}

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
            case_eq      : thm,
            case_elim    : thm,
            case_cong    : thm,
            nchotomy     : thm,
            case_const   : term,
            constructors : term list,
            destructors  : thm list,
            recognizers  : thm list,
            size         : (term * shared_thm) option,
            encode       : (term * shared_thm) option,
            lift         : term option,
            distinct     : thm option,
            one_one      : thm option,
            fields       : (string * rcd_fieldinfo) list,
            accessors    : thm list,
            updates      : thm list,
            simpls       : simpfrag,
            extra        : ThyDataSexp.t list} ;

open FunctionalRecordUpdate
fun gcons_mkUp z = makeUpdate22 z
fun update_DTY z = let
  fun from accessors axiom case_cong case_const case_def case_eq case_elim
           constructors destructors distinct encode extra fields induction lift
           nchotomy one_one recognizers simpls size ty updates =
    {accessors = accessors, axiom = axiom, case_cong = case_cong,
     case_const = case_const, case_def = case_def, case_eq = case_eq,
     case_elim = case_elim, constructors = constructors,
     destructors = destructors, distinct = distinct, encode = encode,
     extra = extra, fields = fields, induction = induction, lift = lift,
     nchotomy = nchotomy, one_one = one_one, recognizers = recognizers,
     simpls = simpls, size = size, ty = ty, updates = updates}
  (* fields in reverse order to above *)
  fun from' updates ty size simpls recognizers one_one nchotomy lift induction
            fields extra encode distinct destructors constructors case_elim
            case_eq case_def case_const case_cong axiom accessors =
    {accessors = accessors, axiom = axiom, case_cong = case_cong,
     case_const = case_const, case_def = case_def, case_eq = case_eq,
     case_elim = case_elim, constructors = constructors, destructors = destructors,
     distinct = distinct, encode = encode, extra = extra, fields = fields,
     induction = induction, lift = lift, nchotomy = nchotomy,
     one_one = one_one, recognizers = recognizers, simpls = simpls,
     size = size, ty = ty, updates = updates}
  (* first order *)
  fun to f {accessors, axiom, case_cong, case_const, case_def, case_eq,
            case_elim, constructors, destructors, distinct, encode, extra, fields,
            induction, lift, nchotomy, one_one, recognizers, simpls, size, ty,
            updates} =
    f accessors axiom case_cong case_const case_def case_eq case_elim
      constructors destructors distinct encode extra fields induction lift
      nchotomy one_one recognizers simpls size ty updates
in
  gcons_mkUp (from, from', to)
end z

type ntyrec = {encode : (term * thm) option,
               extra : ThyDataSexp.t list,
               induction : thm option,
               nchotomy : thm option,
               simpls : simpfrag.simpfrag,
               size : (term * thm) option
              };

fun gcons_mkUp z = makeUpdate6 z
fun update_NTY z = let
  fun from encode extra induction nchotomy simpls size =
    {encode = encode, extra = extra, induction = induction,
     nchotomy = nchotomy, simpls = simpls, size = size}
  (* fields in reverse order to above *)
  fun from' size simpls nchotomy induction extra encode =
    {encode = encode, extra = extra, induction = induction,
     nchotomy = nchotomy, simpls = simpls, size = size}
  (* first order *)
  fun to f {encode, extra, induction, nchotomy, simpls, size} =
    f encode extra induction nchotomy simpls size
in
  gcons_mkUp (from, from', to)
end z


type ntyinfo = hol_type * ntyrec

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

fun destructors_of (DFACTS {destructors,...}) = destructors
  | destructors_of (NFACTS _) = [];

fun recognizers_of (DFACTS {recognizers,...}) = recognizers
  | recognizers_of (NFACTS _) = [];

fun case_const_of (DFACTS {case_const,...}) = case_const
  | case_const_of (NFACTS (ty,_)) =
      raise ERR "case_const_of" (dollarty ty^" is not a datatype");

fun case_cong_of (DFACTS {case_cong,...}) = case_cong
  | case_cong_of (NFACTS (ty,_)) =
       raise ERR "case_cong_of" (dollarty ty^" is not a datatype");

fun case_def_of (DFACTS {case_def,...}) = case_def
  | case_def_of (NFACTS (ty,_)) =
       raise ERR "case_def_of" (dollarty ty^" is not a datatype");

fun case_eq_of (DFACTS {case_eq, ...}) = case_eq
  | case_eq_of (NFACTS (ty,_)) =
       raise ERR "case_eq_of" (dollarty ty^" is not a datatype");

fun case_elim_of (DFACTS {case_elim, ...}) = case_elim
  | case_elim_of (NFACTS (ty,_)) =
       raise ERR "case_elim_of" (dollarty ty^" is not a datatype");

fun extra_of (DFACTS{extra,...}) = extra
  | extra_of (NFACTS(_, {extra,...})) = extra

fun induction_of0 (DFACTS {induction,...}) = induction
  | induction_of0 (NFACTS (ty,{induction,...}))
     = raise ERR "induction_of0" "not a mutrec. datatype";

fun induction_of (DFACTS {induction,...}) = thm_of induction
  | induction_of (NFACTS(_,{induction=SOME th,...})) = th
  | induction_of (NFACTS(ty,{induction=NONE,...})) =
        raise ERR "induction_of" (dollarty ty^" no induction theorem available");

fun nchotomy_of (DFACTS {nchotomy,...}) = nchotomy
  | nchotomy_of (NFACTS(_,{nchotomy=SOME th,...})) = th
  | nchotomy_of (NFACTS(ty,{nchotomy=NONE,...})) =
        raise ERR "nchotomy_of" (dollarty ty^" no cases theorem available");

fun distinct_of (DFACTS {distinct,...}) = distinct
  | distinct_of (NFACTS (ty,_)) = NONE

fun one_one_of (DFACTS {one_one,...}) = one_one
  | one_one_of (NFACTS (ty,_)) = NONE

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
  | size_of0 (NFACTS (ty,{size,...})) = Option.map (I ## ORIG) size

fun size_of (DFACTS {size=NONE,...}) = NONE
  | size_of (DFACTS {size=SOME(tm,def),...}) = SOME(tm,thm_of def)
  | size_of (NFACTS(_,{size,...})) = size;

fun encode_of0(DFACTS {encode,...}) = encode
  | encode_of0(NFACTS (ty,{encode,...})) = Option.map (I ## ORIG) encode

fun encode_of(DFACTS {encode=NONE,...}) = NONE
  | encode_of(DFACTS {encode=SOME(tm,def),...}) = SOME(tm,thm_of def)
  | encode_of(NFACTS(_,{encode,...})) = encode;

fun lift_of(DFACTS {lift,...}) = lift
  | lift_of(NFACTS (ty,_)) =
       raise ERR "lift_of" (dollarty ty^" is not a datatype")
;

fun extras_of (DFACTS{extra,...}) = extra
  | extras_of (NFACTS(_, {extra,...})) = extra

(*---------------------------------------------------------------------------
                    Making alterations
 ---------------------------------------------------------------------------*)

fun put_nchotomy th (DFACTS dty) = DFACTS (update_DTY dty (U #nchotomy th) $$)
  | put_nchotomy th (NFACTS(ty,ntyr)) =
      NFACTS(ty,update_NTY ntyr (U #nchotomy (SOME th)) $$)

fun put_simpls thl (DFACTS dty) = DFACTS (update_DTY dty (U #simpls thl) $$)
  | put_simpls ssf (NFACTS (ty,nty)) =
      NFACTS(ty, update_NTY nty (U #simpls ssf) $$)

fun add_rewrs thl tyi =
  let
    val {convs,rewrs} = simpls_of tyi
  in
    put_simpls {convs = convs, rewrs = rewrs @ thl} tyi
  end

val add_convs = simpfrag.add_convs
fun add_ssfrag_convs cds (DFACTS dty) =
    DFACTS (update_DTY dty(U #simpls (add_convs cds (#simpls dty))) $$)
  | add_ssfrag_convs cds (NFACTS(ty,nty)) =
      NFACTS(ty, update_NTY nty (U #simpls (add_convs cds (#simpls nty))) $$)

fun put_induction th (DFACTS dty) = DFACTS (update_DTY dty (U #induction th) $$)
  | put_induction (ORIG th) (NFACTS(ty,ntyr)) =
      NFACTS(ty,update_NTY ntyr (U #induction (SOME th)) $$)
  | put_induction (COPY th) (NFACTS _) =
      raise ERR "put_induction" "non-datatype but mutrec"

fun put_axiom th (DFACTS dty) = DFACTS (update_DTY dty (U #axiom th) $$)
  | put_axiom _ (NFACTS(ty,ntyr)) =
      raise ERR "put_axiom" "updating non-datatype"

fun put_size szinfo (DFACTS dty) =
      DFACTS (update_DTY dty (U #size (SOME szinfo)) $$)
  | put_size (size_tm,ORIG size_rw) (NFACTS(ty,ntyr)) =
      NFACTS(ty,update_NTY ntyr (U #size (SOME(size_tm,size_rw))) $$)
  | put_size (size_tm,COPY size_rw) (NFACTS _) =
      raise ERR "put_size" "non-datatype but mutrec"

fun put_encode encinfo (DFACTS dty) =
      DFACTS (update_DTY dty (U #encode (SOME encinfo)) $$)
  | put_encode (encode_tm,ORIG encode_rw)
               (NFACTS(ty, ntyr)) =
      NFACTS(ty, update_NTY ntyr (U #encode (SOME(encode_tm,encode_rw))) $$)
  | put_encode (encode_tm,COPY encode_rw) (NFACTS _) =
      raise ERR "put_encode" "non-datatype but mutrec"

fun put_extra e tyi =
  case tyi of
      DFACTS dty => DFACTS (update_DTY dty (U #extra e) $$)
    | NFACTS(ty,ntyr) => NFACTS (ty, update_NTY ntyr (U #extra e) $$)

fun add_extra e tyi =
  case tyi of
      DFACTS dty => DFACTS (update_DTY dty (U #extra (#extra dty @ e)) $$)
    | NFACTS (ty, ntyr) =>
        NFACTS (ty, update_NTY ntyr (U #extra (#extra ntyr @ e)) $$)

fun put_lift lift_tm (DFACTS dty) =
      DFACTS (update_DTY dty (U #lift (SOME lift_tm)) $$)
  | put_lift _ _ = raise ERR "put_lift" "not a datatype";

fun put_fields flds (DFACTS dty) = DFACTS (update_DTY dty (U #fields flds) $$)
  | put_fields _ _ = raise ERR "put_fields" "not a datatype";

fun put_accessors thl (DFACTS dty) =
      DFACTS (update_DTY dty (U #accessors thl) $$)
  | put_accessors _ _ = raise ERR "put_accessors" "not a datatype";

fun put_updates thl (DFACTS dty) =
      DFACTS (update_DTY dty (U #updates thl) $$)
  | put_updates _ _ = raise ERR "put_updates" "not a datatype";

fun put_recognizers thl (DFACTS dty) =
      DFACTS (update_DTY dty (U #recognizers thl) $$)
  | put_recognizers _ _ = raise ERR "put_recognizers" "not a datatype";

fun put_destructors thl (DFACTS dty) =
      DFACTS (update_DTY dty (U #destructors thl) $$)
  | put_destructors _ _ = raise ERR "put_destructors" "not a datatype";

(*---------------------------------------------------------------------------*
 * Returns the datatype name and the constructors. The code is a copy of     *
 * the beginning of "Datatype.define_case".                                  *
 *---------------------------------------------------------------------------*)

fun basic_info case_def =
 let val clauses = (strip_conj o concl) case_def
     val lefts   = map (fst o dest_eq o #2 o strip_forall) clauses
     val constrs = map (#1 o strip_comb o hd o #2 o strip_comb) lefts
     val ty      = type_of (hd (#2 (strip_comb (Lib.trye hd lefts))))
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

fun mk_datatype_info_no_simpls rcd =
  let
    val {ax,case_def,case_eq,case_elim,case_cong,induction,
         nchotomy,size,encode,lift,one_one,
         fields, accessors, updates, distinct,
         destructors,recognizers} = rcd
    val (ty,ty_names,constructors) = basic_info case_def
  in
    DFACTS
      {ty           = ty,
       constructors = constructors,
       destructors  = destructors,
       recognizers  = recognizers,
       case_const   = defn_const case_def,
       case_def     = case_def,
       case_eq      = case_eq,
       case_elim    = case_elim,
       case_cong    = case_cong,
       induction    = induction,
       nchotomy     = nchotomy,
       one_one      = one_one,
       distinct     = distinct,
       fields       = fields,
       accessors    = accessors,
       updates      = updates,
       simpls       = {rewrs = [], convs = []},
       size         = size,
       encode       = encode,
       lift         = lift,
       axiom        = ax,
       extra        = []}
  end

fun gen_std_rewrs tyi =
  let
    val D  = case distinct_of tyi of NONE => [] | SOME x => CONJUNCTS x
    val inj = case one_one_of tyi of NONE => [] | SOME th => [th]
    val c = D @ map GSYM D @ inj
  in
    case_def_of tyi :: c handle HOL_ERR _ => c
  end
fun add_std_simpls tyi = add_rewrs (gen_std_rewrs tyi) tyi

fun mk_datatype_info rcd =
    rcd |> mk_datatype_info_no_simpls |> add_std_simpls

local fun mk_ti (n,ax,ind)
                (cdef::cds) (ccong::cgs) (oo::oos) (d::ds) (nch::nchs) =
            mk_datatype_info{ax=COPY(n,ax), induction=COPY(n,ind),
                      case_def=cdef,case_cong=ccong, nchotomy=nch,
                      case_eq =
                        prove_case_eq_thm {case_def = cdef, nchotomy = nch},
                      case_elim =
                        prove_case_ho_elim_thm {case_def = cdef, nchotomy = nch},
                      one_one=oo, distinct=d,size=NONE, encode=NONE,
                      lift=NONE, fields=[], accessors=[],updates=[],
                      recognizers=[],destructors=[]}
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
     val cased1 = hd case_defs
     val casec1 = hd case_congs
     val nch1 = hd nchotomyl
     val tyinfo_1 = mk_datatype_info_no_simpls
           {ax=ORIG ax, induction=ORIG ind,
            case_def = cased1, case_cong = casec1, nchotomy = nch1,
            case_eq =
              prove_case_eq_thm {case_def = cased1, nchotomy = nch1},
            case_elim =
              prove_case_ho_elim_thm {case_def = cased1, nchotomy = nch1},
            size=NONE, encode=NONE, lift=NONE,
            fields=[], accessors=[],updates=[],
            one_one=hd one_ones, distinct=hd distincts,
            recognizers=[],destructors=[]}
 in
   if length nchotomyl = 1 then [tyinfo_1]
   else let val tyname = ty_name_of tyinfo_1
        in tyinfo_1 :: mk_ti (tyname,ax,ind)
                          (tl case_defs) (tl case_congs)
                          (tl one_ones) (tl distincts) (tl nchotomyl)
        end
 end
end;

fun mk_nondatatype_info (ty,{encode,induction,nchotomy,size}) =
  NFACTS(ty,{encode=encode,induction=induction,size=size,extra=[],
             nchotomy=nchotomy,simpls=simpfrag.empty_simpfrag});

fun name_pair(s1,s2) = s1^"$"^s2;

fun pp_tyinfo tyi =
  let
    open Portable smpp
    val pp_type = lift Parse.pp_type
    val pp_term = lift Parse.pp_term
    val pp_thm = lift Parse.pp_thm
    val pp_sexp =
        lift (ThyDataSexp.pp_sexp Parse.pp_type Parse.pp_term Parse.pp_thm)
  in
    case tyi of
        d as DFACTS recd =>
        let
          val {ty,constructors, case_const, case_def, case_cong, induction,
               nchotomy,one_one,distinct,simpls,size,encode,lift,axiom, case_eq,
               case_elim, fields, accessors, updates,recognizers,destructors,extra}
              = recd
          val ty_namestring = name_pair (ty_name_of d)
        in
          block CONSISTENT 0 (
            block INCONSISTENT 0 (
              add_string "-----------------------" >> add_newline >>
              add_string "-----------------------" >> add_newline >>
              add_string "HOL datatype:" >> add_break(1,0) >>
              add_string (Lib.quote ty_namestring)
            ) >> add_break(1,0) >>

            block CONSISTENT 1 (
              add_string "Primitive recursion:" >> add_break (1,0) >>
              (case axiom of
                   ORIG thm  => pp_thm thm
                 | COPY(sp,_) => add_string ("see "^Lib.quote (name_pair sp)))
            ) >> add_break(1,0) >>

            block CONSISTENT 1 (
              add_string "Case analysis:" >> add_break (1,0) >> pp_thm case_def
            ) >> add_break(1,0) >>

            (case size of
                 NONE => nothing
               | SOME (tm,size_def) =>
                 block CONSISTENT 1 (
                   add_string "Size:" >> add_break (1,0) >>
                   (case size_def of
                        COPY(sp,th) =>
                          add_string ("see "^Lib.quote (name_pair sp))
                      | ORIG th    => if is_const tm then pp_thm th
                                      else pp_term tm)
                 ) >> add_break(1,0)) >>

            (case encode of
                 NONE => nothing
               | SOME (tm,encode_def) =>
                 (block CONSISTENT 1 (
                     add_string "Encoder:" >> add_break (1,0) >>
                     (case encode_def of
                          COPY(sp,th) =>
                            add_string ("see "^Lib.quote (name_pair sp))
                        | ORIG th => if is_const tm then pp_thm th
                                     else pp_term tm)
                   ) >> add_break(1,0))) >>

            block CONSISTENT 1 (
              add_string "Induction:" >> add_break (1,0) >>
              (case induction of
                   ORIG thm  => pp_thm thm
                 | COPY(sp,_) => add_string ("see "^Lib.quote (name_pair sp)))
            ) >> add_break(1,0) >>

            block CONSISTENT 1 (
              add_string "Case completeness:" >> add_break (1,0) >>
              pp_thm nchotomy
            ) >> add_break(1,0) >>

            block CONSISTENT 1 (
              add_string "Case-const equality split:" >> add_break (1,0) >>
              pp_thm case_eq
            ) >> add_break(1,0) >>

            block CONSISTENT 1 (
              add_string "Case-const higher-order split:" >> add_break (1,0) >>
              pp_thm case_elim
            ) >> add_break(1,0) >>

            block CONSISTENT 1 (
              add_string "Extras: [" >> add_break(1,0) >>
              pr_list pp_sexp (add_string "," >> add_break(1,0)) extra >>
              add_string "]"
            ) >>

            let fun do11 thm =
                     block CONSISTENT 1 (add_string "One-to-one:" >>
                                         add_break (1,0) >> pp_thm thm)
                fun do_distinct thm =
                     block CONSISTENT 1 (add_string "Distinctness:" >>
                                         add_break (1,0) >> pp_thm thm)
            in
              case (one_one,distinct)
               of (NONE,NONE) => nothing
                | (NONE,SOME thm) => add_break(1,0) >> do_distinct thm
                | (SOME thm,NONE) => add_break(1,0) >> do11 thm
                | (SOME thm1,SOME thm2) => add_break(1,0) >> do11 thm1 >>
                                           add_break(1,0) >> do_distinct thm2
            end
          )
        end
      | NFACTS(ty,{nchotomy,induction,size,encode,extra,...}) =>
        block CONSISTENT 0 (
          block INCONSISTENT 0 (
             add_string "-----------------------" >> add_newline >>
             add_string "-----------------------" >> add_newline >>
             add_string "HOL type:" >> add_break(1,0) >> pp_type ty
          ) >> add_break(1,0) >>

          block CONSISTENT 1 (
            add_string "Case completeness:" >> add_break (1,0) >>
            (case nchotomy of
                 NONE => add_string "none"
               | SOME thm => pp_thm thm)
          ) >> add_break(1,0) >>

          block CONSISTENT 1 (
            add_string "Induction:" >> add_break (1,0) >>
            (case induction of
                 NONE  => add_string "none"
               | SOME thm => pp_thm thm)
          ) >> add_break(1,0) >>

          block CONSISTENT 1 (
            add_string "Size:" >> add_break (1,0) >>
            (case size of
                 NONE => add_string "none"
               | SOME (tm,size_def) =>
                 block CONSISTENT 1 (
                     if is_const tm then pp_thm size_def else pp_term tm
                 )
            )
          ) >> add_break(1,0) >>

          block CONSISTENT 1 (
            add_string "Extras:" >> add_break(1,0) >>
            pr_list pp_sexp (add_string "," >> add_break(1,0)) extra
          )
        )
  end

val pp_tyinfo = Parse.mlower o pp_tyinfo

(*---------------------------------------------------------------------------*)
(* Database of facts.                                                        *)
(*---------------------------------------------------------------------------*)

type typeBase = tyinfo TypeNet.typenet

val empty : typeBase = TypeNet.empty

val fold = TypeNet.fold

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

fun insert db x = TypeNet.insert(db,normalise_ty (ty_of x), x);

fun get db s = let
  fun foldthis (ty,tyi as DFACTS _,acc) =
      if #2 (type_names ty) = s then tyi::acc else acc
    | foldthis (ty, _, acc) = acc
in
  TypeNet.fold foldthis [] db
end

fun listItems db = map #2 (TypeNet.listItems db)

fun toPmatchThry tbase {Thy,Tyop} =
    case prim_get tbase (Thy,Tyop) of
        NONE => NONE
      | SOME tyi => SOME {case_const = case_const_of tyi,
                          constructors = constructors_of tyi}



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
        case sorted of
            [] => NONE
          | (_, tyi) :: _ => SOME tyi
      end


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

fun tystring ty =
 let val (thy,name) = type_names ty
 in String.concat [thy,"$",name]
 end;

(*---------------------------------------------------------------------------*)
(* gamma models polymorphic functions of the form                            *)
(*                                                                           *)
(*  ty |-> ty_size size1 ... sizen arg = ...                                 *)
(*                                                                           *)
(* where arg is a term with a type having n type variables. In order to      *)
(* synthesize the correct instance of ty_size, we have to match the types    *)
(* of size1...sizen against the concrete types found in the instance of type *)
(* ty. Hence the complex lead-up to matching.                                *)
(*---------------------------------------------------------------------------*)

fun typeValue (theta,gamma,undef) =
 let fun tyValue ty =
      case theta ty
       of SOME fvar => fvar
        | NONE =>
            case gamma ty
             of SOME f =>
                 (let val args = snd(dest_type ty)
                      val csizefns = map tyValue args
                      val (tys,rng) = strip_fun (type_of f)
                      val (gen_sizefn_tys,vty) = front_last tys
                      val tyinst = match_type (list_mk_fun(gen_sizefn_tys,bool))
                                              (list_mk_fun(map type_of csizefns,bool))
                  in list_mk_comb(inst tyinst f, csizefns)
                  end handle HOL_ERR _
                      => (WARN "typeValue"
                           ("Badly typed terms at type constructor "
                            ^Lib.quote (tystring ty)^". Continuing anyway.");
                          undef ty))
               | NONE => undef ty
 in tyValue
 end

(*---------------------------------------------------------------------------*)
(*    Map a HOL type (ty) into a term having type :ty -> num.                *)
(*---------------------------------------------------------------------------*)

fun num() = mk_thy_type{Tyop="num",Thy="num",Args=[]}
fun Zero() = mk_thy_const{Name="0",Thy="num", Ty=num()}
             handle HOL_ERR _ =>
             raise ERR "type_size.Zero()" "Numbers not declared"

fun type_size_pre theta db ty =
 let fun K0 ty = mk_abs(mk_var("v",ty),Zero())
     fun theta2 ty = case theta ty of
         NONE => if is_vartype ty then SOME (K0 ty) else NONE
       | SOME sz => if type_of sz = (ty --> num()) then SOME sz
         else raise (ERR "type_size_pre" "pre-supplied size has wrong type")
     val gamma = Option.map fst o
                 Option.composePartial (size_of,fetch db)
  in
    typeValue (theta,gamma,K0) ty
  end

val type_size = type_size_pre (fn _ => NONE)

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

(* ----------------------------------------------------------------------
    Syntax operations on the (extensible) set of case expressions.

    All implemented in Pmatch
   ---------------------------------------------------------------------- *)

fun dest_case tbase = Pmatch.dest_case (toPmatchThry tbase)
fun is_case tbase = Pmatch.is_case (toPmatchThry tbase)
fun strip_case tbase = Pmatch.strip_case (toPmatchThry tbase)
fun mk_case tbase = Pmatch.mk_case (toPmatchThry tbase)

(*---------------------------------------------------------------------------*)
(* Syntax operations for record types.                                       *)
(*---------------------------------------------------------------------------*)

fun dest_record_type tybase ty =
  case Lib.total (fields_of o valOf o prim_get tybase o type_names) ty
    of SOME (fields as (_::_)) => fields
     | otherwise => raise ERR "dest_record_type" "not a record type";

fun is_record_type tybase ty = Lib.can (dest_record_type tybase) ty;

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
    let
      val err = ERR "get_field_name" ("unable to parse "^Lib.quote s2)
    in
      case String.fields (equal #".") s2 of
          ["recordtype", ty, "seldef", fld] =>
          if ty = s1 andalso String.isSuffix "_fupd" fld then
            String.extract (fld, 0, SOME(String.size fld - 5))
          else raise err
        | _ => raise err
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
 if is_record_type tybase ty then
   let
     val (Thy,Tyop) = type_names ty
     fun mkrtfup f = mk_recordtype_fieldfupd {tyname=Tyop, fieldname = f}
     val fupds = map (mkrtfup o #1) fields
     val updfns = map (fn n => prim_mk_const{Name=n,Thy=Thy}) fupds
     fun ifn c = let val (_,ty') = dom_rng (type_of c)
                     val theta = match_type ty' (ty --> ty)
                 in inst theta c
                 end
     val updfns' = map ifn updfns
     fun mk_field (updfn,v) tm =
         mk_comb(mk_comb(updfn, mk_K_1(v,type_of v)),tm)
   in
     itlist mk_field (zip updfns' (map snd fields)) (mk_arb ty)
   end
 else raise ERR "mk_record" "first arg. not a record type";

exception OptionExn = Option
open ThyDataSexp
fun ty_to_key ty =
  let
    val {Thy,Tyop,...} = dest_thy_type ty
  in
    List [String Thy, String Tyop]
  end

fun field s v = [Sym s, v]
fun option f v =
  case v of
      NONE => Sym "NONE"
    | SOME v0 => List [Sym "SOME", f v0]
fun rcdfinfo_to_sexp {ty,accessor,fupd} =
    List [Type ty, Term accessor, Term fupd]

fun dtyiToSEXPs (dtyi : dtyinfo) =
    field "ty" (Type (#ty dtyi)) @
    field "axiom" (Thm (thm_of (#axiom dtyi))) @
    field "induction" (Thm (thm_of (#induction dtyi))) @
    field "case_def" (Thm (#case_def dtyi)) @
    field "case_eq" (Thm (#case_eq dtyi)) @
    field "case_elim" (Thm (#case_elim dtyi)) @
    field "case_cong" (Thm (#case_cong dtyi)) @
    field "case_const" (Term (#case_const dtyi)) @
    field "constructors" (List (map Term (#constructors dtyi))) @
    field "destructors" (List (map Thm (#destructors dtyi))) @
    field "recognizers" (List (map Thm (#recognizers dtyi))) @
    field "size" (option (fn (t,th) => List [Term t, Thm (thm_of th)])
                         (#size dtyi)) @
    field "encode" (option (fn (t,th) => List [Term t, Thm (thm_of th)])
                           (#encode dtyi)) @
    field "lift" (option Term (#lift dtyi)) @
    field "distinct" (option Thm (#distinct dtyi)) @
    field "nchotomy" (Thm (#nchotomy dtyi)) @
    field "one_one" (option Thm (#one_one dtyi)) @
    field "fields"
          (List (map (fn (s,rfi) => List[String s, rcdfinfo_to_sexp rfi])
                     (#fields dtyi))) @
    field "accessors" (List (map Thm (#accessors dtyi))) @
    field "updates" (List (map Thm (#updates dtyi))) @
    field "simpls" (List (map Thm (#rewrs (#simpls dtyi)))) @
    field "extra" (List (#extra dtyi))

fun toSEXP0 tyi =
  case tyi of
      DFACTS dtyi => List (Sym "DFACTS" :: dtyiToSEXPs dtyi)
    | NFACTS (ty,{nchotomy, induction, size, encode, extra, simpls}) =>
        List (
          Sym "NFACTS" ::
          field "ty" (Type ty) @
          field "nchotomy" (option Thm nchotomy) @
          field "induction" (option Thm induction) @
          field "extra" (List extra) @
          field "size" (option (fn (t,th) => List [Term t, Thm th]) size) @
          field "encode" (option (fn (t,th) => List [Term t, Thm th]) encode) @
          field "simpls" (List (map Thm (#rewrs simpls)))
        )

fun toSEXP tyi =
  List [ty_to_key (ty_of tyi), toSEXP0 tyi]

fun fromSEXP0 s =
  let
    fun string (String s) = s | string _ = raise OptionExn
    fun ty (Type t) = t | ty _ = raise OptionExn
    fun tm (Term t) = t | tm _ = raise OptionExn
    fun thm (Thm th) = th | thm _ = raise OptionExn
    fun sthm (Thm th) = ORIG th | sthm _ = raise OptionExn
    fun dest_option df (Sym "NONE") = NONE
      | dest_option df (List [Sym "SOME", v]) = SOME (df v)
      | dest_option _ _ = raise OptionExn
    fun dest_pair df1 df2 (List [s1, s2]) = (df1 s1, df2 s2)
      | dest_pair _ _ _ = raise OptionExn
    fun dest_rfi (List [typ, acc, fupd]) = {ty = ty typ, accessor = tm acc,
                                            fupd = tm fupd}
      | dest_rfi _ = raise OptionExn

    fun H nm f x = f x
       handle OptionExn => raise ERR "fromSEXP" ("Bad encoding for field "^nm)
  in
    case s of
        List [Sym "DFACTS",
              Sym "ty", Type typ,
              Sym "axiom", Thm axiom,
              Sym "induction", Thm induction,
              Sym "case_def", Thm case_def,
              Sym "case_eq", Thm case_eq,
              Sym "case_elim", Thm case_elim,
              Sym "case_cong", Thm case_cong,
              Sym "case_const", Term case_const,
              Sym "constructors", List clist,
              Sym "destructors", List dlist,
              Sym "recognizers", List rlist,
              Sym "size", size_option,
              Sym "encode", encode_option,
              Sym "lift", lift_option,
              Sym "distinct", distinct_option,
              Sym "nchotomy", Thm nchotomy,
              Sym "one_one", one_one_option,
              Sym "fields", List field_list,
              Sym "accessors", List accessor_list,
              Sym "updates", List update_list,
              Sym "simpls", List fragrewr_list,
              Sym "extra", List extra] =>
        (SOME (
            DFACTS {ty = typ, axiom = ORIG axiom, induction = ORIG induction,
                    case_def = case_def, case_eq = case_eq,
                    case_elim = case_elim, case_cong = case_cong,
                    case_const = case_const,
                    constructors = H "constructors" (map tm) clist,
                    destructors = H "destructors" (map thm) dlist,
                    recognizers = H "recognizers" (map thm) rlist,
                    size =
                      H "size" (dest_option (dest_pair tm sthm)) size_option,
                    encode = H "encode"
                               (dest_option (dest_pair tm sthm)) encode_option,
                    lift = H "lift" (dest_option tm) lift_option,
                    distinct = H "distinct" (dest_option thm) distinct_option,
                    nchotomy = nchotomy,
                    one_one = H "one_one" (dest_option thm) one_one_option,
                    fields = H "fields"
                               (map (dest_pair string dest_rfi)) field_list,
                    accessors = H "accessors" (map thm) accessor_list,
                    updates = H "updates" (map thm) update_list,
                    simpls = simpfrag.add_rwts simpfrag.empty_simpfrag
                                 (H "simpls" (map thm) fragrewr_list),
                    extra = extra}
          ) handle OptionExn => NONE)
      | List [Sym "NFACTS", Sym "ty", Type typ,
              Sym "nchotomy", nch_option,
              Sym "induction", ind_option,
              Sym "extra", List extra,
              Sym "size", size_option,
              Sym "encode", encode_option,
              Sym "simpls", List rewrs] =>
        (SOME (
            NFACTS (typ, {
                     nchotomy = H "nchotomy" (dest_option thm) nch_option,
                     induction = H "induction" (dest_option thm) ind_option,
                     extra = extra,
                     size = H "size" (dest_option (dest_pair tm thm))
                              size_option,
                     encode = H "encode" (dest_option (dest_pair tm thm))
                                encode_option,
                     simpls = simpfrag.add_rwts simpfrag.empty_simpfrag
                                                (H "simpls" (map thm) rewrs)}))
         handle OptionExn => NONE)
      | _ => NONE
  end

fun fromSEXP s =
  case s of
      List[_, s0] => fromSEXP0 s0
    | _ => NONE

end (* struct *)
