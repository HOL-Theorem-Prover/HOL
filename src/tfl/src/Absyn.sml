structure Absyn :> Absyn =
struct

open HolKernel;
infix ##;

type term = Term.term
type pretype = TCPretype.pretype
type 'a quotation = 'a Portable.quotation

fun ERR f s = 
    HOL_ERR{origin_structure="Absyn", 
            origin_function=f, message=s};

   datatype vstruct 
       = VAQ    of term
       | VIDENT of string 
       | VPAIR  of vstruct * vstruct
       | VTYPED of vstruct * pretype 

   datatype absyn 
       = AQ    of term 
       | IDENT of string
       | APP   of absyn * absyn
       | LAM   of vstruct * absyn
       | TYPED of absyn * pretype


fun to_vstruct (parse_term.SIMPLE s)     = VIDENT s
  | to_vstruct (parse_term.VPAIR(v1,v2)) = VPAIR(to_vstruct v1,to_vstruct v2)
  | to_vstruct (parse_term.TYPEDV(v,ty)) = VTYPED(to_vstruct v, ty)
  | to_vstruct (parse_term.VS_AQ x)      = VAQ x
  | to_vstruct (parse_term.RESTYPEDV _)  = raise ERR "to_vstruct" 
                                              "RESTYPEDV should be gone";

fun to_absyn (parse_term.COMB(M,N))    = APP(to_absyn M,to_absyn N)
  | to_absyn (parse_term.VAR s)        = IDENT s
  | to_absyn (parse_term.ABS (v,M))    = LAM (to_vstruct v, to_absyn M)
  | to_absyn (parse_term.AQ x)         = AQ x
  | to_absyn (parse_term.TYPED(M,pty)) = TYPED(to_absyn M, pty);


val quote_to_absyn = to_absyn o Parse.parse_preTerm o wfrecUtils.norm_quote;

fun from_vstr (VIDENT s)      = parse_term.SIMPLE s
  | from_vstr (VPAIR (v1,v2)) = parse_term.VPAIR(from_vstr v1,from_vstr v2)
  | from_vstr (VTYPED (v,ty)) = parse_term.TYPEDV(from_vstr v,ty)
  | from_vstr (VAQ x)         = parse_term.VS_AQ x;

fun from_absyn (APP(M,N))  = parse_term.COMB(from_absyn M,from_absyn N)
  | from_absyn (IDENT s)   = parse_term.VAR s
  | from_absyn (LAM(v,M))  = parse_term.ABS(from_vstr v, from_absyn M)
  | from_absyn (AQ x)      = parse_term.AQ x
  | from_absyn (TYPED(M, pty)) = parse_term.TYPED(from_absyn M, pty);

fun absyn_to_term asy = Parse.toTerm (Parse.term_grammar()) (from_absyn asy);


(*---------------------------------------------------------------------------
        Useful absyn operations.
 ---------------------------------------------------------------------------*)

fun mk_AQ x        = AQ x
fun mk_ident s     = IDENT s
fun mk_app (M,N)   = APP(M,N)
fun mk_lam (v,M)   = LAM(v,M)
fun mk_typed(M,ty) = TYPED(M,ty);

fun genAQ (AQ1,AQ2) f x err = (AQ1##AQ2) (f x) handle HOL_ERR _ => raise err;
fun binAQ f x e  = genAQ(AQ,AQ) f x e;

fun dest_ident (IDENT s) = s
  | dest_ident (AQ x) = 
      (wfrecUtils.atom_name x 
       handle HOL_ERR _ => raise ERR "dest_ident" 
                                      "Expected a variable or constatnt")
  | dest_ident _ =  raise ERR "dest_ident" "Expected an identifier";

fun dest_app (APP(M,N)) = (M,N)
  | dest_app (AQ x)     = binAQ Psyntax.dest_comb x (ERR "dest_app" "AQ")
  | dest_app  _         = raise ERR "dest_app" "Expected an application";

fun dest_AQ (AQ x) = x
  | dest_AQ _ = raise ERR "dest_AQ" "";

fun dest_typed (TYPED p) = p
  | dest_typed  _ = raise ERR "dest_typed" "";

fun tuple_to_vstruct tm =
  if Term.is_var tm 
  then VIDENT(#Name(Term.dest_var tm))
  else let val (M,N) = Psyntax.dest_comb tm
           val (M1,M2) = Psyntax.dest_comb M
           val {Name,...} = Term.dest_const M1
       in if Name = "," 
            then VPAIR(tuple_to_vstruct M2, tuple_to_vstruct N)
            else raise ERR "tuple_to_vstruct" ""
       end;

fun dest_lam (LAM p) = p
  | dest_lam (AQ x) = 
      if is_abs x 
      then let val {Bvar,Body} = Term.dest_abs x
               val {Name=id,...} = Term.dest_var Bvar
           in (VIDENT id, AQ Body)
           end
      else let val (vstr,body) = Psyntax.dest_pabs x
           in (tuple_to_vstruct vstr, AQ body)
           end
  | dest_lam _ = raise ERR "dest_lam" "";


fun list_mk_app (M,[]) = M
  | list_mk_app (M,h::t) = list_mk_app (mk_app(M,h),t);

fun mk_binop s (M,N) = mk_app(mk_app(mk_ident s,M),N);
fun list_mk_binop s = end_itlist (curry (mk_binop s));

local fun dest_binop_term s tm =
        let val (M,N) = Psyntax.dest_comb tm
            val (M1,M2) = Psyntax.dest_comb M
            val {Name,...} = Term.dest_const M1
        in if Name=s then (M2,N) 
           else raise ERR "dest_binop.dest" "unexpected term"
        end
in
fun dest_binop str =
 let val err = ERR "dest_binop" ("Expected a "^Lib.quote str)
     fun dest (APP(APP(IDENT s,M),N)) = if s=str then (M,N) else raise err
       | dest (AQ x) = binAQ (dest_binop_term str) x err
       | dest  _ = raise err
 in dest end
end;

fun gen_strip dest =
    let fun brk ht = 
         let val (h,t) = dest ht
         in h::brk t
         end handle HOL_ERR _ => [ht]
    in brk end;

val mk_eq   = mk_binop  "="
val mk_conj = mk_binop  "/\\"
val mk_disj = mk_binop  "\\/"
val mk_imp  = mk_binop  "==>";
val mk_pair = mk_binop  ","
val list_mk_conj = list_mk_binop "/\\"
val list_mk_disj = list_mk_binop "\\/"
val list_mk_imp  = list_mk_binop "==>";
val list_mk_pair = list_mk_binop ",";

val dest_eq   = dest_binop  "="
val dest_conj = dest_binop  "/\\"
val dest_disj = dest_binop  "\\/"
val dest_imp  = dest_binop  "==>"
val dest_pair = dest_binop  ",";

fun strip_app t =
 let fun strip tm accum = 
          let val (M,N) = dest_app tm
          in strip M (N::accum)
          end handle HOL_ERR _ => (tm,accum)
 in strip t []
 end;

val strip_conj = gen_strip dest_conj
val strip_disj = gen_strip dest_disj
val strip_imp  = gen_strip dest_imp;
val strip_pair = gen_strip dest_pair;

fun mk_binder s (v,M) = mk_app(mk_ident s,mk_lam(v,M));
val mk_forall  = mk_binder "!"
val mk_exists  = mk_binder "?"
val mk_exists1 = mk_binder "?!"
val mk_select  = mk_binder "@";
fun list_mk_binder mk_binder (L,M) = itlist (curry mk_binder) L M;
val list_mk_lam     = list_mk_binder mk_lam
val list_mk_forall  = list_mk_binder mk_forall
val list_mk_exists  = list_mk_binder mk_exists
val list_mk_exists1 = list_mk_binder mk_exists1
val list_mk_select  = list_mk_binder mk_select;

local fun err0 str = ERR "dest_binder" ("Expected a "^Lib.quote str)
      fun dest_term_binder s tm ex =
       let val (c,lam) = Psyntax.dest_comb tm
           val {Name,...} = Term.dest_const c
       in if Name <> s then raise ex else dest_lam (AQ lam)
       end handle HOL_ERR _ => raise ex
in
fun dest_binder str =
 let val err = err0 str
     fun dest (APP(IDENT s, M)) = if s=str then dest_lam M else raise err
       | dest (AQ x) = dest_term_binder str x err
       | dest  _ = raise err
 in dest end
end;

val dest_forall  = dest_binder "!"
val dest_exists  = dest_binder "?"
val dest_exists1 = dest_binder "?!"
val dest_select  = dest_binder "@";

fun strip_front dest =
    let fun brk ht = 
         let val (h,t) = dest ht
             val (L,b) = brk t
         in (h::L,b)
         end handle HOL_ERR _ => ([],ht)
    in brk end;

val strip_lam     = strip_front dest_lam
val strip_forall  = strip_front dest_forall
val strip_exists  = strip_front dest_exists
val strip_exists1 = strip_front dest_exists1
val strip_select  = strip_front dest_select;

val is_ident   = Lib.can dest_forall
val is_app     = Lib.can dest_app
val is_lam     = Lib.can dest_lam
val is_AQ      = Lib.can dest_AQ
val is_typed   = Lib.can dest_typed
val is_eq      = Lib.can dest_eq
val is_conj    = Lib.can dest_conj
val is_disj    = Lib.can dest_disj
val is_imp     = Lib.can dest_imp
val is_pair    = Lib.can dest_pair
val is_forall  = Lib.can dest_forall
val is_exists  = Lib.can dest_exists
val is_exists1 = Lib.can dest_exists1
val is_select  = Lib.can dest_select;

end;
