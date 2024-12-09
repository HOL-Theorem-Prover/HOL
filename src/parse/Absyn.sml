structure Absyn :> Absyn =
struct

open Feedback HolKernel;

type term         = Term.term
type pretype      = Pretype.pretype
type 'a quotation = 'a Portable.quotation

val ERR = mk_HOL_ERR "Absyn";
val ERRloc = mk_HOL_ERRloc "Absyn";

open Absyn_dtype

(*---------------------------------------------------------------------------
        Useful absyn operations.
 ---------------------------------------------------------------------------*)

fun traverse applyp f t = let
  val traverse = traverse applyp f
in
  if applyp t then f traverse t
  else case t of
    APP(locn,t1,t2)   => APP(locn,traverse t1, traverse t2)
  | LAM(locn,vs,t)    => LAM(locn,vs, traverse t)
  | TYPED(locn,t,pty) => TYPED(locn,traverse t, pty)
  | allelse           => allelse
end

fun ultimately s (IDENT (_, s'))      = (s = s')
  | ultimately s (TYPED (_, t', _))   = ultimately s t'
  | ultimately s _ = false

fun locn_of_absyn x =
  case x of
      AQ    (locn,_)   => locn
    | IDENT (locn,_)   => locn
    | QIDENT(locn,_,_) => locn
    | APP   (locn,_,_) => locn
    | LAM   (locn,_,_) => locn
    | TYPED (locn,_,_) => locn

fun locn_of_vstruct x =
  case x of
      VAQ    (locn,_)   => locn
    | VIDENT (locn,_)   => locn
    | VPAIR  (locn,_,_) => locn
    | VTYPED (locn,_,_) => locn

fun to_vstruct t =
  case t of
      APP(l, APP(_, comma, t1), t2) =>
        if ultimately "," comma then VPAIR(l, to_vstruct t1, to_vstruct t2)
        else raise ERRloc "to_vstruct" (locn_of_absyn t)
                   "Bad variable structure"
    | AQ p => VAQ p
    | IDENT p  => VIDENT p
    | TYPED(l, t, pty) => VTYPED(l, to_vstruct t, pty)
    | _ => raise ERRloc "to_vstructp" (locn_of_absyn t) "Bad variable-structure"

fun atom_name tm = fst(dest_var tm handle HOL_ERR _ => dest_const tm);

val dest_pair = sdest_binop (",", "pair") (ERR "dest_pair" "");
val is_pair = Lib.can dest_pair;

fun mk_pair (fst,snd) =
 let val fsty = type_of fst
     val sndty = type_of snd
     val c = mk_thy_const{Name=",",Thy="pair",
              Ty=fsty --> sndty
                   --> mk_thy_type{Tyop="prod",Thy="pair",Args=[fsty,sndty]}}
 in list_mk_comb(c,[fst,snd])
 end;

local val ucheck = Lib.assert (Lib.curry (op =) "UNCURRY" o fst o dest_const)
fun dpa tm =
  dest_abs tm
  handle HOL_ERR _
  => let val (Rator,Rand) = dest_comb tm
         val _ = ucheck Rator
         val (lv, body) = dpa Rand
         val (rv, body) = dpa body
     in
       (mk_pair(lv, rv), body)
     end
in
fun dest_pabs tm =
   let val (pr as (varstruct,_)) = dpa tm
   in if is_pair varstruct then pr
      else raise ERR "dest_pabs" "not a paired abstraction"
   end
end;

val nolocn = locn.Loc_None  (* i.e., compiler-generated text *)
fun mk_AQ x        = AQ   (nolocn,x)
fun mk_ident s     = IDENT(nolocn,s)
fun mk_app (M,N)   = APP  (locn.between (locn_of_absyn M) (locn_of_absyn N),M,N)
fun mk_lam (v,M)   = LAM  (locn.between (locn_of_vstruct v) (locn_of_absyn M),v,M)
fun mk_typed(M,ty) = TYPED(locn.near (locn_of_absyn M),M,ty);

fun binAQ f x locn err = let val (t1,t2) = f x
                         in
                             (AQ(locn,t1),AQ(locn,t2))
                         end
                             handle HOL_ERR _ => raise err;

fun dest_ident (IDENT (_,s)) = s
  | dest_ident (AQ (_,x)) =
      (atom_name x
       handle HOL_ERR _ => raise ERR "dest_ident"
                                      "Expected a variable or constatnt")
  | dest_ident t =  raise ERRloc "dest_ident" (locn_of_absyn t) "Expected an identifier";

fun dest_app (APP(_,M,N))  = (M,N)
  | dest_app (AQ (locn,x)) = binAQ dest_comb x locn (ERRloc "dest_app" locn "AQ")
  | dest_app  t         = raise ERRloc "dest_app" (locn_of_absyn t) "Expected an application";

fun dest_AQ (AQ (_,x)) = x
  | dest_AQ t = raise ERRloc "dest_AQ" (locn_of_absyn t) "Expected an antiquotation";

fun dest_typed (TYPED (_,M,ty)) = (M,ty)
  | dest_typed  t = raise ERRloc "dest_typed" (locn_of_absyn t) "Expected a typed thing";

fun tuple_to_vstruct locn tm =
  if Term.is_var tm
  then VIDENT(locn,fst(Term.dest_var tm))
  else let val (M,N) = dest_comb tm
           val (M1,M2) = dest_comb M
       in if fst(Term.dest_const M1) = ","
            then VPAIR(locn,tuple_to_vstruct locn M2,tuple_to_vstruct locn N)
            else raise ERR "tuple_to_vstruct" ""
       end;

fun dest_lam (LAM (_,v,M)) = (v,M)
  | dest_lam (AQ (locn,x)) =
      if is_abs x
      then let val (Bvar,Body) = Term.dest_abs x
               val (id,_) = Term.dest_var Bvar
           in (VIDENT (locn,id), AQ (locn,Body))
           end
      else let val (vstr,body) = dest_pabs x
           in (tuple_to_vstruct locn vstr, AQ (locn,body))
           end
  | dest_lam t = raise ERRloc "dest_lam" (locn_of_absyn t) "Expected an abstraction"


fun list_mk_app (M,[]) = M
  | list_mk_app (M,h::t) = list_mk_app (mk_app(M,h),t);

fun mk_binop s (M,N) = mk_app(mk_app(mk_ident s,M),N);
fun list_mk_binop s = end_itlist (curry (mk_binop s));

local fun dest_binop_term s tm =
        let val (M,N) = dest_comb tm
            val (M1,M2) = dest_comb M
        in if fst(Term.dest_const M1) = s then (M2,N)
           else raise ERR "dest_binop.dest" "unexpected term"
        end
in
fun dest_binop str =
 let fun err locn = ERRloc "dest_binop" locn ("Expected a "^Lib.quote str)
     fun dest (APP(_,APP(_,IDENT (locn,s),M),N)) = if s=str then (M,N) else raise err locn
       | dest (AQ (locn,x)) = binAQ (dest_binop_term str) x locn (err locn)
       | dest  t = raise err (locn_of_absyn t)
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

local fun err0 str locn = ERRloc "dest_binder" locn ("Expected a "^Lib.quote str)
      fun dest_term_binder s locn tm ex =
       let val (c,lam) = dest_comb tm
       in if fst(Term.dest_const c) <> s
            then raise ex
            else dest_lam (AQ (locn, lam))
       end handle HOL_ERR _ => raise ex
in
fun dest_binder str =
 let fun err locn = err0 str locn
     fun dest (APP(_,IDENT (locn,s),M)) = if s=str then dest_lam M else raise err locn
       | dest (AQ (locn,x)) = dest_term_binder str locn x (err locn)
       | dest  t = raise err (locn_of_absyn t)
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
