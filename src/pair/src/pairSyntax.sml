(*---------------------------------------------------------------------------*
 * Syntax support for the theory of pairs. When possible, functions          *
 * below deal with both paired and unpaired input.                           *
 *---------------------------------------------------------------------------*)

structure pairSyntax :> pairSyntax =
struct

open HolKernel boolTheory pairTheory boolSyntax Abbrev;

infix |->;

val ERR = mk_HOL_ERR "pairSyntax";

(*---------------------------------------------------------------------------
             Operations on product types
 ---------------------------------------------------------------------------*)

fun mk_prod (ty1,ty2) = Type.mk_thy_type{Tyop="prod",Thy="pair",Args=[ty1,ty2]}

fun dest_prod ty = 
  case total dest_thy_type ty
   of SOME{Tyop="prod", Thy="pair", Args=[ty1,ty2]} => (ty1,ty2)
    | other => raise ERR "dest_prod" "not a product type";

val strip_prod = strip_binop (total dest_prod);
val list_mk_prod = end_itlist (curry mk_prod);


(*---------------------------------------------------------------------------
         Useful constants in the theory of pairs
 ---------------------------------------------------------------------------*)

val uncurry_tm  = pairTheory.uncurry_tm;
val comma_tm    = pairTheory.comma_tm;
val fst_tm      = prim_mk_const {Name="FST",     Thy="pair"};
val snd_tm      = prim_mk_const {Name="SND",     Thy="pair"};
val curry_tm    = prim_mk_const {Name="CURRY",   Thy="pair"};
val pair_map_tm = prim_mk_const {Name="##",      Thy="pair"};


(*---------------------------------------------------------------------------
     Make a pair from two components, or a tuple from a list of components
 ---------------------------------------------------------------------------*)

fun mk_pair(fst,snd) =
 let val ty1 = type_of fst
     and ty2 = type_of snd
 in list_mk_comb(inst [alpha |-> ty1, beta |-> ty2] comma_tm, [fst,snd])
 end 

val list_mk_pair = end_itlist (curry mk_pair);

(*---------------------------------------------------------------------------
      Take a pair apart, once, and repeatedly. The atoms appear
      in left-to-right order.
 ---------------------------------------------------------------------------*)

val dest_pair = pairTheory.dest_pair
val strip_pair = pairTheory.strip_pair

fun spine_pair M = 
  case total dest_pair M
   of NONE => [M]
    | SOME (fst,snd) => fst :: spine_pair snd;

(*---------------------------------------------------------------------------
    Inverse of strip_pair ... returns unconsumed elements in input list.
    This is so that it can be used easily over lists of things to be
    unstripped.
 ---------------------------------------------------------------------------*)

local fun break [] = raise ERR "unstrip_pair" "unable"
        | break (h::t) = (h,t)
in
fun unstrip_pair ty V =
   if is_vartype ty then break V
   else case total dest_prod ty
         of SOME(ty1,ty2) =>
             let val (ltm,vs1) = unstrip_pair ty1 V
                 val (rtm,vs2) = unstrip_pair ty2 vs1
             in (mk_pair(ltm,rtm), vs2)
             end
          | NONE => break V
end;

(*---------------------------------------------------------------------------
       Is it a pair?
 ---------------------------------------------------------------------------*)

val is_pair = can dest_pair;


(*---------------------------------------------------------------------------
      Making applications of FST and SND
 ---------------------------------------------------------------------------*)

fun mk_fst tm =
  let val (ty1,ty2) = dest_prod (type_of tm)
  in mk_comb(inst[alpha |-> ty1, beta |-> ty2] fst_tm, tm)
  end
  handle HOL_ERR _ => raise ERR "mk_fst" "";

fun mk_snd tm =
  let val (ty1,ty2) = dest_prod (type_of tm)
  in mk_comb(inst[alpha |-> ty1, beta |-> ty2] snd_tm, tm)
  end
  handle HOL_ERR _ => raise ERR "mk_snd" "";

fun mk_uncurry_tm(xt,yt,zt) = 
  inst [alpha |-> xt, beta |-> yt, gamma |-> zt] uncurry_tm;

fun is_uncurry_tm c = 
 case total dest_thy_const c
  of SOME{Name="UNCURRY",Thy="pair",...} => true
   | otherwise => false;

fun mk_curry (f,x,y) = 
  let val (pty,rty) = dom_rng (type_of f)
      val (aty,bty) = dest_prod pty
  in list_mk_comb
       (inst [alpha |-> aty, beta |-> bty, gamma |-> rty] curry_tm, [f,x,y])
  end
  handle HOL_ERR _ => raise ERR "mk_uncurry" "";

fun mk_uncurry (f,x) = 
  case strip_fun (type_of f)
   of ([a,b],c) => mk_comb(mk_comb(mk_uncurry_tm(a,b,c),f),x)
    | other => raise ERR "mk_uncurry" "";

fun mk_pair_map(f,g,p) =
 let val (df,rf) = dom_rng (type_of f)
     val (dg,rg) = dom_rng (type_of g)
 in list_mk_comb(inst[alpha |-> df, beta  |-> dg, 
                      gamma |-> rf, delta |-> rg] pair_map_tm, [f,g,p])
 end;


val dest_fst     = dest_monop fst_tm     (ERR "dest_fst" "")
val dest_snd     = dest_monop snd_tm     (ERR "dest_snd" "")
val dest_uncurry = dest_binop uncurry_tm (ERR "dest_uncurry" "");
fun dest_curry tm = 
  let val (M,y) = with_exn dest_comb tm (ERR "dest_curry" "")
      val (f,x) = dest_binop curry_tm (ERR "dest_curry" "") M
  in (f,x,y)
  end;

fun dest_pair_map tm = 
  let val (M,p) = with_exn dest_comb tm (ERR "dest_pair_map" "")
      val (f,g) = dest_binop pair_map_tm (ERR "dest_pair_map" "") M
  in (f,g,p)
  end;

val is_fst = can dest_fst
val is_snd = can dest_snd
val is_curry = can dest_curry
val is_uncurry = can dest_uncurry
val is_pair_map = can dest_pair_map;


(*---------------------------------------------------------------------------*)
(* Constructor, destructor and discriminator functions for paired            *)
(* abstractions and ordinary abstractions.                                   *)
(* [JRH 91.07.17]                                                            *)
(*---------------------------------------------------------------------------*)

val mk_pabs = pairTheory.mk_pabs;

fun mk_plet (p as (vstruct,rhs,body)) = 
  mk_let (mk_pabs (vstruct,body),rhs) 
  handle HOL_ERR _ => raise ERR "mk_plet" "";

fun mk_pforall (p as (vstruct,_)) =
 mk_comb(inst [alpha |-> type_of vstruct] universal, mk_pabs p)
 handle HOL_ERR _ => raise ERR "mk_pforall" "";

fun mk_pexists (p as (vstruct,_)) =
 mk_comb(inst [alpha |-> type_of vstruct] existential,mk_pabs p)
 handle HOL_ERR _ => raise ERR "mk_pexists" "";

fun mk_pexists1 (p as (vstruct,_)) =
 mk_comb(inst [alpha |-> type_of vstruct] exists1, mk_pabs p)
 handle HOL_ERR _ => raise ERR "mk_pexists1" "";

fun mk_pselect (p as (vstruct,body)) =
 mk_comb(inst [alpha |-> type_of vstruct] select,mk_pabs p)
 handle HOL_ERR _ => raise ERR "mk_pselect" "";

fun dest_pabs tm =
 Term.dest_abs tm
 handle HOL_ERR _
  => let val (Rator,Rand) = with_exn dest_comb tm (ERR "dest_pabs" "")
     in if is_uncurry_tm Rator
        then let val (lv, body) = dest_pabs Rand
                 val (rv, body) = dest_pabs body
             in (mk_pair(lv, rv), body)
             end
        else raise ERR "dest_pabs" ""
     end;

fun pbvar tm = fst (dest_pabs tm) handle HOL_ERR _ => failwith "pbvar"
and pbody tm = snd (dest_pabs tm) handle HOL_ERR _ => failwith "pbody" ;


local val LET_ERR     = ERR "dest_plet"     "not a (possibly paired) \"let\""
      val FORALL_ERR  = ERR "dest_pforall"  "not a (possibly paired) \"!\""
      val EXISTS_ERR  = ERR "dest_pexists"  "not a (possibly paired) \"?\""
      val EXISTS1_ERR = ERR "dest_pexists1" "not a (possibly paired) \"?!\""
      val SELECT_ERR  = ERR "dest_pselect"  "not a (possibly paired) \"@\""
in 
fun dest_pbinder c e M =
  let val (Rator,Rand) = with_exn dest_comb M e
  in if same_const c Rator 
     then with_exn dest_pabs Rand e
     else raise e
  end

val dest_plet     = dest_pbinder let_tm      LET_ERR
val dest_pforall  = dest_pbinder universal   FORALL_ERR
val dest_pexists  = dest_pbinder existential EXISTS_ERR
val dest_pexists1 = dest_pbinder exists1     EXISTS1_ERR
val dest_pselect  = dest_pbinder select      SELECT_ERR
end;

val is_pabs     = can dest_pabs
val is_plet     = can dest_plet
val is_pforall  = can dest_pforall
val is_pexists  = can dest_pexists
val is_pexists1 = can dest_pexists1
val is_pselect  = can dest_pselect;

fun list_mk_pabs(V,M)    = itlist (curry mk_pabs) V M
fun list_mk_pforall(V,M) = itlist (curry mk_pforall) V M
fun list_mk_pexists(V,M) = itlist (curry mk_pexists) V M;

fun strip dest =
 let fun decomp M =
       case dest M
       of NONE => ([],M)
        | SOME(vstruct,body) => 
           let val (V,kern) = strip dest body 
           in (vstruct::V,kern) 
           end
 in decomp
 end;

val strip_pabs    = strip (total dest_pabs)
val strip_pforall = strip (total dest_pforall)
val strip_pexists = strip (total dest_pexists);


(*---------------------------------------------------------------------------
     A "vstruct" is a tuple of variables, with no duplicate occurrences.
 ---------------------------------------------------------------------------*)

val is_vstruct = pairTheory.is_vstruct;

(* ===================================================================== *)
(* Generates a pair structure of variable with the same structure as     *)
(* its parameter.                                                        *)
(* ===================================================================== *)

fun genvarstruct ty =
  case total dest_prod ty
   of SOME(ty1,ty2) => mk_pair(genvarstruct ty1, genvarstruct ty2)
    | NONE => genvar ty;


end;
