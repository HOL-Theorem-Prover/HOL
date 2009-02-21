(*---------------------------------------------------------------------------*
 * Syntax support for the theory of pairs. When possible, functions          *
 * below deal with both paired and unpaired input.                           *
 *---------------------------------------------------------------------------*)

structure pairSyntax :> pairSyntax =
struct

open HolKernel boolTheory pairTheory boolSyntax Abbrev;

val ERR = mk_HOL_ERR "pairSyntax";

(*---------------------------------------------------------------------------
             Operations on product types
 ---------------------------------------------------------------------------*)

fun mk_prod (ty1,ty2) = Type.mk_thy_type{Tyop="prod",Thy="pair",Args=[ty1,ty2]}

fun dest_prod ty = 
  case total dest_thy_type ty
   of SOME{Tyop="prod", Thy="pair", Args=[ty1,ty2]} => (ty1,ty2)
    | other => raise ERR "dest_prod" "not a product type";

val spine_prod = spine_binop (total dest_prod);
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
val lex_tm      = prim_mk_const {Name="LEX",     Thy="pair"};


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
val spine_pair = pairTheory.spine_pair

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

fun mk_curry (f,x,y) = 
  let val (pty,rty) = dom_rng (type_of f)
      val (aty,bty) = dest_prod pty
  in list_mk_comb
       (inst [alpha |-> aty, beta |-> bty, gamma |-> rty] curry_tm, [f,x,y])
  end
  handle HOL_ERR _ => raise ERR "mk_curry" "";

fun mk_uncurry (f,x) = 
  case strip_fun (type_of f)
   of ([a,b],c) => mk_comb(mk_comb(mk_uncurry_tm(a,b,c),f),x)
    | other => raise ERR "mk_uncurry" "";

fun mk_pair_map(f,g) =
 let val (df,rf) = dom_rng (type_of f)
     val (dg,rg) = dom_rng (type_of g)
 in list_mk_comb(inst[alpha |-> df, beta  |-> dg, 
                      gamma |-> rf, delta |-> rg] pair_map_tm, [f,g])
 end;

fun mk_lex (r1,r2) =
 let val (dr1,_) = dom_rng (type_of r1)
     val (dr2,_) = dom_rng (type_of r2)
 in list_mk_comb(inst[alpha |-> dr1, beta |-> dr2] lex_tm, [r1,r2])
 end;

val dest_fst = dest_monop fst_tm (ERR "dest_fst" "")
val dest_snd = dest_monop snd_tm (ERR "dest_snd" "")

fun dest_curry tm = 
  let val (M,y) = with_exn dest_comb tm (ERR "dest_curry" "")
      val (f,x) = dest_binop curry_tm (ERR "dest_curry" "") M
  in (f,x,y)
  end;

val dest_pair_map = dest_binop pair_map_tm (ERR "dest_pair_map" "");

val dest_lex = dest_binop lex_tm (ERR "dest_lex" "");

val is_fst = can dest_fst
val is_snd = can dest_snd
val is_curry = can dest_curry
val is_pair_map = can dest_pair_map;
val is_lex = can dest_lex;


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
     in if same_const uncurry_tm Rator
        then let val (lv, body) = dest_pabs Rand
                 val (rv, body) = dest_pabs body
             in (mk_pair(lv, rv), body)
             end
        else raise ERR "dest_pabs" ""
     end;

fun pbvar tm = fst (dest_pabs tm) handle HOL_ERR _ => failwith "pbvar"
and pbody tm = snd (dest_pabs tm) handle HOL_ERR _ => failwith "pbody" ;

fun dest_plet M =
  let val (f,rhs) = dest_let M
      val (vstruct,body) = dest_pabs f
  in (vstruct,rhs,body)
  end
  handle _ => raise ERR "dest_plet" "not a (possibly paired) \"let\""



(*---------------------------------------------------------------------------*)
(* Paired binders                                                            *)
(*---------------------------------------------------------------------------*)

local val FORALL_ERR  = ERR "dest_pforall"  "not a (possibly paired) \"!\""
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
val dest_pforall  = dest_pbinder universal   FORALL_ERR
val dest_pexists  = dest_pbinder existential EXISTS_ERR
val dest_pexists1 = dest_pbinder exists1     EXISTS1_ERR
val dest_pselect  = dest_pbinder select      SELECT_ERR
end;

val dest_uncurry = dest_pabs o dest_monop uncurry_tm (ERR "dest_uncurry" "");
val is_uncurry = can dest_uncurry

val is_pabs     = can dest_pabs
val is_plet     = can dest_plet
val is_pforall  = can dest_pforall
val is_pexists  = can dest_pexists
val is_pexists1 = can dest_pexists1
val is_pselect  = can dest_pselect;

fun list_mk_pabs(V,M)    = itlist (curry mk_pabs) V M
fun list_mk_pforall(V,M) = itlist (curry mk_pforall) V M
fun list_mk_pexists(V,M) = itlist (curry mk_pexists) V M;

(*---------------------------------------------------------------------------*)

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



(*---------------------------------------------------------------------------*)
(* Support for dealing with the syntax of any kind of let.                   *)
(*---------------------------------------------------------------------------*)

local 
  fun dest_plet' tm = 
     let val (a,b,c) = dest_plet tm
     in ([(a,b)],c)
     end
  fun dest_simple_let tm = 
     let val (f,x) = dest_let tm
         val (v,M) = dest_abs f
     in ([(v,x)],M)
     end
  fun dest_and_let tm acc = 
    let val (f,x) = boolSyntax.dest_let tm
    in if is_let f
       then dest_and_let f (x::acc)
       else let val (blist,M) = strip_pabs f
            in (zip blist (x::acc), M)
            end
    end
  fun fixup (l,r) = 
    let val (vstructs,M) = strip_pabs r
    in (list_mk_comb(l,vstructs),M)
    end
in
fun dest_anylet tm = 
  let val (blist,M) = dest_simple_let tm handle HOL_ERR _ => 
                      dest_plet' tm      handle HOL_ERR _ => 
                      dest_and_let tm []
  in (map fixup blist,M)
  end
  handle HOL_ERR _ => raise ERR "dest_anylet" "not a \"let\"-term"
end;

local fun abstr (l,r) = 
        if is_pair l orelse is_var l then (l,r)
        else let val (f,args) = strip_comb l
             in (f,list_mk_pabs(args,r))
             end
      fun reorg(l,r,M) = let val (a,b) = abstr(l,r) in (a,b,M) end
in
fun mk_anylet ([],M) = raise ERR "mk_anylet" "no binding"
  | mk_anylet ([(l,r)],M) = mk_plet (reorg(l,r,M))
  | mk_anylet (blist,M) = 
      let val (L,R) = unzip (map abstr blist)
          val abstr = list_mk_pabs(L,M)
      in rev_itlist (fn r => fn tm => mk_let(tm,r)) R abstr
      end
end;

fun strip_anylet tm = 
  case total dest_anylet tm
   of SOME(blist,M) =>
       let val (L,N) = strip_anylet M
       in (blist::L,N)
       end
    | NONE => ([],tm);

fun list_mk_anylet (L,M) = itlist (curry mk_anylet) L M;

(* Examples 
  val tm1 = Term `let x = M in N x`;
  val tm2 = Term `let (x,y,z) = M in N x y z`;
  val tm3 = Term `let x = M and y = N in P x y`;
  val tm4 = Term `let (x,y) = M and z = N in P x y z`;
  val tm5 = Term `let (x,y) = M and z = N in let u = x in P x y z u`;
  val tm6 = Term `let f(x,y) = M 
                  and g z = N 
                  in let u = x in P (g(f(x,u)))`;
  val tm7 = Term `let f x = M in P (f y)`;
  val tm8 = Term `let g x = A in 
                  let v = g x y in
                  let f x y (a,b) = g a
                  and foo = M 
                  in f x foo v`;
*)


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


(*---------------------------------------------------------------------------*)
(* Lift from ML pairs to HOL pairs                                           *)
(*---------------------------------------------------------------------------*)

fun lift_prod ty =
  let val comma = TypeBasePure.cinst ty comma_tm
  in 
     fn f => fn g => fn (x,y) => list_mk_comb(comma, [f x, g y])
  end


end
