(*---------------------------------------------------------------------------
 * Derived syntax for higher order logic.
 *---------------------------------------------------------------------------*)
(* Modified      : September 22, 1997, Ken Larsen                            *)
(*functor DSYNTAX (structure Match : Match_sig
                 structure Term : Term_sig
                 structure Lexis: Lexis_sig
                 sharing Match.Term = Term) : Dsyntax_sig = *)

structure Dsyntax :> Dsyntax =
struct


fun DSYNTAX_ERR function message = 
    Exception.HOL_ERR{origin_structure = "Dsyntax",
		      origin_function = function,
		      message = message};
open Exception Type Term
infixr 3 -->;
val |-> = Lib.|->; infix 5 |->;

(*---------------------------------------------------------------------------
          Some common type "shapes"
 ---------------------------------------------------------------------------*)

fun infix_ty ty1 ty2 = ty1 --> ty1 --> ty2;
fun select_ty ty = (ty --> bool) --> ty;
fun quant_ty ty =  (ty --> bool) --> bool;
val b2b2b = infix_ty bool bool;

exception BAD
fun dest_monop M s e = 
   let val {Rator=c, Rand=tm} = Term.dest_comb M
   in if ((#Name(dest_const c) = s) handle HOL_ERR _ => false) 
      then (c,tm) else raise e
   end

fun dest_binop M s e = 
  let val {Rator,Rand=tm2} = Term.dest_comb M
      val {Rator=c,Rand=tm1} = Term.dest_comb Rator
  in
    if ((#Name(dest_const c) = s) handle HOL_ERR _ => false) 
     then (c,tm1,tm2) else raise e
  end 

fun dest_binder M s e = 
  let val {Rator=c, Rand} = Term.dest_comb M
  in
     if ((#Name(dest_const c) = s) handle HOL_ERR _ => false) 
     then dest_abs Rand else raise e
  end 

(*---------------------------------------------------------------------------
 * Derived syntax from theory "min"
 *---------------------------------------------------------------------------*)

fun mk_eq{lhs,rhs} = 
   list_mk_comb(mk_const{Name="=",Ty=infix_ty(type_of lhs) bool},[lhs,rhs])
   handle HOL_ERR _ => raise DSYNTAX_ERR "mk_eq" "lhs and rhs have different types"

fun mk_imp{ant,conseq} = 
 list_mk_comb(mk_const{Name="==>",Ty=b2b2b},[ant,conseq])
 handle HOL_ERR _ => raise DSYNTAX_ERR "mk_imp" "Non-boolean argument"

fun mk_select(s as {Bvar, Body}) = 
   mk_comb{Rator = mk_const{Name="@",Ty=select_ty (type_of Bvar)},
           Rand = mk_abs s}
   handle HOL_ERR _ => raise DSYNTAX_ERR"mk_select" "";

fun dest_eq M = 
   let val (_,tm1,tm2) = dest_binop M "=" (DSYNTAX_ERR"dest_eq" "not an \"=\"")
   in {lhs=tm1, rhs=tm2}
   end;
val lhs = #lhs o dest_eq
and rhs = #rhs o dest_eq

local val err = DSYNTAX_ERR"dest_imp" "not an \"==>\""
in
fun dest_imp M = 
   let val (_,tm1,tm2) = dest_binop M "==>" err
   in {ant=tm1, conseq=tm2}
   end handle HOL_ERR _ 
   => let val (_,tm) = dest_monop M "~" err 
      in {ant=tm,conseq=mk_const{Name="F",Ty=bool}}
      end
end;

fun dest_select M = dest_binder M "@" (DSYNTAX_ERR"dest_select" "not a \"@\"");


(*---------------------------------------------------------------------------
 * Derived syntax from theory "bool"
 *---------------------------------------------------------------------------*)

local fun mk_quant s (a as {Bvar,...}) = 
   mk_comb{Rator=mk_const{Name=s, Ty=quant_ty (type_of Bvar)}, Rand=mk_abs a}
   handle HOL_ERR _ => raise DSYNTAX_ERR"mk_quant" ("not a "^s)
in
  val mk_forall = mk_quant "!"
  and mk_exists = mk_quant "?"
end;

fun dest_forall M = dest_binder M "!" (DSYNTAX_ERR"dest_forall" "not a \"!\"");
fun dest_exists M = dest_binder M "?" (DSYNTAX_ERR"dest_exists" "not a \"?\"");


(*---------------------------------------------------------------------------
 * Negation 
 *---------------------------------------------------------------------------*)

fun mk_neg M = mk_comb{Rator=mk_const{Name="~",Ty=bool-->bool}, Rand=M};

fun dest_neg M = Lib.snd(dest_monop M "~" (DSYNTAX_ERR"dest_neg" "not a neg"));

(*---------------------------------------------------------------------------
 *   /\  \/ 
 *---------------------------------------------------------------------------*)

fun mk_conj{conj1,conj2} = 
   list_mk_comb(mk_const{Name="/\\",Ty=b2b2b},[conj1,conj2])
   handle HOL_ERR _ => raise DSYNTAX_ERR "mk_conj" "Non-boolean argument"

fun mk_disj{disj1,disj2} = 
   list_mk_comb(mk_const{Name="\\/",Ty=b2b2b},[disj1,disj2])
   handle HOL_ERR _ => raise DSYNTAX_ERR "mk_disj" "Non-boolean argument"

fun dest_conj M = 
 let val (_,tm1,tm2) = dest_binop M "/\\" (DSYNTAX_ERR"dest_conj" "not a conj")
 in {conj1=tm1, conj2=tm2}
 end

fun dest_disj M = 
 let val (_,tm1,tm2) = dest_binop M "\\/" (DSYNTAX_ERR"dest_disj" "not a disj")
 in {disj1=tm1, disj2=tm2}
 end;

(*---------------------------------------------------------------------------
 * Conditional 
 *---------------------------------------------------------------------------*)
local fun cond_ty ty = bool --> ty --> ty --> ty
in
fun mk_cond {cond,larm,rarm} = 
  list_mk_comb(mk_const{Name="COND",Ty=cond_ty(type_of larm)},[cond,larm,rarm])
  handle HOL_ERR _ => raise DSYNTAX_ERR"mk_cond" ""
end;

local val NOT_A_COND = DSYNTAX_ERR"dest_cond" "not a cond"
in
fun dest_cond M =
  let val {Rator,Rand=t2} = dest_comb M handle HOL_ERR _ => raise NOT_A_COND
      val (_,b,t1) = dest_binop Rator "COND" NOT_A_COND
  in
    {cond=b, larm=t1, rarm=t2}
  end
end;



(*---------------------------------------------------------------------------
 * The theory of pairs
 *---------------------------------------------------------------------------*)
fun prod_ty ty1 ty2 = Type.mk_type{Tyop="prod",Args=[ty1,ty2]};
fun comma_ty ty1 ty2 = ty1 --> ty2 --> prod_ty ty1 ty2;

fun mk_pair{fst, snd} = 
  let val ty1 = type_of fst  and ty2 = type_of snd
  in 
    list_mk_comb(mk_const{Name=",", Ty=comma_ty ty1 ty2},[fst,snd])
  end;

fun dest_pair M = 
  let val (_,tm1,tm2) = dest_binop M "," 
                          (DSYNTAX_ERR"dest_pair" "not a pair")
  in {fst=tm1, snd=tm2}
  end;


(* ===================================================================== *)
(* Syntax functions for let-terms:                                       *)
(*                                                                       *)
(* mk_let ("f","x") = "LET f x"                                          *)
(* dest_let "LET f x" = ("f","x")                                        *)
(* ===================================================================== *)

fun mk_let{func, arg} =
   let val fty = type_of func
       val c = mk_const{Name="LET", Ty=fty --> fty}
   in 
     list_mk_comb(c,[func,arg])
   end 
  handle HOL_ERR _ => raise DSYNTAX_ERR"mk_let" "";

fun dest_let M = 
  let val (_,f,x) = dest_binop M "LET" 
                      (DSYNTAX_ERR"dest_let" "not a let term")
  in 
    {func=f, arg=x}
  end;


(* ===================================================================== *)
(* Syntax functions for lists added [RJB 90.10.24].                      *)
(* ===================================================================== *)

(*---------------------------------------------------------------------------
 * mk_cons ("t","[t1;...;tn]") ----> "[t;t1;...;tn]" 
 *---------------------------------------------------------------------------*)

local fun cons_ty hty tty =  hty --> tty --> tty
in
fun mk_cons{hd, tl} =
   let val hty = type_of hd
       and tty = type_of tl
   in list_mk_comb(mk_const{Name="CONS",Ty=cons_ty hty tty},[hd,tl])
   end
   handle HOL_ERR _ => raise DSYNTAX_ERR"mk_cons" ""
end;

(*---------------------------------------------------------------------------
 * dest_cons "[t;t1;...;tn]" ----> ("t","[t1;...;tn]") 
 *---------------------------------------------------------------------------*)

fun dest_cons M = 
  let val (_,h,t) = dest_binop M "CONS" (DSYNTAX_ERR"dest_cons" "not a cons")
  in
     {hd=h,tl=t}
  end;
val is_cons = Lib.can dest_cons;

(*---------------------------------------------------------------------------
 * mk_list (["t1";...;"tn"],":ty") ----> "[t1;...;tn]:(ty)list" 
 *---------------------------------------------------------------------------*)

fun mk_list{els,ty} = 
   Lib.itlist (fn h => fn t => mk_cons{hd=h, tl=t})
          els (mk_const{Name="NIL",Ty=Type.mk_type{Tyop="list",Args = [ty]}})
   handle HOL_ERR _ => raise DSYNTAX_ERR "mk_list" "";

(*---------------------------------------------------------------------------
 * dest_list "[t1;...;tn]:(ty)list" ----> (["t1";...;"tn"],":ty") 
 *---------------------------------------------------------------------------*)
fun dest_list tm =
   if (is_cons tm)
   then let val {hd,tl} = dest_cons tm 
            val {els,ty} = dest_list tl
        in {els = hd::els, ty = ty}
        end
   else case (dest_const tm handle _ 
               => raise DSYNTAX_ERR "dest_list" "not a list term")
         of {Name="NIL", Ty} => 
              (case (Type.dest_type Ty)
                of {Args=[ty],...} => {els = [], ty = ty}
                 | _ => raise DSYNTAX_ERR "dest_list" "implementation error")
          | _ => raise DSYNTAX_ERR "dest_list" "not a list term";

val is_list = Lib.can dest_list;

(*---------------------------------------------------------------------------*)
(* If list_mk_cons were to be implemented it should behave as follows:       *)
(*                                                                           *)
(* list_mk_cons (["h1";...;"hm"],"[t1;...;tn]") ----> "[h1;...;hm;t1;...;tn]"*)
(*                                                                           *)
(* though I don't think it would be used much [RJB 90.10.24].                *)
(*---------------------------------------------------------------------------*)


val is_eq     = Lib.can dest_eq
val is_imp    = Lib.can dest_imp
val is_select = Lib.can dest_select;
val is_forall = Lib.can dest_forall
and is_exists = Lib.can dest_exists;
val is_neg    = Lib.can dest_neg;
val is_conj   = Lib.can dest_conj
and is_disj   = Lib.can dest_disj;
val is_cond   = Lib.can dest_cond;
val is_pair   = Lib.can dest_pair;
val is_let    = Lib.can dest_let;


(*---------------------------------------------------------------------------
 * Construction and destruction functions that deal with SML lists 
 *---------------------------------------------------------------------------*)

(* list_mk_comb defined in term.sml *)
fun list_mk_abs (vars,t) = 
    Lib.itlist (fn v => fn b => mk_abs{Bvar=v, Body=b}) vars t;
fun list_mk_imp(antel,conc) =
    Lib.itlist(fn a => fn tm => mk_imp{ant=a,conseq=tm}) antel conc;
fun list_mk_exists (vlist,t) = 
   Lib.itlist (fn v => fn b => mk_exists{Bvar = v, Body = b}) vlist t;
fun list_mk_forall (vlist,t) = 
   Lib.itlist (fn v => fn b => mk_forall{Bvar = v, Body = b}) vlist t;
val list_mk_conj =
    Lib.end_itlist(fn c1 => fn tm => mk_conj{conj1=c1, conj2=tm})
val list_mk_disj = 
    Lib.end_itlist(fn d1 => fn tm => mk_disj{disj1=d1, disj2=tm})
val list_mk_pair = 
    Lib.end_itlist(fn a => fn p => mk_pair{fst=a, snd=p});

fun gen_all tm = list_mk_forall (Term.free_vars tm, tm);

local fun dest M rands =
        let val {Rator,Rand} = dest_comb M
        in dest Rator (Rand::rands)
        end handle HOL_ERR _ => (M,rands)
in
  fun strip_comb tm = dest tm []
end;

fun strip_abs tm =
   if (is_abs tm)
   then let val {Bvar,Body} = dest_abs tm
            val (bvs, core) = strip_abs Body
        in (Bvar::bvs, core)
        end
  else ([],tm);

fun strip_imp fm =
   if (is_imp fm)
   then let val {ant,conseq} = dest_imp fm
	    val (was,wb) = strip_imp conseq
        in ((ant::was), wb)
        end
   else ([],fm);

fun strip_forall fm =
   if (is_forall fm)
   then let val {Bvar,Body} = dest_forall fm
            val (bvs,core) = strip_forall Body
        in ((Bvar::bvs), core)
        end
   else ([],fm);


fun strip_exists fm =
   if (is_exists fm)
   then let val {Bvar, Body} = dest_exists fm 
            val (bvs,core) = strip_exists Body
        in
        ((Bvar::bvs), core)
        end
   else ([],fm);

fun strip_conj w = 
   if (is_conj w)
   then let val {conj1,conj2} = dest_conj w
        in
        (strip_conj conj1)@(strip_conj conj2)
        end
   else [w];


fun strip_disj w =
   if (is_disj w)
   then let val {disj1,disj2} = dest_disj w 
        in
        (strip_disj disj1)@(strip_disj disj2)
        end
   else [w];

fun strip_pair tm = 
   if (is_pair tm) 
   then let val {fst,snd} = dest_pair tm
            fun dtuple t =
               if (is_pair t)
               then let val{fst,snd} = dest_pair t
                    in (fst :: dtuple snd)
                    end
               else [t]
        in fst::dtuple snd
        end
   else [tm];


(*---------------------------------------------------------------------------*)
(* Constructor, destructor and discriminator functions for paired            *)
(* abstractions.                                                             *)
(* [JRH 91.07.17]                                                            *)
(*---------------------------------------------------------------------------*)

local fun mk_uncurry(xt,yt,zt) =
        mk_const{Name="UNCURRY",Ty = (xt-->yt-->zt) --> prod_ty xt yt --> zt}
      fun mpa(varstruct,body) =
         if (is_var varstruct) then mk_abs{Bvar=varstruct, Body=body}
         else let val {fst,snd} = dest_pair varstruct
                  val cab = mpa(fst,mpa(snd,body))
                  val unk = mk_uncurry(type_of fst,type_of snd,type_of body)
              in 
               mk_comb{Rator=unk, Rand=cab}
              end
in
fun mk_pabs{varstruct,body} = mpa(Lib.assert is_pair varstruct, body)
   handle HOL_ERR _ => raise DSYNTAX_ERR"mk_pabs" ""
end;

(*---------------------------------------------------------------------------*)
(* dest_pabs - Destroys (possibly multiply) paired abstraction               *)
(*---------------------------------------------------------------------------*)

local val ucheck = Lib.assert (Lib.curry (op =) "UNCURRY" o #Name o dest_const)
fun dpa tm =
   let val {Bvar,Body} = dest_abs tm
   in {varstruct=Bvar, body=Body}
   end handle HOL_ERR _ 
   => let val {Rator,Rand} = dest_comb tm
          val _ = ucheck Rator
          val {varstruct=lv, body} = dpa Rand
          val {varstruct=rv, body} = dpa body
      in 
        {varstruct=mk_pair{fst=lv, snd=rv}, body=body}
      end
in
fun dest_pabs tm = 
   let val (pr as {varstruct, ...}) = dpa tm
   in if (is_pair varstruct) then pr
      else raise DSYNTAX_ERR "dest_pabs" "not a paired abstraction"
   end
end;

val is_pabs = Lib.can dest_pabs;

(*---------------------------------------------------------------------------*
 * Used to implement natural deduction style discharging of hypotheses. All  *
 * hypotheses alpha-convertible to the dischargee are removed.               *
 *---------------------------------------------------------------------------*)
fun disch(w,wl) = Lib.gather (not o Term.aconv w) wl;


(*---------------------------------------------------------------------------
 * Search a term for a sub-term satisfying the predicate P.
 *---------------------------------------------------------------------------*)
fun find_term P =
   let fun find_tm tm =
      if (P tm) then  tm 
      else if (is_abs tm)
           then find_tm (#Body(dest_abs tm))
           else if (is_comb tm)
                then find_tm (#Rator(dest_comb tm))
                     handle HOL_ERR _ => find_tm (#Rand(dest_comb tm))
                else raise DSYNTAX_ERR "find_term" ""
   in find_tm
   end;

(*---------------------------------------------------------------------------
 * find_terms: (term -> bool) -> term -> term list
 * 
 *  Find all subterms in a term that satisfy a given predicate p.
 *
 * Added TFM 88.03.31							
 *---------------------------------------------------------------------------*)
fun find_terms P tm =
   let fun accum tl tm =
      let val tl' = if (P tm) then (tm::tl) else tl 
      in if (is_abs tm)
         then accum tl' (#Body(dest_abs tm))
         else if (is_comb tm)
              then accum (accum tl' (#Rator(dest_comb tm))) 
                        (#Rand(dest_comb tm))
              else tl' 
      end
   in accum [] tm
   end;



(*---------------------------------------------------------------------------
 * Subst_occs 
 * Put a new variable in tm2 at designated (and free) occurrences of redex.
 * Rebuilds the entire term.
 *---------------------------------------------------------------------------*)
local
fun splice ({redex,...}:{redex:term,residue:term}) v occs tm2 =
   let fun graft (r as {occs = [], ...}) = r
         | graft {tm, occs, count} =
          if (redex = tm)
          then if (Portable_List.hd occs = count+1)
               then {tm = v, occs = Portable_List.tl occs, count = count+1}
               else {tm = tm, occs = occs, count = count+1}
          else if (is_comb tm)
               then let val {Rator, Rand} = dest_comb tm
                        val {tm = Rator', occs = occs', count = count'} =
                                        graft {tm=Rator,occs=occs,count=count}
                        val {tm = Rand', occs = occs'', count = count''} =
                                        graft {tm=Rand,occs=occs',count=count'}
                    in {tm = mk_comb{Rator = Rator', Rand = Rand'},
                        occs = occs'', count = count''}
                    end
               else if (is_abs tm)
                    then let val {Bvar,Body} = dest_abs tm
                             val {tm, count, occs} =
                                        graft{tm=Body,count=count,occs=occs}
                         in {tm = mk_abs{Bvar = Bvar, Body = tm},
                             count = count, occs = occs}
                         end
                    else {tm = tm, occs = occs, count = count}
   in #tm(graft {tm = tm2, occs = occs, count = 0})
   end

fun rev_itlist3 f L1 L2 L3 base_value =
 let fun rev_it3 (a::rst1) (b::rst2) (c::rst3) base = 
             rev_it3 rst1 rst2 rst3 (f a b c base)
       | rev_it3 [] [] [] base = base
       | rev_it3 _ _ _ _ = raise DSYNTAX_ERR "rev_itlist3"
                                  "not all lists have same size"
 in rev_it3 L1 L2 L3 base_value
 end

val sort = Lib.sort (Lib.curry (op <=) : int -> int -> bool)
in
fun subst_occs occ_lists tm_subst tm =
   let val occ_lists' = map sort occ_lists
       val (new_vars,theta) = 
               Lib.itlist (fn {redex,residue} => fn (V,T) =>
                         let val v = genvar(type_of redex)
                         in (v::V,  (v |-> residue)::T)  end)
                      tm_subst ([],[])
       val template = rev_itlist3 splice tm_subst new_vars occ_lists' tm
   in subst theta template
   end
end;



(*---------------------------------------------------------------------------
 * For restricted binders. Adding a pair "(B,R)" to this list, if "B" is the 
 * name of a binder and "R" is the name of a constant, will enable parsing 
 * of terms with the form 
 *
 *     B <varstruct list>::<restr>. M
 *---------------------------------------------------------------------------*)
local val basic_binders = ["!","?","@","\\"]
      val basic_restrictions = Lib.zip basic_binders 
           ["RES_FORALL","RES_EXISTS","RES_SELECT","RES_ABSTRACT"]
      val restricted_binders = ref basic_restrictions
in
fun binder_restrictions() = !restricted_binders
fun associate_restriction(p as (binder_str,const_name)) = 
   case (Lib.assoc1 binder_str (!restricted_binders))
     of NONE =>
        ((case (Term.const_decl binder_str)
          of {place=Binder,...} =>
             if (Lib.can Term.const_decl const_name)
              then restricted_binders := p :: !restricted_binders
              else raise DSYNTAX_ERR"restrict_binder"
                  (Lib.quote const_name^" is not the name of a constant")
           | _ => raise DSYNTAX_ERR"restrict_binder"
                   (Lib.quote binder_str^" is not the name of a binder"))
          handle HOL_ERR _ => raise DSYNTAX_ERR"restrict_binder"
                  (Lib.quote binder_str^" is not the name of a constant"))

      | SOME _ => raise DSYNTAX_ERR"restrict_binder"
                   ("Binder "^Lib.quote binder_str^" is already restricted")

fun delete_restriction binder =
   if (Lib.mem binder basic_binders)
   then raise DSYNTAX_ERR "delete_restriction"
            (Lib.quote binder^" cannot have its restriction deleted")
   else 
   restricted_binders :=
     Lib.set_diff (!restricted_binders)
                  [(binder,Lib.assoc binder(!restricted_binders))]
                  handle HOL_ERR _
                  => raise DSYNTAX_ERR"delete_restriction"
                             (Lib.quote binder^" is not restricted")
end;


val _ = Term.pair_ops dest_pabs dest_pair strip_pair binder_restrictions;

end; (* DSYNTAX *)
