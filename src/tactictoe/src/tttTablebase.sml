(* ========================================================================= *)
(* FILE          : tttTablebase.sml                                          *)
(* DESCRIPTION   : List provable theorems by their proof length.             *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure tttTablebase :> tttTablebase =
struct

load "tttSynt";

open HolKernel boolLib Abbrev tttTools tttSynt

val ERR = mk_HOL_ERR "tttTablebase"
val dbg = dbg_file "tttTablebase"

(* -------------------------------------------------------------------------
   Test
   ------------------------------------------------------------------------- *)

fun is_refl tm = is_eq tm andalso (let val (a,b) = dest_eq tm in a = b end)

fun is_inst tm1 tm2 = can (match_term tm1) tm2

fun is_subs (tm1,tm2) tm3 =
  let
    val sub = [{redex = lhs tm1, residue = rhs tm1}]
    val occl  = find_terms (fn x => x = lhs tm1) tm2
    fun f i _ = subst_occs [[i+1]] sub tm2
  in
    mem tm3 (mapi f occl)
  end
  handle HOL_ERR _ => false

fun all_sub (tm1,tm2) = 
  let 
    val sub    = [{redex = lhs tm1, residue = rhs tm1}]
    val nb_occ = length (find_terms (fn x => x = lhs tm1) tm2) 
  in
    List.tabulate (nb_occ, fn i => subst_occs [[i+1]] sub tm2)
  end
  handle HOL_ERR _ => []


fun is_apterm tm1 tm2 =
  let val pretm = (snd o only_hd o fst o AP_TERM_TAC) ([],tm2) in
    pretm = tm1
  end
  handle HOL_ERR _ => false


val ax4 = ``x + 0 = x``;
val ax5 = ``x + SUC y = SUC (x + y)``;
val ax6 = ``0 <> SUC x``;
val ax4' = ``0 + x = x``;
val ax5' = ``SUC y + x  = SUC (x + y)``;
val axl_glob = [ax4,ax5,ax4',ax5',ax6];

datatype conseq =
  Refl |
  Inst of term |
  Ap of term |
  Sub of term * term |
  Nsym of term |
  Sym of term |
  Inj of term

fun way_of_prim tm = 
  let val instl = filter (fn x => is_inst x tm) axl_glob in
    if is_refl tm then [Refl] else [] @
    map Inst instl
  end

   
fun is_negsym tm1 tm2 = 
  let 
    val (a,b) = dest_eq (dest_neg tm1)
    val (c,d) = dest_eq (dest_neg tm2)
  in
    (a,b) = (d,c) 
  end
  handle HOL_ERR _ => false

fun is_sym tm1 tm2 = 
  let 
    val (a,b) = dest_eq tm1
    val (c,d) = dest_eq tm2
  in
    (a,b) = (d,c) 
  end
  handle HOL_ERR _ => false

fun is_inj tm1 tm2 = 
  let 
    val (a,b) = dest_eq (dest_neg tm1)
    val (c,d) = dest_eq (dest_neg tm2)
  in
    mk_comb (``SUC``,a) = c andalso mk_comb (``SUC``, b) = d
    
  end
  handle HOL_ERR _ => false


fun way_of_conseq tml subl tm = 
  let 
    val aptml   = filter (fn x => is_apterm x tm) tml
    val subtml  = map fst (filter (fn x => snd x = tm) subl)
    val nsymtml = filter (fn x => is_negsym x tm) tml
    val symtml  = filter (fn x => is_sym x tm) tml
    val injtml  = filter (fn x => is_inj x tm) tml
  in
    map Ap aptml @ map Sub subtml @ 
    map Nsym nsymtml @ map Sym symtml @ map Inj injtml
  end
;
(* -------------------------------------------------------------------------
   Generate all the terms up to a certain size.
   ------------------------------------------------------------------------- *)
  
  fun negate x = if is_neg x then dest_neg x else mk_neg x
  
  (* parameters of treenns *)
  val cj   = ``(SUC 0) + 0`` ;
  val cset = mk_fast_set Term.compare (find_terms is_const cj);

  (* Terms *)
  fun nofilterf l = l;
  val terml1 = synthetize nofilterf (10000000,7) (``:num``,cset);
  val terml2 = cartesian_product terml1 terml1;
  val terml3 = map mk_eq terml2;
  val terml4 = map mk_neg terml3;
  val terml5 = terml3 @ terml4;
  length terml5;
  
  (* Depth 0 *)
  val prim_wayl = map_assoc way_of_prim terml5;
  val (upl0',pl0) = partition (null o snd) prim_wayl;
  val ql0 = map (negate o fst) pl0;
  val pll = [pl0];
  val upl0 = filter (fn x => not (mem (fst x) ql0)) upl0';
  
  fun distrib l = case l of
      [] => []
    | (a,al) :: m => map (fn x => (a,x)) al @ distrib m

  (* Depth i *)
  fun loop (i,max) (pll, (upl: term list)) =
    if i > max orelse null upl then (pll,upl) else
    let
      val pl = map fst (List.concat pll)
      val (subl1,t) = add_time (map_assoc all_sub) (cartesian_product pl pl)
      val subl2 = distrib subl1
      val _ = print_endline (Real.toString t)
      val (wayl,t) = add_time (map_assoc (way_of_conseq pl subl2)) upl
      val _ = print_endline (Real.toString t)
      val (upli,pli) = partition (null o snd) wayl
      val pli_not = map negate (map fst pli)
      val _ = print_endline (int_to_string (length pli))
      val upli_filtered = filter (fn x => not (mem (fst x) pli_not)) upli
    in
      loop (i+1,max) (pli :: pll, map fst upli_filtered)
    end  
;
  (* *)
  val (new_pll, new_upl) = loop (1,10) (pll, (map fst upl0));

  (* 
    extract proofs from the table base examples
     => induce a policy
   
    Generating a term

    
 
   *)
 
end (* struct *)

(* test 
load "tttTablebase"; open tttTablebase tttTools;


0 + SUC (SUC 0) <> 0

0 + SUC (SUC 0) = SUC (SUC 0)


SUC (SUC 0) <> 0

SUC 0 <> 0


 meta_term + 0  

 A small recurrent network on top too choose the path?

 Policy has size [1,2] but there are a lot more of intermediate nodes 
 then.

!x. x + 0 = x & 0

  0 + 0 = 0

0 + 0 = 0

if t + 0 = t
then (build_term t) + 0 = (build_term t)

 



   x + 0 = x => S (x) + 0 = S (x)

               

0 <> SUC 0

SUC 0 <> SUC (SUC 0) injectivity


SUC (SUC 0) <> 0

SUC (SUC 0) = 0



(* can derive the filter function from the nn scoring function *)

val maxsize = 20;

(* signature *)
val pax1  = ("ADD_ASSOC", ``(x+y)+z = x+(y+z)``);
val pax3  = ("MUL_ASSOC", ``(x*y)*z = x*(y*z)``);
val pax14 = ("LE_S",   ``0 < SUC 0``);
val cl    = List.concat (map (find_terms is_const o snd) [pax14,pax1,pax3]);
val cset  = mk_fast_set Term.compare cl;

val metatm = ``meta_var : num = meta_var``;

val sub1 = [{redex = ``meta_var:num``, residue = ``SUC meta_var``}];
val sub2 = [{redex = ``meta_var:num``, residue = ``meta_var + meta_var``}];
val sub3 = [{redex = ``meta_var:num``, residue = ``0``}];
val subl = [sub1,sub2,sub3];

val metatml1 = build_fo_cut subl metatm;
val metatml2 = 
  mk_fast_set Term.compare (List.concat (map (build_fo_cut subl) metatml1));
val metatml3 = 
  mk_fast_set Term.compare (List.concat (map (build_fo_cut subl) metatml2));
val metatml4 = 
  mk_fast_set Term.compare (List.concat (map (build_fo_cut subl) metatml3));
val metatml5 = 
  mk_fast_set Term.compare (List.concat (map (build_fo_cut subl) metatml4));
val metatml6 = 
  mk_fast_set Term.compare (List.concat (map (build_fo_cut subl) metatml5));


The only way to decide 0 = SUC 0 is to prove that 0 <> SUC 0

*)



