(*=====================================================================  *)
(* FILE          : permLib.sml                                           *)
(* DESCRIPTION   : some code to handle permutations                      *)
(*                                                                       *)
(* AUTHORS       : Thomas Tuerk                                          *)
(* DATE          : March 2009                                            *)
(* ===================================================================== *)


structure permLib :> permLib =
struct

(*
quietdec := true;
loadPath := 
            (concat [Globals.HOLDIR, "/src/sort"])::
            !loadPath;

map load ["sortingTheory"];
quietdec := true;
*)


open HolKernel Parse boolLib Drule sortingTheory listTheory

(*
quietdec := false;
*)



val LIST_NIL_CONV =
    QCONV (REWRITE_CONV [CONJUNCT1 APPEND, APPEND_NIL])


val PERM_tm = ``PERM``;
val dest_PERM = dest_binop PERM_tm (mk_HOL_ERR "permLib" "dest_PERM" "")  
val is_PERM = can dest_PERM;


(*
val t = ``PERM (x1::l1 ++ (l2 ++ (x2::x3::l3) ++ x4::l4)) (x1::l1 ++ ((x2::x3::l3) ++ x4::l4 ++ l2))``  
val t1 =  ``x1::x2::x3::(l1 ++ (x2::x3::l3 ++ x4::l4 ++ l2 ++ l4))``
val t2 =  ``x1::x2::x8::(x4::l4 ++ l2++l4)``
*)


local
   fun strip_perm_list_acc xs ls t =
      if (listSyntax.is_cons t) then 
         let val (x,l) = listSyntax.dest_cons t; in 
             strip_perm_list_acc (x::xs) ls l 
         end
      else if (listSyntax.is_append t) then
         let
             val (t1,t2) = listSyntax.dest_append t;
             val (xs', ls') = strip_perm_list_acc xs ls t1;
         in
             strip_perm_list_acc xs' ls' t2
         end
      else
         if (listSyntax.is_nil t) then (xs,ls) else (xs, t::ls)    
in
   fun strip_perm_list t = 
      let
         val (xs,ls) = strip_perm_list_acc [] [] t
      in
         (Listsort.sort Term.compare xs, Listsort.sort Term.compare ls)
      end;
end;


fun bag_inter cmp [] _ = []
  | bag_inter cmp _ [] = []
  | bag_inter cmp (x::xs) (y::ys) =
    case cmp (x, y) of
        LESS    => bag_inter cmp xs (y::ys)
      | GREATER => bag_inter cmp (x::xs) ys
      | EQUAL   => x::(bag_inter cmp xs ys);


fun perm_list_inter t1 t2 =
  let
     val (xs1,ls1) = strip_perm_list t1
     val (xs2,ls2) = strip_perm_list t2   
  in
     (bag_inter Term.compare xs1 xs2,
      bag_inter Term.compare ls1 ls2)
  end;

fun perm_sub_list t1 t2 =
  let
     val (xs1,ls1) = strip_perm_list t1
     val (xs2,ls2) = strip_perm_list t2   

     val xs = bag_inter Term.compare xs1 xs2;
     val ls = bag_inter Term.compare ls1 ls2;

     val t1_sub = (length xs = length xs1) andalso (length ls = length ls1);
     val t2_sub = (length xs = length xs2) andalso (length ls = length ls2);
  in
     (t1_sub, t2_sub, (xs, ls))
  end;



(*dummy for testing

fun PERM_MOVE_CONS_TO_FRONT e t = SOME (
let val t' = rand t in
mk_thm ([], ``PERM ^t' = PERM (^e::^t')``) end);
*)


fun PERM_MOVE_CONS_TO_FRONT e t =
if (listSyntax.is_cons (rand t)) then
   let
      val (x, l) = listSyntax.dest_cons (rand t);
   in
      if (aconv x e) then SOME (REFL t) else
      let
         val l_term = mk_icomb (PERM_tm, l)
         val l_thm_opt = PERM_MOVE_CONS_TO_FRONT e l_term;
      in
         if not (isSome l_thm_opt) then NONE else
         let
            val l2 = (rand o rand o rhs o  concl o valOf) l_thm_opt
         in
            SOME (MP (ISPECL [x,l,e,l2] PERM_FUN_CONS_11_SWAP_AT_FRONT)
               (valOf l_thm_opt))
         end
      end
   end
else if (listSyntax.is_append (rand t)) then
   let
      val (l1,l2) = listSyntax.dest_append (rand t)
      val l1_thm_opt = PERM_MOVE_CONS_TO_FRONT e (mk_icomb (PERM_tm, l1))
      val l2_thm_opt = if isSome l1_thm_opt then NONE else
                       PERM_MOVE_CONS_TO_FRONT e (mk_icomb (PERM_tm, l2))
   in
      if (isSome l1_thm_opt) then
         let
            val l1' = (rand o rand o rhs o  concl o valOf) l1_thm_opt
         in
            SOME (MP (ISPECL [l2,l1,e,l1'] PERM_FUN_CONS_APPEND_1) 
                     (valOf l1_thm_opt))
         end
      else if (isSome l2_thm_opt) then
         let
            val l2' = (rand o rand o rhs o  concl o valOf) l2_thm_opt
         in
            SOME (MP (ISPECL [l1,l2,e,l2'] PERM_FUN_CONS_APPEND_2) 
                     (valOf l2_thm_opt))
         end
      else NONE
   end
else NONE;


(*
   val t = ``PERM (x1::x2::x3::[])``;
   val xs = free_vars t;
   PERM_MOVE_CONS_TO_FRONT_CONV xs t
*)
fun PERM_MOVE_CONS_TO_FRONT_CONV [] t = REFL t
  | PERM_MOVE_CONS_TO_FRONT_CONV (x::xs) t =
    let
       val thm0_opt = PERM_MOVE_CONS_TO_FRONT x t;
       val _ = if isSome thm0_opt then () else raise UNCHANGED;
       val thm0 = valOf thm0_opt;

       val l1 = (rand o rand o rhs o concl) thm0;
       val thm1 = PERM_MOVE_CONS_TO_FRONT_CONV xs (mk_icomb (PERM_tm, l1));
       val l2 = (rand o rhs o concl) thm1;

       val thm2 = ISPECL [x, l1, l2] PERM_FUN_CONS_IFF
       val thm3 = MP thm2 thm1
    in
       TRANS thm0 thm3
    end;




(*dummy for testing

fun PERM_MOVE_APPEND_TO_FRONT l t = SOME (
let val t' = rand t in
mk_thm ([], ``PERM ^t' = PERM (^l ++ ^t')``) end);
*)


fun PERM_MOVE_APPEND_TO_FRONT l t =
if (listSyntax.is_nil l) then
   let
      val ty = listSyntax.dest_list_type (type_of l)
      val tm = inst [alpha |-> ty] PERM_tm;
   in
      SOME (AP_TERM tm (GSYM (ISPEC (rand t) (CONJUNCT1 APPEND))))
   end      
else if (listSyntax.is_cons (rand t)) then
   let
      val (x, l') = listSyntax.dest_cons (rand t);
   in
      let
         val l'_term = mk_icomb (PERM_tm, l')
         val l'_thm_opt = PERM_MOVE_APPEND_TO_FRONT l l'_term;
      in
         if not (isSome l'_thm_opt) then NONE else
         let
            val l2 = (rand o rand o rhs o  concl o valOf) l'_thm_opt
         in
            SOME (MP (ISPECL [x,l',l,l2] PERM_FUN_CONS_11_APPEND)
               (valOf l'_thm_opt))
         end
      end
   end
else if (listSyntax.is_append (rand t)) then
   let
      val (l1,l2) = listSyntax.dest_append (rand t);
   in
      if (aconv l1 l) then SOME (REFL t) else
      if (aconv l2 l) then
         SOME (REWR_CONV PERM_FUN_APPEND t)
      else
      let
         val l1_thm_opt = PERM_MOVE_APPEND_TO_FRONT l (mk_icomb (PERM_tm, l1))
         val l2_thm_opt = if isSome l1_thm_opt then NONE else
                       PERM_MOVE_APPEND_TO_FRONT l (mk_icomb (PERM_tm, l2)) 
      in
         if (isSome l1_thm_opt) then
            let
               val l1' = (rand o rand o rhs o  concl o valOf) l1_thm_opt
            in
               SOME (MP (ISPECL [l1,l,l1',l2] PERM_FUN_APPEND_APPEND_1) 
                        (valOf l1_thm_opt))
            end
         else if (isSome l2_thm_opt) then
            let
               val l2' = (rand o rand o rhs o  concl o valOf) l2_thm_opt
            in
               SOME (MP (ISPECL [l2,l,l2',l1] PERM_FUN_APPEND_APPEND_2) 
                        (valOf l2_thm_opt))
            end
         else NONE
      end
   end
else if (aconv l (rand t)) then
   let
      val ty = listSyntax.dest_list_type (type_of l)
      val tm = inst [alpha |-> ty] PERM_tm;
   in
      SOME (AP_TERM tm (GSYM (ISPEC l APPEND_NIL)))
   end
else NONE;



(*
   val t = ``PERM (x1++x2++x3)``;
   val ls = free_vars t;
   PERM_MOVE_APPEND_TO_FRONT_CONV ls t

   val (l::ls) = ls
   val t = (mk_icomb (PERM_tm, l1))
*)

fun PERM_MOVE_APPEND_TO_FRONT_CONV [] t = REFL t
  | PERM_MOVE_APPEND_TO_FRONT_CONV (l::ls) t =
    let
       val thm0_opt = PERM_MOVE_APPEND_TO_FRONT l t;
       val _ = if isSome thm0_opt then () else raise UNCHANGED;
       val thm0 = valOf thm0_opt;

       val l1 = (rand o rand o rhs o concl) thm0;
       val thm1 = PERM_MOVE_APPEND_TO_FRONT_CONV ls (mk_icomb (PERM_tm, l1));
       val l2 = (rand o rhs o concl) thm1;

       val thm2 = ISPECL [l, l1, l2] PERM_FUN_APPEND_IFF
       val thm3 = MP thm2 thm1
    in
       TRANS thm0 thm3
    end;



(*
val l = hd ls
val l = ``x::(l3 ++ z3::l2 ++ x::z::x1::y::l1 ++ x3::x5::l0)``;
val xs = [``x:'a``, ``x1:'a``, ``y:'a``, ``x:'a``];
val ls = [``l2:'a list``, ``l0:'a list``, ``l3:'a list``];

val (xs,ls) = strip_perm_list l
*)

fun PERM_SPLIT_el_lists l (xs,ls) =
let
   val t = mk_icomb (PERM_tm, l);

   val thm0 = (QCHANGED_CONV (PERM_MOVE_APPEND_TO_FRONT_CONV ls) THENC
               RAND_CONV (REWR_CONV (GSYM (CONJUNCT1 APPEND))) THENC
               QCHANGED_CONV (PERM_MOVE_CONS_TO_FRONT_CONV xs)) t;
   val thm1 = CONV_RULE (RHS_CONV (REWRITE_CONV [GSYM (CONJUNCT2 APPEND)])) thm0

   val thm2 = CONV_RULE (RHS_CONV (RAND_CONV (
		 quantHeuristicsLib.BOUNDED_REPEATC (length ls) (REWR_CONV APPEND_ASSOC)))) thm1;

   val thm3 = CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV LIST_NIL_CONV))) thm2
in
   CONV_RULE (REWR_CONV (GSYM PERM_EQUIVALENCE_ALT_DEF)) thm3
end


fun PERM_ELIM_DUPLICATES_CONV t = 
let
   val (l1,l2) = dest_PERM t handle HOL_ERR _ => raise UNCHANGED;
   val common_terms = perm_list_inter l1 l2;

   val thm_l1 = PERM_SPLIT_el_lists l1 common_terms;
   val thm_l2 = PERM_SPLIT_el_lists l2 common_terms;

   val l3 = (rand o concl) thm_l1
   val l4 = (rand o concl) thm_l2

   val (lc,l3') = listSyntax.dest_append l3
   val (_,l4') = listSyntax.dest_append l4

   val thm0 = ISPECL [lc,l1,l3',l2,l4'] PERM_CONG_APPEND_IFF;
   val thm1 = MP thm0 thm_l1
   val thm2 = MP thm1 thm_l2
   val thm3 = CONV_RULE (RHS_CONV (REWRITE_CONV [PERM_REFL, PERM_NIL, NOT_CONS_NIL,
			    APPEND_eq_NIL])) thm2
in
   thm3
end;

(*
PERM_SPLIT l l2

val ls = ``l1:'a list``
val l = ``l2 ++ x::l1``
*)

fun PERM_SPLIT ls l = 
let
   val (b,_,common_terms) = perm_sub_list ls l;
   val _ = if b then () else raise UNCHANGED;

   val thm_l = PERM_SPLIT_el_lists l common_terms;
   val thm_ls = PERM_SPLIT_el_lists ls common_terms;
   val thm_ls = CONV_RULE (RAND_CONV (REWR_CONV APPEND_NIL)) thm_ls;

   val l' = (rand o concl) thm_l
   val ls' = (rand o concl) thm_ls
   val (lc,l'') = listSyntax.dest_append l'

   val thm0 = ISPECL [l,lc,ls,l''] PERM_FUN_SPLIT;
   val thm1 = MP thm0 thm_l
   val thm2 = MP thm1 thm_ls
in
   thm2
end;


fun PERM_NO_ELIM_NORMALISE_CONV t =
let
   val (l1,l2) = dest_PERM t handle HOL_ERR _ => raise UNCHANGED;

   fun ELIM_NIL_RULE thm = CONV_RULE (RAND_CONV (REWR_CONV APPEND_NIL)) thm 
                             handle HOL_ERR _ => thm;

   val thm_l1 = ELIM_NIL_RULE (PERM_SPLIT_el_lists l1 (strip_perm_list l1));
   val thm_l2 = ELIM_NIL_RULE (PERM_SPLIT_el_lists l2 (strip_perm_list l2));

   val l1' = (rand o concl) thm_l1
   val l2' = (rand o concl) thm_l2

   val thm0 = ISPECL [l1,l1',l2,l2'] PERM_CONG_2;
   val thm1 = MP thm0 thm_l1
   val thm2 = MP thm1 thm_l2
   val thm3 = CONV_RULE (RHS_CONV (REWRITE_CONV [APPEND, APPEND_NIL])) thm2
in
   thm3
end;

fun PERM_TURN_CONV t =
let
   val (l1,l2) = dest_PERM t handle HOL_ERR _ => raise UNCHANGED;

   val (xs1,ls1) = strip_perm_list l1;
   val (xs2,ls2) = strip_perm_list l2;
   val comp = pair_compare (list_compare Term.compare, list_compare Term.compare);

   val turn = (length xs1 + length ls1 < length xs2 + length ls2) orelse
              ((length xs1 + length ls1 = length xs2 + length ls2) andalso
               (length ls1 < length ls2)) orelse
              ((length ls1 = length ls2) andalso
               (length xs1 = length xs2) andalso
               (comp ((xs1,ls1), (xs2,ls2)) = LESS))
in
   if turn then REWR_CONV PERM_SYM t else raise UNCHANGED
end;


val PERM_NORMALISE_CONV = PERM_ELIM_DUPLICATES_CONV THENC
                          PERM_NO_ELIM_NORMALISE_CONV THENC
			  PERM_TURN_CONV;

(*
val thm = (ASSUME ``PERM l1 [x;y;z]``)
val t = ``PERM (z::y::x'::l2) (l3++(x'::l1))``

show_assums := true
PERM_REWR_CONV thm t
*)


fun PERM_REWR_CONV thm t = 
let
   val (l,r) = dest_PERM (concl thm)

   val (l1,l2) = dest_PERM t handle HOL_ERR _ => raise UNCHANGED;
   val (turn,split_thm) = 
     (false, PERM_SPLIT l l1) handle UNCHANGED =>
     (true,  PERM_SPLIT l l2);

   val (thm0,l1,l2) = if turn then (ISPECL [l1,l2] PERM_SYM,l2,l1) else (REFL t,l1,l2);

   val l1' = (rand o concl) split_thm
   val thm1a = ISPECL [l1,l1',l2,l2] PERM_CONG_2
   val thm1b = MP thm1a split_thm
   val thm1c = MP thm1b (ISPEC l2 PERM_REFL);
   val thm1 = TRANS thm0 thm1c


   val thm2a = ISPECL [l,r,rand l1',l2] PERM_REWR
   val thm2b = MP thm2a thm
   val thm2 = TRANS thm1 thm2b

   val thm3 = CONV_RULE (RHS_CONV PERM_NORMALISE_CONV) thm2
in
   thm3
end;


fun PERM_SIMP_CONV thmL t =
   let
      val _ = if is_PERM t then () else raise UNCHANGED;
      val thm =  FIRST_CONV ((CHANGED_CONV PERM_NORMALISE_CONV)::(map (QCHANGED_CONV o PERM_REWR_CONV) thmL)) t;
   in
      thm
   end;


exception perm_reducer_context of thm list

fun perm_reducer_get_context e = 
    (raise e) 
    handle perm_reducer_context thmL => thmL;

val thm_ref = ref []
val PERM_REDUCER =
  Traverse.REDUCER {name = SOME "PERM_REDUCER",
           initial = perm_reducer_context [],
           addcontext = fn (ctx, thmL) => (thm_ref := thmL :: !thm_ref;
			       perm_reducer_context (append (filter (is_PERM o concl) 
                                                    (flatten (map BODY_CONJUNCTS thmL))) 
                               (perm_reducer_get_context ctx))),
           apply = fn args => QCHANGED_CONV (PERM_SIMP_CONV (perm_reducer_get_context (#context args)))
              };

val PERM_ss = simpLib.SSFRAG
    {name=SOME"PERM_ss",
     convs = [], rewrs = [], filter = NONE, dprocs = [PERM_REDUCER], congs = [],
     ac = []
     }


(* 

val conv = SIMP_CONV (std_ss++PERM_ss) []


conv ``X /\ (PERM (x::l1++l2) (l2++[x])) /\ Z``
conv ``(PERM (x::z::l1++l2) (l3++x::l1)) /\ Z``

conv ``(X /\ (PERM (l2++[]++[z]) (y::l4)) /\ Y) ==> ((PERM (x::z::l1++l2) (l3++x::l1)))``

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC (std_ss++PERM_ss) []

*)


end
