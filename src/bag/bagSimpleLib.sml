structure bagSimpleLib :> bagSimpleLib =
struct

open HolKernel boolLib bossLib

local open bagTheory in end

open bagSyntax 



(******************************************************************************)
(* This file contains tools to handle "simple" bags.                          *)
(*                                                                            *)
(* In the context of this file, a "simple" bag is a bag, that just consists   *)
(* of insertions into the empty bag. For example                              *)
(*                                                                            *)
(* {|x1;x2;x3;x4|}, {||}, {|x1|} are simple bags                              *)
(*                                                                            *)
(* BAG_UNION {|x1;x2|} {|x3;x4|}, BAG_INSERT e b are not                      *)                                        
(*                                                                            *)
(******************************************************************************)

val is_simple = can dest_bag;


(******************************************************************************)
(* Resorting bags                                                             *)
(*                                                                            *)
(* The insert of bags commutes. Therefore, there order can be easily changed. *)
(* For example: {|x0; x1; x2; x3; x4|} = {|x0; x3; x2; x1; x4|}               *)
(*                                                                            *)
(* This conversion provides a way of doing such resorts. It gets a list       *)
(* of integers that represent the positions of elements in the original list; *)
(* counting starts with zero. It then sorts these elements to the front of    *)
(* the new bag. Any remaining elements are placed behind them. It's           *)
(* assumed that the elements of this list of integers are pairwise distinct.  *)
(*                                                                            *)
(* For example:                                                               *)
(* BAG_RESORT_CONV [0,3,2] ``{|x0; x1; x2; x3; x4|}`` results in              *)
(*                           {|x0; x3; x2; x1; x4|}                           *)
(******************************************************************************)


local
   fun BAG_RESORT___BRING_TO_FRONT_CONV 0 b = REFL b
     | BAG_RESORT___BRING_TO_FRONT_CONV n b =
    let
        (*remove frist element and 
          bring to front in rest of the bag*)
	val (e1,b') = bagSyntax.dest_insert b;                      
        val thm0 = BAG_RESORT___BRING_TO_FRONT_CONV (n-1) b';

        (*add first element again*)
	val thm1 = AP_TERM (rator b) thm0;

        (*swap the first two elements*)
        val (e2, b'') = bagSyntax.dest_insert (rhs (concl thm0));
        val thm2 = ISPECL [b'', e1, e2] bagTheory.BAG_INSERT_commutes
        val thm3 = TRANS thm1 thm2
    in
        thm3
    end;

in
   fun BAG_RESORT_CONV [] b = REFL b (*nothing to do*)
   |   BAG_RESORT_CONV [n] b = BAG_RESORT___BRING_TO_FRONT_CONV n b (*that's simple :-)*)
   |   BAG_RESORT_CONV (n::n2::ns) b = 
   let
      (*first bring the first element, i.e. n, to the front*)
      val thm0 = BAG_RESORT___BRING_TO_FRONT_CONV n b;

      (*remove first element*)
      val (insert_e1,b') = dest_comb (rhs (concl thm0));

      (*resort the rest of the bag
        elements that occur before the one just moved to the front have the 
        some position in b' as they had in b. The others moved one position to
        the front *)
      val ns' = map (fn m => if (n < m) then (m - 1) else m) (n2::ns);
      val thm1 = BAG_RESORT_CONV ns' b';

      (*combine again*)
      val thm2 = AP_TERM insert_e1 thm1;
      val thm3 = TRANS thm0 thm2
   in
      thm3
   end;
end




(******************************************************************************)
(* BAG_IMAGE_CONV                                                             *)
(*                                                                            *)
(* Moves BAG_IMAGE over very simple bags that consists of repeatedly          *)
(* inserting elements into the empty bag. For these bags, it's very easy to   *)
(* show that they are finite.                                                 *)
(*                                                                            *)
(* For example:                                                               *)
(* BAG_IMAGE_CONV ``BAG_IMAGE f {|x0; x1; x2; x3; x4|}`` results in           *)
(*                              {|f x0; f x1; f x2; f x3; f x4|}              *)
(******************************************************************************)

fun BAG_IMAGE_CONV___FINITE t =
   let val (f,b) = dest_image t in
   if (is_empty b) then
      let
         val bag_type = bagSyntax.base_type b
	 val finite_thm = INST_TYPE [alpha |-> bag_type] bagTheory.FINITE_EMPTY_BAG;
	 val bag_thm = ISPEC f bagTheory.BAG_IMAGE_EMPTY
      in
	 (finite_thm, bag_thm)
      end
   else if (is_union b) then
      let
         val (b1,b2) = dest_union b;
         val t1 = mk_image (f, b1)
         val t2 = mk_image (f, b2)
         val (finite_thm1, bag_thm1) = BAG_IMAGE_CONV___FINITE t1;
         val (finite_thm2, bag_thm2) = BAG_IMAGE_CONV___FINITE t2;
         val finite_thm12 = CONJ finite_thm1 finite_thm2    

	 val finite_thm = EQ_MP (GSYM (ISPECL [b1,b2] bagTheory.FINITE_BAG_UNION))
                              finite_thm12
	 val bag_thm' = MP (ISPECL [b1,b2,f] bagTheory.BAG_IMAGE_FINITE_UNION) finite_thm12
         val bag_thm'' =  CONV_RULE (RHS_CONV (
              ((RATOR_CONV o RAND_CONV) (K bag_thm1)) THENC
              ((RAND_CONV) (K bag_thm2)))) bag_thm'
      in
	 (finite_thm, bag_thm'')
      end   
   else 
      let
         val (e,b') = dest_insert b;
         val t' = mk_image (f, b')
         val (finite_thm, bag_thm) = BAG_IMAGE_CONV___FINITE t';
	 val finite_thm2 = SPEC e (MP (ISPEC b' bagTheory.FINITE_BAG_INSERT) finite_thm);
	 val bag_thm' = MP (ISPECL [b',f,e]
	       (bagTheory.BAG_IMAGE_FINITE_INSERT)) finite_thm
         val bag_thm2 =  CONV_RULE (RHS_CONV (RAND_CONV 
                   (K bag_thm))) bag_thm'
      in
         (finite_thm2, bag_thm2)
      end
   end handle HOL_ERR _ => raise UNCHANGED;


val BAG_IMAGE_CONV = snd o BAG_IMAGE_CONV___FINITE;


(******************************************************************************)
(* BAG_CARD_CONV                                                              *)
(*                                                                            *)
(* Moves BAG_IMAGE over very simple bags that consists of repeatedly          *)
(* inserting elements into the empty bag. For these bags, it's very easy to   *)
(* show that they are finite.                                                 *)
(*                                                                            *)
(* For example:                                                               *)
(* BAG_IMAGE_CONV ``BAG_IMAGE f {|x0; x1; x2; x3; x4|}`` results in           *)
(*                              {|f x0; f x1; f x2; f x3; f x4|}              *)
(******************************************************************************)

local
   val card_empty_thm = CONJUNCT1 bagTheory.BAG_CARD_THM
   val card_insert_thm = CONV_RULE (DEPTH_CONV RIGHT_IMP_FORALL_CONV)
                               (CONJUNCT2 bagTheory.BAG_CARD_THM)
   val eval_num_RULE = CONV_RULE (RHS_CONV numLib.REDUCE_CONV)

  fun BAG_CARD_CONV___FINITE b =
  (if (is_empty b) then
      let
         val bag_type = bagSyntax.base_type b
	 val finite_thm = INST_TYPE [alpha |-> bag_type] bagTheory.FINITE_EMPTY_BAG;
	 val card_thm = INST_TYPE [alpha |-> bag_type] card_empty_thm;
      in
	 (finite_thm, card_thm)
      end   
   else if (is_union b) then
      let
         val (b1,b2) = dest_union b;
         val (finite_thm1, card_thm1) = BAG_CARD_CONV___FINITE b1;
         val (finite_thm2, card_thm2) = BAG_CARD_CONV___FINITE b2;
         val finite_thm12 = CONJ finite_thm1 finite_thm2    

	 val finite_thm = EQ_MP (GSYM (ISPECL [b1,b2] bagTheory.FINITE_BAG_UNION))
                              finite_thm12
	 val card_thm' = MP (ISPECL [b1,b2] bagTheory.BAG_CARD_UNION) finite_thm12
         val card_thm'' =  CONV_RULE (RHS_CONV (
              ((RATOR_CONV o RAND_CONV) (K card_thm1)) THENC
              ((RAND_CONV) (K card_thm2)))) card_thm'
      in
	 (finite_thm, eval_num_RULE card_thm'')
      end   
   else 
      let
         val (e,b') = dest_insert b;
         val (finite_thm, card_thm) = BAG_CARD_CONV___FINITE b';

	 val finite_thm2 = SPEC e (MP (ISPEC b' bagTheory.FINITE_BAG_INSERT) finite_thm);
	 val card_thm' = MP (ISPECL [b',e] card_insert_thm) finite_thm
         val card_thm2 =  CONV_RULE (RHS_CONV (
              (RATOR_CONV o RAND_CONV) (K card_thm))) card_thm'
      in
         (finite_thm2, eval_num_RULE card_thm2)
      end
   ) handle HOL_ERR _ => raise UNCHANGED;
in
   fun BAG_CARD_CONV tm = 
   let
      val b = dest_card tm
      val (_, thm) = BAG_CARD_CONV___FINITE b
   in
      thm
   end;
end


(******************************************************************************)
(* GET_BAG_IN_THMS                                                            *)
(*                                                                            *)
(* Generates BAG_IN theorems for all elements of very simple bags that        *)
(* consists of repeatedly inserting elements into the empty bag.              *)
(* show that they are finite.                                                 *)
(*                                                                            *)
(* For example:                                                               *)
(* GET_BAG_IN_THMS ``{|x0; x1; x2|}`` results in                              *)
(*                                                                            *)
(* [ |- BAG_IN x0 {|x0; x1; x2|},                                             *)
(*   |- BAG_IN x1 {|x0; x1; x2|},                                             *)
(*   |- BAG_IN x2 {|x0; x1; x2|}]                                             *)
(*                                                                            *)
(******************************************************************************)

local
   val BAG_EVERY_BAG_IN_THM = prove (
      ``!b:'a -> num. BAG_EVERY (\e. BAG_IN e b) b``,
      REWRITE_TAC [bagTheory.BAG_EVERY] THEN
      BETA_TAC THEN REWRITE_TAC[])

   val BAG_EVERY_STEP_CONV = (PART_MATCH lhs (CONJUNCT2 bagTheory.BAG_EVERY_THM))

   fun BAG_EVERY_TO_LIST l thm =
       let
          val thm0 = CONV_RULE BAG_EVERY_STEP_CONV thm
          val thm1 = BETA_RULE (CONJUNCT1 thm0)
       in
          BAG_EVERY_TO_LIST (thm1::l) (CONJUNCT2 thm0)
       end handle HOL_ERR _ => rev l
in
   fun GET_BAG_IN_THMS b =
      BAG_EVERY_TO_LIST [] (ISPEC b BAG_EVERY_BAG_IN_THM)
end;




(******************************************************************************)
(* GET_PRED_PAIR_LIST                                                         *)
(*                                                                            *)
(* Given two bag that just consists of INSERTS and EMPTY_BAG, this functions  *)
(* destructs these bags and searches for pairs of elements that satisfy       *)
(* a given predicate. It returns two lists of element numbers that represent  *)
(* the positions of the found pairs. These lists are suitable to be given to  *)
(* BAG_RESORT_CONV. This function is useful to find pairs and sort them to    *)
(* the front of two bags. It is for example used by SUB_BAG_INSERT_CANCEL_CONV*)
(******************************************************************************)

local
fun find_pairs p nl1 nl2 n [] l2 = (rev nl1, rev nl2)
    | find_pairs p nl1 nl2 n (e::l1) l2 =
    let
       val found_opt = first_opt (fn n2 => fn e2 =>
           if (not (mem n2 nl2)) andalso (p e e2) then
               SOME n2
           else NONE) l2
       val (nl1', nl2') = if isSome found_opt then
           (n::nl1, (valOf found_opt)::nl2) else (nl1, nl2)
    in
      find_pairs p nl1' nl2' (n+1) l1 l2
    end;
in
  fun get_resort_lists___pred_pair p b1 b2 =
  let
     val l1 = fst (strip_insert b1);
     val l2 = fst (strip_insert b2);
  in
     find_pairs p [] [] 0 l1 l2
  end
end;

fun get_resort_positions___pred_pair P b1 b2 =
let
   val l1 = fst (strip_insert b1);
   val l2 = fst (strip_insert b2);

   val found_opt = first_opt (fn n1 => fn e1 =>
       SOME (n1, valOf (first_opt (
         fn n2 => fn e2 => if (P e1 e2) then SOME n2 else NONE) l2))) l1
in
   found_opt
end;

local
   fun get_resort_list___pred_int p n nL [] = rev nL
     | get_resort_list___pred_int p n nL (t::ts) =
       let val nL' = if (p t) then (n::nL) else nL in
          get_resort_list___pred_int p (n+1) nL' ts
       end
in
  fun get_resort_list___pred p t =
  let
     val tl = fst (strip_insert t)
  in
      get_resort_list___pred_int p 0 [] tl
  end
end;

fun get_resort_position___pred p t =
    first_opt (fn n => fn e => if (p e) then SOME n else NONE) (fst (strip_insert t));






(******************************************************************************)
(* SUB_BAG_INSERT_CANCEL_CONV                                                 *)
(*                                                                            *)
(* Eleminates common elements from the two heaps. While bagSimps.CANCEL_CONV  *)
(* eliminates common parts joined with BAG_UNION, this conversion handles     *)
(* BAG_INSERT.                                                                *)
(*                                                                            *)
(* For example:                                                               *)
(* SUB_BAG_INSERT_CANCEL_CONV ``SUB_BAG {|x1;x0;x2'|} {|x0;x1;x2;x3|}``       *)
(* results in                                                                 *)
(*                                                                            *)
(* |- SUB_BAG {|x1;x0;x2'|} {|x0;x1;x2;x3|} =                                 *)
(*    SUB_BAG {|      x2'|} {|      x2;x3|} =                                 *)
(*                                                                            *)
(******************************************************************************)
local
   val sub_bag_empty1 = prove (
     ``!b:'a->num. SUB_BAG EMPTY_BAG b = T``, REWRITE_TAC [bagTheory.SUB_BAG_EMPTY])
   val sub_bag_empty2 = CONJUNCT2 bagTheory.SUB_BAG_EMPTY;
   val sub_bag_refl = prove (
     ``!b:'a -> num. SUB_BAG b b = T``, REWRITE_TAC [bagTheory.SUB_BAG_REFL])

   val conv2 = TRY_CONV (PART_MATCH lhs bagTheory.SUB_BAG_INSERT)
   val conv3 = TRY_CONV (PART_MATCH lhs sub_bag_empty1)
   val conv4 = TRY_CONV (PART_MATCH lhs sub_bag_empty2)
   val conv5 = TRY_CONV (PART_MATCH lhs sub_bag_refl)
in

fun SUB_BAG_INSERT_CANCEL_CONV tm =
   let
      val (b1,b2) = bagSyntax.dest_sub_bag tm
      val (n1L,n2L) = get_resort_lists___pred_pair aconv b1 b2
      val _ = if null n1L then raise UNCHANGED else ();

      val conv1 = ((RATOR_CONV o RAND_CONV) 
                      (BAG_RESORT_CONV n1L)) THENC
                  (RAND_CONV 
                      (BAG_RESORT_CONV n2L))
   in
      (conv1 THENC REPEATC conv2 THENC conv3 THENC conv4 THENC conv5) tm
   end handle HOL_ERR _ => raise UNCHANGED;
end


(******************************************************************************)
(* BAG_DIFF_INSERT_CANCEL_CONV                                                *)
(*                                                                            *)
(* Eleminates common elements from the two heaps. While bagSimps.CANCEL_CONV  *)
(* eliminates common parts joined with BAG_UNION, this conversion handles     *)
(* BAG_INSERT.                                                                *)
(*                                                                            *)
(* For example:                                                               *)
(* BAG_DIFF_INSERT_CANCEL_CONV ``BAG_DIFF {|x0;x1;x2;x3|} {|x1;x0;x2'|}``     *)
(* results in                                                                 *)
(*                                                                            *)
(* |- BAG_DIFF {|x0;x1;x2;x3|} {|x1;x0;x2'|} =                                *)
(*    BAG_DIFF {|      x2;x3|} {|      x2'|}                                  *)
(*                                                                            *)
(* The empty bag is removed as a parameter of diff as well, so                *)
(* BAG_DIFF_INSERT_CANCEL_CONV ``BAG_DIFF {|x0;x1;x2;x3|} {|x1;x0;x2|}``      *)
(* results in                                                                 *)
(*                                                                            *)
(* |- BAG_DIFF {|x0;x1;x2;x3|} {|x1;x0;x2|} =                                 *)
(*             {|         x3|}                                                *)
(******************************************************************************)

local
  val empty_thmL = CONJUNCTS bagTheory.BAG_DIFF_EMPTY
  val empty_thm1 = el 2 empty_thmL
  val empty_thm2 = el 3 empty_thmL
in
fun BAG_DIFF_INSERT_CANCEL_CONV tm =
   let
      val (b1,b2) = bagSyntax.dest_diff tm
      val (n1L,n2L) = get_resort_lists___pred_pair aconv b1 b2
      val _ = if null n1L andalso not (bagSyntax.is_empty b1)
                 andalso not (bagSyntax.is_empty b2) then raise UNCHANGED else ();

      val conv1 = ((RATOR_CONV o RAND_CONV) 
                      (BAG_RESORT_CONV n1L)) THENC
                  (RAND_CONV 
                      (BAG_RESORT_CONV n2L))
      val conv2 = PART_MATCH lhs bagTheory.BAG_DIFF_INSERT_same
      val conv3 = TRY_CONV (PART_MATCH lhs empty_thm1)
      val conv4 = TRY_CONV (PART_MATCH lhs empty_thm2)
 
   in
      (conv1 THENC REPEATC conv2 THENC conv3 THENC conv4) tm
   end handle HOL_ERR _ => raise UNCHANGED;
end





(******************************************************************************)
(* SIMPLE_BAG_NORMALISE_CONV                                                  *)
(*                                                                            *)
(* Combines the conversions for BAG_IMAGE, BAG_DIFF und simplifacations for   *)
(* BAG_UNION to simplifiy bags. The goal is to get a simple bag as the reuslt.*)
(******************************************************************************)

local
  val empty_thmL = CONJUNCTS bagTheory.BAG_DIFF_EMPTY
  val empty_thm1 = el 2 empty_thmL
  val empty_thm2 = el 3 empty_thmL

  fun BIN_OP_CONV c =
     RAND_CONV c THENC (RATOR_CONV o RAND_CONV) c

  val bag_union_insert_thmL = CONJUNCTS (
      CONV_RULE (DEPTH_CONV FORALL_AND_CONV) bagTheory.BAG_UNION_INSERT)
  val bag_union_empty_thmL = CONJUNCTS bagTheory.BAG_UNION_EMPTY

  val bag_union_thm1a = el 1 bag_union_insert_thmL
  val bag_union_thm1b = el 2 bag_union_empty_thmL
  val bag_union_thm2a = el 2 bag_union_insert_thmL
  val bag_union_thm2b = el 1 bag_union_empty_thmL

  val bag_union_conv_step = 
     FIRST_CONV [
        PART_MATCH lhs bag_union_thm2b,
        PART_MATCH lhs bag_union_thm1a,
        PART_MATCH lhs bag_union_thm1b,
        PART_MATCH lhs bag_union_thm2a]

  fun bag_union_conv tm =
      (bag_union_conv_step THENC
       TRY_CONV (RAND_CONV bag_union_conv)) tm

in
fun SIMPLE_BAG_NORMALISE_CONV tm =
   if bagSyntax.is_union tm then
      ((BIN_OP_CONV SIMPLE_BAG_NORMALISE_CONV) THENC
       bag_union_conv) tm
   else if (bagSyntax.is_diff tm) then
      ((BIN_OP_CONV SIMPLE_BAG_NORMALISE_CONV) THENC
        BAG_DIFF_INSERT_CANCEL_CONV) tm
   else if (bagSyntax.is_insert tm) then
      RAND_CONV SIMPLE_BAG_NORMALISE_CONV tm
   else if (bagSyntax.is_image tm) then
      ((RAND_CONV SIMPLE_BAG_NORMALISE_CONV) THENC
       BAG_IMAGE_CONV) tm
   else raise UNCHANGED;
end



(******************************************************************************)
(* BAG_EQ_INSERT_CANCEL_CONV                                                  *)
(******************************************************************************)

local
  val bag_card_eq_thm = prove (
     ``!(b1:'a -> num) b2. ~(BAG_CARD b1 = BAG_CARD b2) ==> ((b1 = b2) = F)``,
       REPEAT GEN_TAC THEN Cases_on `b1 = b2` THEN ASM_REWRITE_TAC[])
in
fun BAG_EQ_INSERT_CANCEL_CONV tm =
   let
      val (b1,b2) = dest_eq tm
      val b1_thm = SIMPLE_BAG_NORMALISE_CONV b1 handle UNCHANGED => REFL b1
      val b2_thm = SIMPLE_BAG_NORMALISE_CONV b2 handle UNCHANGED => REFL b2

      val b1' = rhs (concl b1_thm)
      val b2' = rhs (concl b2_thm)

      val thm_simp = ((RAND_CONV (K b2_thm)) THENC
                     ((RATOR_CONV o RAND_CONV) (K b1_thm))) tm

      val (b1L,b1_rest) = strip_insert b1'
      val (b2L,b2_rest) = strip_insert b2'
   in
      if (not (length b1L = length b2L) andalso
         (bagSyntax.is_empty b1_rest) andalso
         (bagSyntax.is_empty b2_rest)) then
      let
         val thm0 = ISPECL [b1',b2'] bag_card_eq_thm
         val precond = (fst o dest_imp o concl) thm0;

         val precond_thm = EQT_ELIM (
            ((DEPTH_CONV BAG_CARD_CONV) THENC
             numLib.REDUCE_CONV) precond)
         val thm1 = MP thm0 precond_thm
      in
         TRANS thm_simp thm1
      end else let
         val (n1L,n2L) = get_resort_lists___pred_pair aconv b1' b2'
         val _ = if null n1L then raise UNCHANGED else ();
         val conv1 = ((RATOR_CONV o RAND_CONV) 
                         (BAG_RESORT_CONV n1L)) THENC
                      (RAND_CONV (BAG_RESORT_CONV n2L))
         val conv2 = PART_MATCH lhs bagTheory.BAG_INSERT_ONE_ONE
         fun conv3 t = let
                          val (t1,t2) = dest_eq t;
                          val _ = if (aconv t1 t2) then () else raise UNCHANGED;
                       in
                          EQT_INTRO (REFL t1)
                       end handle HOL_ERR _ => raise UNCHANGED;
      in
         CONV_RULE (RHS_CONV
            (conv1 THENC REPEATC conv2 THENC conv3)) thm_simp
      end
   end handle HOL_ERR _ => raise UNCHANGED;
end


(******************************************************************************)
(* SUB_BAG_INSERT_SOLVE                                                       *)
(*                                                                            *)
(* Calls SUB_BAG_INSERT_CANCEL_CONV and assumes that the left heap becomes    *)
(* emty. It then tries to apply SUB_BAG_EMPTY                                 *)
(*                                                                            *)
(******************************************************************************)

local
   val empty_thm = CONJUNCT1 bagTheory.SUB_BAG_EMPTY
in
   fun SUB_BAG_INSERT_SOLVE tm =
   let
      val _ = if bagSyntax.is_sub_bag tm then () else Feedback.fail();

      val thm0 = (RAND_CONV SIMPLE_BAG_NORMALISE_CONV THENC
                  (RATOR_CONV o RAND_CONV) SIMPLE_BAG_NORMALISE_CONV) tm
                 handle UNCHANGED => REFL tm


      val thm1 = CONV_RULE (RHS_CONV SUB_BAG_INSERT_CANCEL_CONV) thm0
   in
      EQT_ELIM thm1
   end;
end;


end;
