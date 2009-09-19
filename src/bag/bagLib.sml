structure bagLib :> bagLib =
struct

open HolKernel boolLib bossLib

local open bagTheory in end

open bagSyntax bagSimps




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
	 val finite_thm = INST_TYPE [alpha |-> bag_type] FINITE_EMPTY_BAG;
	 val bag_thm = ISPEC f bagTheory.BAG_IMAGE_EMPTY
      in
	 (finite_thm, bag_thm)
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


end;
