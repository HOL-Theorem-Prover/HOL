structure fracUtils :> fracUtils =
struct

open HolKernel boolLib Parse bossLib;

(* interactive mode
app load ["pairTheory", "pairLib",
	"integerTheory", "intLib",
	"jbUtils"];
*)

open
	pairTheory pairLib
	integerTheory intLib
	jbUtils;

(*--------------------------------------------------------------------------
 *  dest_frac : term -> term * term list
 *--------------------------------------------------------------------------*)

fun dest_frac (t1:term) =
	if is_comb t1 then
		let
			val (top_rator, top_rand) = dest_comb t1;
		in
			if top_rator=``abs_frac`` then
				let
					val (this_nmr, this_dnm) = dest_pair (top_rand);
				in
					(``abs_frac``,[this_nmr,this_dnm])
				end
			else
				if top_rator=``frac_ainv`` orelse top_rator=``frac_minv`` orelse top_rator=``rep_rat`` then
					(top_rator, [top_rand])
				else
					let
						val (this_op, this_first, this_second) = dest_binop_triple t1;
					in
						(this_op, [this_first, this_second])
					end
		end
	else (* t1 must be a variable *)
		(t1,[])

(* ---------- test cases ---------- *
	dest_frac ``f1:frac``;
	dest_frac ``abs_frac(3i,4i)``;
	dest_frac ``frac_add f1 f2``;
	dest_frac ``frac_add (frac_sub f1 f2) f3``;
	dest_frac ``frac_add (abs_frac(3i,4i)) (abs_frac(4i,5i))``;
 * ---------- test cases ---------- *)

(*--------------------------------------------------------------------------
 *  extract_frac : term -> term list
 *--------------------------------------------------------------------------*)

fun extract_frac (t1:term) =
	extract_terms_of_type ``:frac`` t1;

(* ---------- test cases ---------- *
	extract_frac ``4i + (frac_nmr(abs_frac(3i,4i))) = 3``;
	extract_frac ``frac_add f1 f2 = sub f1 f2``;
	extract_frac ``!f1 f2. nmr (frac_add f1 f2) = frac_dnm (frac_sub f1 f2)``;
	extract_frac ``frac_nmr (frac_add f1 f2) = frac_dnm (frac_sub f1 f2)``;
 * ---------- test cases ---------- *)

(*--------------------------------------------------------------------------
 *  extract_abs_frac : term -> term list
 *--------------------------------------------------------------------------*)

fun extract_abs_frac (t1:term) =
	if is_comb t1 then
		let
			val (top_rator, top_rand) = dest_comb t1;
		in
			if top_rator = ``abs_frac`` then
				[t1]
			else
				list_merge (extract_abs_frac top_rator) (extract_abs_frac top_rand)
		end
	else
		[];

(* ---------- test cases ---------- *
	extract_abs_frac ``abs_rat( abs_frac(1,2) ) + abs_rat (abs_frac(1,3) ) = abs_rat(abs_frac (5,6))``;
	extract_abs_frac ``4i + (frac_nmr(abs_frac(3i,4i))) = 3``;
	extract_abs_frac ``frac_nmr (abs_frac(4,frac_nmr(abs_frac(3,4))))``;
 * ---------- test cases ---------- *)

(*--------------------------------------------------------------------------
 *  extract_frac_fun : term list -> term -> (term * term * term) list
 *--------------------------------------------------------------------------*)

fun extract_frac_fun (l2:term list) (t1:term) =
  if is_comb t1 then
    let
      val (top_rator, top_rand) = dest_comb t1;
    in
      if (in_list l2 top_rator) andalso is_comb top_rand then
        let
          val (second_rator, second_rand) = dest_comb top_rand;
        in
          if second_rator = ``abs_frac`` then
            let
              val (this_nmr, this_dnm) = dest_pair (second_rand);
              val sub_fracs = list_merge (extract_frac_fun l2 this_nmr) (extract_frac_fun l2 this_dnm)
            in
                [(top_rator,this_nmr,this_dnm)] @ sub_fracs
            end
          else (* not second_rator = ``abs_frac`` *)
            extract_frac_fun l2 top_rand
        end
      else (* not (top_rator = l2 andalso is_comb top_rand) *)
        list_merge (extract_frac_fun l2 top_rator) (extract_frac_fun l2 top_rand)
    end
  else (* not is_comb t1 *)
    [];

(* ---------- test cases ---------- *
	extract_frac_fun [``frac_nmr``] ``4i + (nmr(abs_frac(3i,4i)))``;
	extract_frac_fun [``frac_nmr``] ``frac_add (abs_frac(4,frac_nmr(abs_frac(3,4)))) (abs_frac(3,4))``;
	extract_frac_fun [``frac_nmr``] ``frac_nmr(abs_frac(3,4)) + frac_dnm(abs_frac(4,5))``;
	extract_frac_fun [``frac_nmr``] ``frac_nmr (abs_frac(4,frac_nmr(abs_frac(3,4))))``;
	extract_frac_fun [``frac_nmr``] ``frac_nmr (abs_frac(4,frac_nmr(abs_frac(3,4))))``;
	extract_frac_fun [``frac_nmr``,``frac_dnm``] ``nmr(abs_frac(3,4)) + dnm(abs_frac(4,5))``;
 * ---------- test cases ---------- *)

(*--------------------------------------------------------------------------
 *  INT_GT0_CONV : conv
 *
 *    t1          (with t1 greater than zero)
 *   -----------
 *    |- 0 < t1
 *--------------------------------------------------------------------------*)

fun INT_GT0_CONV (t1:term) =
	EQT_ELIM (intLib.ARITH_CONV ``0 < ^t1``);

(*==========================================================================
 * end of structure
 *==========================================================================*)
end;
