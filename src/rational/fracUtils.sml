structure fracUtils :> fracUtils =
struct

open HolKernel boolLib bossLib;

structure Parse =
struct
open Parse
val (Type,Term) = parse_from_grammars fracTheory.frac_grammars
end

open Parse pairTheory pairLib integerTheory intLib

(*--------------------------------------------------------------------------
 *  dest_frac : term -> term * term list
 *--------------------------------------------------------------------------*)
fun dest_comb2 t = let val (fx,y) = dest_comb t
                       val (f,x) = dest_comb fx
                   in
                     (f, [x,y])
                   end
fun is_rep_rat t = let val {Thy,Name,...} = dest_thy_const t
                   in
                     Thy = "rat" andalso Name = "rep_rat"
                   end handle HOL_ERR _ => false


fun dest_frac (t1:term) =
  if is_comb t1 then
    let
      val (top_rator, top_rand) = dest_comb t1
    in
      if top_rator ~~ ``abs_frac`` then
        let
          val (this_nmr, this_dnm) = dest_pair (top_rand);
        in
          (``abs_frac``,[this_nmr,this_dnm])
        end
      else
        if top_rator ~~ ``frac_ainv`` orelse top_rator ~~ ``frac_minv`` orelse
           is_rep_rat top_rator
        then
          (top_rator, [top_rand])
        else
          let
            val (f, args) = dest_comb2 t1
          in
            (f, args)
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

val frac_ty = mk_thy_type {Thy = "frac", Tyop = "frac", Args = []}
fun extract_frac t =
    if type_of t = frac_ty then [t]
    else case dest_term t of
             COMB (t1,t2) => op_U aconv [extract_frac t1, extract_frac t2]
           | _ => []

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
      val (top_rator, top_rand) = dest_comb t1
    in
      if top_rator ~~ ``abs_frac`` then [t1]
      else
        op_union aconv (extract_abs_frac top_rator) (extract_abs_frac top_rand)
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

fun ttrip_eq (t1,t2,t3) (ta,tb,tc) =
  pair_eq (pair_eq aconv aconv) aconv ((t1,t2),t3) ((ta,tb),tc)

fun extract_frac_fun (l2:term list) (t1:term) =
  if is_comb t1 then
    let
      val (top_rator, top_rand) = dest_comb t1;
    in
      if tmem top_rator l2 andalso is_comb top_rand then
        let
          val (second_rator, second_rand) = dest_comb top_rand;
        in
          if second_rator ~~ ``abs_frac`` then
            let
              val (this_nmr, this_dnm) = dest_pair (second_rand)
              val sub_fracs =
                  op_union ttrip_eq
                           (extract_frac_fun l2 this_nmr)
                           (extract_frac_fun l2 this_dnm)
            in
                [(top_rator,this_nmr,this_dnm)] @ sub_fracs
            end
          else (* not second_rator = ``abs_frac`` *)
            extract_frac_fun l2 top_rand
        end
      else (* not (top_rator = l2 andalso is_comb top_rand) *)
        op_union ttrip_eq (extract_frac_fun l2 top_rator)
                 (extract_frac_fun l2 top_rand)
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

(*==========================================================================
 * end of structure
 *==========================================================================*)
end;
