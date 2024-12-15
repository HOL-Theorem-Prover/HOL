structure ratUtils :> ratUtils =
struct

open HolKernel boolLib Parse bossLib;

open pairTheory pairLib integerTheory intLib

structure Parse =
struct
 open Parse
 val (Type,Term) = parse_from_grammars fracTheory.frac_grammars
end;


(*--------------------------------------------------------------------------
 *  dest_rat : term -> term * term list
 *--------------------------------------------------------------------------*)

fun dest_rat (t1:term) =
  if is_comb t1 then
    let
      val (top_rator, top_rand) = dest_comb t1
    in
      if top_rator ~~ ``abs_rat`` then (``abs_rat``,[top_rand])
      else
        (* Hier gibt es noch Probleme: X (v1:vec) ist auch vom Typ rat *)
        if top_rator ~~ ``rat_ainv`` orelse top_rator ~~ ``rat_minv`` orelse
           top_rator ~~ ``X`` orelse top_rator ~~ ``Y``
        then
          (top_rator, [top_rand])
        else
          let
            val (f, xs) = strip_comb t1
            val _ = length xs = 2 orelse
                    raise mk_HOL_ERR "ratUtils" "dest_rat" "Not binary"
          in
            (f, xs)
          end
    end
  else (* t1 must be a variable *)
    (t1,[])

(* ---------- test cases ---------- *
        dest_rat ``r1:rat``;
        dest_rat ``abs_rat( abs_frac(3i,4i) )``;
        dest_rat ``rat_add r1 r2``;
        dest_rat ``rat_add (rat_sub r1 r2) r3``;
        dest_rat ``rat_add (abs_rat(abs_frac(3i,4i))) (abs_rat(abs_frac(4i,5i)))``;
 * ---------- test cases ---------- *)


(*--------------------------------------------------------------------------
 *  extract_rat : term -> term list
 *--------------------------------------------------------------------------*)

fun extract_rat (t1:term) =
    let val s =
            find_maximal_terms (fn t => type_of t = “:rat” orelse is_abs t) t1
    in
      s |> HOLset.filter (not o is_abs) |> HOLset.listItems
    end


(* ---------- test cases ---------- *
        extract_rat ``4i + (rat_nmr(abs_rat(abs_frac(3i,4i)))) = 3``;
        extract_rat ``rat_add r1 r2 = rat_sub r1 r2``;
        extract_rat ``!r1 r2. rat_nmr (rat_add r1 r2) = rat_dnm (rat_sub r1 r2)``;
        extract_rat ``rat_nmr (rat_add r1 r2) = rat_dnm (rat_sub r1 r2)``;
 * ---------- test cases ---------- *)

(*--------------------------------------------------------------------------
 *  rat_vars_of_term : term -> term list
 *--------------------------------------------------------------------------*)

fun extract_rat_vars t1 =
        filter (fn t => type_of t=``:rat``) (free_vars t1);

(*--------------------------------------------------------------------------
 *  extract_rat_equations : term -> term list
 *--------------------------------------------------------------------------*)

fun extract_rat_equations (t1:term) =
        if (is_comb t1) then
                if (is_eq t1) andalso (type_of (fst (dest_eq t1)) = ``:rat``) then
                        [t1]
                else
                        let val (ta,tb) = dest_comb t1 in
                                (extract_rat_equations ta) @ (extract_rat_equations tb)
                        end
        else
                [];


(*--------------------------------------------------------------------------
 *  extract_rat_minv : term -> term list
 *--------------------------------------------------------------------------*)

fun extract_rat_minv (t1:term) =
  if (is_comb t1) then
    if rator t1 ~~ ``rat_minv`` then [t1]
    else
      let
        val (ta,tb) = dest_comb t1
      in
        tunion (extract_rat_minv ta) (extract_rat_minv tb)
      end
  else
    [];

(*==========================================================================
 * end of structure
 *==========================================================================*)
end;
