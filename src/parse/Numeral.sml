(*---------------------------------------------------------------------------*
 *    Numerals
 *
 * A numeral is a nest of NUMERAL_BIT{1,2}s built up from ALT_ZERO wrapped
 * inside the NUMERAL tag, or it is a straight ZERO constant.  This
 * difference in treatment between zero and the other numerals leaves
 * zero as a constant in the logic, which is useful elsewhere.
 * (Principle of least surprises and all that.)  The use of ALT_ZERO rather
 * than ZERO inside the representations for other numerals means that
 * theorems of the form 0 = x will not match inside other numerals.
 *---------------------------------------------------------------------------*)

structure Numeral :> Numeral =
struct

open Feedback HolKernel;

type num = Arbnum.num;

fun ERR f s = HOL_ERR
 {origin_structure="Numeral",
  origin_function=f, message=s};


fun is_numtype ty =
   if Type.is_vartype ty then false
   else case Type.dest_thy_type ty
         of {Thy="num",Tyop="num", Args=[]} => true
          | _ => false

fun is_num2num_type ty = 
   let val (ty1,ty2) = Type.dom_rng ty
   in is_numtype ty1 andalso is_numtype ty2
   end handle HOL_ERR _ => false;

(*---------------------------------------------------------------------------
      Checks if t is a sequence of applications of NUMERAL_BIT1 
      and NUMERAL_BIT2 to ALT_ZERO 
 ---------------------------------------------------------------------------*)

fun is_nb t =
   if is_const t 
   then let val {Name, Thy, Ty} = dest_thy_const t
        in Name = "ALT_ZERO" andalso Thy="arithmetic" andalso is_numtype Ty
        end
   else let val {Rand, Rator} = dest_comb t
            val {Name, Thy, Ty} = dest_thy_const Rator
        in (Name="NUMERAL_BIT1" orelse Name="NUMERAL_BIT2") 
            andalso Thy = "arithmetic"
            andalso is_num2num_type Ty andalso is_nb Rand
        end

fun is_numeral t = 
  if is_const t 
  then let val {Name,Thy,Ty} = dest_thy_const t
       in is_numtype Ty andalso Name = "0" andalso Thy="num"
       end
  else let val {Rator,Rand} = dest_comb t
           val {Name,Thy,Ty} = dest_thy_const Rator
       in Name="NUMERAL" andalso Thy="arithmetic" 
          andalso is_num2num_type Ty andalso is_nb Rand
       end handle HOL_ERR _ => false;


(* Seems wrong - does recurse check that the nest ends in ALT_ZERO? *)

fun dest_numeral t =
  if not(is_numeral t) then raise ERR "dest_numeral" "Term is not a numeral"
  else
  if is_const t then Arbnum.zero
  else 
  let open Arbnum
      fun dest t =
         if is_comb t 
         then let val {Rator, Rand} = dest_comb t
              in case #Name(dest_const Rator) 
                  of "NUMERAL_BIT1" => two * dest Rand + one
                   | "NUMERAL_BIT2" => two * dest Rand + two
                   | _ => raise ERR "dest_numeral" 
                                    "This should never ever happen"
              end
         else zero
  in
     dest (rand t)
   end;

fun gen_mk_numeral {mk_comb, ZERO, ALT_ZERO, NUMERAL, BIT1, BIT2} n =
 let open Arbnum
     fun positive x =
       if x = zero then ALT_ZERO else 
       if x mod two = one 
         then mk_comb{Rator=BIT1, Rand=positive ((x-one) div two)}
         else mk_comb{Rator=BIT2, Rand=positive ((x-two) div two)}
 in
  if n=zero then ZERO else mk_comb{Rator=NUMERAL, Rand=positive n}
 end;


end (* Numeral *)
