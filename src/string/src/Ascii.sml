(* =====================================================================*)
(* FILE		: ascii_conv.sml					*)
(* DESCRIPTION  : Defines a conv for determining when two ascii values	*)
(*		  are equal.						*)
(*									*)
(* 		  Assumes that ascii is a parent of current thy.	*)
(*									*)
(* AUTHOR	: (c) T. Melham 1988					*)
(* DATE		: 87.05.30						*)
(* REVISED	: 90.10.27						*)
(* TRANSLATOR   : Konrad Slind, University of Calgary                   *)
(* =====================================================================*)


structure Ascii :> Ascii =
struct

open HolKernel Parse boolLib Drule Conv Rsyntax;

fun ASCII_ERR{function, message} = HOL_ERR{origin_structure = "Ascii",
                                           origin_function = function,
                                           message = message};
infix ##;
infix 5 |->;
(* fun (r1 |-> r2) = {redex=r1, residue = r2}; *)

(* --------------------------------------------------------------------- *)
(* ascii_EQ_CONV: decision-procedure for equality of ascii constants.	 *)
(* --------------------------------------------------------------------- *)
local

(* check checks that constructor is indeed ASCII *)
val check = assert (fn c => #Name(dest_const c) = "ASCII")
val T = --`T`--
val F = --`F`--


(* ckargs checks if all args of ASCII are either T or F *)

val ckargs = assert (all (fn tm => tm=T orelse tm=F))


(* strip checks that term is ASCII applied to 8 args, all of which are T or F,
   returns the list of args *)

val strip = snd o (check##ckargs) o strip_comb


(* end result: THM says that if an ASCII combination is equal then
 the args of the ASCII constructor are equal, and VARS are the 16 args of
 the ASCII constructors of the combinations *)

val (thm,vars) = let val th = asciiTheory.ASCII_11
                     val vars = fst(strip_forall(concl th))
               in
               (fst(EQ_IMP_RULE (SPECL vars th)), vars)
               end

(* argument to fc is something like .|- (b0 = b0') /\ ... /\ (b6 = b6') .
 If all these pairs are indeed equal, then it returns the argument,
 else returns the first offending pair *)
fun fc th =
   let val (t,c) = CONJ_PAIR th
       val {lhs, rhs} = dest_eq(concl t)
   in if (lhs=rhs)
      then fc c
      else t
   end handle _ => th;

fun mk_subst (t::terms, v::vars) =
    (v |-> t)::mk_subst (terms, vars)
  | mk_subst ([],[]) = []
  | mk_subst (_, _) = raise ASCII_ERR{function = "ascii_EQ_CONV", message = ""}
in

(* when passed in the term --`ASCII b0 ... b7 = ASCII b0' ... b7'`--,
 ascii_EQ_CONV returns the theorem
 |- (ASCII b0 ... b7 = ASCII b0' ... b7) = Q
 where Q is a T if the terms are indeed equal and Q is a F if not *)

fun ascii_EQ_CONV tm =
    let val {lhs,rhs} = dest_eq tm
        val l = strip lhs
        val r = strip rhs
    in if (l=r)
       then EQT_INTRO(REFL(rand tm))
       else let val cntr = fc(UNDISCH (INST (mk_subst (l@r,vars)) thm))
                val false_thm = EQ_MP (bool_EQ_CONV (concl cntr)) cntr
            in EQF_INTRO (NOT_INTRO (DISCH tm false_thm))
            end
    end
    handle _ => raise ASCII_ERR{function = "ascii_EQ_CONV", message = ""}
end;

(* -------------------------------------------------- TESTS ---
ascii_EQ_CONV (--`ASCII T T T T T T T T = ASCII F F F F F F F F`--);
ascii_EQ_CONV (--`ASCII F F F F F F F F = ASCII T T T T T T T T`--);

ascii_EQ_CONV (--`ASCII T T T T T T T T = ASCII T F F F F F F F`--);
ascii_EQ_CONV (--`ASCII F F F F F F F F = ASCII F T T T T T T T`--);

ascii_EQ_CONV (--`ASCII T T T T T T T T = ASCII T T F F F F F F`--);
ascii_EQ_CONV (--`ASCII F F F F F F F F = ASCII F F T T T T T T`--);

ascii_EQ_CONV (--`ASCII T T T T T T T T = ASCII T T T F F F F F`--);
ascii_EQ_CONV (--`ASCII F F F F F F F F = ASCII F F F T T T T T`--);

ascii_EQ_CONV (--`ASCII T T T T T T T T = ASCII T T T T F F F F`--);
ascii_EQ_CONV (--`ASCII F F F F F F F F = ASCII F F F F T T T T`--);

ascii_EQ_CONV (--`ASCII T T T T T T T T = ASCII T T T T T F F F`--);
ascii_EQ_CONV (--`ASCII F F F F F F F F = ASCII F F F F F T T T`--);

ascii_EQ_CONV (--`ASCII T T T T T T T T = ASCII T T T T T T F F`--);
ascii_EQ_CONV (--`ASCII F F F F F F F F = ASCII F F F F F F T T`--);

ascii_EQ_CONV (--`ASCII T T T T T T T T = ASCII T T T T T T T F`--);
ascii_EQ_CONV (--`ASCII F F F F F F F F = ASCII F F F F F F F T`--);

ascii_EQ_CONV (--`ASCII T T T T T T T T = ASCII T T T T T T T T`--);
ascii_EQ_CONV (--`ASCII F F F F F F F F = ASCII F F F F F F F F`--);

ascii_EQ_CONV (--`ASCII F T F T T F T F = ASCII F T F T T F T F`--);
ascii_EQ_CONV (--`ASCII F T F T T F T F = ASCII F T F T T F T x`--);
-------------------------------------------------------------------*)

end; (* Ascii_EQ_CONV *)
