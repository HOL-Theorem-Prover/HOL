(* =====================================================================*)
(* FILE		 : string_conv.ml                                       *)
(* DESCRIPTION   : define the axiom scheme for character strings.	*)
(*									*)
(*									*)
(* AUTHOR	: T. Melham						*)
(* DATE		: 87.08.23						*)
(* REVISED	: 90.10.27						*)
(* TRANSLATOR   : Konrad Slind, University of Calgary                   *)
(* =====================================================================*)

structure String_conv :> String_conv =
struct

open HolKernel boolLib 

val ERR = mk_HOL_ERR "String_conv" "string_CONV";

(* ---------------------------------------------------------------------*)
(* string_CONV  "defines" the infinite family of constants:		*)
(*									*)
(*	'a'  = STRING(ASCII F T T F F F F T) ""				*)
(*	'ab' = STRING(ASCII F T T F F F F T) "b"			*)
(*									*)
(*	 ... etc							*)
(*									*)
(* The auxiliary function bits n m computes the representation in n 	*)
(* bits of m MOD (2**n)							*)
(* ---------------------------------------------------------------------*)

local val A = Parse.Term `ASCII`
      val STRING = Parse.Term`STRING`
      fun bits 0 _ = []
        | bits n m =
           let val hm = m div 2
            in (if (hm*2 = m) then F else T) :: bits (n-1) hm
            end
      val string_CONV_tag = Tag.read"string_CONV"
      val string_thm = Thm.mk_oracle_thm string_CONV_tag  
in
fun string_CONV tm =
 let val (str,ty) = dest_const tm
     val _ = assert (fn t => fst(dest_type t) = "string") ty
 in if str="emptystring" then raise ERR "empty string"
 else
 case String.explode str
  of #"\""::h::t =>
      let val code = rev (bits 8 (Char.ord h))
          val def = mk_comb(mk_comb(STRING, list_mk_comb(A,code)),
                            mk_const(String.implode (#"\""::t),ty))
        in string_thm ([], mk_eq(tm,def))
        end
   | _ => raise ERR "badly formed string literal"
 end
 handle e => raise (wrap_exn "String_conv" "string_CONV" e)
end;

end; (* String_conv *)
