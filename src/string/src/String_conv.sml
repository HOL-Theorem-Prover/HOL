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

open HolKernel boolLib Rsyntax

fun STRING_CONV_ERR m = HOL_ERR{origin_structure="String_conv",
                                origin_function = "string_CONV",
                                message = m};

(* ---------------------------------------------------------------------*)
(* string_CONV  "defines" the infinite family of constants:		*)
(*									*)
(*	'a'  = STRING(ASCII F T T F F F F T) ""				*)
(*	'ab' = STRING(ASCII F T T F F F F T) "b"			*)
(*									*)
(*	 ... etc							*)
(*									*)
(* The auxiliary function bits n m computes the representation in n 	*)
(* bits of m (MOD 2**n)							*)
(* ---------------------------------------------------------------------*)

local val T = Parse.Term `T`
      and F = Parse.Term `F`
      and A = Parse.Term `ASCII`
      val STRING = Parse.Term`STRING`
      fun bits 0 _ = []
        | bits n m =
           let val hm = m div 2
            in (if (hm*2 = m) then F else T) :: (bits (n-1) hm)
            end
      val string_CONV_tag = Tag.read"string_CONV"
in
fun string_CONV tm =
 let val {Name=str, Ty=ty} = dest_const tm
     val _ = assert (fn t => #Tyop(dest_type t) = "string") ty
 in
 if (str = "emptystring") then raise STRING_CONV_ERR "empty string"
 else
 case String.explode str
  of (#"\""::h::t) =>
        let val code = rev (bits 8 (Char.ord h))
            val tm1 = mk_comb {Rator=STRING, Rand=list_mk_comb(A,code)}
            val def = mk_comb {Rator=tm1,
                Rand=mk_const{Name=String.implode (#"\""::t),Ty=ty}}
        in
           Thm.mk_oracle_thm string_CONV_tag ([], mk_eq{lhs=tm, rhs=def})
        end
   | _ => raise STRING_CONV_ERR "badly formed string literal"
 end
 handle e as HOL_ERR{origin_function = "string_CONV",...} => raise e
        | _ => raise STRING_CONV_ERR ""
end;

end; (* String_conv *)
