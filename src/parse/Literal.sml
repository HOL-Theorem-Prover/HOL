(*---------------------------------------------------------------------------*
 *    Literals for numbers and strings.
 *
 * A numeral is a nest of BIT{1,2}s built up from ALT_ZERO wrapped
 * inside the NUMERAL tag, or it is a straight ZERO constant.  This
 * difference in treatment between zero and the other numerals leaves
 * zero as a constant in the logic, which is useful elsewhere.
 * (Principle of least surprises and all that.)  The use of ALT_ZERO rather
 * than ZERO inside the representations for other numerals means that
 * theorems of the form 0 = x will not match inside other numerals.
 *
 * A string literal is a bit like a list of characters, except that
 * CONS is replaced by STRING and NIL is replaced by EMPTYSTRING.
 *
 *     STRING (CHAR c_0) (STRING ... (STRING (CHAR c_n) EMPTYSTRING) ...)
 *
 * The code in this structure has been generalized to work with
 * terms and also preterms, since it is also used to build preterms
 * by the parser.
 *---------------------------------------------------------------------------*)

structure Literal :> Literal =
struct

open HolKernel;

type num = Arbnum.num;

val ERR = mk_HOL_ERR "Literal";

(*---------------------------------------------------------------------------
                 NUMERALS
 ---------------------------------------------------------------------------*)

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
    Checks if t is 0 or a sequence of applications of BIT1 and BIT2 to ZERO,
    perhaps with an outer application of NUMERAL. In BNF :

     <numeral> ::= 0 | NUMERAL <bits>
     <bits>    ::= ZERO | BIT1 (<bits>) | BIT2 (<bits>)
 ---------------------------------------------------------------------------*)

fun dest_zero t =
 case total dest_thy_const t
  of SOME {Name="0", Thy="num",...} => Arbnum.zero
   | otherwise => raise ERR "dest_zero" "expected 0";

fun dest_ZERO t =
 case total dest_thy_const t
  of SOME {Name="ZERO", Thy="arithmetic",...} => Arbnum.zero
   | otherwise => raise ERR "dest_zero" "expected ZERO";

fun dest_b1 tm =
 case total ((dest_thy_const##I) o dest_comb) tm
  of SOME ({Name="BIT1", Thy="arithmetic",...},t) => t
   | otherwise => raise ERR "dest_b1" "expected BIT1";

fun dest_b2 tm =
 case total ((dest_thy_const##I) o dest_comb) tm
  of SOME ({Name="BIT2", Thy="arithmetic",...},t) => t
   | otherwise => raise ERR "dest_b2" "expected BIT2";

local open Arbnum
in
fun dest_bare_numeral t =
  dest_ZERO t
  handle HOL_ERR _ => two * dest_bare_numeral (dest_b1 t) + one
  handle HOL_ERR _ => two * dest_bare_numeral (dest_b2 t) + two
end

fun dest_numeral tm =
 dest_zero tm
 handle HOL_ERR _ =>
    (case total ((dest_thy_const##I) o dest_comb) tm
      of SOME ({Name="NUMERAL", Thy="arithmetic",...},t)
         => with_exn dest_bare_numeral t
              (ERR "dest_numeral" "term is not a numeral")
       | otherwise => raise ERR "dest_numeral" "term is not a numeral"
    )


(*---------------------------------------------------------------------------
   A "relaxed" numeral is one where the NUMERAL might not be there. These
   occasionally occur, for example when the NUMERAL tag has been rewritten
   away. In BNF :

     <relaxed_numeral> ::= 0 | NUMERAL <bits> | <bits>
     <bits>            ::= ZERO | BIT1 (<bits>) | BIT2 (<bits>)
 ---------------------------------------------------------------------------*)

fun relaxed_dest_numeral tm =
                     dest_numeral tm
 handle HOL_ERR _ => dest_bare_numeral tm
 handle HOL_ERR _ => raise ERR "relaxed_dest_numeral" "term is not a numeral";

val is_zero = Lib.can dest_zero;
val is_ZERO = Lib.can dest_ZERO;
val is_bare_numeral = Lib.can dest_bare_numeral;
val is_numeral = Lib.can dest_numeral;

fun gen_mk_numeral {mk_comb, ZERO, ALT_ZERO, NUMERAL, BIT1, BIT2} n =
 let open Arbnum
     fun positive x =
       if x = zero then ALT_ZERO else
       if x mod two = one
         then mk_comb(BIT1, positive ((x-one) div two))
         else mk_comb(BIT2, positive ((x-two) div two))
 in
   if n=zero then ZERO else mk_comb(NUMERAL,positive n)
 end;

fun mk_numerallit_term n =
    let
      val num_ty = mk_thy_type{Thy = "num", Tyop = "num", Args = []}
      val ALT_ZERO =
          mk_thy_const{Thy = "arithmetic", Name = "ZERO", Ty = num_ty}
      val ZERO = mk_thy_const{Thy = "num", Name = "0", Ty = num_ty}
      fun mkf s =
          mk_thy_const{Thy = "arithmetic", Name = s, Ty = num_ty --> num_ty}
    in
      gen_mk_numeral{mk_comb=mk_comb,ZERO = ZERO, ALT_ZERO= ALT_ZERO,
                     NUMERAL = mkf "NUMERAL", BIT1 = mkf "BIT1",
                     BIT2 = mkf "BIT2"} n
    end

(*---------------------------------------------------------------------------
                  STRINGS
 ---------------------------------------------------------------------------*)

val dest_chr    = sdest_monop ("CHR","string") (ERR "dest_chr" "")
val dest_string = sdest_binop ("CONS","list") (ERR "dest_string" "")
val fromHOLchar = Char.chr o Arbnum.toInt o dest_numeral o dest_chr

val dest_char_lit = fromHOLchar
val is_char_lit = can dest_char_lit

fun is_char_type ty = let
  val {Thy,Tyop,Args} = dest_thy_type ty
in
  Thy = "string" andalso Tyop = "char" andalso null Args
end handle HOL_ERR _ => false

fun is_string_type ty = let
  val {Thy,Tyop,Args} = dest_thy_type ty
in
  Thy = "list" andalso Tyop = "list" andalso List.all is_char_type Args
end handle HOL_ERR _ => false

fun is_emptystring tm =
  case total dest_thy_const tm of
    SOME {Name="NIL",Thy="list",Ty} => is_string_type Ty
  | otherwise => false

fun dest_string_lit tm =
    if is_emptystring tm then ""
    else let
        val (front,e) = Lib.front_last (strip_binop dest_string tm)
      in
        if is_emptystring e then
          String.implode (itlist (cons o fromHOLchar) front [])
        else raise ERR "dest_string_lit" "not terminated by EMPTYSTRING"
      end

val is_string_lit = can dest_string_lit

val paranoid_stringlitpp = ref false
val _ = Feedback.register_btrace
            ("paranoid string literal printing", paranoid_stringlitpp)
fun string_literalpp {ldelim,rdelim} s =
    if not (!paranoid_stringlitpp) then
      ldelim ^ String.toString s ^ rdelim
    else let
        val limit = size s
        fun sub i = String.sub(s,i)
        fun extract(i,c) = String.extract(s,i,c)
        val concat = String.concat
        val toString = String.toString
        fun recurse A lastc start i =
            if i >= limit then
              concat (List.rev(rdelim :: toString (extract(start,NONE))::A))
            else
              case (lastc, sub i) of
                (#"(", #"*") => let
                  val p =
                      toString (extract(start,SOME (i - start - 1))) ^ "(\\042"
                in
                  recurse (p::A) #" " (i + 1) (i + 1)
                end
              | (#"*", #")") => let
                  val p =
                      toString (extract(start,SOME(i - start - 1))) ^ "\\042)"
                in
                  recurse (p::A) #" " (i + 1) (i + 1)
                end
              | (_, c) => recurse A c start (i + 1)
      in
        recurse [ldelim] #" " 0 0
      end

fun delim_pair {ldelim} =
    case ldelim of
        "\"" => {ldelim = "\"", rdelim = "\""}
      | "\194\171" => {ldelim = ldelim, rdelim = "\194\187"}
      | "\226\128\185" => {ldelim = ldelim, rdelim = "\226\128\186"}
      | _ => raise Fail ("delim_pair: bad left delim: "^ldelim)

(*---------------------------------------------------------------------------*)
(* Redefine dest_string_lit to handle cases where c in CHR (c) is either a   *)
(* "bare" numeral or of the form (NUMERAL ...). Used in ML generation.       *)
(*---------------------------------------------------------------------------*)

local
  val fromHOLchar = Char.chr o Arbnum.toInt o relaxed_dest_numeral o dest_chr
in
fun relaxed_dest_string_lit tm =
    if is_emptystring tm then ""
    else let
        val (front,e) = Lib.front_last (strip_binop dest_string tm)
      in
        if is_emptystring e then
          String.implode (itlist (cons o fromHOLchar) front [])
        else raise ERR "relaxed_dest_string_lit"
                       "not terminated by EMPTYSTRING"
      end
end;

fun mk_string_lit {mk_string,fromMLchar,emptystring} s = let
  fun recurse (acc, i) =
      if i < 0 then acc
      else let
          val c = String.sub(s,i)
        in
          recurse (mk_string (fromMLchar c, acc), i - 1)
        end
in
  recurse (emptystring, String.size s - 1)
end

fun mk_charlit_term c =
    let
      val char_ty = mk_thy_type{Args = [], Thy = "string", Tyop = "char"}
      val num_ty = mk_thy_type{Args = [], Thy = "num", Tyop = "num"}
      val CHR_t =
          mk_thy_const{Name = "CHR", Thy = "string", Ty = num_ty --> char_ty}
    in
      c |> Char.ord |> Arbnum.fromInt |> mk_numerallit_term
        |> curry mk_comb CHR_t
    end handle HOL_ERR _ =>
               raise ERR "mk_charlit_term"
                     "Can't build character values in this theory context"

fun mk_stringlit_term s =
    let
      val char_ty = mk_thy_type{Args = [], Thy = "string", Tyop = "char"}
      val string_ty = mk_thy_type{Args = [char_ty], Thy = "list", Tyop = "list"}
      val cons_t = mk_thy_const{Name = "CONS", Thy = "list",
                                Ty = char_ty --> (string_ty --> string_ty)}
      fun mks (t1, t2) = list_mk_comb(cons_t, [t1,t2])
    in
      mk_string_lit {mk_string = mks, fromMLchar = mk_charlit_term,
                     emptystring = mk_thy_const{Name = "NIL", Thy = "list",
                                                Ty = string_ty}}
                    s
    end handle HOL_ERR _ =>
               raise ERR "mk_stringlit_term"
                     "Can't build string values in this theory context"


(*---------------------------------------------------------------------------*)
(* There are other possible literals, e.g. for word[n]. This ref cell is     *)
(* updated when a new class of literals is created. This is used by the      *)
(* function definition package to help process definitions with literals in  *)
(* patterns.                                                                 *)
(*---------------------------------------------------------------------------*)

local
   val literals = ref [is_numeral, is_string_lit, is_char_lit]
in
   fun add_literal is_lit = literals := !literals @ [is_lit]
   fun is_literal tm = List.exists (fn f => f tm) (!literals)
end

fun is_pure_literal x =
  is_literal x andalso not (is_zero x) andalso not (is_string_lit x);


end (* Literal *)
