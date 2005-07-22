(* ===================================================================== *)
(* FILE          : Lexis.sml                                             *)
(* DESCRIPTION   : predicates defining various lexical classes for HOL:  *)
(*                                                                       *)
(*                     1. type variables                                 *)
(*                     2. type constants                                 *)
(*                     3. term constants                                 *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* REVISED       : October,   1994, to improve efficiency.               *)
(* MODIFIED      : September 22, 1997, Ken Larsen                        *)
(* ===================================================================== *)

structure Lexis :> Lexis =
struct

val ERR = Feedback.mk_HOL_ERR "Lexis";

(*---------------------------------------------------------------------------
 * Here we use extra space to get better runtimes. Strings are not exploded;
 * finding out whether a string belongs in a particular syntax class is done
 * by checking that the ordinal of each character in the string is the
 * index (in a particular bytearray) of a box containing a 1.
 *
 * We work only with ascii characters, so we allocate bytearrays of size 128.
 * A bytearray is compact - each element of the array occupies only 1 byte.
 * Since we are using only 0 and 1, we could probably use "bit"arrays, but
 * sheer laziness prevents us.
 *
 * Portability hack by Ken Larsen, bzero is the representation of a byte/bit
 * zero, bone is the representation of one.
 *
 *---------------------------------------------------------------------------*)


val bzero = 0wx0 : Word8.word
val bone  = 0wx1 : Word8.word

val ordof = Portable.ordof;

val hol_symbols   = Word8Array.array(128,bzero);
val sml_symbols   = Word8Array.array(128,bzero);
val alphabet      = Word8Array.array(128,bzero);
val numbers       = Word8Array.array(128,bzero);
val tyvar_ids     = Word8Array.array(128,bzero);
val alphanumerics = Word8Array.array(128,bzero);
val parens        = Word8Array.array(128,bzero);

fun setup table P =
   Lib.for_se 0 127
     (fn i => if P(Char.chr i) then Word8Array.update(table,i,bone) else ());

(*---------------------------------------------------------------------------
 * Utility for examining the contents of character tables
 *
 * fun accum table =
 *    implode
 *      (Lib.for 0 127
 *      (fn i => if (Word8Array.sub(table,i) = bone) then chr i
                 else ""));
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * Various familiar predicates, used only to build the tables, so we can
 * afford to write them naively.
 *---------------------------------------------------------------------------*)

val is_alphabetic = Char.isAlpha
val is_numeric    = Char.isDigit

fun is_alphanumeric #"_" = true
  | is_alphanumeric #"'" = true
  | is_alphanumeric ch = Char.isAlphaNum ch

fun is_paren #"(" = true
  | is_paren #")" = true
  | is_paren _ = false;


(*---------------------------------------------------------------------------
 * Used for type variables, in which a prime is required in the first
 * position in the string, but allowed nowhere else.
 *---------------------------------------------------------------------------*)

fun is_alphanumeric_no_prime ch =
   is_alphabetic ch orelse is_numeric ch orelse ch = #"_";

fun in_string str =
   let val strlist = String.explode str
       val memb = Lib.C Lib.mem strlist
   in memb
   end;

val hol_symbolics = "#?+*/\\=<>&%@!,:;_|~-";
val sml_symbolics = "!%&$+/:<=>?@~|#*\\-~^";
val is_hol_symbol = in_string hol_symbolics
val is_sml_symbol = in_string sml_symbolics;

(* Build the character tables *)

val _ = setup hol_symbols is_hol_symbol;
val _ = setup sml_symbols is_sml_symbol;
val _ = setup alphabet is_alphabetic;
val _ = setup numbers is_numeric;
val _ = setup alphanumerics is_alphanumeric;
val _ = setup tyvar_ids is_alphanumeric_no_prime;
val _ = setup parens is_paren;


fun in_class(table,i) = (Word8Array.sub(table,i) = bone)
                         handle _ => false;

(*---------------------------------------------------------------------------
 * Now for the efficient string predicates. Generally, the empty string
 * is not allowed.
 *---------------------------------------------------------------------------*)

fun ok_identifier str =
   let fun loop i = (Word8Array.sub(alphanumerics,ordof(str,i)) = bone)
                     andalso loop(i+1)
   in
   ((Word8Array.sub(alphabet,ordof(str,0)) = bone) handle _ => false)
   andalso
   (loop 1 handle _ => true)
   end;


val allowed_type_constant = ok_identifier;

local val prime = ordof("'",0)
in
fun allowed_user_type_var str =
   let fun loop i = (Word8Array.sub(tyvar_ids,ordof(str,i)) = bone)
                     andalso loop(i+1)
   in
   ((ordof(str,0) = prime) handle _ => false)
   andalso
   ((Word8Array.sub(alphabet,ordof(str,1)) = bone) handle _ => false)
   andalso
   (loop 2 handle _ => true)
   end
end;


fun ok_symbolic str =
   let fun loop i = (Word8Array.sub(hol_symbols,ordof(str,i)) = bone)
                     andalso loop(i+1)
   in
   ((Word8Array.sub(hol_symbols,ordof(str,0)) = bone)
    handle _ => false)
   andalso
   (loop 1 handle _ => true)
   end;

fun ok_sml_identifier str =
  let val sub = Word8Array.sub
      fun alphaloop i =
             (sub(alphanumerics,ordof(str,i)) = bone) andalso alphaloop(i+1)
      fun symloop i =
             (sub(sml_symbols,ordof(str,i)) = bone) andalso symloop(i+1)
   in
     if ((sub(alphabet,ordof(str,0)) = bone) handle _ => false)
     then (alphaloop 1 handle _ => true)
     else if ((sub(sml_symbols,ordof(str,0)) = bone) handle _ => false)
          then (symloop 1 handle _ => true)
          else false
   end;


(*---------------------------------------------------------------------------
 * Predicate to tell if a prospective constant to-be-defined has an
 * acceptable name. Note that this function does not recognize members of
 * constant families (just those that serve to define such families).
 *---------------------------------------------------------------------------*)

fun allowed_term_constant "let"        = false
  | allowed_term_constant "in"         = false
  | allowed_term_constant "and"        = false
  | allowed_term_constant "of"         = false
  | allowed_term_constant "\\"         = false
  | allowed_term_constant ";"          = false
  | allowed_term_constant "=>"         = false
  | allowed_term_constant "|"          = false
  | allowed_term_constant ":"          = false
  | allowed_term_constant ":="         = false
  | allowed_term_constant "with"       = false
  | allowed_term_constant "updated_by" = false
  | allowed_term_constant "0"          = true  (* only this numeral is OK *)
  | allowed_term_constant str =
    if Word8Array.sub(alphabet,ordof(str,0)) = bone then ok_identifier str else
    if Word8Array.sub(hol_symbols,ordof(str,0)) = bone then ok_symbolic str
    else false;


(*---------------------------------------------------------------------------
 * Strings representing negative integers return false, since we are only
 * (currently) interested in :num.
 *---------------------------------------------------------------------------*)

fun is_num_literal str =
   let fun loop i =
         (Word8Array.sub(numbers,ordof(str,i)) = bone) andalso loop(i+1)
   in
   ((Word8Array.sub(numbers,ordof(str,0)) = bone) handle _ => false)
   andalso
   (loop 1 handle _ => true)
   end;

local val dquote = #"\""
in
fun is_string_literal s = String.size s > 1
    andalso (String.sub(s,0) = dquote)
    andalso (String.sub(s,String.size s - 1) = dquote)
fun is_char_literal s = String.size s = 4 andalso
                        String.sub(s,0) = #"#" andalso
                        String.sub(s,1) = dquote andalso
                        String.sub(s,size s - 1) = dquote
end;




(*---------------------------------------------------------------------------*
 * Renaming support. We allow renaming by priming, and by attaching          *
 * numeric subscripts.                                                       *
 *---------------------------------------------------------------------------*)

local fun num2name s i = s^Lib.int_to_string i
      fun subscripts x s =
        let val project = num2name (s^x)
            val cnt = ref 0
            fun incr() = (cnt := !cnt + 1; project (!cnt))
        in incr
        end
      fun primes s =
        let val current = ref s
            fun next () = (current := Lib.prime (!current); !current)
        in next
        end
in
fun nameStrm s =
  (case !Globals.priming of NONE => primes | SOME x => subscripts x) s
end;


(*---------------------------------------------------------------------------
   String variants, on type variables and term variables. Each,
   given a string produce another one that is different, but which is in
   some sense the "next" string in a sequence.

    `tyvar_vary' can be used to generate  'a, 'b, 'c ... 'z, 'a0 ...

    `tmvar_vary' can be used to generate f, f0, f1, f2, f3 ...

     A call to

       gen_variant f avoids s

     uses a varying function such as the two given here to produce a variant
     of s that doesn't appear in the list avoids.
 ---------------------------------------------------------------------------*)

fun tyvar_vary s =
 let open Substring
     val ss = all s
     val (nonletters, letters) = splitr Char.isAlpha ss
     val szletters = size letters
 in
  if szletters > 0
  then case sub(letters, szletters - 1)
        of #"z" => concat [nonletters,
                           slice(letters, 0, SOME (szletters - 1)),
                           all "a0"]
         | #"Z" => concat [nonletters,
                           slice(letters, 0, SOME (szletters - 1)),
                           all "a0"]
         | c => concat [nonletters,
                        slice(letters, 0, SOME (szletters - 1)),
                        all (str (chr (ord c + 1)))]
  else let val (nondigits, digits) = splitr Char.isDigit ss
           val szdigits = size digits
       in
        if szdigits > 0
        then let val n = valOf (Int.fromString (string digits))
             in concat [nondigits, all (Int.toString (n + 1))]
             end
        else concat [nondigits, all "0"]
       end
 end

fun tmvar_vary s =
 let open Substring
     val ss = all s
     val (nondigits, digits) = splitr Char.isDigit ss
 in
   if size digits > 0
   then let val n = valOf (Int.fromString (string digits))
        in concat [nondigits, all (Int.toString (n + 1))]
        end
  else concat [nondigits, all "0"]
end

fun gen_variant vfn avoids s =
  if Lib.mem s avoids then gen_variant vfn avoids (vfn s) else s

end; (* Lexis *)
