structure ParseDoc :> ParseDoc =
struct

open Substring;
exception ParseError of string

fun I x = x;

fun curry f x y = f (x,y)
fun equal x y = (x=y)
infix ##;
fun (f##g) (x,y) = (f x, g y);

fun butlast [] = raise Fail "butlast"
  | butlast [x] = []
  | butlast (h::t) = h::butlast t;

fun flat [] = []
  | flat ([]::rst) = flat rst
  | flat ((h::t)::rst) = h::flat(t::rst);

infixr 4 \/
infixr 5 /\
fun (f \/ g) x = f x orelse g x
fun (f /\ g) x = f x andalso g x;

fun occurs s ss = not (isEmpty (#2 (position s ss)));

fun fetch_contents docfile =
  let val istrm = TextIO.openIn docfile
      val contents = Substring.all (TextIO.inputAll istrm)
      val _ = TextIO.closeIn istrm
  in contents
  end;

fun fetch str = Substring.string (fetch_contents str);

(*---------------------------------------------------------------------------
       A HOL ".doc" file has the format

         \DOC <ident>

         ( \<keyword> <paragraph>* )*

         \ENDDOC
 ---------------------------------------------------------------------------*)

datatype markup
   = PARA
   | TEXT of substring
   | BRKT of substring
   | XMPL of substring;

datatype section
   = TYPE of substring
   | FIELD of string * markup list
   | SEEALSO of substring list;


val valid_keywords =
    Binaryset.addList(Binaryset.empty String.compare,
                      ["DOC", "ELTYPE", "BLTYPE", "TYPE", "SYNOPSIS",
                       "COMMENTS", "USES", "SEEALSO", "KEYWORDS", "DESCRIBE",
                       "FAILURE", "EXAMPLE", "ENDDOC", "LIBRARY",
                       "STRUCTURE"])

local val noindent = Substring.all "noindent"
      val noindent_size = Substring.size noindent
in
fun noindent_elim (ss1::ss2::rst) =
     let val (ssa,ssb) = position "noindent" ss2
     in if isEmpty ssa
          then noindent_elim (all (concat[ss1, triml noindent_size ssb])::rst)
          else ss1::noindent_elim (ss2::rst)
     end
  | noindent_elim l = l
end;

fun divide ss =
  if isEmpty ss
    then []
    else let val (ss1,ss2) = position "\n\\" ss
         in
           if isEmpty ss1 then divide (triml 2 ss2)
           else ss1::divide (triml 2 ss2)
         end;

local val BLTYPE = Substring.all "BLTYPE"
      val ELTYPE = Substring.all "ELTYPE"
      val TYPEss = Substring.all "TYPE"
      val BLTYPEsize = Substring.size ELTYPE
in
fun longtype_elim (l as (doc::ss1::ss2::rst)) =
     let val (ssa,ssb) = position "BLTYPE" ss1
         val (ssc,ssd) = position "ELTYPE" ss2
     in if isEmpty ssa andalso isEmpty ssc
          then doc :: all(concat[TYPEss, triml BLTYPEsize ssb]) :: rst
          else l
     end
  | longtype_elim l = l
end;

fun warn s = TextIO.output(TextIO.stdErr, s)

fun find_doc ss = let
  val (ssa, ssb) = position "\\DOC" ss
  val _ = not (isEmpty ssb) orelse raise ParseError "No \\DOC beginning entry"
  val _ = isEmpty ssa orelse raise ParseError "Text before \\DOC"
  val (docpart, rest) = position "\n" ss
  val docheader = slice(docpart, 1, NONE)
  val _ = size docheader > 4 orelse raise ParseError "Empty \\DOC part"
in
  (docheader, slice(rest,1,NONE))
end

fun to_sections ss =
  let open Substring
      val (docpart, rest) = find_doc ss
      val sslist = docpart :: divide rest
      (* butlast below drops final \enddoc *)
      val sslist1 = noindent_elim (longtype_elim (butlast sslist))
  in
   map ((string##dropl Char.isSpace) o splitl (not o Char.isSpace)) sslist1
  end;

(*---------------------------------------------------------------------------
        Divide into maximal chunks of text enclosed by braces.
 ---------------------------------------------------------------------------*)

fun braces ss =
  case getc ss of
    SOME(#"}", ss1) => let
    in
      case getc ss1 of
        SOME(#"}", ss2) => braces ss2
      | _ => ss1
    end
  | SOME(_, ss1) => braces ss1
  | NONE => raise ParseError "No closing brace"


fun markup ss =
 let val (ssa,ssb) = position "{" ss
 in if isEmpty ssb then [TEXT ss]
    else let val ssc = braces ssb
             val (s,i,n) = base ssa
             val (_,j,_) = base ssc
             val chunk = substring (s,i+n+1,j-(i+n+2))
         in TEXT ssa
             :: (if occurs "\n" chunk then XMPL chunk else BRKT chunk)
             :: markup ssc
         end
 end;

val paragraphs =
  let fun para (TEXT ss) =
           let fun insP ss =
                let val (ssa,ssb) = position "\n\n" ss
                in if isEmpty ssb then [TEXT ss]
                   else TEXT ssa::PARA::insP (dropl Char.isSpace ssb)
                end
           in insP ss
           end
        | para other = [other]
  in flat o map para
  end;


(* Rejects singleton braces wherever they might appear.  Doesn't require
   doubled braces to balance. *)
fun elim_double_braces ss = let
  fun isBrace c = c = #"{" orelse c = #"}"
  fun recurse acc ss = let
    val (ssa, ssb) = splitl (not o isBrace) ss
  in
    case size ssb of
      0 => concat (rev (ssa::acc))
    | 1 => raise ParseError "singleton brace in {}-delimited text"
    | _ => if sub(ssb,0) <> sub(ssb,1) then
             raise ParseError "singleton brace in {}-delimited text"
           else let
               val (s,j,n) = base ssa
               val (s,k,m) = base ssb
             in
               recurse (substring(s,j,n+1)::acc) (substring(s,k+2,m-2))
             end
  end
in
  all (recurse [] ss)
end

fun parse_type ss =
 let val ss' =
      case getc (dropl Char.isSpace ss)
       of SOME(#"{", ss1) =>
           let val ss2 = dropr Char.isSpace ss1
           in if sub(ss2,size ss2 - 1) = #"}" then trimr 1 ss2
              else raise ParseError "Closing brace not found in \\TYPE"
           end
        | other => ss
  in elim_double_braces ss'
  end

fun trimws [] = []
  | trimws [TEXT ss] = [TEXT (dropr Char.isSpace ss)]
  | trimws (x::xs) = x :: trimws xs

fun parse_file docfile =
 let fun db_out (BRKT ss) = BRKT (elim_double_braces ss)
       | db_out (XMPL ss) = XMPL (elim_double_braces ss)
       | db_out otherwise = otherwise

     fun section (tag, ss) =
       case tag
        of "TYPE" => TYPE (parse_type ss)
         | "SEEALSO" => SEEALSO
                          (tokens (Char.isSpace \/ equal #",")
                             (dropr (Char.isSpace \/ equal #".") ss))
         | otherwise =>
           FIELD (tag, trimws (List.map db_out (paragraphs (markup ss))))
  in
     List.map section (to_sections (fetch_contents docfile))
  end handle ParseError s => raise ParseError (docfile^": "^s)
           | x => (warn ("Exception raised in "^docfile^"\n"); raise x)

end; (* struct *)