(*---------------------------------------------------------------------------
                Parsing datatype specifications
 ---------------------------------------------------------------------------*)

structure ParseDatatype :> ParseDatatype =
struct

fun ERR s1 s2 =
 Exception.HOL_ERR
  {origin_structure = "ParseDatatype",
   origin_function = s1,
   message = s2};


type index = int  (* index in the underlying string. *)
type 'a location = 'a * index;

datatype tyspec_lexeme 
           = eq 
           | geq
           | bar
           | of_tok 
           | semicolon
           | name of string location
           | alien of Char.char location;


val symbolic = Char.contains "$#?+*/\\=<>&%@!:;|-~.," 
val alphanumeric = Char.contains
          "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_'"

local open Option Strm
      fun ERR1 s = raise (ERR "speclex" s)
      fun getname P (ssl,s0) =
         let val (ss1,s1) = splitl P s0
             open Substring
         in 
          (string (span (ssl,ss1)), s1)
         end
in
fun speclex s =
 case get s
  of NONE => NONE
   | SOME (AQ x, s1) => ERR1 "Not expecting an antiquote" (* where? *)
   | SOME (CH c, s1) => 
      if Char.isSpace c then speclex s1
      else
      let val (s,k,_) = base s1
          val i = k-1   (* Need to move back 1 to get index of c *)
      in case c of 
         #"(" => (case get s1 
                   of SOME (CH #"*",s2) => mapPartial speclex (MLcomment s2)
                    | _ => SOME (alien (c,i),s1))
       | otherwise =>
            if symbolic c orelse alphanumeric c
            then let val first = Substring.substring(s,i,1)
                     val pred = if symbolic c then symbolic else alphanumeric
                     val (str,s2) = getname pred (first, s1) 
                 in case str 
                     of "of" => SOME(of_tok, s2)
                      | ";"  => SOME (semicolon,s2) 
                      | "|"  => SOME (bar,s2)  
                      | "="  => SOME (eq,s2)  
                      | "=>" => SOME (geq,s2)  
                      |  _   => SOME (name (str,i), s2)
                 end 
            else SOME (alien(c,i), s1)
       end
end;


(*---------------------------------------------------------------------------*
 * We've already got a type on the stack on entry.                           *
 *---------------------------------------------------------------------------*)
fun gtypes (stk,ss) =
  case speclex ss
   of SOME (geq, rst) => 
        (case Pretype.prs_pretype (0, ([],rst))
          of ([ty],rst1) => gtypes (ty::stk, rst1)
           | _ => raise ERR "gtypes" "expected a single type")
    | _ => (rev stk,ss);


(*---------------------------------------------------------------------------*
 * Have consumed constructor when typel is called. If there's an "of" we     *
 * expect some types to follow. Otherwise, we're at a nullary type           *
 * constructor.                                                              *
 *---------------------------------------------------------------------------*)
fun typel s =
  case speclex s 
   of SOME (of_tok, s1) => gtypes (Pretype.prs_pretype (0, ([],s1)))
    | _ => ([],s);

fun clause s =
  case speclex s 
   of SOME (name(c,i), s1) => (c,typel s1)
    | _ => raise ERR "clause" "expected an (symbolic) identifier";

fun clauses s =
  let val (nm,(l,s1)) = clause s
  in 
    case speclex s1
     of SOME(bar,s2) => let val (C,s3) = clauses s2 in ((nm,l)::C, s3) end
      | _ => ([(nm,l)],s1)
  end;

fun pdatatype s =
 case speclex s
  of NONE => raise ERR "pdatatype" "empty type specification"
   | SOME (name(p,i), s1) =>
      (case speclex s1
        of SOME (eq, s2) => let val (C,s3) = clauses s2 in ((p,C),s3) end
         |  _ => raise ERR "pdatatype" "expected an \"=\" after new type name")
   | SOME _ => raise ERR "pdatatype"
                "expected the type name alone on the left of the equality";


type datatypeAST = string 
                   * ((string * Pretype.ground Pretype.pretype list) list)

fun pdatatypel (L:datatypeAST list) s =
 case speclex s
  of SOME (name _, _) => 
      let val (dtype,s1) = pdatatype s
      in case speclex s1
          of SOME(semicolon,s2) => pdatatypel (dtype::L) s2
           | _ => (rev (dtype::L), s1)
      end
   | _ => raise ERR "pdatatypel" "expecting the name of a type";


fun rawparse strm = pdatatypel [] strm;

fun parse q = 
  let val (astl, s1) = rawparse (Strm.strm_of q)
  in case speclex s1
      of NONE => astl
       | _ => raise ERR "parse" (String.concat 
                  ["unparsed input remains: ", Lib.quote (Strm.string_of s1)])
  end;

(*---------------------------------------------------------------------------
          tests

quotation := true;

parse `foo = NIL | CONS of 'a => 'a foo`;
parse `list = NIL | :: of 'a => list`;
parse `void = Void`;
parse `pair = CONST of 'a#'b`;
parse `onetest = OOOO of one`;
parse `tri = Hi | Lo | Fl`;
parse `iso = ISO of 'a`;
parse `ty = C1 of 'a 
          | C2 
          | C3 of 'a => 'b => ty
          | C4 of ty => 'c => ty => 'a => 'b 
          | C5 of ty => ty`;
parse `bintree = LEAF of 'a | TREE of bintree => bintree`;
parse `typ = C of one 
                  => (one#one) 
                  => (one -> one -> 'a list)
                  => ('a,one#one,'a list) ty`;
parse `Typ = D of one 
                  # (one#one) 
                  # (one -> one -> 'a list)
                  # ('a, one#one, 'a list) ty`;

parse `atexp = var_exp of var
           | let_exp of dec => exp ;

       exp = aexp    of atexp
           | app_exp of exp => atexp
           | fn_exp  of match ;

     match = match  of rule
           | matchl of rule => match ;

      rule = rule of pat => exp ;

       dec = val_dec   of valbind
           | local_dec of dec => dec
           | seq_dec   of dec => dec ;

   valbind = bind  of pat => exp
           | bindl of pat => exp => valbind
           | rec_bind of valbind ;

       pat = wild_pat
           | var_pat of var`;

val state = Type`:ind->bool`;
val nexp  = Type`:^state -> ind`;
val bexp  = Type`:^state -> bool`;

parse `comm = skip 
            | :=    of bool list => ^nexp 
            | ;;    of comm => comm
            | if    of ^bexp => comm => comm
            | while of ^bexp => comm`;

parse `ascii = ASCII of bool=>bool=>bool=>bool=>bool=>bool=>bool=>bool`;
*)

 
end;
