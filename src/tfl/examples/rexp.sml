(*---------------------------------------------------------------------------*)
(* Regular expressions and a regexp matcher.                                 *)
(*---------------------------------------------------------------------------*)

app load ["stringLib", "metisLib"]; open metisLib;

(*---------------------------------------------------------------------------*)
(* Datatype of regular expressions                                           *)
(*---------------------------------------------------------------------------*)

Hol_datatype `regexp = Any                       (* Any character *)
                     | Epsilon                   (* Empty string *)
                     | Atom of char              (* Specific character *)
                     | Or of regexp => regexp    (* Union *)
                     | Then of regexp => regexp  (* Concatenation *)
                     | Repeat of regexp`;        (* Iterated concat, >= 0 *)

(*---------------------------------------------------------------------------*)
(* Following mysterious invocations remove old-style syntax for conditionals *)
(* from the grammar and thus allow | to be used for "or" patterns.           *)
(*---------------------------------------------------------------------------*)

val _ = remove_termtok{term_name = "COND",tok="=>"};  
val _ = overload_on ("|", Term`$Or`);
val _ = overload_on ("#", Term`$Then`);

val _ = set_fixity "|" (Infixr 501);
val _ = set_fixity "#" (Infixr 601);


(*---------------------------------------------------------------------------*)
(* Checker - as a tail recursion.                                            *)
(*---------------------------------------------------------------------------*)

val match_defn = Hol_defn "match"
  `(match [] l               = SOME l)                            /\
   (match (Epsilon::t) l     = match t l)                         /\ 
   (match (Any::t) (_::u)    = match t u)                         /\
   (match (Any::t)    []     = NONE)                              /\
   (match (Atom c::t) []     = NONE)                              /\
   (match (Atom c::t) (h::u) = if h=c then match t u else NONE)   /\
   (match (r1 | r2::t) l     = if match (r1::t) l = SOME [] 
                               then SOME [] else match (r2::t) l) /\
   (match (r1 # r2::t) l     = match (r1::r2::t) l)               /\
   (match (Repeat r::t) l    = 
      if match t l = SOME [] then SOME []  (* munch r 0 times, then t *)
      else        (* either NONE, or didn't munch all of l *)
         case match [r] l 
          of NONE -> NONE (* couldn't match an r *)
          || SOME l' ->   (* matched an r *)
               if LENGTH l' < LENGTH l   (* and consumed some of l *)
                  then match (Repeat r::t) l'
                  else NONE)`;

(*---------------------------------------------------------------------------*)
(* Packaged up.                                                              *)
(*---------------------------------------------------------------------------*)

val check_def = Define `check r s = (match [r] (EXPLODE s) = SOME [])`;

(*---------------------------------------------------------------------------
     Termination of match. We need a subsidiary measure function on 
     regexps which makes a 2-argument regexp bigger than a 
     list of 2 regexps. Adapted from a similar termination proof
     for Wang's algorithm in  tfl/examples/proplog.
 ---------------------------------------------------------------------------*)

val Meas_def = Define 
    `(Meas Any   = 0)
 /\  (Meas (Atom c)  = 0)
 /\  (Meas (x | y)  = Meas x + Meas y + 2)
 /\  (Meas (x # y)  = Meas x + Meas y + 2)
 /\  (Meas (Repeat r)  = SUC (Meas r))`;


val (match_def, match_ind) = Defn.tprove
(match_defn,
 WF_REL_TAC `measure (list_size Meas) LEX (measure LENGTH)`
 THEN RW_TAC list_ss [Meas_def, listTheory.list_size_def]);

(*---------------------------------------------------------------------------*)
(* Examples                                                                  *)
(*---------------------------------------------------------------------------*)

fun CHECK r s = Count.apply EVAL 
                  (Term `check ^r ^(stringSyntax.fromMLstring s)`);

val One = rhs(concl(EVAL(Term`Atom(HD(EXPLODE "1"))`)));
val Two = rhs(concl(EVAL(Term`Atom(HD(EXPLODE "2"))`)));
val a = rhs(concl(EVAL(Term`Atom(HD(EXPLODE "a"))`)));
val b = rhs(concl(EVAL(Term`Atom(HD(EXPLODE "b"))`)));
val c = rhs(concl(EVAL(Term`Atom(HD(EXPLODE "c"))`)));

val r0 = Term `^One # ^Two`;
val r1 = Term `Repeat (^One # ^Two)`
val r2 = Term `Repeat Any # ^One`;
val r3 = Term `^r2 # ^r1`;

(* val true  = *) CHECK r0 "12";
(* val true  = *) CHECK r1 "12";
(* val true  = *) CHECK r1 "1212";
(* val true  = *) CHECK r1 "121212121212121212121212";
(* val false = *) CHECK r1 "12123";
(* val false = *) CHECK r2 "";
(* val true  = *) CHECK r2 "1";
(* val true  = *) CHECK r2 "0001";
(* val false = *) CHECK r2 "0002";
(* val true  = *) CHECK r3 "00011212";
(* val false = *) CHECK r3 "00011213";
(* val true  = *) CHECK (Term`Repeat(Repeat Any)`) "";
(* val true  = *) CHECK (Term`Repeat(Repeat Any)`) "0";
(* val true  = *) CHECK (Term`Repeat(Repeat Any)`) "0123";
(* val true  = *) CHECK (Term`Repeat (Any # Repeat Any)`) "0";
(* val true  = *) CHECK (Term`Repeat (Any # Repeat Any)`) "01";
(* val true  = *) CHECK (Term`Repeat (Any # Repeat Any)`) "012";
(* val true  = *) CHECK (Term`^a # Repeat(^a | ^b) # Repeat(^b # ^a)`) "abba";

(* At most 2 a's. Alphabet = {a,b} *)
val AtMostTwo_a = Term `Repeat ^b 
                     |  Repeat ^b # (^a | ^a # Repeat ^b # ^a) # Repeat ^b`;
CHECK AtMostTwo_a "";
CHECK AtMostTwo_a "b";
CHECK AtMostTwo_a "a";
CHECK AtMostTwo_a "aa";
CHECK AtMostTwo_a "ab";
CHECK AtMostTwo_a "ba";
CHECK AtMostTwo_a "bb";
CHECK AtMostTwo_a "abbbbabbbb";
CHECK AtMostTwo_a "bbbbabbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
(* false *) CHECK AtMostTwo_a "abbbbabbbab";

(* Exactly 2 a's. Alphabet = {a,b} *)
val ExactlyTwo_a = Term `Repeat ^b # ^a # Repeat ^b # ^a # Repeat ^b`;

(* false *) CHECK ExactlyTwo_a "";
(* false *) CHECK ExactlyTwo_a "b";
(* false *) CHECK ExactlyTwo_a "a";
(* true *)  CHECK ExactlyTwo_a "aa";
(* false *) CHECK ExactlyTwo_a "ab";
(* false *) CHECK ExactlyTwo_a "ba";
(* false *) CHECK ExactlyTwo_a "bb";
CHECK ExactlyTwo_a "abbbbabbbb";
CHECK ExactlyTwo_a "bbbbabbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbab";
(* false *) CHECK ExactlyTwo_a "abbbbabbbab";

(* All strings of length 0-3 *)
val UpTo3 = Term `Epsilon | Any | Any#Any | Any#Any#Any`;

CHECK UpTo3 "";
CHECK UpTo3 "b";
CHECK UpTo3 "a";
CHECK UpTo3 "aa";
(* false *) CHECK UpTo3 "abbbbabbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

(* All strings with no occurrences of aa or bb *)
val NoRepeats = Term `Any | Repeat (^a # ^b) | Repeat (^b # ^a)`;

CHECK NoRepeats "";
CHECK NoRepeats "a";
CHECK NoRepeats "b";
(* false *) CHECK NoRepeats "aa";
CHECK NoRepeats "ab";
CHECK NoRepeats "ba";
(* false *) CHECK NoRepeats "bb";
CHECK NoRepeats "ababababababababababababababababababababababababababab";
(* false *) 
CHECK NoRepeats "abababababababababababbababababababababababababababab";
