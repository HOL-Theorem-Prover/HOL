signature Defn =
sig

   type hol_type = Type.hol_type
   type term = Term.term
   type thm = Thm.thm
   type conv = Abbrev.conv
   type tactic = Abbrev.tactic

   type defn

   val monitoring : bool ref

   val define : string -> term -> defn


   (* What kind of definition is it? *)

   val abbrev  : defn -> bool
   val primrec : defn -> bool
   val nestrec : defn -> bool
   val mutrec  : defn -> bool


   (* Extracting recursion equations, in various formats *)

   val eqns_of : defn -> thm
   val eqnl_of : defn -> thm list


   (* Extracting induction theorem *)
   val ind_of     : defn -> thm option

   (* Peculiar to nested and mutual recursions, respectively *)
   val aux_defn   : defn -> defn option
   val union_defn : defn -> defn option


   (* Parameters of a schematic defn *)
   val parameters : defn -> term list

   (* Extracting termination conditions, setting termination relation *)

   val tcs_of     : defn -> term list
   val reln_of    : defn -> term option
   val set_reln   : defn -> term -> defn

   (* Manipulating termination conditions *)

   val inst_defn  : defn -> (term,term)Lib.subst * 
                            (hol_type,hol_type)Lib.subst -> defn
   val elim_tcs   : defn -> thm list -> defn
   val simp_tcs   : defn -> conv -> defn
   val prove_tcs  : defn -> tactic -> defn


(* Derivable
   type goalstack = goalstackLib.goalstack
   type proofs = goalstackLib.proofs

   val gstack_of  : defn -> goalstack
   val g_of       : defn -> proofs           (* side-effecting *)
   val guess_reln : defn -> term list
*)


(*
   (* Lower level information: functional of a defn, 
      patterns used in defn. *)

   val fnal_of   : defn -> term
   val pats_of   : defn -> term * XX list

*)


(*
Examples.

app load ["Defn"]; 

fun D s q = Defn.define s (Term q);

val Fact = 
D "Fact"
  `(Fact 0 = 1) /\
   (Fact (SUC n) = Fact n * SUC n)`;

val fact = 
D "fact" 
  `fact(n) = if n=0 then 1 else n * fact(n-1)`;

val While = 
D "While" 
  `While s = if B s then While (C s) else s`;

val N = 
D "N1"
  `N x = if x>100 then x-10 else N(N(x+11))`;

val even_odd =
D "EO"
  `(even 0 = T)           /\
   (even (SUC n) = odd n) /\
   (odd 0 = F)            /\
   (odd (SUC n) = even n)`;

val gcd = 
D "gcd"
  `(gcd 0 y = y)           /\
   (gcd (SUC x) 0 = SUC x) /\
   (gcd (SUC x) (SUC y) = 
         if y <= x then gcd(x-y)   (SUC y) 
                   else gcd(SUC x) (y-x))`;

val g5 =
D "g5"
  `(g5(0,x,y,z) = 1) /\
   (g5(w,0,y,z) = 2) /\
   (g5(w,x,0,z) = 3) /\
   (g5(w,x,y,0) = 4)`;

val g4 = 
D "g4"
  `(g4 0 x y = 1) /\
   (g4 w 0 y = 2) /\
   (g4 w x 0 = 3)`;


val Nine1 =
 D "Nine1"
   `% x = if x>100 then x-10 else %(%(x+11))`;  (* fails *)

val even_odd =
D "OE"
  `(&& 0 = T)          /\
   (&& (SUC n) = !! n) /\
   (!! 0 = F)          /\
   (!! (SUC n) = && n)`;
*)

end
