(* =====================================================================
    FILE: mk_res_quan.ml	    DATE: 1 Aug 92	
    BY: Wai Wong		

    Create the theory res_quan containing all theorems about
    restricted quantifiers.

  Original documentation (drawn from versions file for 1.12

 Syntactic support for restricted quantification and abstraction is now
 provided. This follows a suggestion discussed at the Second HOL Users
 Meeting and implements a methods of simulating subtypes and dependent
 types with predicates.

 Currently no derived rules are provided to support this notation, so
 any inferences will need to work on the underlying semantic
 representation.

 The new syntax automatically translates as follows:

    \v::P. B    <---->   RES_ABTRACT P (\v. B)
    !v::P. B    <---->   RES_FORALL  P (\v. B)
    ?v::P. B    <---->   RES_EXISTS  P (\v. B)
    @v::P. B    <---->   RES_SELECT  P (\v. B)

 Anything can be written between the binder and `::` that could be
 written between the binder and `.` in the old notation. See the
 examples below.

 The flag `print_restrict` has default true, but if set to false will
 disable the pretty printing. This is useful for seeing what the
 semantics of particular restricted abstractions are.

 The constants RES_ABSTRACT, RES_FORALL, RES_EXISTS and RES_SELECT are
 defined in the theory `bool` by:

    |- RES_ABSTRACT P B =  \x:'a. (P x => B x | ARB:'b )

    |- RES_FORALL P B   =  !x:'a. P x ==> B x

    |- RES_EXISTS P B   =  ?x:'a. P x /\ B x

    |- RES_SELECT P B   =  @x:'a. P x /\ B x

 where ARB is defined in the theory `bool` by:

    |- ARB  =  @x:'a. T

 User defined binders can also have restricted forms. If B is the name
 of a binder and RES_B is the name of a suitable constant (which
 must be explicitly defined), then executing:

    associate_restriction(`B`, `RES_B`);;

 will cause the parser and pretty-printer to support:

    Bv::P. B    <---->   RES_B  P (\v. B)

 Note that associations between user defined binders and their
 restrictions are not stored in the theory, so they have to be set up
 for each hol session (e.g. with a hol-init.ml file).

 Examples of built-in restrictions:

    #"!x y::P. x<y";;
    "!x y :: P. x < y" : term

    #set_flag(`print_restrict`, false);;
    true : bool

    #"!x y::P. x<y";;
    "RES_FORALL P(\x. RES_FORALL P(\y. x < y))" : term

    #"?(x,y) p::(\(m,n).m<n). p=(x,y)";;
    "RES_EXISTS
     (\(m,n). m < n)
     (\(x,y). RES_EXISTS(\(m,n). m < n)(\p. p = x,y))"
    : term

    #"\x y z::P.[0;x;y;z]";;
    "RES_ABSTRACT P(\x. RES_ABSTRACT P(\y. RES_ABSTRACT P(\z. [0;x;y;z])))"
    : term

 A conversion that rewrites away the constants RES_ABSTRACT,
 RES_FORALL, RES_EXISTS and RES_SELECT is:

    let RESTRICT_CONV =
     DEPTH_CONV
      (REWRITE_CONV (definition `bool` `RES_ABSTRACT`) ORELSEC
       REWRITE_CONV (definition `bool` `RES_FORALL`)   ORELSEC
       REWRITE_CONV (definition `bool` `RES_EXISTS`)   ORELSEC
       REWRITE_CONV (definition `bool` `RES_SELECT`))
     THENC DEPTH_CONV BETA_CONV;;

 This is a bit unsatisfactory, as is shown by the example below:

    #let t = "!x y::P.?f:num->num::Q. f(@n::R.T) = (x+y)";;
    t = "!x y :: P. ?f :: Q. f(@n :: R. T) = x + y" : term

    #RESTRICT_CONV t;;
    |- (!x y :: P. ?f :: Q. f(@n :: R. T) = x + y) =
       (!x. P x ==> (!x'. P x' ==> (?x. Q x /\ (x(@x. R x /\ T) = x + x'))))

 The variable "x" in the definitions of RES_ABSTRACT, RES_FORALL,
 RES_EXISTS and RES_SELECT gets confused with the variable in t.  This
 can be avoided by changing RESTRICT_CONV to perform explicit
 alpha-conversion. For example:

    RES_FORALL P (\v. B[v]) ---> !v. P v ==> B[v]

 This is straightforward (but not yet implemented). Dealing with the case
 when v is a variable structure is also desirable. For example:

    #let t1 = "!(m,n)::P. m<n";;
    t1 = "!(m,n) :: P. m < n" : term

    #RESTRICT_CONV t1;;
    |- (!(m,n) :: P. m < n) = (!x. P x ==> (\(m,n). m < n)x)

 If anyone writes the desired conversions please let us know!

 Example of a user-defined restriction:

    #new_binder_definition(`DURING`, "DURING(p:num#num->bool) = $!p");;
    |- !p. $DURING p = $! p

    #"DURING x::(m,n). p x";;
    no restriction constant associated with DURING
    skipping: x " ;; parse failed

    #new_definition
    # (`RES_DURING`, "RES_DURING(m,n)p = !x. m<=x /\ x<=n ==> p x");;
    |- !m n p. RES_DURING(m,n)p = (!x. m <= x /\ x <= n ==> p x)

    #associate_restriction(`DURING`,`RES_DURING`);;
    () : void

    #"DURING x::(m,n). p x";;
    "DURING x :: (m,n). p x" : term

    #set_flag(`print_restrict`,false);;
    true : bool

    #"DURING x::(m,n). p x";;
    "RES_DURING(m,n)(\x. p x)" : term

 ===================================================================== *)


structure res_quanScript =
struct


open HolKernel Parse basicHol90Lib;

val _ = new_theory"res_quan";

type thm = Thm.thm
infix THEN THENL;

(* --------------------------------------------------------------------- *)
(* Definitions to support restricted abstractions and quantifications    *)
(* --------------------------------------------------------------------- *)

val RES_FORALL = new_definition
 ("RES_FORALL", (--`RES_FORALL P B = !x:'a. P x ==> B x`--));

val RES_EXISTS = new_definition
 ("RES_EXISTS", (--`RES_EXISTS P B = ?x:'a. P x /\ B x`--));

val RES_SELECT = new_definition
 ("RES_SELECT", (--`RES_SELECT P B = @x:'a. P x /\ B x`--));

val RES_ABSTRACT = new_definition
 ("RES_ABSTRACT", (--`RES_ABSTRACT P B = \x:'a. (P x => B x | ARB:'b)`--));

val _ = associate_restriction ("\\", "RES_ABSTRACT");
val _ = associate_restriction ("!",  "RES_FORALL");
val _ = associate_restriction ("?",  "RES_EXISTS");
val _ = associate_restriction ("@",  "RES_SELECT");


(* ===================================================================== *)
(* Properties of restricted quantification.                              *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* RESQ_FORALL	    	    	    					*)
(* --------------------------------------------------------------------- *)

val RESQ_FORALL_CONJ_DIST = store_thm("RESQ_FORALL_CONJ_DIST",
    (--`!P Q R.
     (!(i:'a) :: P. (Q i /\ R i)) = (!i :: P. Q i) /\ (!i :: P. R i)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RES_FORALL]
    THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);

val RESQ_FORALL_DISJ_DIST = store_thm("RESQ_FORALL_DISJ_DIST",
    (--`!P Q R.
     (!(i:'a) :: \i. P i \/ Q i. R i) = (!i :: P. R i) /\ (!i :: Q. R i)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RES_FORALL] THEN
    BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);

val RESQ_FORALL_UNIQUE = store_thm("RESQ_FORALL_UNIQUE",
    (--`!P j. (!(i:'a) :: ($= j). P i) = P j`--),
    REWRITE_TAC [RES_FORALL] THEN BETA_TAC THEN
    REPEAT GEN_TAC THEN EQ_TAC THENL
       [DISCH_THEN (fn th =>
             ACCEPT_TAC(MP (SPEC (--`j:'a`--) th) (REFL (--`j:'a`--)) )),
        DISCH_TAC THEN GEN_TAC THEN DISCH_THEN (fn th => SUBST1_TAC (SYM th))
        THEN FIRST_ASSUM ACCEPT_TAC]);

val RESQ_FORALL_FORALL = store_thm("RESQ_FORALL_FORALL",
    (--`!(P:'a->bool) (R:'a->'b->bool) (x:'b).
        (!x. !i :: P. R i x) = (!i :: P. !x. R i x)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RES_FORALL]
    THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val RESQ_FORALL_REORDER = store_thm("RESQ_FORALL_REORDER",
    (--`!(P:'a->bool) (Q:'b->bool) (R:'a->'b->bool).
        (!i :: P. !j :: Q. R i j) = (!j :: Q. !i :: P. R i j)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RES_FORALL] THEN
    BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);

(* --------------------------------------------------------------------- *)
(* RESQ_EXISTS	    	    	    					*)
(* --------------------------------------------------------------------- *)

val RESQ_EXISTS_DISJ_DIST = store_thm("RESQ_EXISTS_DISJ_DIST",
    (--`!P Q R.
     (?(i:'a) :: P. (Q i \/ R i)) = (?i :: P. Q i) \/ (?i :: P. R i)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RES_EXISTS]
    THEN BETA_TAC THEN PURE_ONCE_REWRITE_TAC[CONJ_SYM]
    THEN PURE_ONCE_REWRITE_TAC[RIGHT_AND_OVER_OR]
    THEN CONV_TAC (ONCE_DEPTH_CONV EXISTS_OR_CONV) THEN REFL_TAC);

val RESQ_DISJ_EXISTS_DIST = store_thm("RESQ_DISJ_EXISTS_DIST",
    (--`!P Q R.
     (?(i:'a) :: \i. P i \/ Q i. R i) = (?i :: P. R i) \/ (?i :: Q. R i)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RES_EXISTS]
    THEN BETA_TAC THEN PURE_ONCE_REWRITE_TAC[RIGHT_AND_OVER_OR]
    THEN CONV_TAC (ONCE_DEPTH_CONV EXISTS_OR_CONV) THEN REFL_TAC);

val RESQ_EXISTS_UNIQUE = store_thm("RESQ_EXISTS_UNIQUE",
    (--`!P j. (?(i:'a) :: ($= j). P i) = P j`--),
    REWRITE_TAC [RES_EXISTS] THEN BETA_TAC THEN REPEAT GEN_TAC
    THEN EQ_TAC THENL[
      DISCH_THEN (CHOOSE_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[],
      DISCH_TAC THEN EXISTS_TAC (--`j:'a`--) THEN  ASM_REWRITE_TAC[]]);

val RESQ_EXISTS_REORDER = store_thm("RESQ_EXISTS_REORDER",
    (--`!(P:'a->bool) (Q:'b->bool) (R:'a->'b->bool).
        (?i :: P. ?j :: Q. R i j) = (?j :: Q. ?i :: P. R i j)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RES_EXISTS] THEN BETA_TAC
    THEN EQ_TAC THEN DISCH_THEN (CHOOSE_THEN STRIP_ASSUME_TAC) THENL[
      EXISTS_TAC (--`x':'b`--) THEN CONJ_TAC THENL[
    	ALL_TAC, EXISTS_TAC(--`x:'a`--) THEN CONJ_TAC],
      EXISTS_TAC (--`x':'a`--) THEN CONJ_TAC THENL[
    	ALL_TAC, EXISTS_TAC(--`x:'b`--) THEN CONJ_TAC]]
    THEN FIRST_ASSUM ACCEPT_TAC);


val _ = export_theory();

val _ = let
  val ^^ = Path.concat
  infix ^^
in
  export_theory_as_docfiles (Path.parentArc ^^ "help" ^^ "thms")
end

end;
