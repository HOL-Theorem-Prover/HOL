(* ===================================================================== *)
(* FILE          : mk_restr_binder.sml                                   *)
(* DESCRIPTION   : Restricted quantifiers. Translated from hol88         *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : May 17, 1993                                          *)
(* ===================================================================== *)


(*---------------------------------------------------------------------------
 *  Original documentation (drawn from versions file for 1.12
 *
 * Syntactic support for restricted quantification and abstraction is now
 * provided. This follows a suggestion discussed at the Second HOL Users
 * Meeting and implements a methods of simulating subtypes and dependent
 * types with predicates. 
 * 
 * Currently no derived rules are provided to support this notation, so
 * any inferences will need to work on the underlying semantic
 * representation.
 * 
 * The new syntax automatically translates as follows:
 * 
 *    \v::P. B    <---->   RES_ABTRACT P (\v. B)
 *    !v::P. B    <---->   RES_FORALL  P (\v. B)
 *    ?v::P. B    <---->   RES_EXISTS  P (\v. B)
 *    @v::P. B    <---->   RES_SELECT  P (\v. B)
 * 
 * Anything can be written between the binder and `::` that could be
 * written between the binder and `.` in the old notation. See the
 * examples below.
 * 
 * The flag `print_restrict` has default true, but if set to false will
 * disable the pretty printing. This is useful for seeing what the
 * semantics of particular restricted abstractions are.
 * 
 * The constants RES_ABSTRACT, RES_FORALL, RES_EXISTS and RES_SELECT are
 * defined in the theory `bool` by:
 * 
 *    |- RES_ABSTRACT P B =  \x:'a. (P x => B x | ARB:'b )
 * 
 *    |- RES_FORALL P B   =  !x:'a. P x ==> B x
 * 
 *    |- RES_EXISTS P B   =  ?x:'a. P x /\ B x
 * 
 *    |- RES_SELECT P B   =  @x:'a. P x /\ B x
 * 
 * where ARB is defined in the theory `bool` by:
 * 
 *    |- ARB  =  @x:'a. T
 * 
 * User defined binders can also have restricted forms. If B is the name
 * of a binder and RES_B is the name of a suitable constant (which
 * must be explicitly defined), then executing:
 * 
 *    associate_restriction(`B`, `RES_B`);;
 * 
 * will cause the parser and pretty-printer to support:
 * 
 *    Bv::P. B    <---->   RES_B  P (\v. B)
 * 
 * Note that associations between user defined binders and their
 * restrictions are not stored in the theory, so they have to be set up
 * for each hol session (e.g. with a hol-init.ml file).
 * 
 * Examples of built-in restrictions:
 * 
 *    #"!x y::P. x<y";;
 *    "!x y :: P. x < y" : term
 * 
 *    #set_flag(`print_restrict`, false);;
 *    true : bool
 *    
 *    #"!x y::P. x<y";;
 *    "RES_FORALL P(\x. RES_FORALL P(\y. x < y))" : term
 * 
 *    #"?(x,y) p::(\(m,n).m<n). p=(x,y)";;
 *    "RES_EXISTS
 *     (\(m,n). m < n)
 *     (\(x,y). RES_EXISTS(\(m,n). m < n)(\p. p = x,y))"
 *    : term
 * 
 *    #"\x y z::P.[0;x;y;z]";;
 *    "RES_ABSTRACT P(\x. RES_ABSTRACT P(\y. RES_ABSTRACT P(\z. [0;x;y;z])))"
 *    : term
 * 
 * A conversion that rewrites away the constants RES_ABSTRACT,
 * RES_FORALL, RES_EXISTS and RES_SELECT is:
 * 
 *    let RESTRICT_CONV =
 *     DEPTH_CONV
 *      (REWRITE_CONV (definition `bool` `RES_ABSTRACT`) ORELSEC
 *       REWRITE_CONV (definition `bool` `RES_FORALL`)   ORELSEC
 *       REWRITE_CONV (definition `bool` `RES_EXISTS`)   ORELSEC
 *       REWRITE_CONV (definition `bool` `RES_SELECT`))
 *     THENC DEPTH_CONV BETA_CONV;;
 * 
 * This is a bit unsatisfactory, as is shown by the example below:
 * 
 *    #let t = "!x y::P.?f:num->num::Q. f(@n::R.T) = (x+y)";;
 *    t = "!x y :: P. ?f :: Q. f(@n :: R. T) = x + y" : term
 * 
 *    #RESTRICT_CONV t;;
 *    |- (!x y :: P. ?f :: Q. f(@n :: R. T) = x + y) =
 *       (!x. P x ==> (!x'. P x' ==> (?x. Q x /\ (x(@x. R x /\ T) = x + x'))))
 * 
 * The variable "x" in the definitions of RES_ABSTRACT, RES_FORALL,
 * RES_EXISTS and RES_SELECT gets confused with the variable in t.  This
 * can be avoided by changing RESTRICT_CONV to perform explicit
 * alpha-conversion. For example:
 * 
 *    RES_FORALL P (\v. B[v]) ---> !v. P v ==> B[v]
 * 
 * This is straightforward (but not yet implemented). Dealing with the case 
 * when v is a variable structure is also desirable. For example:
 * 
 *    #let t1 = "!(m,n)::P. m<n";;
 *    t1 = "!(m,n) :: P. m < n" : term
 * 
 *    #RESTRICT_CONV t1;;
 *    |- (!(m,n) :: P. m < n) = (!x. P x ==> (\(m,n). m < n)x)
 * 
 * If anyone writes the desired conversions please let us know!
 * 
 * Example of a user-defined restriction:
 * 
 *    #new_binder_definition(`DURING`, "DURING(p:num#num->bool) = $!p");;
 *    |- !p. $DURING p = $! p
 * 
 *    #"DURING x::(m,n). p x";;
 *    no restriction constant associated with DURING
 *    skipping: x " ;; parse failed     
 * 
 *    #new_definition
 *    # (`RES_DURING`, "RES_DURING(m,n)p = !x. m<=x /\ x<=n ==> p x");;
 *    |- !m n p. RES_DURING(m,n)p = (!x. m <= x /\ x <= n ==> p x)
 * 
 *    #associate_restriction(`DURING`,`RES_DURING`);;
 *    () : void
 * 
 *    #"DURING x::(m,n). p x";;
 *    "DURING x :: (m,n). p x" : term
 * 
 *    #set_flag(`print_restrict`,false);;
 *    true : bool
 * 
 *    #"DURING x::(m,n). p x";;
 *    "RES_DURING(m,n)(\x. p x)" : term
 * 
 *---------------------------------------------------------------------------*)


structure restr_binderScript =
struct

type thm = Thm.thm;

local open boolTheory in end;

open HolKernel Parse ;

val _ = new_theory "restr_binder";

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


val _ = export_theory();

end;
