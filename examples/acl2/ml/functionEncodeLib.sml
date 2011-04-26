(*****************************************************************************)
(* functionEncodeLib.sml :                                                   *)
(*     Translates functions between HOL and an embedded language using the   *)
(*     coding functions defined in encodeLib.                                *)
(*                                                                           *)
(*****************************************************************************)

structure functionEncodeLib :> functionEncodeLib =
struct

(*****************************************************************************)
(* Bugs:                                                                     *)
(*     1) Datatypes using fcps, eg:                                          *)
(*            wordlist = Nil | Cons of 'a word => wordlist                   *)
(*        currently fail. This is due to problems in the method of           *)
(*        derivation of function type for encode/decode et al...             *)
(*        This shouldn't take too long to fix...                             *)
(*                                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Suggested Improvements:                                                   *)
(*     1) (Minor) If is_target_function et al return false, the *reason* is  *)
(*        not collected. A function should be created to log this and use it *)
(*        in the error message.                                              *)
(*     2) (Minor) When a coding function is added its form is not checked    *)
(*     3) (Minor) When a coding theorem is added its form is not checked     *)
(*     4) (Minor) Some functions & theorems had to be added for :sexp, these *)
(*        should not be necessary.                                           *)
(*     5) (Minor) general_detect can be automatically calculated for         *)
(*        monomorphic types, but this is not currently done.                 *)
(*     6) (Major) The backtracking rewriter does not currently cross         *)
(*        encoding boundaries (eg. decode (encode x)). The suggested fix is  *)
(*        in append_detector. However, this currently breaks other pieces of *)
(*        code.                                                              *)
(*     7) (Minor) 'Cannot resolve head term:                                 *)
(*                  !x. %%genvar%%11776 x ==> (I (I x) = x)' appears quite   *)
(*        often in the trace. First of all: why, secondly, it can be proved! *)
(*     8) (Minor) When a polytypic theorem is added it should be confirmed   *)
(*        to be of the correct conditional form.                             *)
(*     9) (Minor) The polytypic functions I've created add LISTS of theorems *)
(*        These then output a 'check' theorem to prevent looping. This is    *)
(*        quite bad form... Hence:                                           *)
(*             Either (a) change polytypic rewrites to use lists or          *)
(*                    (b) amend the functions so that a single rewrite is    *)
(*                        not used                                           *)
(*    10) (Minor) The generators for map_compose seem to be slightly flaky,  *)
(*        they require the theorem for simple types, and don't perform many  *)
(*        checks.                                                            *)
(*    11) (Major) Addition of propagation theorems for definitions should    *)
(*        remove old propagation theorems. This may have been implemented by *)
(*        the addition of scrubbing, however...                              *)
(*    12) (Major) An assumption manager should be used, with maps to perform *)
(*        (and cache!) the various conversions required. Should help speed   *)
(*        things up... Especially in include_assumption_list                 *)
(*    13) (Minor) You can't flatten fix functions. They could be helpful in  *)
(*        some circumstances.                                                *)
(*                                                                           *)
(*****************************************************************************)

(* -- Interactive use only --

local
val traces = ref [];
fun clear_trace
    (trace : {default : int, max : int, name : string, trace_level : int}) =
    (traces := trace::(!traces) ;
     Feedback.set_trace (#name trace) 0)
fun reset_trace
    (trace : {default : int, max : int, name : string, trace_level : int}) =
    (Feedback.set_trace (#name trace) (#trace_level trace));
in
fun clear_traces () =
    (traces := [] ; app clear_trace (Feedback.traces ()));
fun reset_traces () =
    (app reset_trace (!traces) ; traces := []);
end;


quietdec := true;
clear_traces();

load "encodeLib";
Feedback.set_trace "polytypicLib.Trace" 0;

use "functionEncodeLib.sml";
reset_traces();
Feedback.set_trace "polytypicLib.Trace" 1;

*)

open HolKernel bossLib proofManagerLib boolSyntax Parse Lib Term Thm Drule Type
open Conv Tactic Tactical Rewrite
open boolTheory combinTheory
open polytypicLib encodeLib Feedback;


(*****************************************************************************)
(* Trace functionality:                                                      *)
(*                                                                           *)
(* trace : int -> string -> unit                                             *)
(*     Prints a trace message if the trace level supplied is greater than    *)
(*     the level registered.                                                 *)
(*                                                                           *)
(*****************************************************************************)
val Trace = ref 0;

val _ = register_trace ("functionEncodeLib.Trace",Trace,4);

fun trace level s = if level <= !Trace then print s else ();

(*****************************************************************************)
(* is_encoded_term: term -> bool                                             *)
(*     Checks to determine whether a term is an encoder applied to a value.  *)
(*     The term must be of one of the three forms:                           *)
(*     a) (encode : t -> target) x    where encode is a valid encoder        *)
(*     b) (f : t -> target) x        where target is a known translation     *)
(*     c) (f : t -> 'b) x                                                    *)
(*                                                                           *)
(* diagnose_encoded_term : term -> unit                                      *)
(*     This informs the user of why a particular is not considered to be     *)
(*     an encoded term.                                                      *)
(*                                                                           *)
(*****************************************************************************)

fun is_encoded_term term =
let val (ratort,randt) = dest_comb term
    val t = type_of randt
    val target = type_of term
    val enc = get_encode_function target t
in
    (is_const (fst (strip_comb enc)) andalso can (match_term enc) ratort)
    orelse (is_var ratort andalso
  	      (is_vartype target orelse can get_translation_scheme target))
end 	handle e => false

fun diagnose_encoded_term term =
let val (ratort,randt) = dest_comb term handle _ => (term,term)
    val t = type_of randt
    val target = type_of term
    val enc = get_encode_function target t
    val _ = print "Diagnosing encoded term: "
    val _ = print_term term
in
    if not (is_comb term) then
       print "The term is not an instance of function application."
    else if is_const (fst (strip_comb enc)) then
       	    if can (match_term enc) ratort then print "Encoded term"
       	       else (print "The encoder: " ; print_term enc ;
	             print "\n does not match the term's encoder:" ;
		     print_term (rator term))
            else if (is_var ratort andalso
  	      (is_vartype target orelse can get_translation_scheme target))
	      then print "Encoded term"
	      else print ("No encoder exists for the term given and\n" ^
	      	  "and the term does not specify a valid, encoding\n" ^
		  "variable. (Ie. no translation exists for the\n" ^
		  "output type or the output type is not a type variable")
end

(*****************************************************************************)
(* The rewrite database                                                      *)
(*                                                                           *)
(* conditionize_rewrite: thm -> thm                                          *)
(*     Converts a theorem from standard form (as used by add_standard)       *)
(*     to that used by add_conditional_rewrite.                              *)
(*                                                                           *)
(* add_standard_rewrite:                                                     *)
(*     Adds rewrites of the form  |- P ==> (enc a = b)   or   |- (enc a = b) *)
(*                                                                           *)
(* add_conditional_rewrite:                                                  *)
(*     Adds rewrites of the form:                                            *)
(*          |- P0 /\ ... /\ Pn ==>                                           *)
(*                (Q0 ==> encode a0 = A0) /\ ... /\ (Qm ==> encode am = Am)  *)
(*                ==> (encode (F a0 ... an) = F A0 ... Am)                   *)
(*                                                                           *)
(*     No encoders may occur in {A0...Am} and when an empty list is required *)
(*     (either for predicates or recursing encoders) T should be used.       *)
(*                                                                           *)
(* exists_rewrite: string -> bool                                            *)
(*     Returns true if a rewrite of a given name exists.                     *)
(*                                                                           *)
(*****************************************************************************)

val rewrites = ref (Net.empty : (int * string * thm) Net.net)

local
fun nomatch s = mkStandardExn "add_conditional_rewrite"
	("Theorem must be of the form: \n" ^
	 "|- P0 /\\ ... /\\ Pn ==> \n" ^
	 "      (Q0 ==> encode a0 = A0) /\\ ... /\\ (Qm ==> encode am = Am)\n" ^
	 "      ==> (encode (F a0 ... an) = F A0 ... Am)\n" ^
	 "  where no encoders are present in A0 .. Am" ^
	(if s = "" then "" else "\nHowever, " ^ s))
val err1 = "some terms in the conclusion and second antecedent\n are not encoded terms"
fun rall f [] = true | rall f (x::xs) = f x andalso rall f xs handle _ => false
fun choices [] current A = current::A
  | choices (x::xs) current A = choices xs (x::current) (choices xs current A)
in
fun add_conditional_rewrite priority name thm =
let	val _ = trace 2 "->add_conditional_rewrite\n";
	val thm' = CONV_RULE (LAND_CONV (PURE_REWRITE_CONV [GSYM CONJ_ASSOC]))
	    	   	     (SPEC_ALL thm)
	val (predicates,r) = with_exn (dest_imp_only o concl) thm' (nomatch "")
	val (recrewrites,final) = with_exn dest_imp_only r (nomatch "")
	fun mimp x = if is_imp_only x then snd (dest_imp x) else x
	val _ = if is_eq final then () else raise (nomatch "the conclusion is not an equality")
	val stripped = if recrewrites = T then [] else strip_conj recrewrites
	val target = type_of (lhs final)
	val _ = (if rall (is_encoded_term o lhs o mimp) (final::stripped) then () else raise Empty)
			handle _ => raise (nomatch err1)
	val gf = snd o dest_imp_only o snd o dest_imp_only
	fun subset a b = set_eq (intersect (strip_conj a) (strip_conj b)) (strip_conj a)
	fun supercedes (a,b,c) = can (match_term final) (gf (concl c)) andalso
		subset 	((fst o dest_imp_only o concl o C (PART_MATCH gf) (gf (concl c))) thm')
			((fst o dest_imp_only o concl) c) andalso
		a <= priority handle e => wrapException "add_conditional_rewrite" e
	val s = filter supercedes (Net.match (lhs final) (!rewrites))
	val (matches,sups) = partition (curry op= (concl thm') o concl o (fn (a,b,c) => c)) s
	fun ismatch (a,b,c) = mem (a,b,concl c) (map (fn (a,b,c) => (a,b,concl c)) matches)
	val _ = if null matches then () else
			(trace 1 "<<Encoding Warning: Exact match found, removing previous rewrite>>\n" ;
			 rewrites := Net.delete (lhs final,ismatch) (!rewrites))
	fun p (a,b,c) = "Rewrite: " ^ b ^ " with priority: " ^ int_to_string a ^ ":\n" ^ thm_to_string c ^ "\n"
	val _ = if null sups then () else
		trace 1 ("<<Encoding Messing>>: New rewrite matches other rewrites>>\n" ^ String.concat (map p sups))
	val _ = trace 1 ("Adding rewrite:\n" ^ thm_to_string thm ^ "\n")

	val ffs = filter (can dom_rng o type_of) (free_vars (rand (lhs final)))
	val _ = trace 3 ("Free functions : " ^ xlist_to_string term_to_string ffs ^ "\n")

	fun fixs thm =
	let	val a = fst (dest_forall (concl thm))
		val mt = fst (dom_rng (type_of a))
		val thm' = INST_TYPE [snd (dom_rng (type_of a)) |-> fst (dom_rng (type_of a))] thm
		val (a',body) = dest_forall (concl thm')
		val terms = find_terms (fn x => (curry op= a' o rator) x handle _ => false) (concl thm')
		val t = mk_const("I",mt --> mt)
	in
		CONV_RULE (CHANGED_CONV (RAND_CONV (RAND_CONV
			(PURE_REWRITE_CONV (map (fn t => ISPEC (rand t) I_THM) terms))))) (ISPEC t thm)
	end	handle e => SPEC (fst (dest_forall (concl thm))) thm

	fun fix thm list = repeat fixs (GENL list thm)

	val all_thms = op_mk_set (fn a => fn b => concl a = concl b) (map (fix thm') (choices ffs [] []))

	val _ = trace 3 ("Adjusted theorems added: " ^ int_to_string (length all_thms) ^ "\n")
in
	(map (fn thm' => rewrites := Net.insert (lhs final,(priority:int,name:string,thm')) (!rewrites)) all_thms ; ())
end
end;

local
fun nomatch t =
    mkStandardExn "conditionize_rewrite"
    ("Theorem:\n" ^ thm_to_string t ^
     "\nis not of the form: |- P ==> (encode a = b) or |- encode a = b")
fun wrap e = wrapException "conditionize_rewrite" e
fun conva thms = DEPTH_CONV (FIRST_CONV (map REWR_CONV thms))
fun conv thms thm = CONV_RULE (conva thms) (CONV_HYP (conva thms) thm)
fun fix_rewrites [] L = L
  | fix_rewrites (x::xs) L =
  fix_rewrites (map (conv [x]) xs) (x::map (conv [x]) L);
in
fun conditionize_rewrite thm =
let val _ = trace 2 "->conditionize_rewrite\n"
    val thm' = UNDISCH (SPEC_ALL thm) handle _ => SPEC_ALL thm
    val P = hd (hyp thm') handle Empty => T
    val (term,right) = (dest_eq  o concl) thm' handle e => raise (nomatch thm)
    val _ = if is_encoded_term term then () else raise (nomatch thm)
    val terms1 = mk_set (find_terms is_encoded_term right)
    val terms = terms1;
    val target = type_of term
    fun mk_varv s = variant (free_vars term) (Term.mk_var(s,target))
    val vars = map (mk_varv o implode o base26 o fst) (enumerate 0 terms)
               handle e => wrap e
    val assums = mapfilter (ASSUME o mk_eq) (zip terms vars)
    val rewrites = fix_rewrites (filter (not o equal T o concl) assums) [];
in
    DISCH P (CONV_RULE (LAND_CONV
           (PURE_REWRITE_CONV [AND_CLAUSES]))
        (DISCH_LIST_CONJ (map concl (TRUTH::rewrites))
         (RIGHT_CONV_RULE (conva rewrites) thm')))
   handle e => wrap e
end
end

fun add_standard_rewrite priority name thm =
let val toadd = conditionize_rewrite thm
    	      	handle e => wrapException "add_standard_rewrite" e
in
    add_conditional_rewrite priority name toadd
    handle e =>
    raise (mkDebugExn "add_standard_rewrite"
   ("add_conditional_rewrite did not like the output of " ^
    "conditionize_rewrite,\n this should never happen!! Original exception:\n" ^
    exn_to_string e))
end

fun exists_rewrite name =
    exists (curry op= name o (fn (a,b,c) => b)) (Net.listItems (!rewrites));

fun remove_rewrite name =
    rewrites := Net.filter (not o curry op= name o (fn (a,b,c) => b))
    	     		   (!rewrites);

fun scrub_rewrites () =
    rewrites :=
        Net.filter (fn (priority,name,thm) => Theory.uptodate_thm thm)
    	       	   (!rewrites);

(*****************************************************************************)
(* Resolution procedures:                                                    *)
(*                                                                           *)
(*    Main rewrite procedures are 'partial_resolve' and 'full_resolve':      *)
(*      ..._resolve [flag] functions  |- A /\ B /\ C ... ==> P               *)
(*      Will resolve {A,B,C,...} using the functions provided. In the case   *)
(*      of partial_resolve, the flag indicates whether terms in P can be     *)
(*      instantiated.                                                        *)
(*                                                                           *)
(*    Adding an assumption (include_assumption_list):                        *)
(*      Assumptions are stored as a list of disjunctions (ie. CNF):   Assums *)
(*      Auxilliary theorems are provided in the form:  |- P ==> Q :   Extras *)
(*      -- where P is in CNF.                                                *)
(*                                                                           *)
(*      When a new assumption, A |- t, is added to Assums:                   *)
(*          A |- t is resolved against all P for |- P ==> Q in extras:       *)
(*          to get new extras: |- P' \ t ==> Q'. Where P',Q' are             *)
(*          instantiated such that t matches a disjunction, D, in P. Ie:     *)
(*               P = ... /\ D /\ ... and   |- t ==> D                        *)
(*          A |- t is also resolved against all other assumptions, A' |- t': *)
(*             A' |- t' = A' |- t0 \/ ... \/ tn  is converted to:            *)
(*             |- ~t0 /\ ... /\ ~tn ==> ~A'. Which is then resolve against t *)
(*             and converted back to:                                        *)
(*             A |- (t0 \/ ... \/ tn) / t                                    *)
(*          Any new assumptions generated through these procedures undergo   *)
(*          the same procedure.                                              *)
(*                                                                           *)
(*    Resolving a theorem (full_resolve):                                    *)
(*      A theorem of the form: |- A /\ B /\ C ... ==> P is resolved using    *)
(*      full resolve with the following functions:                           *)
(*                                                                           *)
(*           A |- t     t0 \/ ... t ... \/ tn                                *)
(*           -------------------------------- match_disjunction              *)
(*               A |- t0 \/ ... t ... \/ tn                                  *)
(*                                                                           *)
(*             !x. detect x ==> encode (decode x) = x                        *)
(*           ----------------------------------------- match_decenc          *)
(*           |- !x. detect x ==> encode (decode x) = x                       *)
(*                                                                           *)
(*             !x. decode (encode x) = x                                     *)
(*           ---------------------------- match_encdec                       *)
(*           |- !x. decode (encode x) = x                                    *)
(*                                                                           *)
(*             !x. detect (encode x)                                         *)
(*           ------------------------ match_encdet                           *)
(*           |- !x. detect (encode x)                                        *)
(*                                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* NNF_CONV / CNF_CONV : thm -> thm                                          *)
(*                                                                           *)
(*     Like those in normalForms, but ONLY deals with disjunction,           *)
(*     conjunction and negation.                                             *)
(*                                                                           *)
(*****************************************************************************)

local
val thms = CONJUNCT1 NOT_CLAUSES::
    	   (CONJUNCTS (SPEC_ALL DE_MORGAN_THM))
in
val NNF_CONV = TOP_DEPTH_CONV (FIRST_CONV (map REWR_CONV thms));
fun CNF_CONV term =
    (NNF_CONV THENC normalForms.PURE_CNF_CONV) term
end;

(*****************************************************************************)
(* SAFE_MATCH_MP : thm -> thm -> thm                                         *)
(*                                                                           *)
(*     Like MATCH_MP but doesn't mind variable instantiation                 *)
(*     in the assumptions.                                                   *)
(*                                                                           *)
(*****************************************************************************)

fun SAFE_MATCH_MP thm1 thm2 =
let val match = match_term (fst (dest_imp (concl thm1))) (concl thm2)
    	handle e => wrapException "SAFE_MATCH_MP" e
    val vars1 = thm_frees thm1
    val vars2 = thm_frees thm2
in
    if null (intersect (map #residue (fst match)) vars1)
       then MP (INST_TY_TERM match thm1) thm2
           	handle e => wrapException "SAFE_MATCH_MP" e
       else raise (mkStandardExn "SAFE_MATCH_MP"
       	    	  ("Double bind between:\n" ^ thm_to_string thm1 ^
		  "\nand\n" ^ thm_to_string thm2))
end

(*****************************************************************************)
(* match_disjunction : thm -> term -> thm                                    *)
(*                                                                           *)
(*     A0 |- a0 \/ a1 \/ ...   b0 \/ b1 \/ b2 ...                            *)
(*     ------------------------------------------ match_disjunction          *)
(*                A0' |- b0 \/ b1 \/ b2 ...                                  *)
(*                                                                           *)
(*    Where {a0,a1,...} is a subset of {b0,b1,...} up to instantiation and   *)
(*    alpha conversion.                                                      *)
(*                                                                           *)
(*****************************************************************************)

local
fun mappluck f [] = []
  | mappluck f (x::xs) =
  ((f x,x),xs) :: (map (I ## cons x) (mappluck f xs)) handle e =>
     if isFatal e then raise e else (map (I ## cons x) (mappluck f xs));
fun instsubst (m1,m2) = subst m1 o inst m2;
fun MATCH_DISJ_CONV thm term =
    EQ_MP (CONV_RULE bool_EQ_CONV (AC_CONV (DISJ_ASSOC,DISJ_COMM)
    	      		   	    (mk_eq(concl thm,term)))) thm
fun match [] leftover = [([],leftover)]
  | match (d1::d1s) d2s =
let val m = mappluck (C match_term d1) d2s
    val passed = mapfilter (fn ((m,d2),d2s') => (d2,map (instsubst m) d2s')) m
in
    flatten (map (fn (d2,d2s) => map (cons d2 ## I) (match d1s d2s)) passed)
end;
fun prove_term thm fterm (list,leftover) =
    SAFE_MATCH_MP (DISCH_ALL (MATCH_DISJ_CONV
     (foldl (uncurry DISJ2) (ASSUME (list_mk_disj list)) leftover)
     fterm)) thm;
in
fun match_disjunction thm term =
let val thm_disjs = strip_disj (concl thm)
    val term_disjs = strip_disj term
    val matches = match thm_disjs term_disjs
    val fvs = free_vars term @ free_vars (concl thm)
in
    case (filter (null o C set_diff fvs o free_vars o concl)
    	 	 (mapfilter (prove_term thm term) matches))
    of [] => raise (mkStandardExn "match_disjunction"
       	     	   ("Theorem:\n" ^ thm_to_string thm ^ "\n" ^
		   "cannot not match the term: " ^ term_to_string term))
    |  [x] => x
    |  (x::xs) => (trace 1
       "<<Encoding Warning: Multiple matches in disjunction>>" ; x)
end
end;

(*****************************************************************************)
(* head_term         : thm -> term                                           *)
(* tail_thm          : thm -> thm                                            *)
(* resolve_head_term : bool -> thm -> thm -> term list -> term list * thm    *)
(*                                                                           *)
(*     For a theorem, thm,  of the form: A |- t0 /\ t1 /\ t2 ... ==> P       *)
(*         head_term thm  returns t0 and                                     *)
(*         tail_thm  thm  returns A u {t0} |- t1 /\ t2 ... ==> P             *)
(*     For a theorem, thm, of the form: A |- T ==> P                         *)
(*         head_term thm  returns T and                                      *)
(*         tail_thm  thm  returns A |- T ==> P                               *)
(*                                                                           *)
(*     A0 |- a0 \/ a1 \/ ..  A1 |- t0 /\ t1 /\ t2 .. ==> P                   *)
(*     --------------------------------------------------- resolve_head_term *)
(*                 A0 u A1' |- t1 /\ t2 .. ==> P'                            *)
(*                                                                           *)
(*     where t0 = {b0,b1,...} and {a0,a1,...} is a subset of {b0,b1,...}.    *)
(*     If the protect flag, the first argument, is true, then P must equal   *)
(*     P'. If not, then P may be instantiated to achieve a match.            *)
(*     A list of terms is provided, and instantiated in the same manner as P *)
(*                                                                           *)
(*****************************************************************************)

fun head_term thm =
	hd (strip_conj (fst (dest_imp_only (concl thm))))
	handle e => wrapException "head_term" e;

fun resolve_head_term protect rthm thm assumptions =
let	val thm' = if is_conj (fst (dest_imp_only (concl thm))) then
		CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) thm else
		DISCH (head_term thm) (DISCH T (UNDISCH thm))
		handle e => wrapException "resolve_head_term" e
	val rthm' = UNDISCH_CONJ rthm handle e => rthm
	val r = SAFE_MATCH_MP thm' rthm' handle e =>
		raise (mkStandardExn "resolve_head_term"
			("Theorem to resolve:\n" ^ thm_to_string rthm ^
		         "\ndoes not match head term:"
			 ^ term_to_string (head_term thm)))
	val (match1,match2) =
	    match_term (fst (dest_imp_only (concl thm'))) (concl rthm')
	val _ = if   not protect orelse
	      	     snd (strip_imp (concl r)) = snd (strip_imp (concl thm))
		   then ()
		   else raise (mkStandardExn "resolve_head_term"
			("Matching the theorem:\n" ^ thm_to_string thm ^
			 "\nto resolve:\n" ^
			 thm_to_string rthm ^
			 "\nrequires modification of the theorems conclusion."))
	val list = filter (fn x => exists (can (C match_term x))
			(strip_conj (fst (dest_imp_only (concl rthm))))) (hyp r)
			handle e => []
in
	(map (subst match1 o inst match2) assumptions,
	 foldr (fn (x,r) => CONV_RULE (REWR_CONV AND_IMP_INTRO) (DISCH x r))
	       r list)
end

local
fun TUNDISCH thm =
	if fst (dest_imp_only (concl thm)) = T then
		CONV_RULE (FIRST_CONV (map REWR_CONV (CONJUNCTS (SPEC_ALL IMP_CLAUSES)))) thm else UNDISCH thm
in
fun tail_thm thm =
	(if is_conj (fst (dest_imp_only (concl thm)))
	then TUNDISCH (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) thm)
	else 	if head_term thm = T then thm
		else DISCH T (TUNDISCH thm)) handle e => wrapException "tail_thm" e
end;

(*****************************************************************************)
(* dest_encdec  : term -> hol_type * hol_type                                *)
(* match_encdec : term -> thm                                                *)
(*     Returns a theorem matching a term of the form:                        *)
(*     |- !a. decode (encode a) = a                                          *)
(*                                                                           *)
(* dest_decenc  : term -> hol_type * hol_type                                *)
(* match_decenc : term -> thm                                                *)
(*     Returns a theorem matching a term of the form:                        *)
(*     |- !a. detect a ==> encode (decode a) = a                             *)
(*                                                                           *)
(* dest_encdet  : term -> hol_type * hol_type                                *)
(* match_encdet : term -> thm                                                *)
(*     Returns a theorem matching a term of the form:                        *)
(*     |- !a. detect (encode a)                                              *)
(*                                                                           *)
(*****************************************************************************)

local
val err = mkStandardExn "dest_encdec"
                        "Not a term of the form: \"!a. decode (encode a) = a\""
in
fun dest_encdec term =
let	val (var,body) = with_exn dest_forall term err
	val (decoder,encoded_term) = with_exn (dest_comb o lhs) body err
	(*val _ = if is_encoded_term encoded_term then () else raise err*)
	val _ = if var = rhs body then () else raise err
in
	(type_of var,type_of encoded_term)
end
end

fun match_encdec term =
let	val (t,target) = dest_encdec term handle e => wrapException "match_encdec" e
in
	FULL_ENCODE_DECODE_THM target t handle e => wrapException "match_encdec" e
end

local
val err = mkStandardExn "dest_decenc" "Not a term of the form: \"!a. detect a ==> encode (decode a) = a\""
in
fun dest_decenc term =
let	val (var,body) = with_exn dest_forall term err
	val (detect,body2) = with_exn dest_imp_only body err
	val (encode,decoded_term) = with_exn (dest_comb o lhs) body2 err
	val _ = if var = rhs body2 then () else raise err
	val target = type_of var
	val t = type_of decoded_term
	val _ = if exists_translation target t then () else raise err
	val _ = with_exn (match_term encode) (gen_encode_function target t) err
	val _ = with_exn (match_term (rator decoded_term)) (gen_decode_function target t) err
	val _ = with_exn (match_term (rator detect)) (gen_detect_function target t) err
in
	(t,target)
end
end;

fun match_decenc term =
let	val (t,target) = dest_decenc term handle e => wrapException "match_decenc" e
in
	FULL_DECODE_ENCODE_THM target t handle e => wrapException "match_decenc" e
end;

local
val err = mkStandardExn "dest_encdet" "Not a term of the form: \"!a. detect (encode a)\""
in
fun dest_encdet term =
let	val (var,body) = with_exn dest_forall term err
	val (detect,encoded_term) = with_exn dest_comb body err
	val _ = if var = rand encoded_term then () else raise err
	val target = type_of encoded_term
	val t = type_of var
	val _ = if exists_translation target t then () else raise err
	val _ = with_exn (match_term (rator encoded_term)) (gen_encode_function target t) err
	val _ = with_exn (match_term detect) (gen_detect_function target t) err
in
	(t,target)
end
end;

fun match_encdet term =
let	val (t,target) = dest_encdet term handle e => wrapException "match_encdet" e
in
	FULL_ENCODE_DETECT_THM target t handle e => wrapException "match_encdet" e
end;

local
fun presolve protect funcs thm A =
let val head = head_term thm
     	handle e => raise (mkDebugExn "partial_resolve"
   	       	 ("Theorem:\n " ^ thm_to_string thm  ^
		  "\nis not of the form: |- A /\\ B ... ==> P"))
in
    if head = T
       then if null A
       	       then ([],thm)
  	       else (rev A,DISCH_LIST_CONJ (rev A)
               	     (CONV_RULE (FIRST_CONV (map REWR_CONV
         	      (CONJUNCTS (SPEC_ALL IMP_CLAUSES)))) thm))
       else uncurry (C (presolve protect funcs))
       	    	    (resolve_head_term protect
       	    	      	            (tryfind (fn x => x head) funcs) thm A)
            handle e =>
		   if isFatal e
		      then raise e
		      else presolve protect funcs (tail_thm thm) (head::A)
end
in
fun partial_resolve protect funcs thm =
let val (A,r) = presolve protect funcs thm []
in
    if (A = strip_conj (fst (dest_imp_only (concl thm)))
       	  handle e => wrapException "partial_resolve" e)
       then raise UNCHANGED
       else r
end
end;

fun full_resolve funcs thm =
let	val head = head_term thm handle e => raise (mkDebugExn "full_resolve"
			"Theorem is not of the form: |- A /\\ B ... ==> P")
in
	if head = T then
		CONV_RULE (FIRST_CONV (map REWR_CONV
			        (CONJUNCTS (SPEC_ALL IMP_CLAUSES)))) thm
	else full_resolve funcs
			(tryfind_e (mkStandardExn "full_resolve"
				("Cannot resolve head term: "
				 ^ term_to_string head))
				(fn x => snd (resolve_head_term true
				      (x head) thm [])) funcs)
end

local
fun rmatch thm term = (match_term term (concl thm) ; thm)
in
fun resolve_functions assums =
	map match_disjunction assums @
	[match_encdec,match_decenc,match_encdet,DECIDE]
end

(*****************************************************************************)
(* include_assumption_list : thm list -> (thm list * thm list) ->            *)
(*                                                  (thm list * thm list)    *)
(*     Adds a list of assumptions into the current list of assumptions       *)
(*     and auxilliary theorems.                                              *)
(*                                                                           *)
(*     Assumptions are always stored in CNF (conjunction is implicit)        *)
(*     Auxilliary theorems are stored as |- P ==> Q where P is in CNF        *)
(*                                                                           *)
(*     Additional assumptions are first converted to CNF then resolved       *)
(*     against the antecedents of auxilliary theorems. Additional            *)
(*     assumptions may be generated at this stage.                           *)
(*                                                                           *)
(*****************************************************************************)

val IAL_data =
    ref (NONE : (term list * (thm list * ((thm list * thm list)))) option);


local
val NOT_NOT = el 1 (CONJUNCTS NOT_CLAUSES)
val CONTR1 = CONV_RULE (CONTRAPOS_CONV THENC LAND_CONV CNF_CONV) o
    	     DISCH_ALL_CONJ
val CONTR2 = CONV_RULE CNF_CONV o UNDISCH_CONJ o
    	     CONV_RULE (CONTRAPOS_CONV THENC LAND_CONV (REWR_CONV NOT_NOT));
val thm_set = op_mk_set (fn a => fn b => concl a = concl b)
val thm_diff = op_set_diff (fn a => fn b => concl a = concl b)
fun rematch_disjunction vs thm term =
let val result = match_disjunction thm term
    val match = match_term term (concl result)
in
    if exists (C mem ((map #redex o fst) match)) vs then
       raise (mkStandardExn "rematch_disjunction"
			"Variable in assumptions bound")
			else result
end
fun IAL oset L (assums,extras) =
let	val to_avoid = free_varsl oset
	val _ = if !debug then IAL_data := SOME (oset,(L,(assums,extras)))
	      	   	 else ();
	val l = mapfilter (partial_resolve false
	      		  (map (rematch_disjunction to_avoid) L))
	      		  (filter (is_imp_only o concl) extras)
	val e = thm_diff l extras
	val full_e = map (fn x => partial_resolve false (resolve_functions []) x
	    	     	       	  handle UNCHANGED => x) e
			handle e => wrapException "include_assumption_list" e
        val full_a = mapfilter (CONTR2 o
	      	     partial_resolve true
		     	(map (rematch_disjunction to_avoid o SPEC_ALL) L) o
	      	        CONTR1) assums

	val _ = trace 4 ("New theorems: " ^
	      	      	 xlist_to_string thm_to_string (full_a @ full_e) ^ "\n")
	val (newa,newe) = mappartition (CONV_RULE (STRIP_QUANT_CONV (FIRST_CONV
	    (map REWR_CONV (CONJUNCTS (SPEC_ALL IMP_CLAUSES)))))) full_e
			handle e => wrapException "include_assumption_list" e

	val new_assums =
	    thm_diff (flatten (map (CONJUNCTS o CONV_RULE CNF_CONV)
	    	              (newa @ full_a)))
	             (L @ assums)
	val _ = trace 1 ("#(" ^ int_to_string (length new_assums))
	val _ = trace 3 (":" ^ int_to_string (length L) ^
	      	      	":"   ^ int_to_string (length newe))
	val _ = trace 1 ")"

	val _ = if !debug andalso
	      	   exists (not o null o C set_diff oset o hyp)
		   	  (new_assums @ newe)
		then raise (mkDebugExn "include_assumption_list"
		     ("Adding the following assumption\n" ^
		      "(derived from an auxillary theorem):\n" ^
		      thm_to_string
		       (first (not o null o C set_diff oset o hyp) new_assums) ^
		      "\nwill add the unwanted hypothesis to the set:\n" ^
		      term_to_string
		       (tryfind (hd o C set_diff oset o hyp)
		       		(new_assums @ newe))))
		 else ()
in
	case (new_assums,thm_diff newe extras)
	of ([],[]) => (thm_set (L @ assums),thm_set extras)
	|  (NA,NE) => IAL oset (thm_set (NA @ L)) (NA @ assums,NE @ extras)
end
in
fun include_assumption_list [] AE =
    (trace 2 "->include_assumption_list\n" ; AE)
  | include_assumption_list L AE =
let val oset = mk_set (flatten (map hyp (L @ fst AE)))
    val new_assums =
    	flatten (map (CONJUNCTS o CONV_RULE CNF_CONV) L)
in
    (trace 2 "->include_assumption_list\n" ;
     trace 3 ("Including: " ^ xlist_to_string thm_to_string L ^ "\n") ;
     (IAL oset new_assums AE)
     	  before (trace 3 "\n"))
end
end;

(*****************************************************************************)
(* Tests                                                                     *)
(*
fun rinclude [] AE = AE
  | rinclude (x::xs) AE =
    rinclude xs (include_assumption_list (map ASSUME x) AE)

fun test AE tst =
    full_resolve (resolve_functions (fst AE))
    		 (ASSUME (mk_imp(tst,mk_var("SUCCESS",bool))));

val mat = mk_affirmation_theorems;

rinclude [[``~(arg = [])``]] ([],list_case_proofs);

rinclude [[``~((?c. a = SUC (SUC c)) /\ (?d e. b = d::e))``],
	  [``~(a = 0n)``],[``~(PRE a = 0n)``]]
	 ([],mat ``:num`` @ mat ``:'a list``);


*)


(*****************************************************************************)
(* return_matches : thm list -> term                                         *)
(*                        -> (string * thm list) * (string * thm) list       *)
(*                                                                           *)
(*     return_matches assumptions term  returns a list of instantiated       *)
(*     !rewrites that match a term. It does this in three stages:            *)
(*        1) Use HO_PART_MATCH to match the term                             *)
(*        2) Match any uninstantiated encoders and instantiate               *)
(*        3) Attempt to resolve any conditions using the assumptions         *)
(*     Fails if any of the steps fail. This can include double-bind          *)
(*     problems instantiating encoders.                                      *)
(*                                                                           *)
(*     Stage 2 is returned as the left part of the tuple for debugging       *)
(*     purposes as it allows tracking of partial matches.                    *)
(*                                                                           *)
(* match_single_rewrite : thm list -> term ->                                *)
(*                                        int * string * thm -> string * thm *)
(*     As return_matches, except it matches a single rewrite.                *)
(*                                                                           *)
(*****************************************************************************)

val return_matches_data = ref NONE;

local
fun mapthm f (a,b,c) = (a,b,f c)
fun revmatch [] = []
  | revmatch ({residue,redex}::xs) = (residue |-> redex) :: revmatch xs;
fun ismem a [] = false
  | ismem a (x::xs) =
  ((match_term a x = (revmatch ## revmatch) (match_term x a)) orelse ismem a xs)
  handle _ => ismem a xs
fun subset [] _ = true
  | subset (x::xs) ys = mem x ys andalso subset xs ys;
fun compile [] match2 = match2
  | compile ({redex,residue}::xs) match2 =
let val match1 = filter (curry op= redex o #redex) match2
in
    if all (curry op= residue o #residue) match1
    then (if null match1
    	  then (redex |-> residue)::(compile xs match2)
          else compile xs match2)
    else raise Match
end;
fun compile_matches [] = []
  | compile_matches (x::xs) = compile x (compile_matches xs)
fun nomatch s thm =
let val name = if s = "" then "return_matches" else "return_matches (" ^ s ^ ")"
in
    raise (mkDebugExn name
("Theorem: " ^ thm_to_string thm ^ "\nis not of the form: \n" ^
"|- P0 /\\ ... /\\ Pn ==> \n" ^
"      (Q0 ==> encode a0 = A0) /\\ ... /\\ (Qm ==> encode am = Am) ==>\n" ^
"      (encode (F a0 ... an) = F A0 ... Am)"))
end
fun mimp x = if is_imp x then ((strip_conj ## I) (dest_imp x)) else ([],x)
fun instantiate_encoders (priority,name,thm) =
let	val (l,final) = (dest_imp_only o snd o dest_imp_only o concl) thm
		handle e => nomatch "instantiate_encoders" thm
	val encoding_terms = filter (not o curry op= T) (strip_conj l)
	val target = (type_of o lhs) final
		handle e => nomatch "instantiate_encoders" thm
	val encoders = mapfilter (gen_encode_function target o type_of o rand o
	    lhs o snd o mimp) encoding_terms
	val (match1,match2) = unzip (map2 (fn e => fn t =>
	    match_term (rator (lhs (snd (mimp t)))) e) encoders encoding_terms)
in
	(priority,name,
	INST_TY_TERM (compile_matches match1, compile_matches match2) thm)
	handle Match =>
	raise (mkDebugExn "return_matches (instantiate_encoders)"
		("Theorem: " ^ thm_to_string thm ^ "\n" ^
		 "cannot have its encoders instantiated as they double bind"))
end
(* Ensure variables are not captured in any translations                     *)
fun adjust thm =
let	val vars = thm_frees thm
in
	INST (map (fn v => v |-> genvar (type_of v)) vars) thm
end;
fun pfs f x = f x handle e =>
    if isFatal e then raise e else
       (trace 4 ("Exception: " ^ polytypicLib.exn_to_string e) ; raise Empty)
fun resolveit assums (p,s,thm) =
    (p,s,(full_resolve (resolve_functions assums) o
    		CONV_RULE (LAND_CONV CNF_CONV)) thm)
in
fun match_single_rewrite assums term rewrite =
    (fn (a,b,c) => (b,c)) (resolveit assums
    	(instantiate_encoders (mapthm (C (HO_PART_MATCH
	      (lhs o snd o dest_imp_only o snd o dest_imp_only))
			   term o adjust) rewrite)))
    handle e => wrapException "match_single_rewrite" e
fun return_matches assums term =
let	val _ = return_matches_data := SOME (assums,term);
	val _ = trace 2 "return_matches->\n"
	val _ = trace 3 (term_to_string (repeat rator (rand term)))
	val matches = Net.match term (!rewrites)
	val _ = trace 3 (":" ^ int_to_string (length matches))
	val matched = mapfilter (mapthm
	    	       (C (HO_PART_MATCH
		       	   (lhs o snd o dest_imp_only o snd o dest_imp_only))
			   term o adjust)) matches
	val _ = trace 3 (":" ^ int_to_string (length matched))
	val ematched = mapfilter (instantiate_encoders) matched
	val hmatched = mapfilter (pfs (resolveit assums)) ematched
	val _ = trace 3 (":" ^ int_to_string (length hmatched) ^ "\n")
in
	(map (fn (a,b,c) => (b,c)) ematched,
	 map (fn (a,b,c) => (b,c))
	     (sort (fn (p1,_,_) => fn (p2,_,_) => p1 > p2) hmatched))
end
end;

(*****************************************************************************)
(* PROPAGATE_THENC : thm list * thm list ->                                  *)
(*                            (thm list * thm list -> term -> thm) ->        *)
(*                                                     (string * thm) -> thm *)
(*     PROPAGATE_THENC (assumptions,extras) next_conv (name,thm)             *)
(*     Applies the rewrite given as (name,thm) by encoding all of the        *)
(*     sub-encoders of the rewrite using next_conv                           *)
(*                                                                           *)
(*     When encoding a theorem of the form:                                  *)
(*          |- (Q0 ==> enc a0 = A0) /\ ... /\ (Qm ==> enc am = Am) ==>       *)
(*                enc (f a0 ... am) = F A0 ... Am                            *)
(*     with a list of assumptions, A, and extra theorems, E, PROPAGATE_THENC *)
(*     progresses by encoding each ai under the assumptions <(A u {Q0}),E>   *)
(*     where <a,b> resolves extra assumptions using include_assumption_list. *)
(*                                                                           *)
(*     It is possible for Ai to be present in any aj, in which case, enc aj  *)
(*     is processed after enc ai. It is also possible for Ai to be of the    *)
(*     form: Fi x y z, where x y z appear in Ai. In such cases, a higher-    *)
(*     order match is performed.                                             *)
(*                                                                           *)
(*     If Qi is empty, then [enc ai = Ai] |- detect Ai is added to the       *)
(*     assumption list of all subsequent encodings and resolved at the end.  *)
(*                                                                           *)
(*****************************************************************************)

val PROPAGATE_THENC_data = ref [];

(*****************************************************************************)
(* append_detector : hol_type -> (term list * term) -> thm list -> thm list  *)
(*     append_detector target (L,e) A takes an encoding term representing    *)
(*     'n L ==> encode x = X' and, provided L is null, derives the theorem:  *)
(*     [encode x = X] |- detect X  and appends it, and the theorem:          *)
(*     [encode x = X] |- encode x = X to the list of assumptions A.          *)
(*     This is then provided as an assumption for further encodings.         *)
(*                                                                           *)
(*****************************************************************************)

fun append_detector target ([],e) A =
    (DISCH e (CONV_RULE (RAND_CONV (REWR_CONV (ASSUME e)))
     (ISPEC (rand (lhs e))
      (FULL_ENCODE_DETECT_THM target (type_of (rand (lhs e))))))::A
(* possible fix for backtracking:   (DISCH e (ASSUME e)) :: A*)
    handle _ => A)
  | append_detector target _ A = A;

(*****************************************************************************)
(* remove_head : thm -> thm -> thm                                           *)
(*    remove_head M N takes theorems M and N, of the form:                   *)
(*         |- A,    |- {A} u Q ==> P                                         *)
(*    and returns the theorem:                                               *)
(*         |- Q ==> P                                                        *)
(*    If Q is empty, {}, then |- T ==> P is returned.                        *)
(*                                                                           *)
(*****************************************************************************)

fun remove_head r thm =
let val h = fst (dest_imp (concl thm))
    	    handle e => wrapException "remove_head" e
    val x = fst (dest_conj h) handle _ => h
    val thm' = INST_TY_TERM (match_term x (concl r)) thm
in
    CONV_RULE (LAND_CONV (LAND_CONV (REWR_CONV (EQT_INTRO r)) THENC
    	       REWR_CONV (CONJUNCT1 (SPEC_ALL AND_CLAUSES)))) thm'
    handle e =>
    CONV_RULE (LAND_CONV (REWR_CONV (EQT_INTRO r))) thm'
end

(*****************************************************************************)
(* HO_INST_TY_TERM :                                                         *)
(*        {redex : term, residue : term} list *                              *)
(*        {redex : hol_type, residue : hol_type} list -> thm -> thm          *)
(* ho_inst_ty_term :                                                         *)
(*        {redex : term, residue : term} list *                              *)
(*        {redex : hol_type, residue : hol_type} list -> term -> term        *)
(*     Takes a higher-order match, as returned from ho_match_term, used to   *)
(*     instantiate the theorem or term from the term given and beta-converts *)
(*     any higher-order terms. Eg.:                                          *)
(*         HO_INST_TY_TERM [a |-> \b. A b] `t (a b)`                         *)
(*                                         |- t ((\b. A b) a) = |- t (A a)   *)
(*     and similar for ho_inst_ty_term.                                      *)
(*                                                                           *)
(*     Note: This is not technically correct, ALL lambda abstractions will   *)
(*           be beta converted, so the following will be incorrect:          *)
(*           ho_inst_ty_term (match_term ``f a`` ``(\b. K c b) a``) ``f a``  *)
(*                                                                           *)
(*****************************************************************************)

local
fun FIX (match : {redex : term, residue : term} list) term
    	mkc mka (beta:term -> 'a) (refl:term -> 'a) tm =
    if is_comb term
       then if (is_abs (#residue
       	       	       (first (curry op= (rator term) o #redex) match))
    	        handle e => false)
    	       then beta tm
               else mkc (FIX match (rator term) mkc mka beta refl (rator tm),
                         FIX match (rand term) mkc mka beta refl (rand tm))
       else if is_abs term
               then mka (bvar tm)
       	               (FIX match (body term) mkc mka beta refl (body tm))
               else refl tm;
fun inst_ty_term match term =
    subst (fst match) (inst (snd match) term);
in
fun HO_INST_TY_TERM (term_match,type_match) thm =
let val hyps = hyp thm
    val thm' = DISCH_ALL_CONJ thm
    val thmb = INST_TY_TERM (term_match,type_match) thm'
    val thma = INST_TYPE type_match thm'
    val rewrite = FIX term_match (concl thma)
    	    MK_COMB (fn bvar => fn body => MK_ABS (GEN bvar body))
	    BETA_CONV REFL (concl thmb)
    val complete = EQ_MP rewrite thmb
in
    case hyps
    of [] => complete
    |  L => UNDISCH_CONJ complete
end handle e => wrapException "HO_INST_TY_TERM" e
fun ho_inst_ty_term (term_match,type_match) term =
    FIX term_match (inst type_match term) mk_comb (curry mk_abs) beta_conv I
    	(inst_ty_term (term_match,type_match) term)
    handle e => wrapException "ho_inst_ty_term" e
end;

local
fun loop_exn name =
(mkDebugExn "PROPAGATE_THENC"
	    ("The rewrite theorem " ^ name ^
	     " appears to contain an encoding loop:\n" ^
	     " ie. it has antecedents: \"(encode (f X) = Y) ..." ^
	     " /\\ (encode (g Y) = X)\""))
fun match_exn name = (mkDebugExn "PROPAGATE_THENC"
 ("Rewrite theorem: " ^ name ^ " is not of the form: \n" ^
  "[] |- P0 /\\ ... /\\ Pn ==> \n" ^
  "      (Q0 ==> encode a0 = A0) /\\ ... /\\ (Qm ==> encode am = Am)\n" ^
  "      ==> (encode (F a0 ... an) = F A0 ... Am)\n" ^
  "  where no encoders are present in A0 .. Am."))
(* Checks to determine whether the encoder requires results from other *)
(* encoders.                                                           *)
fun clear fvsr (L,e) =
    if e = T then (L,e)
    else (if all (fn tm => not (exists (C free_in tm) fvsr))
	    	     (lhs e :: L)
    then (L,e) else raise Empty)
fun mimp x = if is_imp x then ((strip_conj ## I) (dest_imp x)) else ([],x)
(* Applies remove_head continuously to remove detects from the theorem       *)
fun remove_detect_hyps [] thm =
    (CONV_RULE (REWR_CONV (CONJUNCT1 (SPEC_ALL IMP_CLAUSES))) thm handle e =>
    if concl thm = T then TRUTH else
       raise (mkDebugExn "remove_detect_hyps" (
	       "Could not remove all hypothesese from the theorem:\n" ^
	       	thm_to_string thm)))
  | remove_detect_hyps (r::rs) thm =
    (if head_term thm = T
    	then if not (is_conj (fst (dest_imp_only (concl thm))))
	     	then remove_detect_hyps [] thm
		else remove_detect_hyps (r::rs) (remove_head TRUTH thm)
        else remove_detect_hyps rs (remove_head r thm))
    handle e => remove_detect_hyps [] thm
in
fun PROPAGATE_THENC (assums,extras) conv (name,thm_pre) =
let val _ = trace 2 "->PROPAGATE_THENC\n"
    val _ = trace 1 ("R(" ^ name ^ ")");
    val _ = PROPAGATE_THENC_data :=
    	    ((assums,extras),conv,(name,thm_pre)) :: !PROPAGATE_THENC_data;
    val thm = CONV_RULE (LAND_CONV (PURE_REWRITE_CONV
    	      		[GSYM CONJ_ASSOC])) thm_pre
    val (encoders,final) =
    	(map mimp o strip_conj ## I) (dest_imp_only (concl thm))
	handle e => raise (match_exn name);
    val fvs_right = mapfilter (rhs o snd) encoders
    val target = type_of (rhs final)
    	handle e => raise (match_exn name);

    fun check_hyp thmb =
    	if null (set_diff (hyp thmb) (flatten (map hyp assums))) then thmb
	else raise (mkDebugExn "check_hyp"
	     	    ("PROPAGATE_THENC has altered the hypothesis set," ^
		     " the following terms have been added:\n" ^
		     xlist_to_string term_to_string
		       (set_diff (hyp thmb) (flatten (map hyp assums)))))

    fun enc A [] = []
      | enc A encs =
    let val ((n,(L,e)),rest) =
            pick_e (loop_exn name)
	    	   (I ## clear (mapfilter (rhs o snd o snd) encs)) encs
        val conved = DISCH_LIST_CONJ (T::map (fst o dest_imp o concl) A)
	    	         (DISCH_LIST_CONJ (T::L)
			    (conv (include_assumption_list (map ASSUME L)
			    	  	(assums @ (map UNDISCH A),extras))
						  (lhs e)))
                     handle E =>
		     if e = T then TRUTH else raise E
    in  (n,conved):: (enc (append_detector target (L,e) A) rest)
    end

    val recs = enc [] (enumerate 1 encoders)

    val list = strip_conj (fst (dest_imp_only (concl thm)))
	    	   handle e => raise (match_exn name);

    fun check_cons x rs =
    	if is_imp_only (concl x) then rs else x::rs;

    fun matchit ((n,x),((list,removed),thm)) =
    let val x' = remove_detect_hyps removed x
    	val x'' = CONV_RULE (FIRST_CONV [
    	       	   REWR_CONV (CONJUNCT1 (SPEC_ALL IMP_CLAUSES)),
		   LAND_CONV (REWR_CONV (CONJUNCT1 (SPEC_ALL AND_CLAUSES))),
		   ALL_CONV]) x'
		  handle e => (if concl x' = T then x' else raise e)
        val match = ho_match_term [] Term.empty_tmset (el n list) (concl x'');
	val thm' = HO_INST_TY_TERM match thm
	val list' = map (ho_inst_ty_term match) list
    in	((list',check_cons x'' removed),
    	         HO_MATCH_MP (DISCH (el n list') thm') x'')
    end handle e => wrapException "matchit" e
in
    (check_hyp (snd (foldl matchit ((list,[]),UNDISCH_CONJ thm) recs)) before
     (PROPAGATE_THENC_data := tl (!PROPAGATE_THENC_data)))
    handle e => wrapException "PROPAGATE_THENC" e
end
end

(*****************************************************************************)
(* backchain_rewrite : int -> thm list -> term -> thm                        *)
(*     Attempts to prove (or disprove) the term given by repeatedly applying *)
(*     rewrites in the list:                                                 *)
(*         backchain_rewrite n RR P =                                        *)
(*            a) |- A ==> P = (Q0 /\ Q1 ... ==> P0 \/ ...) /\ ...            *)
(*               ==> !a in A. backchain_rewrite (n + 1) RR a                 *)
(*                   !i. ?j. backchain_rewrite (n + 1) (RR u {Q0,Q1..}) Pi   *)
(*                                                                           *)
(*     This ONLY operates on boolean valued theorems. It was designed to     *)
(*     solve very simple problems relatively quickly. It can certainly be    *)
(*     improved, but does the job for now...                                 *)
(*                                                                           *)
(*****************************************************************************)

fun DISCHL_CONJ hs thm =
    foldr (fn (t,thm) => CONV_RULE (REWR_CONV AND_IMP_INTRO) (DISCH t thm))
    	  (DISCH (last hs) thm) (butlast hs);

fun SOME_CONJ_CONV conv term =
    conv term handle _ =>
    if is_conj term then
       LAND_CONV (SOME_CONJ_CONV conv) term handle _ =>
       RAND_CONV (SOME_CONJ_CONV conv) term
    else NO_CONV term;

val max_depth = ref 8;

val LHS = lhs o snd o strip_imp_only o snd o strip_forall;
val RHS = rhs o snd o strip_imp_only o snd o strip_forall;
val BOOL_RULE =
    CONV_RULE (FIRST_CONV (map REWR_CONV (CONJUNCTS (SPEC_ALL EQ_CLAUSES))));
fun UNBOOL_RULE thm =
    EQF_INTRO thm handle _ => EQT_INTRO thm
val full_strip_imp = (map strip_conj ## I) o strip_imp

fun perform_rewrite depth RR term rewrite =
let val rewrite_thm = HO_PART_MATCH LHS rewrite term
    val (hyp_set,_) = (map (map (backchain_rewrite (depth + 1) RR)) ## I)
    		      (full_strip_imp (concl rewrite_thm))
    val finished =
    	if null hyp_set
	   then rewrite_thm
       	   else foldr (uncurry (C MP)) rewrite_thm
	   	      (map LIST_CONJ hyp_set)
    val poss = strip_conj (rhs (concl finished))
    fun single p thm =
   	    RIGHT_CONV_RULE
	    (SOME_CONJ_CONV (REWR_CONV (UNBOOL_RULE
	    		(apply_rewrite depth RR p))) THENC
	     REWRITE_CONV []) thm
    fun all [] thm = raise Empty
      | all (p::ps) thm =
    (let val x = single p thm in (BOOL_RULE x  handle _ => all ps x) end)
    handle _ => all ps thm;
in
    all poss finished
end
and apply_rewrite depth RR conj =
let val (terms,disjs) = (map strip_conj ## strip_disj) (strip_imp_only conj)
    val sortf = sort (fn a => fn b => term_size (snd (strip_imp_only a))
    	      	     	      	    < term_size (snd (strip_imp_only b)))
    val solved = tryfind_e Empty
    	       	         (backchain_rewrite (depth + 1)
    	       	 	 (map ASSUME (flatten terms) @ RR)) (sortf disjs)
			 handle e => DECIDE ``~F``
in
    if not (exists (curry op= (concl solved)) (disjs)) then
       if dest_neg (concl solved) = conj andalso null (flatten terms)
       	  then solved
       	  else BOOL_RULE ((PURE_ONCE_REWRITE_CONV [
	       UNBOOL_RULE (tryfind_e Empty (backchain_rewrite (depth + 1) RR)
	       		   	    (flatten terms))] THENC
           REWRITE_CONV []) conj)
       else foldr (uncurry DISCHL_CONJ)
	      (BOOL_RULE ((ONCE_REWRITE_CONV [UNBOOL_RULE solved] THENC
	  	    REWRITE_CONV []) (list_mk_disj disjs))) terms
end
and backchain_rewrite depth RR term =
let val _ = trace 3 ("#" ^ int_to_string depth)
    val _ = if depth > !max_depth then raise Empty else ()
    val applicable = filter (can (C match_term term o LHS o concl)) RR
    val (quick,slow) = partition (curry op= T o RHS o concl) applicable
    val sortf = sort (fn a => fn b => length (hyp a) < length (hyp b))
    val quick_ordered = sortf quick
    val slow_ordered = sortf slow
in
    if is_imp_only term
       then DISCH (fst (dest_imp term))
       	    	  (backchain_rewrite depth
		      (map UNBOOL_RULE (CONJUNCTS
		      	   (ASSUME (fst (dest_imp term))))
		      	   @ RR)
		      (snd (dest_imp term))) else
    if term = F then (trace 3 "F" ; DECIDE ``~F``) else
    if term = T then (trace 3 "T" ; TRUTH) else
    if null applicable andalso not (is_neg term)
       then backchain_rewrite depth RR (mk_neg term)
       else
    tryfind_e Empty (perform_rewrite depth RR term) quick_ordered handle _ =>
    tryfind_e Empty (perform_rewrite depth RR term) slow_ordered
end

(*****************************************************************************)
(* ATTEMPT_REWRITE_PROOF : (thm list * thm list) ->                          *)
(*                                       (string * thm) -> (string * thm)    *)
(*    Attempts to prove a term by rewriting using the assumptions and extras *)
(*    The assumptions are converted as follows:                              *)
(*        A |- encode Y = y  --> A |- Y = decode y                           *)
(*        A |- X = Y         --> A |- X = Y : bool                           *)
(*        A |- X = Y         --> A |- P X = P Y                              *)
(*        A |- P             --> A |- P = T                                  *)
(*    The extras are converted as follows:                                   *)
(*        A |- P ==> Q       ==> A |- P ==> Q = T                            *)
(*        A |- P ==> X = Y   ==> A |- P ==> X = Y : bool                     *)
(*        A |- P ==> X = Y   ==> A |- P ==> Q X = Q Y                        *)
(*                                                                           *)
(*****************************************************************************)

fun fix_extra (thm',A) =
let val thm = SPEC_ALL thm'
    val (imps,eq) = strip_imp_only (concl thm)
in
    (if is_eq eq
       then if (type_of (lhs eq) = bool) then (thm::GSYM thm::A) else
       	    let val r = foldr (uncurry DISCH)
	    	      	      (AP_TERM (genvar (type_of (lhs eq) --> bool))
	    	  	   	       (UNDISCH_ALL_ONLY thm)) imps
            in (r::GSYM r::A)
	    end
       else foldr (uncurry DISCH) (UNBOOL_RULE (UNDISCH_ALL_ONLY thm)) imps::A)
   handle _ => A
end;

fun ap_decode thm =
let val target = type_of (lhs (concl thm))
    val t = type_of (rand (lhs (concl thm)))
    val thm' =  AP_TERM (get_decode_function target t) thm
    val encdec = FULL_ENCODE_DECODE_THM target t
in
    CONV_RULE (LAND_CONV (REWR_CONV encdec)) thm'
end;

fun fix_assum (thm,A) =
    (if is_eq (concl thm)
       then let val r = if is_encoded_term (LHS (concl thm)) andalso
       	    	      	   is_var (RHS (concl thm))
       	        then ap_decode thm
	        else if (type_of (lhs (concl thm)) = bool) then thm
	             else AP_TERM (genvar (type_of (lhs (concl thm)) --> bool))
		     	  thm
            in (r::GSYM r::A)
            end
       else UNBOOL_RULE thm::A) handle _ => A

val standard_backchain_thms =
    ref [COND_RAND,COND_RATOR,
    	 DECIDE ``(if a then b else c) = (a ==> b) /\ (~a ==> c)``,
	 DECIDE ``~a = (a ==> F)``];

fun ATTEMPT_REWRITE_PROOF (assums,extras) (string,thm) =
let val RR = foldl fix_assum (foldl fix_extra (!standard_backchain_thms)
    	     	   	     	    extras) assums
    val terms = strip_conj (fst (dest_imp_only (concl thm)))
    val _ = trace 3 "backtracking...\n";
    val _ = trace 4 (xlist_to_string thm_to_string RR);
    val _ = trace 4 "\n";
    val thms = map (fn x => backchain_rewrite 0 RR x before trace 3 "\n") terms
    	handle e => (trace 3 "!!\n"; raise e)
in
   (string:string,MATCH_MP thm (LIST_CONJ thms))
end

(*****************************************************************************)
(* PROPAGATE_ENCODERS_CONV : (thm list * thm list) -> term -> thm            *)
(*                                                                           *)
(*    PROPAGATE_ENCODERS_CONV (assumptions,extras) ``encode M``              *)
(*    propagates encoders through the term M under the assumptions given     *)
(*    with additional theorems to aid resolution given in extras. Theorems   *)
(*    for rewriting are found using 'return_matches' and the reference       *)
(*    functions !conversions.                                                *)
(*                                                                           *)
(*    If no rewrite matches a term then:                                     *)
(*       a) If the term is matched by function in !terminals then REFL term  *)
(*          is returned.                                                     *)
(*       b) If the term is matched by a polytypic theorem, ie. a function    *)
(*          in !polytypic_rewrites returns a theorem, then if that theorem   *)
(*          is not already present in rewrites another attempt is made,      *)
(*          otherwise, an exception is generated                             *)
(*       c) If none of the above occurs, an exception is generated.          *)
(*                                                                           *)
(*    Controlled through the references:                                     *)
(*            !rewrites  : thm list                                          *)
(*                List of propagation theorems in standard form.             *)
(*            !conversions : (int * string * (term -> thm)) list             *)
(*                List of conversions (results in conditional form)          *)
(*            !polytypic_rewrites : (int * string * (term -> thm)) list      *)
(*                List of polytypic propagation theorems                     *)
(*            !terminals : (string * (term -> bool)) list                    *)
(*                List of functions indicating stoppage.                     *)
(*    These are controlled through the functions:                            *)
(*            add_polytypic_rewrite, add_standard_conversion,                *)
(*            add_conditional_conversion, add_terminal                       *)
(*            and the corresponding remove_... functions                     *)
(*        The add_extended_terminal function can also determine the list of  *)
(*        assumptions when deciding whether to stop encoding.                *)
(*                                                                           *)
(*    Note: Free variables in 'extras' are instantiated to avoid variable    *)
(*    capture.                                                               *)
(*                                                                           *)
(*****************************************************************************)

local
val string =  for 1 78 (K #"-");
fun mconcat [] = String.implode string
  | mconcat ((n,s)::L) =
let val ns = explode ("Failure: " ^ int_to_string n)
in  implode (ns @ (List.take(string,length string - length ns))) ^
    "\n" ^ s ^ "\n" ^ mconcat L
end;
fun check_failure ((ematched,assums),term) =
    (map (fn (s,x) => (s,partial_resolve true (resolve_functions assums) x
    	       	  handle UNCHANGED => x)) ematched,
     assums,term);
fun describe_single_failure (pmatched,assums,term) =
   "  Term: " ^ term_to_string term ^ "\n" ^
   "  Assumptions: " ^ xlist_to_string thm_to_string assums ^
   "\n" ^ (if null pmatched then "" else
   "  ... However, the following list of theorems partially matched:\n" ^
	  xlist_to_string (fn (x,y) => x ^ ": " ^ thm_to_string y) pmatched)
fun op_set_eq f a1 a2 =
    null (op_set_diff f a1 a2) andalso null (op_set_diff f a2 a1)
fun eq_term t1 t2 = can (match_term t1) t2 andalso can (match_term t2) t1
fun eq_thm thm1 thm2 =
    eq_term (concl thm1) (concl thm2) andalso
    op_set_eq eq_term (hyp thm1) (hyp thm2)
fun subset a1 a2 = null (op_set_diff eq_thm a1 a2)
fun ssubset a1 a2 = subset a1 a2 andalso not (subset a2 a1)
fun supercedes (p1,a1,t1) (p2,a2,t2) =
    (t2 = t1) andalso
    	((ssubset (map snd p1) (map snd p2) orelse
	 (subset (map snd p1) (map snd p2) andalso subset a1 a2)))
fun reduce [] = []
  | reduce (x::L) =
    if exists (supercedes x) L
    then reduce L
    else x::reduce (filter (not o C supercedes x) L)
in
fun describe_match_failure L =
let val failures = map check_failure L
    val all_failures = reduce failures
    val full_fails = map describe_single_failure all_failures
in
    case full_fails
    of [] => raise Empty
    |  [x] => raise (mkStandardExn "PROPAGATE_ENCODERS_CONV"
       	      	    ("No rewrite matched the following:\n" ^ x))
    |  _   => raise (mkStandardExn "PROPAGATE_ENCODERS_CONV"
       	      	    ("No rewrite matched the following:\n" ^
		    mconcat (enumerate 0 full_fails)))
end
end;


val terminals = ref ([] : (string * (thm list -> term -> bool)) list);
val polytypic_rewrites = ref ([] : (int * string * (term -> thm)) list);
val conversions = ref ([] : (int * string * (term -> thm)) list);
fun clear_rewrites () =
    (rewrites := Net.empty ;
     polytypic_rewrites := [] ;
     conversions := [] ;
     terminals := []);

val propagate_encoders_conv_data =
       ref (NONE : ((thm list * thm list) * term) option);

local
exception MatchFailure of (((string * thm) list * thm list) * term) list
val this_function = "PROPAGATE_ENCODERS_CONV"
fun exists_polytypic_theorem previous (priority,name,theorem) =
let val matches = Net.match (lhs (snd (strip_imp (concl theorem)))) previous
in
    exists (fn (p,n,t) => (p = priority) andalso
    	       	       (aconv (concl theorem) (concl t))) matches
end handle e => wrapException "exists_polytypic_theorem" e
fun tryadd_polytypic_theorem failure success term =
let val previous = !rewrites
    val polys = mapfilter (fn (p,s,f) => (p,s,f term)) (!polytypic_rewrites)
        handle e => wrapException "tryadd_polytypic_theorem" e
    val new_polys = filter (not o exists_polytypic_theorem previous) polys
        handle e => wrapException "tryadd_polytypic_theorem" e
    val sorted = sort (fn (p1,_,_) => fn (p2,_,_) => p1 > p2) new_polys
in
    case sorted
    of [] => failure ()
    |  ((priority,name,thm)::_) =>
       ((trace 1 ("A(" ^ name ^ ")") ;
         trace 2 ("Polytypic theorem: " ^ thm_to_string thm) ;
         (add_conditional_rewrite priority name thm
	 handle e => wrapException "tryadd_polytypic_theorem" e) ;
	 success ()))

end
fun fix_extra e =
let val vs = thm_frees (SPEC_ALL e)
    val vs' = map (fn x => x |-> (genvar o type_of) x) vs
in
    INST vs' e
end
fun terminate (assums,extras) term =
let val (s,_) = first (fn (x,y) => y assums term) (!terminals)
    val _ = trace 1 ("T(" ^ s ^ ")")
in
    SOME (REFL term)
end handle _ => NONE
fun try_all_matches AE [] exns = raise (MatchFailure exns)
  | try_all_matches AE (match::matches) exns =
    PROPAGATE_THENC AE PEC match
    handle MatchFailure L =>
    (try_all_matches AE matches (exns @ L))
and try_backchain_matches AE [] failure exns
    = raise (MatchFailure (failure :: exns))
  | try_backchain_matches AE (ematch::matches) ((fails,assums),term) exns =
    PROPAGATE_THENC AE PEC
        (ATTEMPT_REWRITE_PROOF AE ematch)
    handle Empty => try_backchain_matches AE matches
    	   	    ((ematch::fails,assums),term) exns
         | MatchFailure L => try_backchain_matches AE matches
	            ((fails,assums),term) (exns @ L)
and PEC (AE as (assums,extras)) term =
    case (terminate AE term)
    of SOME thm => thm
    |  NONE =>
    let val _ = propagate_encoders_conv_data := SOME (AE,term)
        val (ematched,matches) = return_matches assums term
	val cmatches =
	    mapfilter (fn (p,n,func) => match_single_rewrite assums
	    	      	  		term (p,n,func term)) (!conversions)
    in
        case (matches @ cmatches)
        of [] => (tryadd_polytypic_theorem
	      	  (fn () => (try_backchain_matches AE ematched
		      	         (([],assums),term) []))
                  (fn () => PEC AE term)
		  term)
	|  L => try_all_matches AE L []
    end
in
fun PROPAGATE_ENCODERS_CONV AE term =
    ((scrub_rewrites() ;
     PEC ((I ## map fix_extra) AE) term) before
      (trace 1 "\n" ; propagate_encoders_conv_data := NONE))
    handle (MatchFailure L) => describe_match_failure L
end;

fun add_extended_terminal (s,func) =
    if exists (curry op= s o fst) (!terminals)
       then raise (mkStandardExn "add_terminal"
       	    	    ("Terminal " ^ s ^ " already exists!"))
       else terminals := (s,func) :: (!terminals);

fun add_terminal (s,func) = add_extended_terminal (s,K func);

fun remove_terminal s =
    terminals := filter (not o curry op= s o fst) (!terminals)

fun add_polytypic_rewrite priority name func =
    if exists (curry op= name o (fn (a,b,c) => b)) (!polytypic_rewrites)
       then raise (mkStandardExn "add_polytypic_rewrite"
       	    	    ("Polytypic rewrite " ^ name ^ " already exists!"))
       else polytypic_rewrites := (priority,name,func) :: (!polytypic_rewrites)

fun remove_polytypic_rewrite s =
    polytypic_rewrites :=
      filter (not o curry op= s o (fn (a,b,c) => b)) (!polytypic_rewrites)

fun add_standard_conversion priority name func =
    if exists (curry op= name o (fn (a,b,c) => b)) (!conversions)
       then raise (mkStandardExn "add_standard_conversion"
       	    	    ("Conversion " ^ name ^ " already exists!"))
       else conversions := (priority,name,conditionize_rewrite o func) ::
       	    		   (!conversions)

fun add_conditional_conversion priority name func =
    if exists (curry op= name o (fn (a,b,c) => b)) (!conversions)
       then raise (mkStandardExn "add_conditional_conversion"
       	    	    ("Conversion " ^ name ^ " already exists!"))
       else conversions := (priority,name,func) ::
       	    		   (!conversions)

fun remove_conversion s =
    conversions := filter (not o curry op= s o (fn (a,b,c) => b)) (!conversions)


(*****************************************************************************)
(* Case processing:                                                          *)
(*                                                                           *)
(* find_comb : int list -> term -> term                                      *)
(*     Repeatedly finds the nth sub-term, eg:                                *)
(*        find_comb [1,2] ``f (g a b) c`` = ``b``                            *)
(*                                                                           *)
(* outermost_constructor      : term -> thm list -> (term -> term) option    *)
(*     Returns a function that finds the outermost leftmost constructed term *)
(*     such that the corresponding value in the template term is a variable  *)
(*     Eg. outermost_constructor ``SEG (SUC 0) 0 a`` (tl (CONJUNCTS SEG))    *)
(*         returns that function that returns the last argument from terms   *)
(*         of the form: SEG a b c = d                                        *)
(*     Fails if the theorems supplied are not function clauses, or if the    *)
(*     the function constants found in the term and clauses are not          *)
(*     equivalent up to the renaming of type variables                       *)
(*                                                                           *)
(* group_by_constructor                                                      *)
(*  :term -> (term -> term) -> thm list -> hol_type * (term * thm list) list *)
(*     Groups clauses to lists matching the outer most left most constructor *)
(*     The function supplied strips the constructor out of the term          *)
(*     Returns a list of clause * thm where if:                              *)
(*        function  = ``f a b c`` then                                       *)
(*        clause(i) = ``f (Ci x y z) a b c                                   *)
(*     Fails if no clauses are given, the function used fails or returns     *)
(*     a term that is not a compound type, or the left hand sides of the     *)
(*     clauses and the function term supplied are inconsistent.              *)
(*                                                                           *)
(* alpha_match_clauses :                                                     *)
(*        : (term -> term) -> (thm * term list) list -> term list * thm list *)
(*     Takes a list of function clauses and a list of missing clauses and    *)
(*     alpha converts them to match each other                               *)
(*     -- The list of missing clauses is simply concatenated, the clauses    *)
(*        are matched using their left hand sides with the sub-term          *)
(*        indicated by the function skipped.                                 *)
(*     Fails if the function given fails or the clauses are not of the       *)
(*     correct form, or if the left hand side of the clauses differ by more  *)
(*     than the sub-term located.                                            *)
(*                                                                           *)
(* condense_missing : (term -> term) -> term list -> term list               *)
(*     Takes a list of missing clauses and determines whether the set of     *)
(*     constructors determined by applying the function is complete, ie.     *)
(*     contains all the constructors for that type:                          *)
(*         condense_missing (rand o lhs) [``f (SUC n)``,``f 0``] = [``f n``] *)
(*     Notes: All arguments to constructors must be free variables           *)
(*            The function given should always perform 'lhs' (historical)    *)
(*                                                                           *)
(* clause_to_case : thm -> thm * term list                                   *)
(*     Converts a function defined using clause structure to use case        *)
(*     Returns a list of missing clauses                                     *)
(*                                                                           *)
(*     Algorithm:                                                            *)
(*       0. Group function clauses by the leftmost outermost constructor.    *)
(*       1. Recursively apply this algorithm to these groups                 *)
(*          --> For a type with n constructors should have n clauses         *)
(*       2. Alpha convert the clauses so that bound variables all match up   *)
(*       3. Fully specialise then generalise for bound variables in the      *)
(*          constructor in question, in left to right fashion.               *)
(*       4. Use Modus Ponens and the "func_case" theorem:                    *)
(*              |-   (!.. f (C0 ..) = A0) /\ .. /\ (!.. f (Cn ..) = An)      *)
(*                 = !x. f x = case A0 ... An x                              *)
(*                                                                           *)
(*     When grouping by constructor, a function term is instantiated to      *)
(*     match the constructor in use to be passed to the recursive call.      *)
(*     Eg. clause_to_case (f [] a) [|- f [] 0 = A, |- f [] (SUC n) = B]      *)
(*     The algorithm terminates if this clause does not have a free variable *)
(*     at the left most outermost constructor.                               *)
(*                                                                           *)
(*     If the grouping by constructor procedure returns an empty group       *)
(*     (this case is missing from the definition) the algorithm returns the  *)
(*     reflection of this clause and adds it to the list of missing calls.   *)
(*                                                                           *)
(*     Fails if the theorem given is not a proper function (conjunction of   *)
(*     universally quantified equalities) or two clauses exist which have    *)
(*     left hand sides that are alpha convertable.                           *)
(*     May also fail if a theorem return by "func_case" is of the wrong form *)
(*     which may happen if the user supplies such a theorem.                 *)
(*                                                                           *)
(* clause_to_case_list : int list -> thm -> (thm * term list)                *)
(*     Exactly as above, but a list is used to indicate the order in which   *)
(*     constructors are processed. Eg.                                       *)
(*         clause_to_case_list [[2],[1]]                                     *)
(*                  |- (f 0 0 = A) /\ (f (SUC n) 0 = B) /\                   *)
(*                     (f (SUC n) 0 = C) /\ (f (SUC n) (SUC m) = C)          *)
(*     will process the second argument first.                               *)
(*     If the list given does not correctly split the constructors then      *)
(*     this function will fail.                                              *)
(*                                                                           *)
(*****************************************************************************)

local
fun fc [] y = y
  | fc (x::xs) y = fc xs (el x (snd (strip_comb y)))
in
fun find_comb l tm = fc l tm handle e =>
	raise (mkStandardExn "find_comb"
		("Could not find the term specified by the list: " ^
		 xlist_to_string int_to_string l))
end

local
fun find_mismatch tm1 tm2 =
let	val (f1,l1) = strip_comb tm1
	val (f2,l2) = strip_comb tm2
	val comb = enumerate 1 (zip l1 l2) handle _ => []
in
	if f1 = f2 orelse not (can polytypicLib.constructors_of (type_of f1))
	then tryfind_e Empty (uncurry cons o (I ## uncurry find_mismatch)) comb
	else 	if is_var f1 andalso is_var f2
		then raise Empty else []
end
fun lex_less _ [] = false
  | lex_less [] _ = true
  | lex_less (x::xs) (y::ys) = x < y orelse x = y andalso lex_less xs ys
in
fun outermost_constructor function clauses =
let	val stripped = map (lhs o snd o strip_forall o concl) clauses
		handle e => raise (mkStandardExn "outermost_constructor"
					"Theorems are not all of the form: \"|- !a0 .. an. F = X\"")
	val normalised = map (fn x => inst (snd (match_term (repeat rator x) (repeat rator function))) x) stripped
		handle e => raise (mkStandardExn "outermost_constructor"
					"Theorems and function term supplied use different function constants")
	val lists = mapfilter (find_mismatch function) normalised
	val sorted = sort lex_less lists
	val list = hd sorted handle _ => []
in
	case list
	of [] => NONE
        |  list  => (trace 3 ("CP:" ^  (xlist_to_string int_to_string list) ^ "\n") ;
			SOME (find_comb list o lhs o snd o strip_forall))
end
end;

fun group_by_constructor _ _ [] =
    raise (mkStandardExn "group_by_constructor" "No function clauses given!")
  | group_by_constructor function outermost clauses =
let	fun om x = outermost x handle e => wrapException "group_by_constructor (outermost)" e
	val terms = map (fn y => (repeat rator (om (concl y)),y)) clauses
	val t = snd (strip_fun (type_of (fst (hd terms))))
	val cs = polytypicLib.constructors_of t handle e =>
		raise (mkStandardExn "group_by_constructor"
			("Function to find constructed terms returned a term with a non-compound type: " ^
			 type_to_string t))
	val matched = map (fn c => (c,map snd (filter (same_const c o fst) terms))) cs
	val _ = if foldl op+ 0 (map (length o snd) matched) = length clauses then ()
			else raise (mkStandardExn "group_by_constructor"
				("The argument pointed to by the function given contains values " ^
				 "which are not constructed terms: " ^ xlist_to_string (term_to_string o fst) terms))
	val replace = om (mk_eq(function,function))
	val fvs = ref (map (fst o dest_var) (free_vars (mk_abs(replace,function))))
	fun genvar t =
	let	val s = first (not o C mem (!fvs)) (map (implode o base26 o fst) (enumerate (length (!fvs)) (""::(!fvs))))
	in	(fvs := s :: (!fvs) ; mk_var(s,t))
	end
	fun mk_cons t c =
	let	val c' = inst [snd (strip_fun (type_of c)) |-> t] c
	in	list_mk_comb(c',map genvar (fst (strip_fun (type_of c')))) end
	fun sub a = subst [replace |-> mk_cons (type_of replace) a]
in
	(t,map (fn (a,b) => (sub a function,b)) matched) handle e => wrapException "group_by_constructor" e
end;

local
val newvars = ref [];
fun gv t =
let val v = genvar (type_of t)
in  (newvars := (v |-> t) :: (!newvars) ; v) end;
fun subst_all_x x term =
    if x = term then gv term
    else if is_comb term
    	    then mk_comb (subst_all_x x (rator term),subst_all_x x (rand term))
	    else if is_abs term
	    	    then mk_abs(bvar term,subst_all_x x (body term))
		    else term;
(* subst_om substitutes ONLY the term matching the function om (f term). *)
(* It does this by substituting everything, then replacing the incorrect *)
(* things.                                                               *)
fun subst_om om f g term =
let val x = om (g term)
    val _ = newvars := [];
    val all_subst = g (subst_all_x x term)
    val y = om all_subst
in
    subst (filter (not o curry op= y o #redex) (!newvars)) (f all_subst)
end;
in
fun alpha_match_clauses outermost [] = ([],[])
  | alpha_match_clauses outermost [(thm,missing)] = (missing,[SPEC_ALL thm])
  | alpha_match_clauses outermost ((lthm,lmissing)::clauses) =
let fun om x = outermost x
        handle e => wrapException "alpha_match_clauses (outermost)" e
    val (rmissing,thms) = alpha_match_clauses om clauses
    val rthm = hd thms
    fun split x = (lhs o snd o strip_forall o concl) x
    	handle e => raise (mkStandardExn "alpha_match_clauses"
             "Clauses must all be of the form: \"|- !a0..an. f X = Y\"")
    val l = subst_om om lhs (fn x => mk_eq(x,x)) (split lthm)
    val r = subst_om om lhs (fn x => mk_eq(x,x)) (split rthm)
    val match = match_term l r
        handle e => raise (mkStandardExn "alpha_match_clauses"
             ("The left hand side of two or more clauses differs " ^
              "outside of the term indicated by 'outermost'"))
in
 (rmissing @ lmissing, (INST_TY_TERM match (SPEC_ALL lthm))::thms)
 handle e => wrapException "alpha_match_clauses" e
end
end;

local
fun match_lists f [] [] = []
  | match_lists f []  _ = raise Empty
  | match_lists f (x::xs) L =
let val (y,ys) = pluck (f x) L handle e => raise Empty
in  (x,y)::match_lists f xs ys
end;
fun freebase26 n vars =
let val var = implode (base26 n)
in  if mem var vars then (freebase26 (n + 1) vars) else var
end
in
fun condense_missing outermost missing =
let val constructors = map (fn x => outermost (mk_eq (x,x))) missing
    handle e => wrapException "condense_missing (outermost)" e
in
   (case (mk_set (map (base_type o type_of) constructors))
    of [] => missing
    | (x::y::ys) => raise (mkDebugExn "condense_missing"
      		    "Types of constructors do not match!")
    | [x] =>
    if all (all is_var o snd o strip_comb) constructors andalso
       can (match_lists (fn b => can (match_term (fst (strip_comb b))))
       	   		 constructors) (constructors_of x)
       then let val var = case (total (tryfind (hd o free_vars)) constructors)
       	    	    	  of SOME var => var
                          |  NONE =>
			     mk_var(freebase26 0 (map (fst o dest_var)
			     		       	      (free_varsl missing)),x)
		val _ = trace 1 ("M:[" ^ int_to_string (length missing) ^ "]")
       	    in [subst (map (fn c => c |-> var) constructors) (hd missing)]
	    end
       else missing)
   handle e => wrapException "condense_missing" e
end
end;

local
fun wrap s = wrapException ("clause_to_case_list" ^ s)
fun ctc omc function [] = (REFL function,[function])
  | ctc omc (function:term) (clauses:thm list) : thm * term list =
    case (omc function clauses)
    of NONE => if length clauses = 1
       	       	  then (hd clauses,[])
		  else raise (mkStandardExn "clause_to_case_list"
    		"Two or more function clauses do not differ by constructors")
    | SOME outermost =>
     let val grouped = (group_by_constructor function outermost clauses)
     	     	       handle e => wrap "" e
         val (t,split_clauses) = (I ## map (uncurry (ctc omc))) grouped
         val (missing,next_thm) = alpha_match_clauses outermost split_clauses
	     	       handle e => wrap "" e
         val missing' = condense_missing outermost missing
         fun gen thm =
         let val list = snd (strip_comb (outermost (concl thm)))
	     	      	handle e => wrap " (outermost)" e
         in GENL list thm end
         val thm = LIST_CONJ (map gen next_thm)
         val rule = fst (EQ_IMP_RULE (SPEC_ALL
	     	    	(generate_source_theorem "func_case" t)))
		    handle e => wrap "" e
 in
  (HO_MATCH_MP rule thm,missing')
  handle e => raise (mkStandardExn "clause_to_case_list"
   ("Could not match the normalised group clauses:\n " ^
    thm_to_string thm ^ "\n" ^
    "with the \"func_case\" theorem generated for type: " ^
    type_to_string t ^ ":\n" ^
    thm_to_string rule))
 end
in
fun clause_to_case_list list thm =
let	val clauses = CONJUNCTS thm
	val left = (repeat rator o lhs o snd o strip_forall o concl o hd) clauses
		handle e => raise (mkStandardExn "clause_to_case_list"
				"Theorem given is not a conjunction of universally quantified equalities")
	val function = list_mk_comb(left,map (fn (a,b) => (mk_var(implode (base26 a),b)))
		(enumerate 0 (fst (strip_fun (type_of left)))))
		handle e => wrapException "clause_to_case_list" e
	val rlist = ref list
	fun omc function clauses =
		case (!rlist)
		of [] => outermost_constructor function clauses
		|  (x::xs) =>
		let	val a = find_comb x function
				handle e => raise (mkStandardExn "clause_to_case_list"
						("The term path: " ^ xlist_to_string int_to_string x ^
						 " cannot find a sub-term in the current function: "
						^ term_to_string function))
			val _ = if is_var a then () else
				raise (mkStandardExn "clause_to_case_list"
						("The term path: " ^ xlist_to_string int_to_string x ^
						 " is selecting a constructed term: " ^ term_to_string function))
		in	(rlist := xs ; SOME (find_comb x o lhs o snd o strip_forall)) end

in
	ctc omc function clauses
end
fun clause_to_case thm =
    clause_to_case_list [] thm handle e => wrapException "clause_to_case" e
end;

(*****************************************************************************)
(* mk_func_case_thm : hol_type -> thm                                        *)
(*     Generates a theorem of the form:                                      *)
(*     |-   (!.. f (C0 ..) = A0 ..) /\ (!.. f (Cn ..) = An ..)               *)
(*        = !x. f x = case A0 .. An x                                        *)
(*     Simply generates the right hand side, applies CASE_SPLIT_CONV and     *)
(*     rewrites the left hand side to remove the case statements.            *)
(*     Fails if the type in question does not have a case definition or      *)
(*     constant supplied for it.                                             *)
(*                                                                           *)
(*     A theorem generator called "func_case" is added at load time.         *)
(*                                                                           *)
(*****************************************************************************)

local
fun get_consts s ts = map (fn (a,b) => (mk_var(s ^ implode (base26 a),b)))
    	       	      	      (enumerate 0 ts)
fun wrap e = wrapException "mk_func_case_thm" e
in
fun mk_func_case_thm t =
let	val c = TypeBase.case_const_of t handle e => wrap e
	val case_def = TypeBase.case_def_of t  handle e => wrap e
	val (ts,rtype) = strip_fun (type_of c)
	val consts = get_consts "f_" ts
	val case_term = fst (dest_comb (list_mk_comb(c,consts)))
	    	      	handle e => wrap e
	val xvar = mk_var("arg",fst (dom_rng (type_of case_term)))
	    	   handle e => wrap e
	val fvar = mk_var("F",type_of xvar --> rtype)
	val full_term = mk_forall(xvar,mk_eq(mk_comb(fvar,xvar),
	    	      mk_comb(case_term,xvar)))  handle e => wrap e
in
	GSYM (RIGHT_CONV_RULE (EVERY_CONJ_CONV (STRIP_QUANT_CONV
		(RAND_CONV (FIRST_CONV (map REWR_CONV (CONJUNCTS case_def))))))
			   (CASE_SPLIT_CONV full_term))
	handle e => wrap e
end
end;

val _ = add_rule_source_theorem_generator "func_case"
      	    (can constructors_of) mk_func_case_thm;

(*****************************************************************************)
(* create_lambda_propagation_term : term -> term                             *)
(*     Given a term of the form: \x (y,z) ... . A  returns the conclusion of *)
(*     a propagation  theorem for lambda abstractions.                       *)
(*                                                                           *)
(* prove_lambda_propagation_term  : term -> thm                              *)
(*     Proves the conclusion generated by the previous function.             *)
(*                                                                           *)
(* make_lambda_propagation_theorem : term -> thm                             *)
(*     Creates a lambda propagation theorem to match the term given.         *)
(*                                                                           *)
(*****************************************************************************)

local
open pairSyntax
fun compn [] _ = []
  | compn (n::xs) L = op:: ((I ## compn xs) (split_after n L));
fun wrap e = wrapException "general_lambda" e
fun general_lambda tm =
let	val terms = map (length o strip_pair) (fst (strip_pabs tm))
	    	    handle e => wrap e
	val names = for 0 (foldl op+ 0 terms) (String.implode o base26)
	val types = for 0 (foldl op+ 0 terms)
	    	    	  (mk_vartype o String.implode o cons #"'" o base26)
	val vars = map2 (curry mk_var) names types handle e => wrap e
	val pairs = map list_mk_pair (compn terms vars) handle e => wrap e

	val out = mk_var(last names,foldr (op-->) (last types) (butlast types))
in
	list_mk_pabs (pairs,list_mk_comb(out,butlast vars)) handle e => wrap e
end
fun split_pairs [] = []
  | split_pairs (x::xs) =
	split_pairs (mk_fst x::mk_snd x::xs) handle e => x::split_pairs xs;
fun wrap e = wrapException "general_lambda_propagation_term" e
fun imp_conj [] term = term
  | imp_conj xs term = mk_imp(list_mk_conj xs,term);
in
fun create_lambda_propagation_term term =
let	val gterm = general_lambda term handle e => wrap e
	val vt = mk_vartype "'output";
	fun enc tm = mk_comb(mk_var("enc",type_of tm --> vt),tm);

	val (pairs,body) = strip_pabs gterm
	val vns = map (String.concat o map (fst o dest_var) o strip_pair) pairs
	val vts = map type_of pairs
	val lterm = enc (list_mk_comb(gterm,map2 (curry mk_var) vns vts));

	val rvars = map (C (curry mk_var) vt o prime) vns;
	val rterm = list_mk_comb(list_mk_abs(rvars,list_mk_comb(mk_var(prime (fst(dest_var(fst(strip_comb body)))),
				foldl (fn (a,b) => (type_of a --> b)) vt rvars),rvars)),rvars)

	val encs = map2 (curry mk_eq) (map enc (map2 (curry mk_var) vns vts)) rvars
	val decs = map (fn e => mk_comb(mk_var("dec",vt --> type_of (rand (lhs e))),rhs e)) encs;
	val dets = map (curry mk_comb (mk_var("det",vt --> bool)) o rhs) encs;


	val eterm = imp_conj dets (mk_eq(enc (list_mk_comb(fst (strip_comb body),split_pairs decs)),
					snd (strip_pabs (fst (strip_comb rterm)))));

	val eds = map2 (fn a => fn b => mk_forall(rand(lhs b),mk_eq(mk_comb(rator a,lhs b),rand (lhs b)))) decs encs;
	val eps = map2 (fn a => fn b => mk_forall(rand(lhs b),mk_comb(rator a,lhs b))) dets encs;
in
	imp_conj (eds @ eps) (mk_imp(foldr mk_conj eterm encs,mk_eq(lterm,rterm)))
end
end;

fun prove_lambda_propagation_term term =
let	val tac = REPEAT STRIP_TAC THEN pairLib.GEN_BETA_TAC THEN
		REPEAT (FIRST_ASSUM (SUBST_ALL_TAC o GSYM) THEN WEAKEN_TAC (fn a => is_eq a andalso lhs a = rhs a)) THEN
		ASSUM_LIST (fn list => RULE_ASSUM_TAC (fn th => if is_forall (concl th) then th else
			PURE_REWRITE_RULE (filter (is_forall o concl) list) th)) THEN
		FIRST_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN ACCEPT_TAC TRUTH
in
	case (tac ([],term) handle e => wrapException "prove_lambda_propagation_term" e)
	of ([],f) => (f [] handle e => wrapException "prove_lambda_propagation_term" e)
	|  _ => raise (mkStandardExn "prove_lambda_propagation_term"
				("Tactic used by this function did not fully solve the term:\n" ^ term_to_string term))
end;

local
fun strip_to_abs term =
    if pairLib.is_pabs term then term else strip_to_abs (rator term)
in
fun make_lambda_propagation_theorem term =
    prove_lambda_propagation_term
    	    (create_lambda_propagation_term (strip_to_abs (rand term)))
	    handle e => wrapException "make_lambda_propagation_theorem" e
end;

(*****************************************************************************)
(* polytypic_let_conv : term -> thm                                          *)
(*     Proves a theorem similar to the lambda conversion, but for let        *)
(*     constructions.                                                        *)
(*****************************************************************************)

fun mk_simplified_let let_term =
let val ty_vars = map (map (fn x => gen_tyvar()) o fst) let_term;
    val prod_types = map pairSyntax.list_mk_prod ty_vars
    val result_type = gen_tyvar();

    val v = ref 0;
    fun next_var t = (mk_var(implode (base26 (!v)),t)) before (v := !v + 1);

    val vars = zip (map (pairSyntax.list_mk_pair o map next_var) ty_vars)
    	       	   (map next_var prod_types);
    val all_vars = flatten (map (pairSyntax.strip_pair o fst) vars)
    val result_var = next_var (foldr op--> result_type
    		     	      	     (map type_of all_vars));
    val result_term = list_mk_comb(result_var,all_vars);
    val simplified_let = pairSyntax.mk_anylet (vars,result_term)
    val encoder = next_var (type_of simplified_let --> gen_tyvar());
in
    (encoder,PURE_REWRITE_CONV [LET_THM] simplified_let)
end handle e => wrapException "mk_simplified_let" e;

fun polytypic_let_conv term =
let val _ = trace 2 "->polytypic_let_conv\n";
    val _ = (pairSyntax.dest_anylet (rand term)) handle _ =>
    	raise (mkStandardExn "polytypic_let_conv"
	      ("Term: " ^ term_to_string term ^
	       "\nis not an encoded let term"));
    val (let_term,result) =
    	           (map (pairSyntax.strip_pair ## I) ## I)
    		   (pairSyntax.dest_anylet (rand term));
    val let_thm1 = (uncurry AP_TERM o mk_simplified_let) let_term;
    val (_,let_thm2) = mk_simplified_let (map (C cons [] o hd ## I) let_term)

    val lambda_thm = make_lambda_propagation_theorem (rhs (concl let_thm1))
    	handle e => wrapException "polytypic_let_conv" e
in
    CONV_RULE (RAND_CONV (RAND_CONV (
    	      LAND_CONV (REWR_CONV (GSYM let_thm1)) THENC
	      RAND_CONV (REWR_CONV (GSYM let_thm2))))) lambda_thm
        handle e => raise (mkDebugExn "polytypic_let_conv"
	       	 ("Could not rewrite lambda theorem:\n " ^
		  thm_to_string lambda_thm ^ "\nto a let expression using:\n" ^
		  thm_to_string let_thm1 ^ "\nand\n" ^
		  thm_to_string let_thm2))
end;

(*****************************************************************************)
(* mk_affirmation_theorems : hol_type -> thm list                            *)
(*                                                                           *)
(*    Returns a list of theorems of the form:                                *)
(*    |- ~(?a... x = C0 a ..) /\ ~(?a... x = C1 a ..) ==> (?a... x = Cn a ..)*)
(*                                                                           *)
(*****************************************************************************)

local
fun wrap e = wrapException "mk_affirmation_theorems" e
fun fix_term term thm =
    DISCH_ALL_CONJ (PURE_REWRITE_RULE [satTheory.NOT_NOT]
    		   		      (MATCH_MP IMP_F (DISCH term thm)))
fun ORDER_CONV term =
let val (l,r) = strip_exists (dest_neg term)
in  case (intersect (free_vars_lr r) l)
    of [] => REFL term
    | order => RAND_CONV (ORDER_EXISTS_CONV order) term
end;
in
fun mk_affirmation_theorems t =
let val nchotomy = SPEC_ALL (TypeBase.nchotomy_of t) handle e => wrap e
    val negated =
        CONV_HYP ORDER_CONV (REWRITE_RULE [] (UNDISCH_CONJ
		 (CONV_RULE (LAND_CONV NNF_CONV)
		 	    (CONTRAPOS (DISCH T nchotomy)))))
    val terms = hyp negated
in
    map (C fix_term negated) terms
end
end;

(*****************************************************************************)
(* EXISTS_REFL_CONV : term -> thm                                            *)
(*    Proves the theorem  |- (?a. b = a) = T  using b as a witness.          *)
(*                                                                           *)
(*****************************************************************************)

fun EXISTS_REFL_CONV term =
let val (var,body) = dest_exists term
    val thm = EXISTS (term,lhs body) (REFL (lhs body))
in
    REWRITE_CONV [thm] term
end

(*****************************************************************************)
(* set_destructors : hol_type -> thm list -> unit                            *)
(*    Sets the destructors for a type and redefines the initial theorem.     *)
(*    Destructors must be of the following form:                             *)
(*       |- !a ... . F (C a ...) = a, ... |- !a b ... . G (C a b ..) = b     *)
(*                                                                           *)
(* nested_constructor_rewrite : term -> thm                                  *)
(*     Returns a polytypic rewrite that converts a nested constructor:       *)
(*        |- bool (?a b. x = C' (C a) (C b)) =                               *)
(*           bool (?a b. x = C' a b) /\ (?a. D x = C a) /\ (?b. D' x = C b)  *)
(*                                                                           *)
(* nested_constructor_theorem : term -> thm                                  *)
(*     Returns a theorem that resolves nested constructors:                  *)
(*     |- (?a b. x = C' a b) /\ (?a. D x = C a) /\ (?b. D' x = C b) ==>      *)
(*        ?a b. x = C' (C a) (C b)                                           *)
(*                                                                           *)
(*****************************************************************************)

local
fun mk_initial [] = raise (mkDebugExn "mk_initial" "Empty list supplied!")
  | mk_initial dest_list =
let val list = map SPEC_ALL dest_list
    val cs = with_exn (map (rand o lhs o concl)) list
    	     	      (mkDebugExn "mk_initial" "Invalid list of constructors")
    val normalized = with_exn (map (C (PART_MATCH (rand o lhs)) (hd cs))) list
    		      (mkDebugExn "mk_initial"
		       "Constructors in list are not identical")
    val constructor = hd cs
    val vars = snd (strip_comb constructor)
    val _ = if exists (not o is_var) vars then
    	    raise (mkStandardExn "mk_initial"
	    	   "Destructor not applied to a ground constructed term!")
            else ();
    val t = type_of constructor
    val arg = variant vars (mk_var("arg",t))
    val left = mk_eq(arg,constructor)
    val term = mk_forall(arg,mk_eq(left,list_mk_conj(list_mk_exists(vars,left)::
		map (subst [constructor |-> arg] o concl) normalized)));
    val thms = mapfilter (fn f => f t) [TypeBase.distinct_of,GSYM o TypeBase.distinct_of,
    	        TypeBase.one_one_of];
in
    (case ((Cases THEN
     REPEAT (CHANGED_TAC (REWRITE_TAC (thms @ list))) THEN
     EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
     CONV_TAC (TOP_DEPTH_CONV EXISTS_AND_CONV THENC
     	       EVERY_CONJ_CONV EXISTS_REFL_CONV) THEN
     REWRITE_TAC [])
     ([],term))
    of ([],func) => func []
    |  _ => raise Empty)
    handle e => raise (mkDebugExn "mk_initial"
       	    	  	      "Failed to prove initial theorem!")
end
fun generalise_term_type t term =
let val (c,args) = strip_comb term
    val c' = first (can (C match_term c)) (constructors_of t)
in
    list_mk_comb(c',map2 generalise_term_type
    			 (fst (strip_fun (type_of c'))) args)
end handle e =>
    if is_var term then mk_var(fst (dest_var term),t) else raise e;
fun rewrite_thm name initials body =
let val na =  mkStandardExn name "Not a nested constructor"
    val initial_type = type_of (hd (fst (strip_forall (concl (hd
    		       	       (CONJUNCTS initials))))));
    val (_,eq) = strip_exists body
    val new_term = generalise_term_type initial_type (rhs eq)
    val nvars = free_vars_lr new_term
    val var = variant nvars (mk_var("argument",initial_type));
    val equality = mk_eq(var,new_term);
    val _ = if null nvars then raise na else ()
    val thm = tryfind (fn initial => SPEC_ALL (UNDISCH_ALL (
    	       PART_MATCH (lhs o snd o strip_forall o snd o strip_imp)
    	      		  (DISCH_ALL initial) equality))) (CONJUNCTS initials)
    val thm' = RIGHT_CONV_RULE
    	       (TOP_DEPTH_CONV EXISTS_AND_CONV THENC
    	       	    EVERY_CONJ_CONV (TRY_CONV EXISTS_REFL_CONV) THENC
				PURE_REWRITE_CONV [AND_CLAUSES])
    	       		       (foldr (MK_EXISTS o uncurry GEN) thm nvars);
    val _ = if not (is_conj (rhs (concl thm'))) then raise na else ()
in
    thm'
end
fun single_term term thm =
let val (var,body) = dest_forall term
    val d = rator (lhs body)
    val e = rator (rand (lhs body))
    val enc = get_encode_function (type_of (rand (lhs body))) (type_of var)
    val dec = get_decode_function (type_of (rand (lhs body))) (type_of var)
in
    INST [d |-> dec, e |-> enc] thm
end
fun fix_hyp thm =
    foldl (uncurry single_term) thm (hyp thm);
in
fun set_destructors target destructors =
let val _ = trace 2 "set_destructors"
    val list1 = map (fn x => ((fst o strip_comb o rand o lhs o
    	      	    	       snd o strip_forall o concl) x,
    	      	    	     SPEC_ALL x)) destructors
    val t = snd (strip_fun (type_of (fst (hd list1))))
    fun inst1 (term,thm) =
    let	val m = match_type (snd (strip_fun (type_of term))) t
    in  (inst m term,INST_TYPE m thm) end;
    val bucketed = bucket_alist (map inst1 list1);

    val initials = map (mk_initial o snd) bucketed
        handle e => wrapException "set_destructors" e

    val _ = remove_coding_theorem_precise target t "destructors" handle e => ()
    val _ = remove_coding_theorem_precise target t "initial" handle e => ()
    val _ = add_coding_theorem_precise target t "destructors"
    	    			       (LIST_CONJ destructors)
    val _ = add_coding_theorem_precise target t "initial" (LIST_CONJ initials)
in
    ()
end
fun nested_constructor_theorem target term =
let val t = with_exn (type_of o lhs o snd o strip_exists) term
    	    	     (mkStandardExn "nested_constructor_theorem"
				"Not a term of the form: ?a.. x = C a..")
    val initial = get_coding_theorem target t "initial"
    val result =  snd (EQ_IMP_RULE
    	       	     (rewrite_thm "nested_constructor_theorem" initial term))
    val result' = fix_hyp result
    val hs = map match_encdec (hyp result')
    handle e => wrapException "nested_constructor" e
in
     DISCH_ALL_CONJ (UNDISCH_CONJ (foldl (uncurry PROVE_HYP) result' hs))
end
fun nested_constructor_rewrite target term =
let val t = with_exn (type_of o lhs o snd o strip_exists o rand) term
    	    	     (mkStandardExn "nested_constructor_theorem"
				"Not a term of the form: bool (?a.. x = C a..)")
    val (enc,body) = with_exn dest_comb term
    		     (mkStandardExn "nested_constructor_rewrite"
		      "Not an encoded term")
    val initial = get_coding_theorem target t "initial"
in
    DISCH_ALL_CONJ (AP_TERM enc
    	      	      (rewrite_thm "nested_constructor_rewrite" initial body))
end
end

(*****************************************************************************)
(* mk_destructor_rewrites : hol_type -> thm list -> thm list                 *)
(*                                                                           *)
(*     Destructors for regular datatypes are generated as:                   *)
(*        |- (FST o decode_pair f g o encode_type f' g') (C x ...) = x       *)
(*     When propagating over such theorems it is *very* important not to     *)
(*     encode 'encode_type f g A' seperately. This is because the final      *)
(*     theorem resolving the encoding must be of the form:                   *)
(*        |- ?x ... . A = C x ... ==>                                        *)
(*           (encode_type f' g' A = X)                                       *)
(*           (encode_pair f' g' (decode_pair f g (encode_type f' g' A)) = X) *)
(*     We therefore produce a theorem of the following form:                 *)
(*        |- (FST (decode_pair f g (encode_type f' g' x)) = X) ==>           *)
(*           ((FST o decode_pair f g o encode_type f' g') x = X)             *)
(*                                                                           *)
(*****************************************************************************)

fun mk_destructor_rewrites target destructors =
let val types = map (type_of o lhs o concl) destructors
    val encs = map (get_encode_function target) types
    val lhss = map (rator o lhs o concl) destructors
    val var = mk_var("arg",fst (dom_rng (type_of (hd lhss))))
    val thms = map2 (fn l => fn e => ASSUME (mk_eq(mk_comb(e,mk_comb(l,var)),
    	       	   genvar target))) lhss encs;
in
    map (DISCH T o DISCH_ALL o CONV_HYP (PURE_REWRITE_CONV [o_THM])) thms
end

(*****************************************************************************)
(* mk_predicate_rewrites : hol_type -> hol_type -> thm list                  *)
(*                                                                           *)
(*    Predicates for regular datatypes are generated as:                     *)
(*             bool (?a b .. . x = Ci a b ..) =                              *)
(*             bool ((FST o decode_pair decode_num I o encode .. x)) = i)    *)
(*                                                                           *)
(*****************************************************************************)

local
fun mk_predicates target t =
let val encoders = CONJUNCTS (get_coding_function_def target t "encode")
    val decode_pair = gen_decode_function target
    		      			  (pairLib.mk_prod(numLib.num,target));
    val map_thm = FULL_ENCODE_DECODE_MAP_THM target
    		  			  (pairLib.mk_prod(numLib.num,alpha));
in
    map (CONV_RULE (FORK_CONV (REWR_CONV (GSYM o_THM),
    	             REWR_CONV pairTheory.FST_PAIR_MAP THENC
		     REWR_CONV I_THM THENC REWR_CONV pairTheory.FST)) o
         MK_FST o
    	 CONV_RULE (BINOP_CONV (REWR_CONV (GSYM o_THM)) THENC
    	      	    	        RAND_CONV (RATOR_CONV (REWR_CONV map_thm))) o
    	 AP_TERM decode_pair o SPEC_ALL) encoders
end
fun pred_term var thm =
let val cons = rand (lhs (concl thm))
    val term = mk_eq(var,cons)
    val vars = snd (strip_comb cons)
in
    mk_eq(list_mk_exists(vars,term),
          mk_eq(mk_comb(rator (lhs (concl thm)),lhs term),rhs (concl thm)))
end;
in
fun mk_predicate_resolve target t =
let val encoders = CONJUNCTS (get_coding_function_def target t "encode")
    val p1 = pairLib.mk_prod(numLib.num,target);
    val p2 = pairLib.mk_prod(numLib.num,alpha);
    val decode_pair = gen_decode_function target p1
    val encode_pair = gen_encode_function target p1
    val thms =
    	map (fn thm =>
	      (CONV_RULE (RAND_CONV (RAND_CONV
	        (REWR_CONV (GSYM o_THM) THENC
                 RATOR_CONV (REWR_CONV
		  (FULL_ENCODE_DECODE_MAP_THM target p2))) THENC
		   REWR_CONV (GSYM o_THM) THENC
		   RATOR_CONV (REWR_CONV
		    (FULL_ENCODE_MAP_ENCODE_THM target p2) THENC
	             PURE_REWRITE_CONV [I_o_ID]) THENC
                     REWR_CONV (GSYM thm))) o
              AP_TERM encode_pair o AP_TERM decode_pair o SPEC_ALL) thm)
	     encoders;
    val var = genvar t
    val nchot = ISPEC var (TypeBase.nchotomy_of t);
    fun fix_thm thm =
    let	val rnd = rand (rhs (concl thm))
    	val term = first (can (match_term rnd) o rhs o snd o strip_exists)
	    	   	 (strip_disj (concl nchot))
        val (vars,tm) = strip_exists term
        val m = match_term rnd (rhs tm)
	val rconv = REWR_CONV (GSYM (ASSUME tm))
    in	CHOOSE_L (vars,ASSUME (list_mk_exists(vars,tm)))
         (CONV_RULE (RAND_CONV (RAND_CONV rconv) THENC
		     LAND_CONV (RAND_CONV (RAND_CONV (RAND_CONV rconv))))
          (INST_TY_TERM m thm))
    end
in
    GEN var (DISJ_CASESL nchot (map fix_thm thms))
end
fun mk_predicate_rewrites target t =
let val predicates = mk_predicates target t
    	handle e => raise (mkStandardExn "mk_predicate_rewrites"
	       ("Could not prove initial predicate theorems...\nis " ^
	        type_to_string t ^ " encoded as a labelled product?\n"))
    val var = genvar t
    val thm =
    (case ((Cases THEN REWRITE_TAC (TypeBase.one_one_of t::
    	   		     GSYM (TypeBase.distinct_of t)::
			     TypeBase.distinct_of t::predicates) THEN
     REPEAT (CHANGED_TAC (CONV_TAC (
     	    EVERY_CONJ_CONV (TRY_CONV EXISTS_REFL_CONV) THENC
	    EVERY_CONJ_CONV (TOP_DEPTH_CONV EXISTS_AND_CONV)))) THEN
     CONV_TAC reduceLib.REDUCE_CONV)
    ([],mk_forall(var,list_mk_conj (map (pred_term var) predicates))))
    of ([],func) => func [] | _ => raise Empty)
    handle _ => raise (mkDebugExn "mk_predicate_rewrites"
    	     	("Could not prove the predicate theorem for the type: " ^
		 type_to_string t))
in
    (mk_destructor_rewrites target predicates,
     map (AP_TERM (get_encode_function target bool))
    	(CONJUNCTS (SPEC_ALL thm)))
end
end

(*****************************************************************************)
(* mk_case_propagation_theorem : hol_type -> hol_type -> term                *)
(*                                                                           *)
(*    Makes a standard propagation theorem, provided destructors have been   *)
(*    provided using set_destructors.                                        *)
(*                                                                           *)
(*****************************************************************************)

local
fun mk_result out var destructors funcname c vars =
let val filtered = filter (can (match_term c) o fst o strip_comb o
    		   rand o lhs o snd o strip_forall o concl) destructors
    fun pos thm = index (curry op= (rhs (concl thm)))
    	    	  	(snd (strip_comb (rand (lhs (concl thm)))));
    val mapped = map (fn x => (pos x,x)) filtered;
    val sorted = map (fn (n,_) => snd (first (curry op= n o fst) mapped))
    	       	     (enumerate 0 (fst (strip_fun (type_of c))));
    val rfunc = mk_var(funcname,foldr (op-->) out (map type_of vars));
 in
    (list_imk_comb(rfunc,
	map (fn x => imk_comb(rator (lhs (concl x)),var)) sorted),sorted)
end handle e => wrapException "mk_result" e
fun wrap e = wrapException "mk_case_propagation_theorem" e
fun set_type t thm =
let val types = map (type_of o rand o lhs o concl) (CONJUNCTS thm)
in
    INST_TYPE (tryfind_e Empty (C match_type t) types) thm
end handle Empty => thm
in
fun mk_case_propagation_theorem target t =
let val _ = trace 2 "->mk_case_propagation_theorem";
    val destructor_thm = set_type t (get_coding_theorem target t "destructors")
    	handle e => wrap e
    val hs = hyp destructor_thm
    val destructors = map SPEC_ALL (CONJUNCTS destructor_thm)
    val constructors = constructors_of t handle e =>
    	raise (mkStandardExn "mk_case_propagation_theorem"
	      		     ("The type: " ^ type_to_string t ^
			      " does not appear to be a regular datatype."))
    val var = mk_var("arg",t)
    val vars = map (fn c => map (fn (n,a) => mk_var(implode (base26 n),a))
	      	   (enumerate 0 (fst (strip_fun (type_of c))))) constructors;
    val cases = map2 (fn v => fn c => list_mk_exists(v,
    	      	     	 mk_eq(var,list_mk_comb(c,v))))
    	        vars constructors
    val (results,thms) = unzip (map2 (fn (n,c) => fn v =>
    		       mk_result (mk_vartype "'out") var destructors
		       		 (implode (base26 n)) c v)
		       (enumerate 0 constructors) vars) handle e => wrap e
    val conditional = list_mk_cond (butlast (zip cases results)) (last results)
    		      handle e => wrap e
    val case_defs1 = map SPEC_ALL (CONJUNCTS (TypeBase.case_def_of t));
    val case_defs2 = map (fn thm => INST_TYPE
    		     	 (match_type (type_of (rhs (concl thm)))
    		     	     	    	(mk_vartype "'out")) thm) case_defs1
		     handle e => wrap e;
    val case_defs3 = map (fn thm => INST_TYPE
    		     	 (match_type (type_of (rand (lhs (concl thm)))) t) thm)
    		     	 case_defs2
		     handle e => wrap e;
    val ordered = map (fn c => first (can (match_term c) o fst o
    		      	       strip_comb o rand o lhs o concl)
    		      	       case_defs3) constructors
	             handle e => wrap e;
    val case_term1 = rator (lhs (concl (hd ordered))) handle e => wrap e
    val normalized = map (C (PART_MATCH (rator o lhs)) case_term1) ordered
    		     handle e => wrap e
    val inst = map2 (fn nml => fn r =>
    	     (fst (strip_comb (rhs (concl nml)))) |-> (fst (strip_comb r)))
    	       	    normalized results handle e => wrap e
    val case_defs = map (INST inst) normalized handle e => wrap e
    val case_term = rator (lhs (concl (hd case_defs))) handle e => wrap e

    val term = mk_forall(var,mk_eq(mk_comb(case_term,var),conditional))
    	       handle e => wrap e
    val enc = mk_var("encode",mk_vartype "'out" --> mk_vartype "'target")
    val thms = mapfilter (fn f => f t)
    	       		 [TypeBase.one_one_of,TypeBase.distinct_of,
			  GSYM o TypeBase.distinct_of]
    	       @ (case_defs @ destructors);
in
    (DISCH_ALL_CONJ (AP_TERM enc (SPEC_ALL
         (case ((Cases THEN REPEAT (CHANGED_TAC (REWRITE_TAC thms)) THEN
                 REPEAT (
		 	CONV_TAC (DEPTH_CONV (EXISTS_REFL_CONV ORELSEC
				 	      EXISTS_AND_CONV)) THEN
		        REWRITE_TAC [])) (hs,term))
          of ([],func) => func []
          |  _ => raise Empty))))
     handle e =>
     (if !debug
     	 then (set_goal(hs,term) ;
	       raise (mkDebugExn "mk_case_propagation_theorem"
     	        "Unable to prove propagation theorem! (Now set as goal)"))
	 else raise (mkDebugExn "mk_case_propagation_theorem"
	         "Unable to prove propagation theorem!"))
end
end

(*****************************************************************************)
(* Propagation theorem for a case constructor for a single constructor.      *)
(*****************************************************************************)

fun mk_single_case_propagation_theorem t =
let val thm = SPEC_ALL (TypeBase.case_def_of t)
    val enc = mk_var("encode",type_of (lhs (concl thm)) --> gen_tyvar())
in
    AP_TERM enc thm
end;

(*****************************************************************************)
(* Propagation theorem for a label type.                                     *)
(*****************************************************************************)

fun mk_label_case_propagation_theorem t =
let val thm = SPEC_ALL (TypeBase.case_def_of t)
    val cs = constructors_of t
    val vlist = map (C (curry mk_var) alpha o implode o base26 o fst)
    	      	    (enumerate 0 cs);
    val var = mk_var("argument",t);
    val ifstatement =
    	list_mk_cond (map2 (fn v => fn c => (mk_eq(var,c),v))
		     	   (butlast vlist) (butlast cs)) (last vlist)
    val encoder = mk_var("encode",alpha --> gen_tyvar());
    val term = mk_eq(TypeBase.mk_case(var,zip cs vlist),ifstatement);

    val nchot = ISPEC var (TypeBase.nchotomy_of t)
    val distinct = TypeBase.distinct_of t
    val thms = map (fn n => CONV_RULE (bool_EQ_CONV)
    	       	       (REWRITE_CONV [GSYM distinct,distinct,thm,ASSUME n]
    	       	       	    term))
    	       	   (strip_disj (concl nchot))
in
   AP_TERM encoder (DISJ_CASESL nchot thms)
end handle e => wrapException "mk_label_case_propagation_theorem" e

(*****************************************************************************)
(* target_function_conv : hol_type -> term -> thm                            *)
(*    If a term is of the form: I M and all subterms of M are functions from *)
(*    over the type given, then I M = M is returned.                         *)
(*****************************************************************************)

fun check_term target M =
    (is_var M andalso type_of M = target) orelse
    (is_const M andalso
        all (curry op= target)
	    (uncurry (C cons) (strip_fun (type_of M)))) orelse
    (pairSyntax.is_pabs M andalso
        both ((all (curry op= target o type_of) o pairSyntax.strip_pair ##
	       check_term target) (pairSyntax.dest_pabs M))) orelse
    (is_comb M andalso check_term target (rator M) andalso
		       check_term target (rand M));

fun target_function_conv target term =
    if same_const (rator term) (mk_const("I",target --> target)) andalso
       check_term target (rand term)
       then REWR_CONV I_THM term
       else NO_CONV term

(*****************************************************************************)
(* dummy_encoder_conv : hol_type -> term -> thm                              *)
(*****************************************************************************)

fun dummy_encoder_conv target term =
    if same_const (rator term) (mk_const("I",target --> target)) andalso
       type_of (rand term) = target andalso is_encoded_term (rand term)
       then REWR_CONV I_THM term
       else NO_CONV term

(*****************************************************************************)
(* add_standard_coding_rewrites : hol_type -> hol_type -> unit               *)
(*                                                                           *)
(* Add rewrites to encode constructors, case theorems, and encoding of       *)
(* decoded terms:                                                            *)
(*      |- encode (C x y z) = cons 0 (encode x) (encode y) (encode z)        *)
(*      |- E (if ?a b c. X = C a b c then A (f0 (R x)) ... = Y) ==>          *)
(*         (E (case x of C a b c -> A a b c ....) = Y                        *)
(*      |- (!x. f0' (f0 x) = x) /\ (encode f0 f1 ... x = X) /\               *)
(*         (?a b c. X = C a b c) ==> T ==>                                   *)
(*              (f0 (f0' (R X)) = R X)                                       *)
(*      |- detect a ==> (encode (decode a) = a)                              *)
(*                                                                           *)
(*****************************************************************************)

local
fun U x = UNDISCH_CONJ x handle e => x
fun check_case_thm target t =
let val strip1 = lhs o snd o strip_imp o concl
    val strip2 = fst o strip_comb o rand
    val all_lhss = mapfilter (fn (a,b,c) => strip1 c)
    		   	     (Net.listItems (!rewrites));
    val all_consts = map strip2 (
    		     	 filter (can (C match_type target) o type_of) all_lhss)
in
   exists (can (C match_term (TypeBase.case_const_of t))) all_consts
end;
fun encode_names target t =
let val conjuncts = enumerate 0 (CONJUNCTS
	 	      (get_coding_function_def target t "encode"))
    val name = fst (dest_type t)
in
    map (fn (n,c) => ("C" ^ int_to_string n ^ "_" ^ name,c)) conjuncts
end
fun add_ifnew_standard_rewrite priority name thm =
    if exists_rewrite name
       then ()
       else add_standard_rewrite priority name thm
fun add_ifnew_conditional_rewrite priority name thm =
    if exists_rewrite name
       then ()
       else add_conditional_rewrite priority name thm
in
fun add_decodeencode_rewrites target t =
let val decenc_thm = DISCH_ALL_CONJ (U (SPEC_ALL (U (SPEC_ALL
    	       	 		(FULL_DECODE_ENCODE_THM target t)))))
	handle e => wrapException "add_decodeencode_function" e
    val name = fst (dest_type t)
in  (add_ifnew_standard_rewrite 0 ("DE_" ^ name) decenc_thm ;
     decenc_thm)
end
fun add_encode_rewrites target t =
let val filtered = filter (not o exists_rewrite o fst) (encode_names target t)
in
    (app (uncurry (add_ifnew_standard_rewrite 0)) filtered ;
     snd (hd filtered))
end;
fun add_case_rewrites target t =
let val (pair_rewrites,destructor_rewrites) =
    	if exists_coding_theorem target t "destructors"
	   orelse length (constructors_of t handle _ => [T]) = 1
	   orelse all (not o can dom_rng o type_of) (constructors_of t)
	   then ([],[])
	   else let val (p,d) = mk_destructors target t
	   	    val _ = set_destructors target d
		in   (p,mk_destructor_rewrites target d)
		end handle e => wrapException "add_case_rewrites" e
    val case_thm =
    	if check_case_thm target t then NONE else
	if length (constructors_of t) = 1 then
	   SOME (mk_single_case_propagation_theorem t)
	else if all (not o can dom_rng o type_of) (constructors_of t) then
	   SOME (mk_label_case_propagation_theorem t)
    	else SOME (mk_case_propagation_theorem target t
    		   handle e => wrapException "add_case_rewrites" e)
    val name = fst (dest_type t)
    val (predicate_rewrites,predicates) =
    	if length (constructors_of t) = 1 orelse
	   all (not o can dom_rng o type_of) (constructors_of t) then ([],[])
	   else    mk_predicate_rewrites target t
    		   handle e => if isFatal e then raise e
		   	       	 else (trace 1 (exn_to_string e) ; ([],[]))
    val predicate_resolve = total (mk_predicate_resolve target) t;
in
    (Option.map (add_ifnew_standard_rewrite 0 ("Case_" ^ name)) case_thm ;
     app (fn (n,c) => add_standard_rewrite 0
     	     	      ("EDp_" ^ name ^ int_to_string n) c)
		      (enumerate 0 pair_rewrites) ;
     app (fn (n,c) => add_ifnew_standard_rewrite 0
     	     	      ("P_" ^ name ^ int_to_string n) c)
		      (enumerate 0 predicates) ;
     Option.map (add_ifnew_standard_rewrite 0 ("PED_" ^ name))
     		 predicate_resolve ;
     app (fn (n,c) => add_ifnew_conditional_rewrite 0
     	     	      ("Po_" ^ name ^ int_to_string n) c)
		      (enumerate 0 predicate_rewrites) ;
     app (fn (n,c) => add_ifnew_conditional_rewrite 0
     	     	      ("Do_" ^ name ^ int_to_string n) c)
		      (enumerate 0 destructor_rewrites) ;
     case_thm)
     handle e => wrapException "add_case_rewrites" e
end
fun add_standard_coding_rewrites target t =
let val _ = if (can (match_type t) (base_type t)) then ()
    	else raise (mkStandardExn "add_standard_coding_rewrites"
	     	   ("The type " ^ type_to_string t ^ " is not a base type"))
    val _ = if can TypeBase.constructors_of t then () else
    	    raise (mkStandardExn "add_standard_coding_rewrites"
	    	  ("The type supplied: " ^ type_to_string t ^
		   " does not appear to be a regular datatype.\n"))
    val _ = encode_type target t
    val _ = add_encode_rewrites target t
    	handle Empty => TRUTH
    	     | e => wrapException "add_standard_coding_rewrites" e
    val _ = add_decodeencode_rewrites target t
    	handle e => wrapException "add_standard_coding_rewrites" e
    val _ = add_case_rewrites target t
    	handle e => wrapException "add_standard_coding_rewrites" e
in
    ()
end
end;

(*****************************************************************************)
(* polytypic_encodedecode, polytypic_casestatement:                          *)
(*    If a statement is of the form: encode (decode x) or encode (case ...)  *)
(*    this function calls add_standard_rewrites then returns the             *)
(*    relevant theorems.                                                     *)
(*                                                                           *)
(*****************************************************************************)

fun polytypic_decodeencode term =
let val (encoder,decoded_term) = dest_comb term
    val target = type_of term
    val var_type = type_of decoded_term
    val decoder = get_decode_function target var_type
    val name = fst (dest_type var_type)
in  (if can (match_term decoder) (rator decoded_term)
       then conditionize_rewrite (add_decodeencode_rewrites target var_type)
       else raise (mkStandardExn "polytypic_decodeencode"
       	    	  		 "Not a term: encode (decode x)"))
end

fun polytypic_casestatement term =
    if (TypeBase.is_case (rand term))
       then conditionize_rewrite (Option.valOf (add_case_rewrites (type_of term)
       	    		 (base_type (type_of (rand (rand term))))))
       else raise (mkStandardExn "polytypic_casestatement"
				 "Not an encoded case statement");

fun polytypic_encodes term =
    if (op_mem (fn a => fn b => can (match_term a) b)
       	       (rand term)
	       (constructors_of (type_of (rand term))))
       then conditionize_rewrite (add_encode_rewrites (type_of term)
       	    			 (base_type (type_of (rand term))))
       else raise (mkStandardExn "polytypic_encodes"
       	    	  		 "Not an encoded constructor");

(*****************************************************************************)
(* prove_propagation_theorem : thm list -> thm -> thm                        *)
(*                                                                           *)
(*    Takes a definition term, D,  of the form:                              *)
(*      ``!a b. <f> a b =                                                    *)
(*        encode (if (detect a /\ detect b /\                                *)
(*                    ... /\ t (decode a) (decode b) /\ ....                 *)
(*                    ... /\ P (decode a) (decode b) /\ ....)                *)
(*                   then f (decode a) (decode b)                            *)
(*                   else bottom)``                                          *)
(*    and proves a propagation theorem:                                      *)
(*    [D] |- P a b ... ==> (encode (f a b) = <f> (encode a) (encode b))      *)
(*                                                                           *)
(*****************************************************************************)

val prove_propagation_theorem_data
    = ref (NONE : (thm option * thm list * term) option);

local
fun exn1 this_function = mkStandardExn this_function
 "Definition is not of the form: \"|- !a b. f a b ... = encode (...)\"";
fun ECC c x =
    c x handle e =>
    MK_CONJ (ECC c (fst (dest_conj x))) (ECC c (snd (dest_conj x))) handle e =>
    NO_CONV x;
fun TCONV conv term =
let val r = conv term
in
    if rhs (concl r) = T then r else NO_CONV term
end;
fun map_thm_vars thm =
    (fn (l,r) =>
     if (same_const (repeat rator l) (repeat rator r) handle _ => false)
     	then filter is_var (snd (strip_comb r))
   	else filter is_var (snd (strip_comb (rand r))))
    (dest_eq (snd (strip_imp (concl (SPEC_ALL thm)))))
fun reduce_hyp (thm1,thm2) =
let val x = tryfind_e Empty (PART_MATCH (snd o dest_imp) thm1) (hyp thm2)
in  PROVE_HYP (UNDISCH_ONLY x) thm2
end handle _ => thm2
fun prove_propagation_theorem_local
    this_function map_thm tautologies definition =
let val _ = prove_propagation_theorem_data
    	  := SOME (map_thm,tautologies,definition);
    val (left,right) = with_exn (dest_eq o snd o strip_forall) definition
    		       (exn1 this_function)
    val _ = trace 1 "Proving propagation theorem...\n"
    val target = type_of right
    val rright = with_exn rand right (exn1 this_function)
    val args = (snd o strip_comb) left
    val function_term = if is_cond rright then (rand o rator) rright else rright
    fun test x = is_var (rand x) handle _ => false
    val decoded_args =
    	case map_thm
	of NONE => filter test ((snd o strip_comb) function_term)
	|  SOME thm =>
	   map2 (fn a => fn b =>
	   	  mk_comb(gen_decode_function target (type_of a),b))
	   	(map_thm_vars thm)
                (map rand
		     (filter test ((snd o strip_comb) function_term)))
        handle e => wrapException this_function e

    val encoded_args = map2 (fn d => fn a =>
            mk_comb(gen_encode_function target (type_of d),
	    	    mk_var(fst(dest_var a),type_of d)))
		    decoded_args args
	    handle e => wrapException this_function e
    val rule = PURE_REWRITE_RULE [o_THM,FUN_EQ_THM,K_THM,I_THM];

    (* Used to use FULL.... changed 09/10/2010 *)
    val encdetall_thms = map (
    	   rule o generate_coding_theorem target "encode_detect_all" o type_of) decoded_args
	   handle e => wrapException this_function e
    val encdecmap_thms = map (
    	   rule o generate_coding_theorem target "encode_decode_map" o type_of) decoded_args
	   handle e => wrapException this_function e
    val allid_thms = map (
    	   rule o FULL_ALL_ID_THM o type_of) decoded_args
	   handle e => wrapException this_function e
    val mapid_thms = map (
    	   rule o FULL_MAP_ID_THM o type_of) decoded_args
	   handle e => wrapException this_function e
    val encmap_thm =
    	   total (rule o FULL_ENCODE_MAP_ENCODE_THM target o type_of o
	    rhs o snd o strip_imp o concl o SPEC_ALL o valOf) map_thm;

    val instantiated =
    	   INST
	   (map2 (fn arg => fn ed => arg |-> ed) args encoded_args)
	   (SPEC_ALL (ASSUME definition))
	   handle e => wrapException this_function e
    val _ = trace 3 ("Instantiated definition:\n" ^
    	    	     thm_to_string instantiated ^ "\n")
    val thms_as_rwrs =
           map (fn t => REWRITE_CONV [t] (snd (strip_forall (concl t))))
    	       tautologies
    val filter_refl = filter
    	(not o exists ((fn x => (lhs x = rhs x)) o snd o strip_forall) o
	 strip_conj o concl o SPEC_ALL)
    fun rwr_conv term =
        (tryfind_e Empty
		  (UNDISCH_CONJ o
		   CONV_RULE (LAND_CONV (PURE_REWRITE_CONV
		   	     (filter_refl (encdecmap_thms @ mapid_thms)))) o
		   C (PART_MATCH (lhs o snd o strip_imp)) term o
		   DISCH_ALL_CONJ)
		  thms_as_rwrs
        handle Empty =>
    	REPEATC (CHANGED_CONV (PURE_REWRITE_CONV (filter_refl
		(encdetall_thms @ allid_thms @ [o_THM,K_o_THM])))) term)
	handle e => wrapException this_function e;
    val cond_proved =
    	   (if is_cond rright then
	      RIGHT_CONV_RULE (RAND_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV (
	          ECC (TCONV rwr_conv) THENC
		  REWRITE_CONV [AND_CLAUSES]))) THENC
		  REWR_CONV (CONJUNCT1 (SPEC_ALL COND_CLAUSES))))
	      instantiated
           else instantiated)
	   handle e => raise (mkStandardExn this_function
	   	  ("Could not prove all terms in the conjunction:\n" ^
		   term_to_string (rand (rator (rator (rand
		   		  (rhs (concl instantiated)))))) ^
		   "\nusing the list of theorems:\n" ^
		   xlist_to_string thm_to_string thms_as_rwrs));
    val cond_proved' = foldl reduce_hyp cond_proved tautologies;
    val list = set_diff (hyp cond_proved') [definition]
    fun MCONV NONE term = REFL term
      | MCONV (SOME map_thm) term =
        UNDISCH_ALL (PART_MATCH (lhs o snd o strip_imp) map_thm term)
    fun fix_I term =
    	if is_encoded_term term then REFL term
	   else SYM (ISPEC term I_THM)
    fun rwr_ed_conv term =
    let val r =
    	(REPEATC (CHANGED_CONV (RAND_CONV (PURE_REWRITE_CONV (filter_refl
		(encdecmap_thms @ mapid_thms @ [I_THM,I_o_ID]))))) THENC
        RAND_CONV (MCONV map_thm) THENC
	PURE_REWRITE_CONV [I_THM,I_o_ID] THENC
        PURE_ONCE_REWRITE_CONV (mapfilter valOf [encmap_thm]) THENC
	PURE_REWRITE_CONV [I_o_ID])
        term handle e => wrapException this_function e
    in
        if all (fn x => is_var x orelse mem x (snd (strip_comb function_term)))
	       (snd (strip_comb (rand (rhs (concl r)))))
	       then RIGHT_CONV_RULE fix_I r else
	raise (mkDebugExn this_function
	      ("Could not fully reduce the term: " ^ term_to_string term))
    end
    fun check x =
    	if length (hyp x) = 1 then x else
	   raise (mkDebugExn this_function
	   	 ("The resulting propagation theorem contains an unwanted " ^
		  "hypothesis:\n" ^ thm_to_string x ^
		  "\nIf this is a polymorphic theorem, check that theorems" ^
		  "\ndemonstrating the limits are map-invariant are included" ^
		  "\neg: (?a b. x = a :: b) ==> (?a b. MAP f x = a :: b)"))
in  check
    (DISCH_LIST_CONJ list (SYM (RIGHT_CONV_RULE rwr_ed_conv cond_proved')))
    before (prove_propagation_theorem_data := NONE)
end
in
fun prove_propagation_theorem tautologies definition =
    prove_propagation_theorem_local
    "prove_propagation_theorem" NONE tautologies definition
fun prove_polymorphic_propagation_theorem map_thm tautologies definition =
    prove_propagation_theorem_local
    "prove_polymorphic_propagation_theorem" (SOME map_thm)
    tautologies definition
end;

(*****************************************************************************)
(* mk_analogue_definition                                                    *)
(*         : hol_type -> string -> thm list -> thm list -> thm -> thm        *)
(* mk_polymorphic_analogue_definition                                        *)
(*         : hol_type -> string -> thm -> thm list -> thm list -> thm -> thm *)
(* mk_analogue_definition_term : string -> thm list -> thm -> term           *)
(*                                                                           *)
(*     mk_analogue_definition target name                                    *)
(*            [... |- !a b. t ...]   (|- f a b = A a b, [\a b. P a b...])    *)
(*     creates a definition term, D, of the following form:                  *)
(*     |- !a b. <f> a b =                                                    *)
(*        encode (if (detect a /\ detect b /\                                *)
(*                    t (decode a) (decode b) /\ ... /\                      *)
(*                    P (decode a) (decode b) /\ ...)                        *)
(*                   then f (decode a) (decode b)                            *)
(*                   else bottom)                                            *)
(*     and returns the propagation theorem:                                  *)
(*     [D] |- P a b /\ ... ==> (encode (f a b) = <f> (encode a) (encode b)) *)
(*                                                                           *)
(*****************************************************************************)

local
val this_function = "MK_DEFINITION";
val exn1 = mkStandardExn this_function
    	   "Function is not of the form: \"|- !a b. P ==> f a b ... = \"";
fun MK_DEFINITION tvs target limits function =
let val tfunction = INST_TYPE (map (fn x => x |-> target) tvs) function
    val sfunction = SPEC_ALL tfunction
    val STRIP = snd o strip_imp o concl
    val (fconst,args) = with_exn (strip_comb o lhs o STRIP) sfunction exn1
    val result_type = with_exn (type_of o rhs o STRIP) sfunction exn1
    val (normal_args,higher_args) = partition is_var args
    val new_args = map (C (curry mk_var) target o fst o dest_var) normal_args
    val decoded_args = map2 (fn arg => fn new_arg =>
    	    mk_comb(gen_decode_function target (type_of arg),new_arg))
	    normal_args new_args handle e => wrapException this_function e
    val specced_limits =
        map (full_beta_conv o C (curry list_imk_comb) decoded_args) limits
    	    handle e => wrapException this_function e
    val detected_args = map2 (fn arg => fn new_arg =>
            mk_comb(gen_detect_function target (type_of arg),new_arg))
	    normal_args new_args handle e => wrapException this_function e
    val decode_map =
    	map (C assoc (zip normal_args decoded_args @
	       	      zip higher_args higher_args)) args
    val body = list_mk_comb(fconst,decode_map)
            handle e => wrapException this_function e
    val bottom = #bottom (get_translation_scheme target)
            handle e => wrapException this_function e
in
     (body,new_args,detected_args,specced_limits,target,result_type,bottom)
end
in
fun mk_analogue_definition_term target name limits function =
let val this_function = "mk_analogue_definition_term"
    val _ = trace 2 "->mk_analogue_definition_term\n"
    val _ = trace 1 ("Creating analogue definition of:\n" ^
    	    	      thm_to_string function ^ "\n")
    val (body,new_args,detected_args,specced_limits,
		target,result_type,bottom) =
	 MK_DEFINITION [] target limits function
	 handle e => wrapException this_function e
    val conditional =
    	    case (detected_args @ specced_limits)
	    of (x::xs) => mk_cond(list_mk_conj(x::xs),body,
		   construct_bottom_value
		   (fn x => is_vartype x orelse x = target) bottom result_type)
	    | [] => body handle e => wrapException this_function e
     val right = mk_comb(gen_encode_function target result_type,conditional)
     	    handle e => wrapException this_function e
     val new_fconst = mk_var(name,foldl op--> target (map type_of new_args))
     val function_term = mk_eq(list_mk_comb(new_fconst,new_args),right)
     	    handle e => wrapException this_function e
in
     list_mk_forall(new_args,function_term)
end  handle e => wrapException this_function e
fun get_tautologies tautologies specced_limits new_args =
let val specced_tauts =
    	mapfilter (fn l => tryfind (C (PART_MATCH I) l) tautologies)
		  specced_limits
    val x = map concl specced_tauts
in case (total (first (not o null o C set_diff new_args o free_vars)) x)
	   of NONE => specced_tauts
	   |  SOME y => raise (mkStandardExn "get_tautologies"
	    	         ("The tautology:\n" ^ term_to_string y ^
			  "\ncontains free variables after instantiation"))
end
fun mk_analogue_definition target name tautologies limits function =
let val this_function = "mk_analogue_definition"
    val _ = trace 2 "->mk_analogue_definition\n"
    val _ = trace 1 ("Creating analogue definition of:\n" ^
    	    	      thm_to_string function ^ "\n")
    val (body,new_args,detected_args,specced_limits
		,target,result_type,bottom) =
	 MK_DEFINITION [] target limits function
	 handle e => wrapException this_function e
    val checked_tauts = get_tautologies tautologies specced_limits new_args
    val conditional =
    	    case (detected_args @ specced_limits)
	    of (x::xs) => mk_cond(list_mk_conj(x::xs),body,
		   construct_bottom_value
		   (fn x => is_vartype x orelse x = target) bottom result_type)
	    | [] => body handle e => wrapException this_function e
     val right = mk_comb(gen_encode_function target result_type,conditional)
     	    handle e => wrapException this_function e
     val new_fconst = mk_var(name,foldl op--> target (map type_of new_args))
     val function_term = mk_eq(list_mk_comb(new_fconst,new_args),right)
     	    handle e => wrapException this_function e
in
    prove_propagation_theorem (checked_tauts @ map ASSUME specced_limits)
         (list_mk_forall(new_args,function_term))
end handle e => wrapException this_function e
fun mk_polymorphic_analogue_definition
    target name map_thm tautologies limits extras function =
let val this_function = "mk_polymorphic_analogue_definition"
    val _ = trace 2 "->mk_polymorphic_analogue_definition\n"
    val _ = trace 1 ("Creating analogue definition of:\n" ^
    	    	      thm_to_string function ^ "\n")
    val map_lhs = lhs o snd o strip_imp o snd o strip_forall o concl
    val maps = snd (strip_comb (map_lhs map_thm))
    	       handle e => wrapException this_function e;
    val tvs = filter is_vartype (flatten
    	      (map (map snd o reachable_graph sub_types o type_of) maps));
    val map_thm1 = INST_TYPE (map (fn x => x |-> target) tvs) map_thm
    val match = match_term
		((fst o strip_comb o map_lhs) function)
		((fst o strip_comb o map_lhs) map_thm1)
		handle e => raise (mkStandardExn this_function
		     ("The instantiated map theorem does not match function." ^
		      "\nMap theorem uses the constant: " ^
		      term_to_string ((fst o strip_comb o map_lhs) map_thm1) ^
		      "\nwhich does not match the function constant: " ^
		      term_to_string ((fst o strip_comb o map_lhs) function)))
    val type_vars = map #redex (filter (curry op= target o #residue)
    		    	(snd match));
    val (body,new_args,detected_args,specced_limits
		,target,result_type,bottom) =
	 MK_DEFINITION type_vars target limits function
	 handle e => wrapException this_function e
    val checked_tauts = get_tautologies tautologies specced_limits new_args
    val conditional =
    	    case (detected_args @ specced_limits)
	    of (x::xs) => mk_cond(list_mk_conj(x::xs),body,
		   construct_bottom_value
		   (fn x => is_vartype x orelse x = target) bottom result_type)
	    | [] => body handle e => wrapException this_function e
     val right = mk_comb(gen_encode_function target result_type,conditional)
     	    handle e => wrapException this_function e
     val new_fconst = mk_var(name,foldl op--> target (map type_of new_args))
     val function_term = mk_eq(list_mk_comb(new_fconst,new_args),right)
     	    handle e => wrapException this_function e
     val taut_limits = map ASSUME specced_limits
     val extra_limits = filter (is_imp o snd o strip_forall o concl) extras
in
    prove_polymorphic_propagation_theorem
         map_thm
         (checked_tauts @ taut_limits @ extra_limits)
         (list_mk_forall(new_args,function_term))
end handle e => wrapException this_function e
end;

(*****************************************************************************)
(* clause_to_limit : term -> term                                            *)
(*                                                                           *)
(*    Converts a missing clause to a limit                                   *)
(*    clause_to_limit ``f (C a b c) (C d)`` =                                *)
(*                       ``\x y. ~((?a b c. x = C a b c) /\ (?d. y = C d))`` *)
(*                                                                           *)
(*****************************************************************************)

fun clause_to_limit missing =
let val (fconst,constructors) = strip_comb missing
    val fvs = free_varsl constructors
    val arg_names = map (implode o base26 o fst) (enumerate 0 constructors)
    val args = map2 (fn an => fn c => variant fvs (mk_var(an,type_of c)))
    	       	    arg_names constructors
    val clauses = mapfilter (fn (arg,cs) =>
    	if is_var cs then raise Empty
	   	     else list_mk_exists(free_vars_lr cs,mk_eq(arg,cs)))
	(zip args constructors)
in
    case clauses
    of [] => raise (mkStandardExn "clause_to_limit"
       	     	   ("Missing clause: " ^ term_to_string missing ^
		    " has no constructors."))
    | _ => list_mk_abs(args,mk_neg(list_mk_conj clauses))
end;

(*****************************************************************************)
(* limit_to_theorems : hol_type -> term -> thm                               *)
(*                                                                           *)
(*    Calculates the nested theorems required for a missing clause limit:    *)
(*    limit_to_theorems ``SEG 0 (SUC n) (a::b::c) =                          *)
(*    |- (?x l. c' = x::l) /\ (?b c. TL c' = b::c) ==> ?a b c. c' = a::b::c  *)
(*                                                                           *)
(*****************************************************************************)

fun limit_to_theorems target term =
    (mapfilter (nested_constructor_theorem target) o strip_conj o dest_neg o
     snd o strip_abs) term
    handle e => wrapException "limit_to_theorems" e

(*****************************************************************************)
(* group_function_clauses : thm -> thm list                                  *)
(*                                                                           *)
(*    Groups a set of mutually recursive equations by function symbol        *)
(*                                                                           *)
(*****************************************************************************)

fun group_function_clauses function =
    map (LIST_CONJ o snd) (bucket_alist (map (fn x =>
    		    ((fst o strip_comb o lhs o snd o strip_imp o
		    	    snd o strip_forall o concl) x,x))
		    (CONJUNCTS function)))
    handle e => wrapException "group_function_clauses" e;

(*****************************************************************************)
(* define_analogue    : string -> thm -> thm * thm                           *)
(* complete_analogues : thm list -> thm list -> thm list -> thm list -> thm  *)
(*                                                                           *)
(*     define_analogue  name  [D] |- P a b ==>                               *)
(*                              (encode (f a b) = <f> (encode a) (encode b)) *)
(*     Defines the definition term D with the name given and removes it from *)
(*     the theorem to return:                                                *)
(*           |- D         and                                                *)
(*           |- P a b ==> (encode (f a b) = <f> (encode a) (encode b))       *)
(*                                                                           *)
(*     complete_analogue extras |- D   |- P a b ==> ...    defn              *)
(*     Inserts the propagation theorem into the rewrite set, then calls      *)
(*     PROPAGATE_ENCODERS_CONV after rewriting using the definition          *)
(*                                                                           *)
(*****************************************************************************)

fun define_analogue name thm =
let val _ = trace 2 "->define_analogue\n"
    val (definition,rewrite) =
    	case (dest_thm thm)
    	of ([D],p) => (D,p)
	| _ => raise (mkStandardExn "define_analogue"
	      ("Theorem should be of the form [Definition] |- Rewrite:" ^
	       "\nHowever, the theorem supplied is not: " ^ thm_to_string thm))
    val defined = new_definition (name,definition)
    	handle e => wrapException "define_analogue" e
in
    (defined,MATCH_MP (DISCH_ALL thm) defined)
    handle e => wrapException "define_analogue" e
end;

local
fun MAYBEIF_RWR_CONV thm term =
    if not (is_cond term)
       then (REWR_CONV thm term handle e => wrapException "MAYBEIF_RWR_CONV" e)
       else
let val (p,a,b) = dest_cond term
    val thma' = PART_MATCH (lhs o snd o strip_imp) thm a
    	      handle e => wrapException "MAYBEIF_RWR_CONV" e
    val thmb = DISCH (mk_neg p) (REFL b)
    val thmp = REFL p
    val thma =
    	DISCH p (if is_imp_only (concl thma')
	   then CONV_RULE (LAND_CONV (REWRITE_CONV [ASSUME p]) THENC
	   		   REWR_CONV (hd (CONJUNCTS (SPEC_ALL IMP_CLAUSES))))
			   thma'
           else thma') handle e =>
	   raise (mkStandardExn "MAYBEIF_RWR_CONV"
	   	 ("Unable to prove the rewrite term: " ^
		  term_to_string (fst (dest_imp (concl thma'))) ^
		  "\nFrom the condition: " ^ term_to_string p))
in
    MATCH_MP COND_CONG (LIST_CONJ [thmp,thma,thmb])
    handle e => wrapException "MAYBEIF_RWR_CONV" e
end
in
fun complete_analogues extras rwrs functions definitions =
let val _ = trace 2 "->complete_analogue\n"
    val names = with_exn (map (fst o dest_const o repeat rator o
    	       		 rand o lhs o snd o strip_imp o snd o strip_forall o
			 concl))
			rwrs
			(mkStandardExn "complete_analogues"
		 	"Rewrite is not of the form: |- !a... encode (f a..) =")
    val _ = map2 (fn name => add_standard_rewrite 0 ("PROP-" ^ name))
    	    	 names rwrs
    	    handle e => wrapException "complete_analogues" e
    val _ = map (fn x =>
    	    	save_thm("prop_" ^ (fst o dest_const o fst o strip_comb o rhs o
				    snd o strip_imp_only o snd o strip_forall o
				    concl) x,x)) rwrs
        handle e => wrapException "complete_analogues" e
    val rewritten = map2 (fn func => fn defn =>
    		    	 CONV_RULE (STRIP_QUANT_CONV (RAND_CONV (RAND_CONV
		  	 	   (MAYBEIF_RWR_CONV defn)))) func)
		  functions definitions
		  handle e => wrapException "complete_analogues" e
in
    LIST_CONJ
      (map (RIGHT_CONV_RULE (PROPAGATE_ENCODERS_CONV ([],extras)) o SPEC_ALL)
      	   rewritten)
    handle e => wrapException "complete_analogues" e
end
end

(*****************************************************************************)
(* convert_definition :                                                      *)
(*        hol_type -> (term * string) list -> (term * term list) list        *)
(*                                               -> thm list -> thm -> thm   *)
(*                                                                           *)
(*    Usage: convert_definition target_type                                  *)
(*    	     			[name map]                                   *)
(*    	     			[limit terms]                                *)
(*           			[extra theorems]                             *)
(*				definition                                   *)
(*        The name map maps function clauses to new names                    *)
(*        Limits map function constants (from the original definition) to    *)
(*        limits applied to these functions, eg:                             *)
(*            [(``SEG``,``\a b c. a + b <= LENGTH c``)]                      *)
(*            [(``LOG``,``\a. 0 < a ==> 0 < a DIV 2``)]                      *)
(*        -- The predicate is applied to the arguments in order, as such,    *)
(*           the abstraction must exactly match the function arguments.      *)
(*        Extra theorems are theorems supplied to assist rewriting, examples *)
(*        of such functions are:                                             *)
(*           |- ~(x = 0) ==> (?d. x = SUC d)                                 *)
(*           |- a + b <= LENGTH c ==> ~((a = 0) /\ (c = []))                 *)
(*           |- 0 < a ==> 0 < a DIV 2                                        *)
(*                                                                           *)
(*    Performs the full conversion:                                          *)
(*         1) Conversion to case form using 'clause_to_case'                 *)
(*         2) Generation of the coding functions using 'encode_type'         *)
(*         3) Generation of the analogous definition using                   *)
(*            'mk_analogue_definition' and 'define_analogue'                 *)
(*         4) Generation of the affirmation theorems using                   *)
(*            'mk_affirmation_theorems'                                      *)
(*            -- This ensures that theorems are predicated on the presence   *)
(*               of constructors, rather than their absense, eg.:            *)
(*               |- (?a. x = SUC a) ==> (encode (PRE a) = ...)               *)
(*         5) Generation of extra limit theorems for nested constructors     *)
(*            using 'limit_to_theorems'                                      *)
(*            -- Theorems are predicated on '?a b c. x = a::b::c' rather     *)
(*               than two clauses using TL                                   *)
(*         6) The propagation of the encoder through the definition using    *)
(*            'complete_analogue', which uses PROPAGATE_ENCODERS_CONV.       *)
(*                                                                           *)
(*    If successful this stores the definition in the current theory,        *)
(*    converted definitions can be loaded back in using load_definitions     *)
(*                                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Given a list of functions and their limits, returns the extra theorems    *)
(* required for forward-chaining:                                            *)
(*     Limit theorems:       |- destructed clause ==> full clause            *)
(*     Affirmation theorems: |- ~(C0 a) /\ ~(C1 a) ==> C2 a                  *)
(*                                                                           *)
(*****************************************************************************)

fun calculate_extra_theorems target list =
let val STRIP = snd o strip_imp o snd o strip_forall o concl o fst
    val arg_types = flatten (map (mapfilter type_of o
		  (snd o strip_comb o lhs o STRIP))
	    list) handle e => wrapException "calculate_extra_theorems" e
    val filtered_arg_types =
    	filter (not o is_vartype) arg_types
    val _ = map (encode_type target o base_type)
    	    	(filter (can constructors_of) filtered_arg_types)
    	    handle e => wrapException "calculate_extra_theorems" e
    fun vbase_type t = if is_vartype t then t else base_type t
    val all_types = mk_set (flatten
    	(map (mk_set o map (vbase_type o fst) o
	     RTC o reachable_graph sub_types) arg_types))
        handle e => wrapException "calculate_extra_theorems" e
    val affirmation_theorems =
    	flatten (mapfilter mk_affirmation_theorems all_types)
    	handle e => wrapException "calculate_extra_theorems" e
    val clause_limits = mapfilter clause_to_limit (flatten (map snd list))
    val nested_theorems = map (limit_to_theorems target) clause_limits
	    		handle e => wrapException "calculate_extra_theorems" e
in
    flatten (affirmation_theorems :: nested_theorems)
end;

local
fun assoc [] a = NONE
  | assoc ((b,c)::xs) a =
    if can (match_term b) a then SOME c else assoc xs a;
fun convert_definition_local error mk_analogue_definition
    		       target name_map limits extras definition =
let val list = map ((DISCH_ALL ## I) o clause_to_case o UNDISCH_ALL)
    	       	   (group_function_clauses definition)
    	       handle e => wrapException error e
    val terms = map (fst o strip_comb o lhs o snd o strip_imp o
    	      	    snd o strip_forall o concl o fst)
    	      	    list handle e => wrapException error e
    val name_list = map (Option.valOf o assoc name_map) terms
    	handle e => raise (mkStandardExn "convert_definition"
	       	    ("No name has been supplied for the function clause: " ^
		     term_to_string (first
		     		    (not o can (Option.valOf o assoc name_map))
				     terms)))
    val limit_list = map ((fn NONE => [] | SOME y => y) o assoc limits) terms
    val rlist = map2 (fn (name,limit) => fn (thm,missing) =>
    	      	    mk_analogue_definition target name (map SPEC_ALL extras)
		    limit thm) (zip name_list limit_list) list
	        handle e => wrapException error e
    val rrlist = map2 define_analogue name_list rlist
    	       	 handle e => wrapException error e
    val  (functions,rwrs) = unzip rrlist
    val definitions = map fst list
    val extra_theorems = calculate_extra_theorems target list
    		       handle e => wrapException error e
    val extras_filtered =
    	(filter (fn x =>
		not (can (match_term (fst (dest_imp (concl x))))
		    	 (snd (dest_imp (concl x))))
	        handle _ => true) (map SPEC_ALL extras));
    val completed = complete_analogues
    		    (extras_filtered @ extra_theorems)
    		    rwrs functions definitions
                    handle e => wrapException error e
    val _ = trace 1 ("Definition(s) converted: \n")
    val _ = app (fn x => trace 1 (thm_to_string x ^ "\n")) (CONJUNCTS completed)

    val _ = map (fn x =>
    	    	save_thm
		    ("translated_" ^
		    fst (dest_const (fst (strip_comb (lhs
		    	(snd (strip_forall (concl x))))))),x))
	    (CONJUNCTS completed)
            handle e => wrapException error e
in  completed
end
in
fun convert_definition target name_map limits extras definition =
    convert_definition_local "convert_definition" mk_analogue_definition
    			     target name_map
    			     limits extras definition
fun convert_polymorphic_definition
    target name_map limits map_thms extras definition =
let fun mad t s l1 l2 function =
    case (assoc map_thms ((fst o strip_comb o lhs o snd o strip_imp o
    	      	    snd o strip_forall o concl) function))
    of SOME map_thm =>
       mk_polymorphic_analogue_definition t s map_thm l1 l2 extras function
    |  NONE => mk_analogue_definition t s l1 l2 function
in
    convert_definition_local "convert_polymorphic_definition"
    			     mad target name_map limits extras definition
end
end;

(*****************************************************************************)
(* load_definitions : string -> thm list                                     *)
(*     Loads function definitions in from the theory given.                  *)
(*                                                                           *)
(*     Definitions are always stored with a corresponding propagation        *)
(*     theorem. We can therefore reload by ensuring that we have both.       *)
(*                                                                           *)
(*****************************************************************************)

fun get_definition theory constant =
let val name = fst (dest_const constant)
    val definition = assoc ("translated_" ^ name) (DB.theorems theory)
    val theorem = assoc ("prop_" ^ name) (DB.theorems theory)
in
    (name,(definition,theorem))
end;

fun load_definitions theory =
let val constants = Theory.constants theory
    val loaded = mapfilter (get_definition theory) constants
    val _ = map (fn (name,(_,theorem)) =>
    	    	add_standard_rewrite 0 ("PROP-" ^ name) theorem) loaded
in
    map (fst o snd) loaded
end;

(*****************************************************************************)
(* encode_until : (term -> bool) list -> thm list * thm list -> term ->      *)
(*                                                     term list list * thm  *)
(*     Performs encoding until one of the function terminals is reached.     *)
(*     Returns the encoded term, along with a list of terminal terms for     *)
(*     each terminal functions used.                                         *)
(*                                                                           *)
(*****************************************************************************)

fun encode_until funcs AE term =
let val _ = trace 2 "->encode_until\n";
    val terminals = map (curry op^ "encode_until_terminal_" o
    		         implode o base26 o fst) (enumerate 0 funcs)
    val lists = map (fn x => ref []) funcs
    fun remove () =
    	app remove_terminal terminals
    val _ = remove();
    fun mk_terminal (n,func) thm_list x =
    	if (func x) then
	   (el n lists := (thm_list,x) :: (!(el n lists)) ; true)
        else false;

    val _ = map2 (curry add_extended_terminal) terminals
    	    	 (map mk_terminal (enumerate 1 funcs))
    val result = PROPAGATE_ENCODERS_CONV AE term
    	       	 handle e => (remove() ; wrapException "encode_until" e)
    val _ = remove();
in
    (map (op!) lists,result)
end;

fun step_PROPAGATE_ENCODERS_CONV AE term =
    snd (encode_until
    	[fn x => (TextIO.input1 TextIO.stdIn ; print_term x ;
	      	 print "\n" ;false)]
	AE term);

local
fun mk_encoder target x = mk_comb(get_encode_function target (type_of x),x);
fun ap_decoder target x =
    AP_TERM (get_decode_function target (type_of (rand (lhs (concl x))))) x;
fun left_encdec target x =
    CONV_RULE (LAND_CONV (REWR_CONV (FULL_ENCODE_DECODE_THM target
    	      (type_of (rand (rand (lhs (concl x)))))))) x;
fun LIST_MK_COMB (a,L) = foldl (uncurry (C (curry MK_COMB))) a L;
fun mk_pres target arg =
let val p = mk_eq(mk_encoder target arg,genvar target)
in
    ((left_encdec target o ap_decoder target o ASSUME) p,SOME p)
    handle _ => (REFL arg,NONE)
end
fun prewrite term =
let val (f,args) = strip_comb (rand term)
    val target = type_of term
    val (rwrs,pres) = unzip (map (mk_pres target) args)
    val result = DISCH_LIST_CONJ (mapfilter Option.valOf pres)
    	       	 (AP_TERM (rator term) (LIST_MK_COMB(REFL f,rwrs)))
in
    DISCH T result
end
in
fun encode_until_recursive funcs AE fterms term =
let val new_rewrites = map prewrite fterms
    	handle e => wrapException "encode_until_recursive" e
    fun remove() = map (fn (a,_) =>
    		       remove_rewrite ("encode_until_recursive_rwr_"
				     ^ int_to_string a))
                   (enumerate 0 new_rewrites)
    val _ = remove()
    fun wrap e = (remove () ; wrapException "encode_until_recursive" e)
    val _ = map (fn (a,b) =>
    	add_conditional_rewrite 100 ("encode_until_recursive_rwr_"
				     ^ int_to_string a) b)
        (enumerate 0 new_rewrites) handle e => wrap e
in
    ((encode_until funcs AE term handle e => wrap e)
    before remove())
end
end;

(*****************************************************************************)
(* get_all_detect_types : hol_type -> hol_type list                          *)
(*     Returns the list of all types in recursion, or nested recursion,      *)
(*     with the type t.                                                      *)
(*                                                                           *)
(*****************************************************************************)

fun get_all_detect_types target t =
let val basetype = most_precise_type
    		   (C (exists_coding_function_precise target) "detect") t
    fun st t = flatten (map (fst o strip_fun o type_of) (constructors_of t))
    	       handle e => (snd (dest_type t) handle e => [])
    val alltypes = (basetype,basetype)::TC (reachable_graph st basetype);
    val match = match_type basetype t
in
    mk_set (map (type_subst match o fst)
    	   	(filter (curry op= basetype o snd) alltypes))
end;

fun is_recursive_detect_type target t =
let val basetype = most_precise_type
    		   (C (exists_coding_function_precise target) "detect") t
    fun st t = flatten (map (fst o strip_fun o type_of) (constructors_of t))
    	       handle e => (snd (dest_type t) handle e => [])
    val alltypes = TC (reachable_graph st basetype);
    val match = match_type basetype t
in
    mem t (map (type_subst match o fst) (filter op= alltypes))
end;

(*****************************************************************************)
(* flatten_recognizers : hol_type -> hol_type -> thm                         *)
(*****************************************************************************)

fun mk_fullname target t =
    if is_vartype t orelse t = target then "ANY"
    else String.concat (op:: ((I ## map (mk_fullname target)) (dest_type t)))

fun SET_CODER thm =
    RIGHT_CONV_RULE (RAND_CONV (REWR_CONV (GSYM combinTheory.I_THM)))
    		    (SPEC_ALL (GSYM thm))
    handle e => wrapException "SET_CODER" e

fun generate_recognizer_terms namef target full_types =
let val _ = map (encode_type target) (filter (not o is_vartype)
    	    	(map base_type full_types))
    val KT = mk_comb(mk_const("K",bool --> target --> bool),
    	     mk_const("T",bool));

    val detectors = map (get_detect_function target) full_types
    val fvs = free_varsl detectors
    val detectors' = map (subst (map (fn x => x |-> KT) fvs)) detectors;

    val var = mk_var("x",target);
    val bool_enc = get_encode_function target bool
in
    map2 (fn t => fn d =>
    	mk_eq(mk_comb(mk_var(namef t,target --> target),var),
	      mk_comb(bool_enc,mk_comb(d,var)))) full_types detectors'
end;

fun flatten_recognizers namef target t =
let val _ = trace 2 "->flatten_recognizers\n"
    val _ = scrub_rewrites()
    val full_types = get_all_detect_types target t
    val funcs = generate_recognizer_terms namef target full_types
    val _ = trace 1 "Creating new recognition functions:\n";
    val _ = app (fn x => trace 1 (term_to_string x ^ "\n")) funcs
    val defns = map2 (fn t => curry new_definition (namef t))
    	      	     full_types funcs
    val _ = map2 (fn t => add_standard_rewrite 1 (namef t)
    	    	       	  o SET_CODER)
    	    	 full_types defns;
    val _ = map2 (fn t => fn d => save_thm("prop_" ^ (namef t),
    	    	       	       	  SET_CODER d))
    	    	 full_types defns;
    val all_detectors =
    	map (C (get_coding_function_def target) "detect") full_types
    val rewrites = map2 (fn d => (RIGHT_CONV_RULE (RAND_CONV (REWR_CONV d))
    		   	      	  o SPEC_ALL)) all_detectors defns
    val general_detects =
    	mapfilter (generate_coding_theorem target "general_detect" o base_type)
    		  full_types
    val finished = map (RIGHT_CONV_RULE (PROPAGATE_ENCODERS_CONV
    		       ([],general_detects)))
    		   rewrites
    val _ = map2 (fn t => fn d =>
    	    	 save_thm("translated_" ^ (namef t),d))
            full_types finished
in
   finished
end handle e => wrapException "flatten_recognizers" e

fun detect_const_type term =
let val target = last (fst (strip_fun (type_of term)))
    val const_map =
    	(get_detect_function target target,target) ::
	(mapfilter (fn t => (get_coding_function_const target t "detect",t))
	    (get_translation_types target))
in
   snd (first (can (match_term term) o fst) const_map)
end;

fun get_detect_type term =
    detect_const_type term handle _ =>
    (if is_comb term then
    	let val (a,b) = strip_comb term
	    val ft = get_detect_type a
	    val ts = map get_detect_type b
	in  mk_type(fst (dest_type ft),ts)
	end
     else raise Empty);

fun recognizer_rewrite target t =
let val detector = SPEC_ALL (get_coding_function_def target t "detect")
    val var = (rand o lhs o concl) detector
    val prior = mk_eq(imk_comb(mk_const("I",alpha --> alpha),var),genvar target)
    val rwr = REWRITE_RULE [combinTheory.I_THM] (ASSUME prior)
    val thm' = CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV (GSYM rwr))))
    	       		 (INST [var |-> (rhs (concl rwr))] detector)
    val thm'' = AP_TERM (get_encode_function target bool) thm'
    val rrwr = ASSUME (mk_eq(rhs (concl thm''),genvar target))
    val thm''' = RIGHT_CONV_RULE (REWR_CONV rrwr) thm''
in
    DISCH T (CONV_RULE (REWR_CONV AND_IMP_INTRO)
    	      (DISCH prior (DISCH (concl rrwr) thm''')))
end handle e => wrapException "recognizer_rewrite" e

fun polytypic_recognizer term =
let val target = type_of term
    val t = get_detect_type (rator (rand term))
    val detector = get_detect_function target t
    val encoder = get_encode_function target bool
    val var = mk_var("x",target);
    val _ = match_term (mk_comb(encoder,mk_comb(detector,var))) term
in
    if is_recursive_detect_type target t
       then (flatten_recognizers (mk_fullname target) target t ;
             DISCH T (snd (hd (snd (return_matches [] term)))))
       else recognizer_rewrite target t
end handle e => raise (mkStandardExn "polytypic_recognizer"
    	   "Not an encoder recognition predicate");

(*****************************************************************************)
(* Like subst, except it acts like REWR_CONV, not SUBST_CONV                 *)
(*****************************************************************************)

fun exact_subst tmap term =
let val term' = subst tmap term
in
    mk_comb(exact_subst tmap (rator term'),exact_subst tmap (rand term'))
    handle _ => mk_abs(bvar term',exact_subst tmap (body term'))
    handle _ => term'
end handle e => wrapException "exact_subst" e

fun subst_all tmap term =
let val all_terms = find_terms (fn t =>
    	    	      	exists (fn r => can (match_term (#redex r)) t) tmap)
			term
    val new_map = map (fn term =>
	    	    tryfind (fn {redex,residue} => term |->
		    	    subst (fst (match_term redex term)) residue) tmap)
	          all_terms
 in exact_subst new_map term
 end handle e => wrapException "subst_all" e

(*****************************************************************************)
(* Takes the induction theorem from a translation scheme, and proves a       *)
(* corresponding relation well-founded:                                      *)
(*      |- (!x. isPair x /\ (left x) /\ (right x) ==> P x) /\                *)
(*         (!x. ~(isPair x) ==> P x) ==>                                     *)
(*              !x. P x                                                      *)
(*                      ===>                                                 *)
(*      |- WF (\y x. isPair x /\ ((y = left x) \/ (y = right x)))            *)
(*                                                                           *)
(*****************************************************************************)

fun get_wf_relation target =
let val scheme = get_translation_scheme target
    	handle e => wrapException "get_wf_relation" e
    val induction = #induction scheme
    val left = #left scheme
    val right = #right scheme
    val pair = #predicate scheme
    val x = mk_var("x",target)
    val y = mk_var("y",target)
    val R = list_mk_abs([y,x],mk_conj(mk_comb(pair,x),
		    mk_disj(mk_eq(y,mk_comb(left,x)),
                            mk_eq(y,mk_comb(right,x)))))
			    handle e => wrapException "get_wf_relation" e
    val term = imk_comb(``WF:('a -> 'a -> bool) -> bool``,R)
    	       handle e => wrapException "get_wf_relation" e
in
    BETA_RULE (prove(term,
        REWRITE_TAC [relationTheory.WF_EQ_INDUCTION_THM] THEN
        NTAC 2 STRIP_TAC THEN
	MATCH_MP_TAC induction THEN REPEAT STRIP_TAC THEN
	RULE_ASSUM_TAC BETA_RULE THEN FIRST_ASSUM MATCH_MP_TAC THEN
	REPEAT STRIP_TAC THEN
	FIRST_ASSUM SUBST_ALL_TAC THEN
	ASM_REWRITE_TAC []))
	handle e => raise (mkStandardExn "get_wf_relation"
	       ("Unable to prove the relation: " ^ term_to_string term ^
	       	" well-founded"))
end;

(*****************************************************************************)
(* ALLOW_CONV : conv -> conv                                                 *)
(*                                                                           *)
(*****************************************************************************)

fun ALLOW_CONV conv term = (conv term) handle UNCHANGED => REFL term;

(*****************************************************************************)
(* make_abstract_funcs ...                                                   *)
(*****************************************************************************)

fun make_abstract_funcs target abstract_terms funcs input_terms =
let val var_map = map (fn (i,a) => a |->
    		      	  (mk_var("ABS" ^ implode (base26 i),target)))
                      (enumerate 0 abstract_terms)
    val new_args = map #residue var_map
    fun reverse x = map (fn {redex,residue} => residue |-> redex) x
    fun mrhs x = mk_comb(rator (rhs x),
    	       	 	 ((fn (a,b,c) => b) o dest_cond o rand o rhs) x)
    	       	 handle _ => rhs x
    fun mlhs x = lhs (snd (strip_forall x))
    val new_funcs = map (fn func =>
    		     let val (var,args) = strip_comb (mlhs func)
		     in  list_mk_comb(mk_var(fst (dest_var var),
		     	 foldl (op-->) target (map type_of (args @ new_args))),
                         args @ new_args)
                     end) funcs
   val func_map1 = map2 (curry op|->) (map mrhs funcs) new_funcs
   val func_map2 = map2 (curry op|->) (map mlhs funcs) new_funcs
in
   (map (fn {redex,residue} => mk_eq(redex,subst (reverse var_map) residue))
        func_map1,
    map (subst var_map o subst func_map2 o subst_all func_map1) input_terms)
end handle e => wrapException "make_abstract_funcs" e

fun create_abstract_recognizers namef f target t =
let fun wrap e = wrapException "create_abstract_recognizers" e
    val _ = trace 2 "->create_abstract_recognizers\n";
    val full_types = get_all_detect_types target t
    val funcs = map (snd o strip_forall)
    	      	(generate_recognizer_terms namef target full_types)
		handle e => wrap e
    val general_detects =
    	mapfilter (SPEC_ALL o
		   generate_coding_theorem target "general_detect" o base_type)
    		  [``:'a list``]
    fun rc detector func =
    let	val thm = RAND_CONV (ALLOW_CONV (ONCE_REWRITE_CONV [detector]))
    	    	  	    (rhs func)
    	val (terms,r) = encode_until_recursive [f o rand] ([],general_detects)
    	    	      	(map rhs funcs) (rhs (concl thm))
    in  (map snd (hd terms),RIGHT_CONV_RULE (ALLOW_CONV (REWR_CONV r)) thm)
    end
    val all_detectors =
    	map (C (get_coding_function_def target) "detect") full_types
	handle e => wrapException "create_abstract_recognizers" e
    val (terminals,thms) = unzip (map2 rc all_detectors funcs)
    			   handle e => wrap e

    val (props,output_terms) =
    	make_abstract_funcs target (mk_set (flatten terminals))
			    funcs (map concl thms)
in
    (props,thms,output_terms)
    handle e => wrap e
end;

(*****************************************************************************)
(* WF_TC_FINISH_TAC : term * term -> tactic                                  *)
(*     Given terms L and R, proves a goal of the form:                       *)
(*       A ?- TC R (L .. R .. x) x                                           *)
(*                                                                           *)
(*****************************************************************************)

fun WF_TC_FINISH_TAC (a,g) =
let val (rrule,trule) = CONJ_PAIR (SPEC_ALL relationTheory.TC_RULES);
    val to = rand g
    val from = rand (rator g)
    val scheme = get_translation_scheme (type_of to);
    val eterm = rand from;
in
    (if   from = beta_conv (mk_comb(#left scheme,to)) orelse
          from = beta_conv (mk_comb(#right scheme,to))
        then MATCH_MP_TAC rrule THEN pairLib.GEN_BETA_TAC
        else MATCH_MP_TAC trule THEN EXISTS_TAC eterm THEN
       	     CONJ_TAC THEN WF_TC_FINISH_TAC)
    (a,g)
end;

(*****************************************************************************)
(* mk_summap     : thm -> thm                                                *)
(*     |- WF R ----> |- WF (inv_image R summap)                              *)
(* mk_sumstart   : thm -> thm                                                *)
(*     |- WF R ----> |- WF (inv_image R (\a. (a,())))                        *)
(* mk_lex        : thm -> thm -> thm                                         *)
(*     |- WF R1, |- WF R2 ---> |- WF (R1 LEX R2)                             *)
(* mk_nested_rel : term list -> thm                                          *)
(*     [R (INL _) (INR _), R (INL (INR a)) (INR (INL x))...]                 *)
(*     ---> |- WF (\a b. (?a'. a = INL a') /\ (?b'. b = INR b') /\ ... )     *)
(*                                                                           *)
(*     Used to relate terms:                                                 *)
(*           R (INL (a,_)) (INR (b,_)) as:                                   *)
(*           a <_sexp b \/ (a = b) /\ (l = INL /\ r = INR)                   *)
(*                                                                           *)
(*****************************************************************************)

local
open sumSyntax pairSyntax
val sumtype = ``:'a + 'b``;
val sumcase = TypeBase.case_const_of sumtype
val WF_inv = Q.SPEC `R` (relationTheory.WF_inv_image);
fun sumt n x = list_mk_sum (for 1 n (K x))
fun mk_sum 0 t b = [b]
      | mk_sum n t b = mk_inl(b,sumt n t)
    	       	       :: (map (C (curry mk_inr) t) (mk_sum (n - 1) t b));
fun mk_sum_tm n =
let val avar = mk_var("a",sumt n alpha)
    val bvar = mk_var("b",beta)
    val alphaa = mk_var("a",alpha)
    fun lfoldr f x = foldr f (last x) (butlast x) handle _ => (hd x)
    fun mk_sumcase L =
        lfoldr (fn (a,b) => list_imk_comb(sumcase,[a,b]))
	       (map (fn a => mk_abs(alphaa,mk_pair(alphaa,a))) L);
in
    mk_pabs(mk_pair(avar,bvar),
	mk_comb(mk_sumcase (mk_sum (n - 1) beta bvar),avar))
end;
fun WF_sum length =
    Q.GEN `R` (ISPEC (mk_sum_tm length) WF_inv);
val WF_ssum = Q.GEN `R` (ISPEC ``(\(a:'a). (a,()))`` WF_inv);
in
fun mk_summap n WF_R =
let val rt = type_of (rand (concl WF_R))
    val sum_type = snd (dest_prod (hd (fst (strip_fun rt))))
    val sum = WF_sum n
    val WF_R' = INST_TYPE (match_type sum_type (sumt n (gen_tyvar()))) WF_R
in
    MATCH_MP sum WF_R'
end handle e => wrapException "mk_summap" e
fun mk_sumstart WF_R =
    MATCH_MP WF_ssum (INST_TYPE
        (match_type (snd (pairSyntax.dest_prod (hd (fst (strip_fun (type_of
    	       	    (rand (concl WF_R)))))))) ``:unit``) WF_R)
    handle e => wrapException "mk_sumstart" e
end;

local
fun get_tyvars thm =
    HOLset.listItems
        (HOLset.addList ((hyp_tyvars thm),type_vars_in_term (concl thm)))
in
fun mk_lex WFRa WFRb =
let val tvsa = get_tyvars WFRa
    val tvsb = get_tyvars WFRb
    val mapa = map (fn v => v |-> gen_tyvar()) tvsa
    val mapb = map (fn v => v |-> gen_tyvar()) tvsb
in
    MATCH_MP pairTheory.WF_LEX
    	     (CONJ (INST_TYPE mapa WFRa) (INST_TYPE mapb WFRb))
end handle e => wrapException "mk_lex" e
end;

local
open sumSyntax
fun match_dub f tm =
    inst (f (fst (dom_rng (type_of tm)))
    	 ((fst o dom_rng o snd o dom_rng o type_of) tm)) tm;
fun is_dub tm =
    (fst o dom_rng o type_of) tm = (fst o dom_rng o snd o dom_rng o type_of) tm;
fun mk_wf_nested_case term =
let val ((R,a),b) = (dest_comb ## I) (dest_comb term);
    val avar = mk_var("a",alpha)
    val bvar = mk_var("b",alpha)
    fun strip x y =
    	if can (match_term (mk_inl (avar,beta))) x
	   then mk_inl (strip (rand x) y ,gen_tyvar())
    	   else if can (match_term (mk_inr (avar,beta))) x
	   	   then mk_inr (strip (rand x) y ,gen_tyvar())
		   else y;
    val a' = strip a avar
    val b' = strip b bvar
    val avar' = mk_var("a'",type_of a')
    val bvar' = mk_var("b'",type_of b')
    val a'' = mk_exists(avar,mk_eq(avar',a'));
    val b'' = mk_exists(bvar,mk_eq(bvar',b'));
    fun rpt x = if is_dub x then x
    	      	   else rpt (match_dub match_type x handle _ =>
		   	     match_dub (C match_type) x) handle _ =>
raise(mkStandardExn "mk_wf_nested_case"
     ("Could not instantiate type of: " ^ term_to_string x ^
      "\nto be of the form: 'a -> 'a -> bool"))
in
    rpt (list_mk_abs([avar',bvar'],list_mk_conj [a'',b'']))
end
fun make_all_terms [] = ``REMPTY:'a -> 'a -> bool``
  | make_all_terms [x] = mk_wf_nested_case x
  | make_all_terms (x::xs) =
let val r1 = mk_wf_nested_case x
    val r2 = make_all_terms xs
    val nty_var1 = gen_tyvar()
    val nty_var2 = gen_tyvar()
    val v1 = fst (dest_abs r1)
    val v2 = fst (dest_abs r2)
    val l1 = length (strip_sum (last (pairSyntax.strip_prod (type_of v1))))
    val l2 = length (strip_sum (last (pairSyntax.strip_prod (type_of v2))))
    val l = Int.max(l1,l2)
    val match = pairSyntax.list_mk_prod(
			(butlast (pairSyntax.strip_prod (type_of v1))) @
			[list_mk_sum (rev (nty_var2 ::
				     for 1 (l - 1) (K nty_var1)))])
    val r1i = inst (match_type (type_of v1) match) r1
    val r2i = inst (match_type (type_of v2) match) r2
    val vars = fst (strip_abs r1i)
in
    list_mk_abs(vars,mk_disj(list_imk_comb(r1i,vars),list_mk_comb(r2i,vars)))
end handle e => wrapException "(make_all_terms)" e
fun prove_nested_case term =
    BETA_RULE ((prove(term,
    pairLib.GEN_BETA_TAC THEN
    REWRITE_TAC [relationTheory.WF_EMPTY_REL,
    		 relationTheory.WF_EQ_INDUCTION_THM] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REPEAT (POP_ASSUM MP_TAC) THEN pairLib.GEN_BETA_TAC THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    METIS_TAC [TypeBase.nchotomy_of ``:'a + 'b``,
    	      sumTheory.sum_distinct,TypeBase.one_one_of ``:'a + 'b``])))
    	      handle e => wrapException "prove_nested_case" e
in
fun mk_nested_rel terms =
    prove_nested_case(imk_comb(``WF:('a -> 'a -> bool) -> bool``,
    					make_all_terms terms))
    handle e => wrapException "mk_nested_rel" e
end;

(*****************************************************************************)
(* WF_RECOGNIZER_TAC : tactic                                                *)
(*     Solves goals of the form: ?- ?R. WF R /\ ... where                    *)
(*     R : target # 'a + target # 'a + .... -> ... -> bool    or             *)
(*     R : target + target + ... -> ... -> bool                              *)
(*                                                                           *)
(*****************************************************************************)

fun WF_RECOGNIZER_TAC (a,g) =
let val _ = proofManagerLib.set_goal (a,g);
    val r = type_of (fst (dest_exists g))
    val txs = sumSyntax.strip_sum (hd (fst (strip_fun r)))
    val target = hd (pairSyntax.strip_prod (hd txs));
    val WF_R = MATCH_MP relationTheory.WF_TC (get_wf_relation target)
    val WF_LEXR =
    	MATCH_MP (pairTheory.WF_LEX) (CONJ WF_R relationTheory.WF_EMPTY_REL);

    val all_terms = map (snd o strip_imp o snd o strip_forall)
    		    (strip_conj (snd (dest_conj (snd (strip_exists g)))))
    fun strip_sum x =
    	if is_comb x andalso exists (fn y => can (match_term y) (rator x))
	   	     [sumSyntax.inl_tm,sumSyntax.inr_tm]
	   then strip_sum (rand x) else x;
    val tmap = hd o pairSyntax.strip_pair o strip_sum
    val same_terms =
    	(filter (op= o (tmap ## tmap) o (snd o dest_comb ## I) o dest_comb)
		all_terms);

    fun mk_rel R = mk_sumstart(mk_summap (length txs)
		       (mk_lex R (mk_nested_rel same_terms)));
    val relation =
        if can pairSyntax.dest_prod (hd txs)
	   then mk_rel WF_LEXR else mk_rel WF_R
    val relation_matched =
    	INST_TYPE (match_type (type_of (rand (concl relation))) r) relation
in
    ((EXISTS_TAC (rand (concl (relation_matched))) THEN
     REWRITE_TAC [relation_matched] THEN
     REPEAT STRIP_TAC THEN
     REPEAT (CHANGED_TAC (REWRITE_TAC
     	    [relationTheory.EMPTY_REL_DEF,pairTheory.LEX_DEF,
	     sumTheory.sum_case_def,relationTheory.inv_image_def,
	     pairTheory.FST,pairTheory.SND,combinTheory.I_THM,
	     sumTheory.sum_distinct] THEN
	    pairLib.GEN_BETA_TAC)) THEN
     RW_TAC std_ss [] THEN
     WF_TC_FINISH_TAC THEN
     CCONTR_TAC THEN FULL_SIMP_TAC std_ss [] THEN NO_TAC) (a,g))
     before proofManagerLib.drop()
end handle e => wrapException "WF_RECOGNIZER_TAC" e

(*****************************************************************************)
(* TARGET_INDUCT_TAC : tactic                                                *)
(*    Performs an induction using a well founded relation derived from the   *)
(*    target type induction scheme.                                          *)
(*                                                                           *)
(*****************************************************************************)

fun TARGET_INDUCT_TAC (a,g) =
let val var = fst (dest_forall g)
    val WF_R = MATCH_MP relationTheory.WF_TC (get_wf_relation (type_of var))
    val scheme = get_translation_scheme (type_of var)
    val left = #left scheme
    val right = #right scheme
in
    (recInduct (REWRITE_RULE [relationTheory.WF_EQ_INDUCTION_THM] WF_R) THEN
    NTAC 2 STRIP_TAC) (a,g)
end;

(*****************************************************************************)
(* find_conditional_thm target t : hol_type -> thm                           *)
(*    Returns a rewrite for conditionals of the form:                        *)
(*        |- IF (P x) f g = if (isPair x) then f else g                      *)
(*                                                                           *)
(*****************************************************************************)

fun find_conditional_thm target =
let val scheme = get_translation_scheme target
    val i = mk_const("I",target --> target);
    val vars = map (C (curry mk_var) target) ["a","b"]
    val pred = beta_conv (mk_comb(#predicate scheme,mk_var("p",target)))
    val cond = imk_comb(i,mk_cond(pred,el 1 vars,el 2 vars));
in
    GSYM (REWRITE_RULE [combinTheory.I_THM]
    	 (snd (encode_until [is_var o rand] ([],[]) cond)))
end;

(*****************************************************************************)
(* PROPAGATE_RECOGNIZERS_TAC : thm list -> thm list -> tactic                *)
(*    Fully solves a goal of the form:                                       *)
(*      ?- !x. bool (detect ... x) = concrete_detect x (f ...) /\ bool ...   *)
(*    Given a list of theorems of the form:                                  *)
(*     |- bool (detect ... x) = if isPair x then ... else ...                *)
(*    Derived from partially encoding, then removing conditionals            *)
(*    and a list of definitions, representing the fully encoded theorems:    *)
(*     |- concrete_detect x (f ...) = if isPair x then ... else ...          *)
(*                                                                           *)
(*****************************************************************************)

local
fun MATCH_CONJ_TAC thm =
    MAP_FIRST (MATCH_MP_TAC o
    	       GENL (fst (strip_forall (concl thm))) o
	       DISCH (fst (dest_imp_only (snd (strip_forall (concl thm))))))
    	  (CONJUNCTS (UNDISCH (SPEC_ALL thm)));
fun PR_FINISH STAC =
    REPEAT (FIRST [REFL_TAC,
    	   FIRST_ASSUM MATCH_CONJ_TAC,
           MAP_FIRST MATCH_MP_TAC (DefnBase.read_congs())
	   THEN REPEAT STRIP_TAC,
	   CHANGED_TAC STAC,
	   MK_COMB_TAC]);
val cond = ``COND:bool -> 'a -> 'a -> 'a``
in
fun PROPAGATE_RECOGNIZERS_TAC theorems definitions x =
let fun is_single thm = null (find_terms (can (match_term cond))
    		      	     		 (rhs (concl thm)));
    val (singles,(thms,defs)) =
    	(I ## unzip) (partition (is_single o fst) (
    		       	     zip theorems definitions));
    fun conv (a,b) = LAND_CONV (REWR_CONV a) THENC RAND_CONV (REWR_CONV b)
    val STAC = CONV_TAC (STRIP_QUANT_CONV
    	       		(EVERY_CONJ_CONV (TRY_CONV
					 (FIRST_CONV (map conv singles)))));
in
     ((REPEAT (CHANGED_TAC STAC) THEN
     TARGET_INDUCT_TAC THEN REPEAT STRIP_TAC THEN
     ONCE_REWRITE_TAC definitions THEN
     ONCE_REWRITE_TAC theorems THEN
     REWRITE_TAC [find_conditional_thm
     		 (type_of (fst (dest_forall (snd x))))] THEN
     TRY IF_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
     RW_TAC (std_ss ++ boolSimps.LET_ss) [] THEN
     PR_FINISH STAC THEN
     WF_TC_FINISH_TAC THEN CCONTR_TAC THEN FULL_SIMP_TAC std_ss []) x)
     handle e => wrapException "PROPAGATE_RECOGNIZERS_TAC" e
end
end

(*****************************************************************************)
(* fix_definition_terms : thm list -> term list -> term list                 *)
(*    Given a list of definitions, replaces the variables matching the       *)
(*    defined constants with the constants.                                  *)
(*                                                                           *)
(*****************************************************************************)

fun fix_definition_terms defns props =
let val consts = map (fst o strip_comb o lhs o snd o strip_forall o concl) defns
    val vars = map (fn c => mk_var(fst (dest_const c),type_of c)) consts
in
    map (subst (map2 (curry op|->) vars consts)) props
end handle e => wrapException "fix_definition_terms" e

(*****************************************************************************)
(* define_with_tactic : hol_type -> conv -> tactic -> term list -> thm list  *)
(*     Attempts to define a list of terms as functions using the tactic      *)
(*     given.                                                                *)
(*                                                                           *)
(*****************************************************************************)

fun make_singles_definitions [] = []
  | make_singles_definitions L =
let val (defn,left) = pick_e Empty (fn s => new_definition
    	      	(fst (dest_var (fst (strip_comb (lhs s)))),s)) L
in
    defn::make_singles_definitions (fix_definition_terms [defn] left)
end;

fun fix_rewrite defs thm =
let val thm' = foldl (fn ((h,h'),thm) => INST_TY_TERM (match_term h h') thm)
    	             thm (zip (hyp thm) (fix_definition_terms defs (hyp thm)))
in
    foldl (uncurry PROVE_HYP) thm' defs
end;

fun define_with_tactic is_single conv tactic terms =
let val (singles,not_singles) = partition is_single terms
    val srws = map (fn x => list_mk_forall (snd (strip_comb (lhs x)),x)) singles
    val dterms = map (ALLOW_CONV (REWRITE_CONV (map ASSUME srws))) not_singles
    val rewrites = map (ALLOW_CONV conv o rhs o concl) dterms
    val name = fst (dest_var (fst (strip_comb (lhs (hd not_singles)))))
    val def_term = list_mk_conj (map (rhs o concl) rewrites)
    val (definition,induction) =
    	case (total new_definition) (name,def_term)
        of NONE => (I ## SOME) (Defn.tprove(
	     	    (Defn.mk_defn name def_term),tactic))
         | SOME defn => (defn,NONE)
   val singles' = fix_definition_terms (CONJUNCTS definition) singles
   val sdefs = make_singles_definitions singles'
   val srws = fix_definition_terms (sdefs @ CONJUNCTS definition) srws
   val dterms' = map (fix_rewrite (sdefs @ CONJUNCTS definition)) dterms
   val penultimate =
       map2 (fn r => CONV_RULE (STRIP_QUANT_CONV (REWR_CONV (GSYM r))))
       rewrites (CONJUNCTS definition)
   val ultimate =
       map2 (fn r => GEN_ALL o CONV_RULE (STRIP_QUANT_CONV
       	    	     	     (REWR_CONV (GSYM r))))
       dterms' penultimate
   val gvarname = fst o dest_var o fst o strip_comb o lhs o snd o strip_forall
   val gconstname = fst o dest_const o fst o strip_comb o
       		  lhs o snd o strip_forall o concl
in
    (map (fn t => first (curry op= (gvarname t) o gconstname)
    	       (sdefs @ ultimate)) terms,induction)
end handle e => wrapException "define_with_tactic" e

(*****************************************************************************)
(* flatten_abstract_recognizers :                                            *)
(*             (term -> bool) -> hol_type -> hol_type -> thm list            *)
(*                                                                           *)
(*    Flattens the recognizers for the type given, abstracting terms that    *)
(*    match the function given as inputs to the recognizer. For example:     *)
(*                                                                           *)
(*****************************************************************************)

fun flatten_abstract_recognizers fname f target t =
let val conditional = find_conditional_thm target
    val (props,thms,terms) = create_abstract_recognizers fname f target t
    val conv = SIMP_CONV (std_ss ++ boolSimps.LET_ss) [] THENC
    	       REWRITE_CONV [conditional]
    val funcs = map lhs terms
    fun is_single x = exists (curry op= (fst (strip_comb (rhs x))) o
			 	fst o strip_comb) funcs
    val (definitions,induction) = define_with_tactic is_single conv
    		      	      WF_RECOGNIZER_TAC terms
    val props' = fix_definition_terms definitions props
    val var = rand (rand (lhs (hd props')))
    val term = mk_forall(var,list_mk_conj props');
    val theorems = map (CONV_RULE conv) thms;
    val props_thms = CONJUNCTS (SPEC_ALL (prove(term,
    		   PROPAGATE_RECOGNIZERS_TAC theorems definitions)));
    fun fmap F f = map (fn x => f (fst (dest_const (fst (strip_comb
    		       	     	  (F (snd (strip_forall (concl x))))))),x));
    val _ = fmap rhs (fn (a,b) => save_thm("prop_" ^ a,b)) props_thms
    val _ = fmap rhs (uncurry (add_standard_rewrite 1)) props_thms
    val _ = fmap lhs (fn (a,b) => save_thm("translated_" ^ a,b))
    	    	     definitions
in
    definitions
end handle e => wrapException "flatten_abstract_recognizers" e

(*****************************************************************************)
(* Theorem tools to get rid of the detector stuff ....                       *)
(*****************************************************************************)

fun generalize_abstract_recognizer_term target t =
let val var = mk_var("x",target)
    val detector = get_detect_function target t
    val boolenc = get_encode_function target bool
    val booldec = get_decode_function target bool
    val x = ref false;
    fun once _ = (!x before (x := true));
    val prop = snd (encode_until [once] ([],[])
                   (mk_comb(boolenc,mk_comb(detector,var))));
    fun fix x = if x = var then x else genvar (type_of x)
    val left = mk_comb(booldec,list_mk_comb((I ## map fix)
                         (strip_comb (rhs (concl prop)))));
    val basetype = (mk_type o (I ## map (K target)) o dest_type) t
    val right = mk_comb(get_detect_function target basetype,var);
in
    mk_forall(var,mk_imp(left,right))
end handle e => wrapException "generalize_abstract_recognizer_term" e;

fun ENCODE_BOOL_UNTIL_CONV target terms term =
let val bool_encdec = FULL_ENCODE_DECODE_THM target bool
    val thm = GSYM (SPEC term bool_encdec);
    val limits = map (fn t => can (match_term t) o rand) terms
in
    RIGHT_CONV_RULE (RAND_CONV (snd o encode_until limits ([],[]))) thm
end;

fun GENERALIZE_ABSTRACT_RECOGNIZER_TAC target t thm (a,g) =
let val right = snd (dest_imp_only (snd (strip_forall g)))
in
   (TARGET_INDUCT_TAC THEN
   ONCE_REWRITE_TAC [thm] THEN
   ONCE_REWRITE_TAC [get_coding_function_def target t "detect"] THEN
   IF_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
   CONV_TAC (RAND_CONV (ENCODE_BOOL_UNTIL_CONV target [right]))) (a,g)
end

fun generalize_abstract_recognizer target t pre_rewrites thm =
   prove(generalize_abstract_recognizer_term target t,
      GENERALIZE_ABSTRACT_RECOGNIZER_TAC target t thm THEN
      ASM_REWRITE_TAC pre_rewrites THEN
      RULE_ASSUM_TAC (CONV_RULE (REPEATC (STRIP_QUANT_CONV
           (RIGHT_IMP_FORALL_CONV ORELSEC REWR_CONV AND_IMP_INTRO)))) THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC pre_rewrites THEN
      WF_TC_FINISH_TAC);

(*****************************************************************************)
(* create_abstracted_definition                                              *)
(*              : (term -> bool) -> hol_type -> string -> thm list ->        *)
(*                                  term list -> thm -> *)

fun encode_all_avoiding f func (assums,extras) term (tset,thmset) =
let val (ends,converted) = encode_until [f o rand,can (match_term func) o rand]
    			   		(assums,extras) term
    val terminals = map snd (el 1 ends)
    val recursions = el 2 ends
    val target = type_of term
    fun mk_encoder x = imk_comb(get_encode_function target (type_of x),x)
    	handle e => raise (mkDebugExn "mk_encoder"
	       ("Could not encode the value: " ^ term_to_string x));
    val recs = foldl (fn ((b,c),a) => map (pair b o mk_encoder)
    	       	     	 	     	 (snd (strip_comb (rand c))) @ a)
    	     [] recursions;
in
    foldl (fn ((x,y),b) => encode_all_avoiding f func (x,extras) y b)
    	  (mk_set(terminals @ tset),converted::thmset) recs
end handle e => wrapException "encode_all_avoiding" e

fun create_abstracted_definition_term
    f target name limits extras function =
let val term = snd (strip_forall
    	     (mk_analogue_definition_term target name
    	       				   limits function))
    val term_thm =
        STRIP_QUANT_CONV (RAND_CONV (RAND_CONV (RATOR_CONV (
                          RAND_CONV (ONCE_REWRITE_CONV [function]))))) term;
    val (tfunc,left) = dest_eq (snd (strip_forall (concl function)));

    val extra_theorems = calculate_extra_theorems target [(function,limits)];
    val (encoder,encoded) = dest_comb (rhs (snd (strip_forall term)))
    val (pred,body,default) = dest_cond encoded
    val assums = map ASSUME (strip_conj pred);

    val (terminals,converted) =
    	encode_all_avoiding f tfunc ([],extras @ extra_theorems)
			      (rand (snd (strip_forall (rhs (concl term_thm)))))
			      ([],[])

    val full_thm = RIGHT_CONV_RULE (STRIP_QUANT_CONV (RAND_CONV
    		   		   (REWR_CONV (last converted)))) term_thm
    val recursions = butlast converted

    val _ = trace 1 ("Unabstracted conversion:\n" ^
    	    	    term_to_string (rhs (concl full_thm)) ^ "\n")
    val _ = trace 1 ("\nRecusion points:\n")
    val _ = map (fn x => (trace 1 (thm_to_string x) ; trace 1 "\n")) recursions
    val _ = trace 1 ("\nTerminals:\n")
    val _ = map (fn x => (trace 1 (term_to_string x) ; trace 1 "\n")) terminals

    fun fixr x =
    	(fn t => PURE_REWRITE_RULE [FULL_ENCODE_DECODE_THM target t]
	    (AP_TERM (get_decode_function target t) x))
	(type_of (rand (lhs (concl x))));

    val recursions' = map fixr recursions;
    val rsubsts = map (op|-> o dest_eq o concl) recursions'

    val (props,output_terms) =
    	make_abstract_funcs target terminals [snd (strip_forall term)]
	    [subst rsubsts (snd (strip_forall (rhs (concl full_thm))))];

    val _ = trace 1 ("\nAbstracted definition:\n" ^
    	    	     term_to_string (hd output_terms));
    val _ = trace 1 ("\nPropagation term:\n" ^
    	    	     term_to_string (hd props) ^ "\n\n");
in
    (hd props,last converted,hd output_terms)
end;

fun convert_abstracted_definition
    f target name limits extras thm pre_rewrites tactic1 tactic2 =
let val (function,missing) = clause_to_case thm
    val limits' = map clause_to_limit missing @ limits
    val (prop,thm,term) = create_abstracted_definition_term
                 f target name limits' extras function
    		 handle e => wrapException "convert_abstracted_definition" e
    val conv = REWRITE_CONV pre_rewrites
    val (definition,ind) = (hd ## I)
    			   (define_with_tactic (K false) conv tactic1 [term])
    val prop' = hd (fix_definition_terms [definition] [prop])
    val vars = free_vars_lr prop'
    fun is_decoded v term =
    	(can (match_term (get_decode_function target (type_of term)))
	    (rator term)
	andalso rand term = v)  handle e => false;
    val decoded_vars = map (fn v => (hd o find_terms (is_decoded v)) prop')
    		       	   vars
    val encoded_vars = map (fn dv => mk_comb(
    		       get_encode_function target (type_of dv),
		       mk_var(fst (dest_var (rand dv)),type_of dv)))
		       decoded_vars;
    val nvars = map rand encoded_vars
    fun lmkimp [] t = t
      | lmkimp L t = mk_imp(list_mk_conj
      	(map (full_beta o C (curry list_imk_comb) nvars) L),t);
    val term = list_mk_forall(nvars,
    	(lmkimp limits' ((subst (map2 (curry op|->) vars encoded_vars) o
 	 subst (map2 (curry op|->) decoded_vars nvars)) prop')));
    val theorem = REWRITE_RULE pre_rewrites thm;
    val encdets = map (FULL_ENCODE_DETECT_THM target o type_of) nvars;
    val encdecs = map (FULL_ENCODE_DECODE_THM target o type_of) nvars;

    val prop_thm = prove(term,tactic2 definition thm)

    val name = (fst o dest_const o fst o strip_comb o rhs o
				    snd o strip_imp_only o snd o strip_forall o
				    concl) prop_thm;

    val _ = add_standard_rewrite 0 name prop_thm;

    val _ = save_thm("prop_" ^ name,prop_thm);
    val _ = save_thm("translated_" ^ name,definition);

in
    definition
end;

fun convert_abstracted_nonrec_definition f target name limits extras thm =
    convert_abstracted_definition f target name limits extras thm []
    NO_TAC
    (fn definition => fn rewrite => fn (a,g) =>
    	let val types = map type_of (fst (strip_forall g))
	in
    	    (REWRITE_TAC [definition,GSYM rewrite] THEN
	    REWRITE_TAC (map (FULL_ENCODE_DETECT_THM target) types) THEN
	    REWRITE_TAC (map (FULL_ENCODE_DECODE_THM target) types) THEN
	    REPEAT STRIP_TAC THEN
	    RW_TAC std_ss [thm]) (a,g)
        end);

end