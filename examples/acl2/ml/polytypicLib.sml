structure polytypicLib :> polytypicLib =
struct

open Binarymap List HolKernel boolLib bossLib Q Parse combinTheory computeLib
     Conv Thm Tactical BasicProvers Tactic Drule Definition
     listTheory numLib listLib pairLib Psyntax
     pairTheory sumTheory Lib arithmeticTheory proofManagerLib;

(*****************************************************************************)
(* Error handling functions:                                                 *)
(*                                                                           *)
(* Standard,Fatal,Debug : exception_level                                    *)
(* polyExn            : exception_level * string list * string -> exn        *)
(* isFatal              : exn -> bool                                        *)
(*     The different exception levels:                                       *)
(*         Standard : General exceptions                                     *)
(*         Fatal    : Input of the correct form, but cannot be computed      *)
(*         Debug    : Input to a lower function was of the wrong form        *)
(*     and an exception constructor for the traced, leveled exceptions.      *)
(*     isFatal considers, Fatal, Debug and the Interrupt exceptions fatal    *)
(*                                                                           *)
(* exn_to_string        : exn -> string                                      *)
(*     Converts an polyExn (and standard exceptions) to a string             *)
(*                                                                           *)
(* wrapException        : string -> exn -> 'a                                *)
(* wrapExceptionHOL     : string -> exn -> 'a                                *)
(*     wrapException adds a name to the trace in an exception and            *)
(*     wrapExceptionHOL adds a name to the trace then converts to a HOL_ERR  *)
(*                                                                           *)
(* Raise                : exn -> 'a                                          *)
(*     As Feedback.Raise but supports polyExn                                *)
(*                                                                           *)
(* mkStandardExn        : string -> string -> exn                            *)
(* mkFatalExn           : string -> string -> exn                            *)
(* mkDebugExn           : string -> string -> exn                            *)
(*     Create the different levels of exception given a function and message *)
(*                                                                           *)
(* tryfind_e            : exn -> ('a -> 'b) -> 'a list -> 'b                 *)
(* first_e              : exn -> ('a -> bool) -> 'a list -> 'a               *)
(* can                  : ('a -> 'b) -> 'a -> bool                           *)
(* total                : ('a -> 'b) -> 'a -> 'b option                      *)
(* repeat               : ('a -> 'a) -> 'a -> 'a                             *)
(*    Like the versions found in 'Lib' except will re-raise Fatal exceptions *)
(*    and can have specific exceptions for the end of the list               *)
(*                                                                           *)
(* debug                : bool                                               *)
(*    Determines whether inputs are tested                                   *)
(*                                                                           *)
(* assert               : string -> (string * ('a -> bool)) list -> 'a -> 'a *)
(*    If the debug flag is set, applies each test to 'a raising a debug      *)
(*    level exception if any fail.                                           *)
(*                                                                           *)
(* guarenteed           : ('a -> 'b) -> 'a -> 'b                             *)
(*    Raises a debug exception if the application fails                      *)
(*                                                                           *)
(* check_standard_conv  : string -> term * thm -> thm                        *)
(* check_matching_conv  : string -> term * thm -> thm                        *)
(*    Checks the output of a conv to make sure it matches the input term     *)
(*                                                                           *)
(*****************************************************************************)

datatype exception_level = Standard | Fatal | Debug;
exception polyExn of exception_level * string list * string;

local
(* Prints a function trace                                                   *)
fun trace_to_string [] = "\n"
  | trace_to_string [x] = "'" ^ x ^ "'\n"
  | trace_to_string (x::xs) = "'" ^ x ^ "' ->\n" ^ trace_to_string xs;

fun print_e s msg ftrace = s ^ msg ^ "\nRaised at:\n" ^ (trace_to_string ftrace)
in
fun exn_to_string (polyExn(Standard,ftrace,msg)) = print_e "Exception: " msg ftrace
  | exn_to_string (polyExn(Fatal   ,ftrace,msg)) = print_e "Fatal exception: " msg ftrace
  | exn_to_string (polyExn(Debug   ,ftrace,msg)) = print_e "Debug exception: " msg ftrace
  | exn_to_string x = Feedback.exn_to_string x
end;

fun Raise e = (print (exn_to_string e) ; raise e)

fun isFatal (polyExn(Fatal,_,_)) = true
  | isFatal (polyExn(Debug,_,_)) = true
  | isFatal (Interrupt) = true
  | isFatal _ = false;

fun wrapException name (polyExn(level,trace,msg)) = raise polyExn(level,name::trace,msg)
  | wrapException name Interrupt = raise Interrupt
  | wrapException name (HOL_ERR {origin_structure,origin_function,source_location,message}) =
    raise polyExn(Standard,[name,origin_structure ^ "." ^ origin_function],locn.toString source_location ^ ":\n" ^ message)
  | wrapException name exn = raise polyExn(Standard,[name],exn_to_string exn);

local
fun set_level Standard msg = msg
  | set_level Debug msg = "Debug: " ^ msg
  | set_level Fatal msg = "Fatal: " ^ msg
in
fun wrapExceptionHOL name (polyExn(level,[],msg)) = raise (mk_HOL_ERR "polyLib" name (set_level level msg))
  | wrapExceptionHOL name (polyExn(level,trace,msg)) =
        raise (foldr (uncurry (Feedback.wrap_exn "polyLib"))
                (mk_HOL_ERR "polyLib" (last trace) (set_level level msg)) (name::(butlast trace)))
  | wrapExceptionHOL name Interrupt = raise Interrupt
  | wrapExceptionHOL name exn = raise (mk_HOL_ERR "polyLib" name (exn_to_string exn))
end

fun mkStandardExn name msg = polyExn(Standard,[name],msg)
fun mkFatalExn    name msg = polyExn(Fatal,[name],msg)
fun mkDebugExn    name msg = polyExn(Debug,[name],msg)

fun tryfind_e exn f [] = raise exn
  | tryfind_e exn f (x::xs) = (f x) handle e => if isFatal e then raise e else tryfind_e exn f xs;

fun first_e exn p [] = raise exn
  | first_e exn p (x::xs) = if (p x handle e => if isFatal e then raise e else false) then x else first_e exn p xs;

fun can f x = (f x ; true) handle e => if isFatal e then raise e else false;

fun total f x = SOME (f x) handle e => if isFatal e then raise e else NONE;

fun repeat f x = repeat f (f x) handle e => if isFatal e then raise e else x;

val debug = ref true;

fun assert fname [] data = data
  | assert fname ((test_msg,test)::tests) data =
        if (!debug) then
                if (test data) handle e => false then assert fname tests data else raise polyExn(Debug,[fname],test_msg)
        else    data;

fun guarenteed f x = (f x)
        handle (polyExn(level,trace,msg))       => wrapException "guarenteed" (polyExn(Debug,trace,msg))
        |      Interrupt                        => raise Interrupt
        |      e                                => wrapException "guarenteed" e;

fun check_standard_conv name (term,thm) =
        if (!debug) then
                if is_eq (concl thm) then
                        if not ((lhs o concl) thm = term)
                                then raise polyExn(Debug,[name],"Standard conv returned a non-matching theorem")
                                else thm
                        else raise polyExn(Debug,[name],"Standard conv did not return an equality")
        else thm

fun check_matching_conv name (term,thm) =
        if (!debug) then
                if is_eq (concl thm) then
                        if not (can (match_term term) ((lhs o concl) thm))
                                then raise polyExn(Debug,[name],"Matching conv returned a non-matching theorem")
                                else thm
                        else raise polyExn(Debug,[name],"Matching conv did not return an equality")
        else thm

(*****************************************************************************)
(* Data Types required                                                       *)
(*                                                                           *)
(* translation_scheme :                                                      *)
(*     Holds the theorems necessary for the creation of polytypic functions  *)
(*     and optionally polytypic theorems.                                    *)
(* function :                                                                *)
(*     Represents a polytypic function, also holds its induction principle   *)
(* functions, theorems :                                                     *)
(*     Binary maps from types to strings to functions or theorems            *)
(* translations :                                                            *)
(*     The map from types to translating functions and theorems              *)
(*                                                                           *)
(*****************************************************************************)

type translation_scheme =
        {target : hol_type, induction : thm, recursion : thm, left : term, right : term, predicate : term, bottom : term, bottom_thm : thm};

type function = {const : term, definition : thm, induction : (thm * (term * (term * hol_type)) list) option}

type functions = (hol_type,(string,function) dict ref) dict;
type theorems = (hol_type,(string,thm) dict ref) dict;
type translations = (hol_type,((functions ref * theorems ref) * translation_scheme)) dict;

(*****************************************************************************)
(* Trace functionality:                                                      *)
(*                                                                           *)
(* type_trace : int -> string -> unit                                        *)
(*     Prints a trace message if the trace level supplied is greater than    *)
(*     the level registered.                                                 *)
(*                                                                           *)
(* Level 0 : No ouput                                                        *)
(* Level 1 : Progress through adding / removing splits and theorem progress  *)
(* Level 2 : Output important intermediate results                           *)
(* Level 3 : Output most intermediate results and function calls             *)
(*****************************************************************************)

val Trace = ref 1;

val _ = register_trace ("polytypicLib.Trace",Trace,3);

fun type_trace level s = if level <= !Trace then print s else ();

(*****************************************************************************)
(* Input testing functions:                                                  *)
(*                                                                           *)
(* both              : (bool * bool) -> bool                                 *)
(*     Returns true for (true,true)                                          *)
(*                                                                           *)
(* is_conjunction_of : (term -> bool) -> term -> bool                        *)
(* is_disjunction_of : (term -> bool) -> term -> bool                        *)
(* is_implication_of : (term -> bool) -> (term -> bool) -> term -> bool      *)
(* is_anything       : term -> bool                                          *)
(*    Recognisers for different terms, 'is_conjunction_of' and               *)
(*    'is_disjunction_of' only work for right-associated strings             *)
(*                                                                           *)
(*****************************************************************************)

fun both (a,b) = a andalso b;

fun is_conjunction_of f x =
        (is_conj x andalso (f (fst (dest_conj x))) andalso is_conjunction_of f (snd (dest_conj x))) orelse
        not (is_conj x) andalso (f x);

fun is_disjunction_of f x =
        (is_disj x andalso (f (fst (dest_disj x))) andalso is_disjunction_of f (snd (dest_disj x))) orelse
        not (is_disj x) andalso (f x);

fun is_implication_of f g x =
        (is_imp x) andalso both ((f ## g) (dest_imp x))

fun is_anything (x:term) = true;

(*****************************************************************************)
(* Printing tools:                                                           *)
(*                                                                           *)
(* xlist_to_string : ('a -> string) -> 'a list -> string                     *)
(* xpair_to_string : ('a -> string) -> ('b -> string) -> string              *)
(*     Prints a list or a pair of items using supplied printing functions    *)
(*                                                                           *)
(*****************************************************************************)

local
fun XL2S f [] = "]"
  | XL2S f [x] = (f x) ^ "]"
  | XL2S f (x::xs) = (f x) ^ "," ^ XL2S f xs
in
fun xlist_to_string f list = "[" ^ XL2S f list
        handle e => wrapException "xlist_to_string" e
end

fun xpair_to_string f g (a,b) = "(" ^ (f a) ^ "," ^ (g b) ^ ")"
        handle e => wrapException "xpair_to_string" e

(*****************************************************************************)
(* General list processing functions                                         *)
(*                                                                           *)
(* pick_e       : exn -> ('a -> 'b) -> 'a list -> 'b * 'a list               *)
(*     Like tryfind_e but returns the rest of the list that cannot be used   *)
(*                                                                           *)
(* bucket_alist : (''a * 'b) list -> (''a * 'b list) list                    *)
(*     Buckets together the first element with a list of the matching second *)
(*                                                                           *)
(* mappartition : ('a -> 'b) -> 'a list -> 'b list * 'a list                 *)
(*     Like mapfilter except returns a list of failures as well              *)
(*                                                                           *)
(* reachable_graph  : (''a -> ''a list) -> ''a -> (''a * ''a) list           *)
(*     Builds the graph of elements reachable from ''a under the function    *)
(*                                                                           *)
(* TC, RTC             : ''a * ''a list -> ''a * ''a list                    *)
(*     Returns the [reflexive] transitive closure of a graph                 *)
(*                                                                           *)
(*****************************************************************************)

fun pick_e exn f [] = raise exn
  | pick_e exn f (x::xs) =
        (f x,xs) handle e => if isFatal e then raise e else (I ## cons x) (pick_e exn f xs);

fun bucket_alist [] = []
  | bucket_alist ((x,y)::xys) =
let     val (a,b) = partition (curry op= x o fst) xys
in      (x,y::map snd a)::bucket_alist b
end

fun mappartition f [] = ([],[])
          | mappartition f (x::xs) = (cons (f x) ## I) (mappartition f xs)
        handle e => if isFatal e then raise e else (I ## cons x) (mappartition f xs);

fun reachable_graph f t =
let     fun BR nodes a G =
        let     val new_nodes = f a
                val new_edges = map (pair a) new_nodes
                val to_search = set_diff new_nodes nodes
        in
                foldl (fn (nn,G) => BR (to_search @ nodes) nn G) (new_edges @ G) to_search
        end
in
        BR [] t []
end

local
        fun all_pairs _ [] = []
          | all_pairs [] _ = []
          | all_pairs (x::xs) ys =
                map (pair x) ys @ all_pairs xs ys;

        fun ep x = map fst o filter (curry op= x o snd)
        fun sp y = map snd o filter (curry op= y o fst)

        fun add_new (x,y) pairs =
                union (all_pairs (x::ep x pairs) (y::sp y pairs)) pairs;
in
        fun TC pairs = foldl (uncurry add_new) [] pairs
        fun RTC pairs = TC (foldl (fn ((x,y),l) => insert (x,x) (insert (y,y) l)) pairs pairs)
end;

(*****************************************************************************)
(* Term and Thm tools:                                                       *)
(*                                                                           *)
(* list_mk_cond      : (term * term) list -> term -> term                    *)
(*     [(P0,a0),..,(Pn,an)] b --> if P0 then a0 else if P1 then ... else b   *)
(* imk_comb          : (term * term) -> term                                 *)
(* list_imk_comb     : (term * term list) -> term                            *)
(*     As mk_comb and list_mk_comb, except the left-hand term is             *)
(*     instantiated to match, if possible.                                   *)
(*                                                                           *)
(* rimk_comb         : (term * term) -> term                                 *)
(*     Like imk_comb, except instantiates the right term instead.            *)
(*                                                                           *)
(* full_beta_conv    : term -> term                                          *)
(*      Like Term.beta_conv, but for a list of abstractions                  *)
(* full_beta         : term -> term                                          *)
(*      As above, except this does not error when given shorter lists.       *)
(*                                                                           *)
(* UNDISCH_ONLY      : thm -> thm                                            *)
(* UNDISCH_ALL_ONLY  : thm -> thm                                            *)
(*     Like Drule.UNDISCH_ALL,Drule.UNDISCH but avoids |- ~A                 *)
(*                                                                           *)
(* UNDISCH_EQ        : thm -> thm                                            *)
(* UNDISCH_ALL_EQ    : thm -> thm                                            *)
(*     |- (A ==> B) = (A ==> C)  --->  [A] |- B = C                          *)
(*                                                                           *)
(* UNDISCH_CONJ      : thm -> thm                                            *)
(*     |- x0 /\ ... /\ xn ==> A  --->  [x0,...,xn] |- A                      *)
(*                                                                           *)
(* DISCH_LIST_CONJ   : term list -> thm -> thm                               *)
(* DISCH_ALL_CONJ    : thm -> thm                                            *)
(*     [x0,...,xn] |- A          --->  |- x0 /\ ... /\ xn ==> A              *)
(*                                                                           *)
(* CONJUNCTS_HYP     : term -> thm -> thm                                    *)
(*     Splits [``A ==> B /\ C``] |- D to [``A ==> B``,``A ...                *)
(*                                                                           *)
(* CONV_HYP          : (term -> thm) -> thm -> thm                           *)
(*     Applies a conversion to all hypotheses of a theorem                   *)
(*                                                                           *)
(* CHOOSE_L          : term list * thm -> thm -> thm                         *)
(*     Performs a CHOOSE for a list of variables                             *)
(*                                                                           *)
(* PROVE_HYP_CHECK   : thm -> thm -> thm                                     *)
(*     Like PROVE_HYP but checks for an effect first                         *)
(*                                                                           *)
(* GEN_THM           : term list -> thm -> thm                               *)
(*    Like Drule.GENL except it fully specifies the thm first                *)
(*                                                                           *)
(* ADDR_AND_CONV     : term -> term -> thm                                   *)
(* ADDL_AND_CONV     : term -> term -> thm                                   *)
(*    Converts a term ``A:bool`` to [B] |- A = A /\ B or [B] |- A = B /\ A   *)
(*                                                                           *)
(* MATCH_CONV        : thm -> term -> thm                                    *)
(*    Fully matches the theorem to the term, including instantiating         *)
(*    variables in the hypothesis                                            *)
(*                                                                           *)
(* CASE_SPLIT_CONV   : term -> thm                                           *)
(*     Converts a term of the form:  '!a. P a'  to perform a split case      *)
(*     |- !a. P a =                                                          *)
(*              (!a0 .. an. P (C0 a0 .. an)) /\ ... /\                       *)
(*              (!a0 .. am. P (Cn a0 .. am))                                 *)
(*                                                                           *)
(* PUSH_COND_CONV    : term -> thm                                           *)
(*    Pushes all function applications over a conditional                    *)
(*    |- f (g (if a then b else c)) = if a then f (g b) else f (g c)         *)
(*                                                                           *)
(* ORDER_FORALL_CONV : term list -> term -> thm                              *)
(*    Re-orders universally quantified variables to make the list given      *)
(*                                                                           *)
(* ORDER_EXISTS_CONV : term list -> term -> thm                              *)
(*    Re-orders existentially quantified variables to make the list given    *)
(*                                                                           *)
(* FUN_EQ_CONV       : term -> thm                                           *)
(*    Converts the term:  |- (!a b... f = g) = (!x a b... f x = g x)         *)
(*                                                                           *)
(* UNFUN_EQ_CONV     : term -> thm                                           *)
(*    Converts the term:  |- (!a b x... f x = g x) = (!a b... f = g)         *)
(*                                                                           *)
(* UNBETA_LIST_CONV  : term list -> term -> thm                              *)
(*    Like UNBETA_CONV but operates on a list of terms                       *)
(*                                                                           *)
(* NTH_CONJ_CONV     : int -> (term -> thm) -> term -> thm                   *)
(*    Performs a conv on the nth term in a conjunction                       *)
(*                                                                           *)
(* MK_CONJ           : thm -> thm -> thm                                     *)
(* LIST_MK_CONJ      : thm list -> thm                                       *)
(*    Makes a theorem |- A /\ B = C /\ D from |- A = C, |- B = D             *)
(*                                                                           *)
(* TC_THMS           : thm list -> thm list                                  *)
(*     Takes a list of theorems and repeatedly applies either TRANS or       *)
(*     IMP_TRANS to get a new set of theorems                                *)
(*                                                                           *)
(* prove_rec_fn_exists : thm -> term -> thm                                  *)
(*   Exactly the same as Prim.prove_rec_fn_exists but performs checking on   *)
(*   the input if the !debug flag has been set                               *)
(*                                                                           *)
(*****************************************************************************)

local
fun LMC [] last = last
  | LMC ((x,y)::xys) last = mk_cond (x,y,LMC xys last)
in
fun list_mk_cond a b = LMC a b handle e => wrapException "list_mk_cond" e
end

fun imk_comb (a,b) =
    mk_comb(inst (match_type (fst (dom_rng (type_of a))) (type_of b)) a,b)
    handle e => wrapException "imk_comb" e

fun rimk_comb (a,b) =
    mk_comb(a,inst (match_type (type_of b) (fst (dom_rng (type_of a)))) b)
    handle e => wrapException "rimk_comb" e

fun list_imk_comb(a,[]) = a
  | list_imk_comb(a,x::xs) = list_imk_comb(imk_comb (a,x),xs)
  handle e => wrapException "list_imk_comb" e;

fun full_beta_conv term =
let val (f,args) = strip_comb term
in
    foldl (fn (a,b) => beta_conv (mk_comb(b,a))) f args
end handle e => wrapException "full_beta_conv" e

fun full_beta x =
    full_beta_conv x handle _ =>
    mk_comb(full_beta (rator x),rand x) handle _ => x;

fun UNDISCH_ONLY thm =
        if is_imp_only (concl thm)
                then guarenteed UNDISCH thm
                else raise (mkStandardExn "UNDISCH_ONLY" "Thm is not of the form: \"|- A ==> B\"");

fun UNDISCH_ALL_ONLY thm =
        if is_imp_only (concl thm)
                then UNDISCH_ALL_ONLY (guarenteed UNDISCH thm)
                else thm;

fun UNDISCH_EQ thm =
let     val a = fst (dest_imp_only (lhs (concl thm)))
        val b = REWRITE_CONV [ASSUME a] a;
in
        CONV_RULE (BINOP_CONV (LAND_CONV (REWR_CONV b) THENC
                FIRST_CONV (map REWR_CONV (CONJUNCTS (SPEC_ALL IMP_CLAUSES))))) thm
end     handle e => raise (mkStandardExn "UNDISCH_EQ" "Thm is not of the form: \"|- (P ==> A) = (P ==> B)\"");

fun UNDISCH_ALL_EQ thm = repeat UNDISCH_EQ thm

fun UNDISCH_CONJ thm =
        (UNDISCH_CONJ (UNDISCH (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) thm)) handle _ =>
        UNDISCH_ONLY thm) handle e => raise (mkStandardExn "UNDISCH_CONJ" "Thm is not of the form: \"|- A ==> B\"");

local
fun DLC [] thm = thm
  | DLC [x] thm = DISCH x thm
  | DLC (x::xs) thm =
        CONV_RULE (TRY_CONV (REWR_CONV AND_IMP_INTRO)) (DISCH x (DLC xs thm))
in
fun DISCH_LIST_CONJ l thm = DLC l thm handle e => wrapException "DISCH_LIST_CONJ" e
end;

fun DISCH_ALL_CONJ thm = DISCH_LIST_CONJ (hyp thm) thm handle e => wrapException "DISCH_ALL_CONJ" e

fun CONJUNCTS_HYP h thm =
let     val (imps,c) = strip_imp_only
                (assert "CONJUNCTS_HYP" [("Hypothesis supplied is not a hypothesis of theorem",C mem (hyp thm))] h)
in
        (PROVE_HYP (foldr (uncurry DISCH)
                (LIST_CONJ (map (UNDISCH_ALL_ONLY o ASSUME o curry list_mk_imp imps) (strip_conj c))) imps) thm)
        handle e => wrapException "CONJUNCTS_HYP" e
end

fun CONV_HYP c thm =
let     fun check h =
                assert "CONV_HYP" [
                        ("CONV returned a non-equality for hypothesis: " ^ term_to_string h,is_eq o concl),
                        ("lhs of returned theorem does not match hypothesis: "  ^ term_to_string h,
                                curry op= h o lhs o concl)] (c h) handle UNCHANGED => REFL h
in
        foldl (fn (h,thm) => PROVE_HYP (UNDISCH_ONLY (snd (EQ_IMP_RULE (check h)))) thm) thm (hyp thm)
end;

local
fun get_exists x =
        let     val (v,b) = Psyntax.dest_exists x
                val (l,r) = get_exists b
        in      (v::l,x::r) end handle e => ([],[])
in
fun CHOOSE_L ([],cthm) thm = thm
  | CHOOSE_L (vars,cthm) thm =
let     val (xvars,bodies) = guarenteed get_exists (assert "CHOOSE_L" [
                                ("cthm is not existentially quantified",boolSyntax.is_exists)] (concl cthm))
        val (xvars',bodies') = (List.take(xvars,length vars),List.take(bodies,length vars))
in
        PROVE_HYP cthm (foldr (uncurry CHOOSE) thm
                (map2 (C pair o ASSUME o subst (map2 (curry op|->) xvars' vars)) bodies' vars))
end handle e => wrapException "CHOOSE_L" e;
end;

fun GEN_THM list thm =
let     val vars = fst (strip_forall (concl thm))
        val vars' = map (fn v => if mem v list then genvar (type_of v) else v) vars
        val _ = assert "GEN_THM" [("List is not a list of variables",all is_var)] list
in
        CONV_RULE (RENAME_VARS_CONV (map (fst o dest_var) list))
                (GENL (map (fn v => assoc v (zip vars vars') handle e => v) list) (SPECL vars' thm))
        handle e => wrapException "GEN_THM" e
end;

fun PROVE_HYP_CHECK th1 th2 =
        PROVE_HYP (assert "PROVE_HYP_CHECK"
                [("Conclusion of first argument is not a hypothesis of the second",C mem (hyp th2) o concl)] th1) th2;

local
        val (AND_L_T::AND_R_T::_) = CONJUNCTS (SPEC_ALL AND_CLAUSES)
        fun ass1 s = assert s [("First argument not of type :bool",curry op= bool o type_of)]
        fun ass2 s = assert s [("Second argument not of type :bool",curry op= bool o type_of)]
in
fun ADDR_AND_CONV term2 term1 =
        check_standard_conv "ADDR_AND_CONV"
                (term1,SYM (RIGHT_CONV_RULE (REWR_CONV AND_R_T)
                        (AP_TERM (mk_comb(conjunction,ass1 "ADDR_AND_CONV" term1))
                        (EQT_INTRO (ASSUME (ass2 "ADDR_AND_CONV" term2))))))
fun ADDL_AND_CONV term2 term1 =
        check_standard_conv "ADDL_AND_CONV"
                (term2,SYM (RIGHT_CONV_RULE (REWR_CONV AND_L_T)
                        (AP_THM (AP_TERM conjunction (EQT_INTRO (ASSUME (ass2 "ADDL_AND_CONV" term2))))
                        (ass1 "ADDL_AND_CONV" term1))))
end;

fun MATCH_CONV thm term =
let     val match = match_term ((lhs o concl) thm) term
in
        if op_mem (fn x => fn y => fst (dest_var x) = fst (dest_var y) handle _ => false)
                ((repeat rator o lhs o concl) thm) (map #redex (fst match))
        then NO_CONV term
        else check_standard_conv "MATCH_CONV"
                (term,REWR_CONV (INST_TY_TERM match thm) term)
end;

fun ORDER_FORALL_CONV list term =
let     val (a,b) = strip_forall term
        val (vars,body) = (List.take(a,length list),list_mk_forall(List.drop(a,length list),b))
                handle e => wrapException "ORDER_FORALL_CONV" e
        val _ = if set_eq vars list then () else
                raise (mkStandardExn "ORDER_FORALL_CONV"
                        ("Variable set: " ^ xlist_to_string term_to_string list ^
                         "\n is equal to the quantifier set of: " ^ term_to_string term))
in
        check_standard_conv "ORDER_FORALL_CONV" (term,IMP_ANTISYM_RULE
                (DISCH_ALL (GENL list (SPECL vars (ASSUME term))))
                (DISCH_ALL (GENL vars (SPECL list (ASSUME (list_mk_forall(list,body))))))
                handle e => wrapException "ORDER_FORALL_CONV" e)
end;

fun ORDER_EXISTS_CONV l term =
let     val (ra,bodya) = strip_exists term
        val (r,body) = (List.take(ra,length l),
                        list_mk_exists(List.drop(ra,length l),bodya))
                        handle e => wrapException "ORDER_EXISTS_CONV" e
        fun mk_exists r l body =
                DISCH_ALL (CHOOSE_L (l,ASSUME (list_mk_exists(l,body)))
                (foldr (uncurry SIMPLE_EXISTS) (ASSUME body) r))
in
        IMP_ANTISYM_RULE (mk_exists l r body) (mk_exists r l body)
        handle e => wrapException "ORDER_EXISTS_CONV" e
end;

local
fun order_conv flip term =
let     val (hs,body) = strip_forall term
        val (front,back) = partition (flip o curry op= ((rand o lhs) body)) hs
in      (ORDER_FORALL_CONV (front @ back) term)
end
in
val FUN_EQ_CONV = STRIP_QUANT_CONV (REWR_CONV FUN_EQ_THM) THENC order_conv I
val UNFUN_EQ_CONV = order_conv not THENC ONCE_DEPTH_CONV (REWR_CONV (GSYM FUN_EQ_THM))
end

local
fun UNBETA_LIST_CONV' [] term = ALL_CONV term
  | UNBETA_LIST_CONV' (x::xs) term =
        (UNBETA_CONV x THENC RATOR_CONV (UNBETA_LIST_CONV' xs)) term
in
fun UNBETA_LIST_CONV list term = check_standard_conv "UNBETA_LIST_CONV"
        (term,(UNBETA_LIST_CONV' (rev list) term) handle e => wrapException "UNBETA_LIST_CONV" e)
end;

local
fun NTH_CONJ_CONV' 0 conv term =
        if is_conj term then AP_THM (AP_TERM conjunction (conv (fst (dest_conj term)))) (snd (dest_conj term))
                        else conv term
  | NTH_CONJ_CONV' n conv term =
        AP_TERM (mk_comb(conjunction,fst (dest_conj term))) (NTH_CONJ_CONV' (n - 1) conv (snd (dest_conj term)))
in
fun NTH_CONJ_CONV n conv term =
let     fun conv' h =
                assert "NTH_CONJ" [
                        ("CONV returned a non-equality for conjunction: " ^ term_to_string h,is_eq o concl),
                        ("CONV returned a theorem that does not match conjunction: "  ^ term_to_string h,
                                curry op= h o lhs o concl)] (conv h)
in
        check_standard_conv "NTH_CONJ_CONV" (term,NTH_CONJ_CONV' n conv' term
                handle e => wrapException "NTH_CONJ_CONV" e)
end
end;

fun CASE_SPLIT_CONV term =
let     val (xvar,body) = dest_forall term handle e => wrapException "CASE_SPLIT_CONV" e
        val t = type_of xvar
        val nchot_thm = TypeBase.nchotomy_of t
                handle e => raise (mkStandardExn "CASE_SPLIT_CONV"
                                ("An nchotomy does not exist for the type of the " ^
                                 " universally quantified variable: " ^ type_to_string t))
        val nchot = ISPEC xvar nchot_thm
                handle e => raise (mkDebugExn "CASE_SPLIT_CONV"
                        ("TypeBase returned an nchotomy for type " ^ type_to_string t ^
                         " which was not universally quantified with a variable of the same type!"))
        val all_vars = find_terms is_var term
        fun VARIANT_CONV term =
        let     val vars = fst (strip_exists term)
        in      RENAME_VARS_CONV (map (fst o dest_var o variant all_vars) vars) term
        end;
        val nchot' = CONV_RULE (EVERY_DISJ_CONV VARIANT_CONV) nchot handle e => wrapException "CASE_SPLIT_CONV" e
        val nchots = strip_disj (concl nchot')

        val full_left = DISCH_ALL (LIST_CONJ (map (fn n => GENL (snd (strip_comb (rhs (snd (strip_exists n)))))
                                (INST [xvar |-> rhs (snd (strip_exists n))] (SPEC_ALL (ASSUME term)))) nchots))
                        handle e => wrapException "CASE_SPLIT_CONV" e

        val r_tm = snd (dest_imp_only (concl full_left)) handle e => wrapException "CASE_SPLIT_CONV" e
        val right = map2 (fn n => fn c => PURE_REWRITE_RULE [GSYM (ASSUME (snd (strip_exists n)))] (SPEC_ALL c)) nchots (CONJUNCTS (ASSUME r_tm))
                        handle e => wrapException "CASE_SPLIT_CONV" e
        val right' = map2 (fn n => fn r => CHOOSE_L (fst (strip_exists n),ASSUME n) r handle _ => r) nchots right
        val full_right = DISCH_ALL (GEN xvar (DISJ_CASESL nchot' right'))
                        handle e => wrapException "CASE_SPLIT_CONV" e
in
        IMP_ANTISYM_RULE full_left full_right handle e => wrapException "CASE_SPLIT_CONV" e
end

local
fun PCC term =
        ((REWR_CONV COND_RAND) ORELSEC (RAND_CONV PCC THENC REWR_CONV COND_RAND) ORELSEC ALL_CONV) term
in
fun PUSH_COND_CONV term = PCC term
        handle UNCHANGED => raise UNCHANGED | e => wrapException "PUSH_COND_CONV" e
end

local
fun MC thm1 thm2 = MK_COMB (AP_TERM conjunction thm1,thm2)
fun LMC [] = raise (mkStandardExn "LIST_MK_CONJ" "Empty list")
  | LMC [x] = x
  | LMC (x::xs) = MC x (LMC xs);
in
fun MK_CONJ thm1 thm2 = MC thm1 thm2 handle e => wrapException "MK_CONJ" e
fun LIST_MK_CONJ [] = LMC []
  | LIST_MK_CONJ thms = LMC thms handle e => wrapException "LIST_MK_CONJ" e
end;

local
fun etrans f l r thm1 thm2 =
let     val (vars1,body1) = strip_forall (concl thm1)
        val (vars2,body2) = strip_forall (concl thm2)
        val match = match_term (l body2) (r body1)
        val _ = if null (set_diff (map #redex (fst match)) vars1) then ()
                else raise Empty
        val _ = if null (set_diff (map #residue (fst match)) vars2) then ()
                else raise Empty
        val thm1' = SPEC_ALL thm1
        val thm2' = INST_TY_TERM match (SPEC_ALL thm2)
in
        GENL vars1 (f thm1' thm2')
end
fun mtrans t1 t2 =
        etrans TRANS lhs rhs t1 t2 handle e =>
        etrans IMP_TRANS (fst o dest_imp_only) (snd o dest_imp_only) t1 t2;
fun trans_all _ [] = []
  | trans_all [] _ = []
  | trans_all (x::xs) ys = (mapfilter (mtrans x) ys) @ trans_all xs ys
in
fun TC_THMS thms =
let     val next = trans_all thms thms
        val diff = op_set_diff (fn a => fn b => concl a = concl b) next thms
in
        if null diff then thms else TC_THMS (diff @ thms)
end
end

local
fun assert' x = assert "prove_rec_fn_exists" x
val dexn = mkDebugExn "prove_rec_fn_exists"
fun PRFE axiom term =
let     val _ = assert' [("Not a (right associative) conjunction of generalised equalities: " ^ term_to_string term,
                        is_conjunction_of (is_eq o snd o strip_forall))] term
        val conjuncts = map (snd o strip_forall) (strip_conj term)
        val funcs = map (fst o strip_comb o lhs) conjuncts
        fun fvs conj = (set_diff (set_diff (free_vars (rhs conj)) (free_vars (lhs conj))) funcs,conj)
        val _ = case (total (first (not o null o fst)) (map fvs conjuncts))
                of SOME (var_list,clause) => raise (dexn ("The variables; " ^ xlist_to_string term_to_string var_list ^
                        " are free in the clause: " ^ term_to_string clause))
                |  NONE => ()
        val ax_err = "Axiom is not an existentially quantified conjunction of equalities: " ^ thm_to_string axiom;
        val _ = assert' [(ax_err,can Psyntax.dest_exists o snd o strip_forall o concl),
                        (ax_err,is_conjunction_of (is_eq o snd o strip_forall) o snd o strip_exists o
                                snd o strip_forall o concl)] axiom;
        val constructors_axiom = map (repeat rator o rand o lhs o snd o strip_forall)
                        ((strip_conj o snd o strip_exists o snd o strip_forall o concl) axiom)
        val constructors_term = map (repeat rator o rand o lhs o snd o strip_forall) (strip_conj term)
        val _ = case (op_set_diff same_const constructors_axiom constructors_term)
                of [] => ()
                |  list => raise (dexn ("The constructors; " ^ xlist_to_string term_to_string list ^
                                " are not used in the function"))
        val _ = case (op_set_diff same_const constructors_term constructors_axiom)
                of [] => ()
                |  list => raise (dexn ("The constructors; " ^ xlist_to_string term_to_string list ^
                        " are used in the function but not specified in the axiom"))
in
        Prim_rec.prove_rec_fn_exists axiom term handle e => wrapException "prove_rec_fn_exists" e
end
in
fun prove_rec_fn_exists axiom term = PRFE axiom term
end;

(*****************************************************************************)
(* Type tools:                                                               *)
(*                                                                           *)
(* constructors_of : hol_type -> term list                                   *)
(*     Like TypeBase.constructors_of except ensures that the result types    *)
(*     match exactly                                                         *)
(*                                                                           *)
(* base26          : int -> string                                           *)
(*     Converts a number to the nth string in the sequence {a,b,..aa,ab,...} *)
(*                                                                           *)
(* base_type       : hol_type -> hol_type                                    *)
(*     Changes a type (t0,t1,t2...) t to ('a,'b,'c,...) t                    *)
(*                                                                           *)
(* sub_types       : hol_type -> hol_type list                               *)
(*     Returns direct sub-types of the type given                            *)
(*                                                                           *)
(* uncurried_sub_types : hol_type -> hol_type list                           *)
(*     Returns direct sub-types of the type given but treats constructors of *)
(*     the type Cn:t0 -> .. -> tn -> t as :t0 * ... * tn -> t                *)
(*                                                                           *)
(* split_nested_recursive_set :                                              *)
(*             hol_type -> (hol_type * (hol_type list * hol_type list)) list *)
(*     Returns a list mapping a set of mutually recursive types to nested    *)
(*     mutually recursive types and direct sub-types                         *)
(*                                                                           *)
(* zip_on_types    :  ('a -> hol_type) -> ('b -> hol_type) ->                *)
(*                                      'a list -> 'b list -> ('a * 'b) list *)
(*     Finds a mapping between two lists by matching types after applying    *)
(*     a pair of functions                                                   *)
(*                                                                           *)
(* get_type_string : hol_type -> string                                      *)
(*     Returns a sanitised name for a type by removing preceding '           *)
(*                                                                           *)
(* SAFE_INST_TYPE, safe_inst, safe_type_subst                                *)
(*     Like their standard counterparts, except they prevent capture of      *)
(*     type variables already in the term                                    *)
(*                                                                           *)
(*****************************************************************************)

fun constructors_of t =
        map (fn c => inst (match_type ((snd o strip_fun o type_of) c) t) c)
                (TypeBase.constructors_of t)
        handle e => wrapException "constructors_of" e;

local
fun base26i n A =
        if n < 26 then (Char.chr (Char.ord #"a" + n)::A)
        else base26i (n div 26 - 1) (Char.chr (Char.ord #"a" + n mod 26)::A)
in
fun base26 n = base26i n []
end;

local
fun mk_nvartype n = mk_vartype (implode (#"'" :: base26 n));
fun get_type_params t =
        if is_vartype t
                then []
                else map (mk_nvartype o fst) (enumerate 0 (snd (dest_type t)))
        handle e => wrapException "get_type_params" e;
fun type_vars_cannonA (t,A) =
        if is_vartype t then t::A
        else if can dest_type t
        then foldl type_vars_cannonA A (snd (dest_type t))
        else [];
fun type_vars_cannon t = rev (mk_set (type_vars_cannonA (t,[])))
in
fun base_type t =
        mk_type (fst (dest_type t),get_type_params t)
        handle e => wrapException "base_type" e;
fun cannon_type t =
        type_subst (map (fn (a,b) => b |-> mk_nvartype a) (enumerate 0 (type_vars_cannon t))) t
end

fun sub_types t =
let     val constructors = constructors_of t
in
        mk_set (flatten (map (fst o strip_fun o type_of) constructors))
end     handle e => []

fun uncurried_subtypes t =
let     val cs = constructors_of t
in
        if can (match_type (mk_prod (alpha,beta))) t then sub_types t
        else mk_set (mapfilter (list_mk_prod o fst o strip_fun o type_of) cs)
end     handle e => [];

fun split_nested_recursive_set t =
let     val G = (t,t)::reachable_graph sub_types t
        val RTC_G = RTC G
        val mr_set = mk_set (filter (fn a => mem (a,t) RTC_G andalso mem (t,a) RTC_G) (map fst G))
        fun is_nested t' = not (exists (can (C match_type (base_type t'))) mr_set)
        val (nmr,pmr) = partition is_nested mr_set
in
        map (fn x => (x,(mk_set ## mk_set)
                (partition (C mem nmr) (map snd (reachable_graph (fn t => set_diff (sub_types t) pmr) x))))) pmr
end     handle e => wrapException "split_nested_recursive_set" e

local
fun pluck_all f [] = []
  | pluck_all f (x::xs) =
        (if f x then (x,xs)::map (I ## cons x) (pluck_all f xs)
                else map (I ## cons x) (pluck_all f xs))
in
fun zip_on_types f g [] [] = []
  | zip_on_types f g _  [] = raise (mkStandardExn "zip_on_types" "Lists of different length")
  | zip_on_types f g [] _  = raise (mkStandardExn "zip_on_types" "Lists of different length")
  | zip_on_types f g (x::xs) ys =
let     val poss_l = pluck_all (can (match_type (f x)) o g) ys handle e => wrapException "zip_on_types" e
in
        tryfind_e (mkStandardExn "zip_on_types" "No match found") (fn (p,l) => (x,p)::zip_on_types f g xs l) poss_l
end
end;

local
val sanitise = filter (fn a => not (a = #"'") andalso not (a = #"%"))
val remove_primes = implode o sanitise o explode
in
fun get_type_string t =
        if      is_vartype t
        then    remove_primes (dest_vartype t)
        else    fst (dest_type t)
        handle e => wrapException "get_type_string" e
end

local
fun mapsfrom s tyvars = map (fn a => a |-> gen_tyvar()) (filter (C mem (map #residue s)) tyvars)
in
fun SAFE_INST_TYPE s thm =
let     val map1 = mapsfrom s (mk_set (flatten (map (type_vars_in_term) (uncurry (C (curry op::)) (dest_thm thm)))))
in
        INST_TYPE s (INST_TYPE map1 thm)
end     handle e => wrapException "SAFE_INST_TYPE" e
fun safe_inst s term =
let     val map1 = mapsfrom s (type_vars_in_term term)
in
        inst s (inst map1 term)
end     handle e => wrapException "safe_inst" e
fun safe_type_subst s t =
let     val map1 = mapsfrom s (type_vars t)
in
        type_subst s (type_subst map1 t)
end     handle e => wrapException "safe_type_subst" e
end;

(*****************************************************************************)
(* Checking functions for different kinds of output:                         *)
(*                                                                           *)
(* is_source_function : term -> bool                                         *)
(*     Returns true if the term is a conjunction of terms of the form:       *)
(*           (!x .. y. fni f0 .. fn (C a0 .. an) = A [fnj a0...])            *)
(*     In particular:                                                        *)
(*           a) there can be no free variables in any clause except fni      *)
(*           b) the function must be defined for all constructors of all     *)
(*              argument types.                                              *)
(*                                                                           *)
(* is_target_function : term -> bool                                         *)
(*     Returns true if the term is a conjunction of terms of the form:       *)
(*           (!x .. y. fni f0 .. fn x = if P x then A x else B x)            *)
(*     In particular:                                                        *)
(*           a) there can be no free variables in any clause except fni      *)
(*           b) calls to any fni cannot occur inside B                       *)
(*     also returns true if terms are singly constructed, eg:                *)
(*           (!x .. y. fni f0 .. fn x = A x)                                 *)
(*                                                                           *)
(* is_expanded_function : term -> bool                                       *)
(*    Returns true if the term is a function term and every recusive call:   *)
(*          fni ... x = ... f0 f1 f2 .. fk a ...                             *)
(*          where a is free in x, or x is free in a                          *)
(*          there is an fni free in {f0..fk}                                 *)
(*    has the function (f0 in this case) defined in the conjunction          *)
(*                                                                           *)
(*****************************************************************************)

local
fun is_function term =
        all (fn x => x term) [
                is_conjunction_of (is_eq o snd o strip_forall),
                is_conjunction_of (is_comb o lhs o snd o strip_forall),
                null o set_diff (free_vars term) o map (repeat rator o lhs o snd o strip_forall) o strip_conj]
val pt = (fn (a,b,c) => a) o dest_cond
val preds = map pt o filter is_cond o map (rhs o snd o strip_forall) o strip_conj
fun xaconv a b = aconv (list_mk_abs(free_vars_lr a,a)) (list_mk_abs(free_vars_lr b,b))
fun is_target_term p c =
        (is_cond o rhs o snd o strip_forall) c andalso
        (xaconv p o pt o rhs o snd o strip_forall) c
fun is_target_term_single c =
        (not o is_cond o rhs o snd o strip_forall) c orelse
        let     val x = (rand o lhs o snd o strip_forall) c
                val (_,_,y) = (dest_cond o rhs o snd o strip_forall) c
        in
                not (free_in x y)
        end
fun is_function_target term =
        is_function term andalso
        (is_conjunction_of is_target_term_single term orelse
         can (tryfind (pt o rhs o snd o strip_forall)) (strip_conj term) andalso
         let    val p = tryfind (pt o rhs o snd o strip_forall) (strip_conj term)
         in     is_conjunction_of (fn x => is_target_term_single x orelse is_target_term p x) term
         end)
fun encodes_constructors C term =
let     val cs = (map (repeat rator o rand o lhs o snd o strip_forall) o strip_conj) term
in
        all is_const cs andalso
        all (fn c => exists (same_const c) C) cs
end
fun get_ftypes term = (mk_set o map (type_of o rand o lhs o snd o strip_forall) o strip_conj) term
fun constructors t = TypeBase.constructors_of t handle _ => []
in
fun is_source_function term =
        is_function term andalso
        encodes_constructors
                (flatten (map constructors (get_ftypes term)))
                term
fun is_target_function term =
        is_function term andalso
        is_function_target term
fun is_expanded_function term =
let     val all_fns = map (repeat rator o lhs o snd o strip_forall) (strip_conj term)
        val rec_calls = flatten (map (fn c =>
                        find_terms (fn t => is_comb t andalso
                                        exists (C free_in (rator t)) all_fns andalso
                                        (free_in ((rand o lhs o snd o strip_forall) c) (rand t) orelse
                                         free_in (rand t) ((rand o lhs o snd o strip_forall) c)))
                                ((rhs o snd o strip_forall) c)) (strip_conj term))
        val shortened = filter (fn x => not (exists (fn t => not (x = t) andalso free_in t x) rec_calls))
                                rec_calls
in
        all (C mem all_fns o repeat rator) shortened
end
end

(*****************************************************************************)
(* SPLIT_FUNCTION_CONV: (term list -> term -> term -> bool) * thm ->         *)
(*                                                 thm list -> term -> thm   *)
(*     SPLIT_FUNCTION_CONV: (is_double_term,pair_def) ho_function_defs term  *)
(*     replaces any higher order functions with their definitions including  *)
(*     a hypothesis stating that the variable used to replace them is        *)
(*     correct. It also rewrites pair_def whenever possible                  *)
(*                                                                           *)
(* RFUN_CONV : thm list -> conv                                              *)
(*     Given a list of equalities, rewrites them in a term provided the      *)
(*     rewrite occurs for a variable in the constructor of the function      *)
(*     being rewritten.                                                      *)
(*                                                                           *)
(* SPLIT_HFUN_CONV: thm -> term list -> term -> (term list * thm)            *)
(*     Replaces a term ...f G x... with f' G' x where f' is a variable       *)
(*     constrained in the hypothesis to follow the definition of f and G' is *)
(*     a subset of G containing only variables in the top definition         *)
(*                                                                           *)
(* SPLIT_PAIR_CONV: (term list -> term -> term -> bool) -> term list ->      *)
(*                                          thm -> term -> (term list * thm) *)
(*     Replaces a pair term ...pair f g x... with the definition of pair, if *)
(*     the pair is of the form pair f0 f1 (L/R x) then a new function is     *)
(*     made                                                                  *)
(*                                                                           *)
(* is_single_constructor: translation_scheme -> term -> bool                 *)
(*     Returns true if the term can be rewritten into the mutual recursion,  *)
(*     and as such requires removal of (L x) and (R x) not just (L (R x))    *)
(*                                                                           *)
(* is_double_term_target : translation_scheme ->                             *)
(*                                term list -> term -> term -> bool          *)
(* is_double_term_source : term list -> term -> term -> bool                 *)
(*     Checks to see if a pair term in a function requires splitting, the    *)
(*     'target' function deals with decoding and detecting whereas the       *)
(*     'source' function deals with encoding                                 *)
(*                                                                           *)
(*****************************************************************************)

fun is_single_constructor (scheme:translation_scheme) term =
let     val err = mkStandardExn "is_single_constructor" "Term is not of the form: 'f a = b'"
        val isP = #predicate scheme
        val left = #left scheme
        val right = #right scheme
        val (l,r) = (dest_eq o snd o strip_forall) term handle e => raise err
        val var = rand l handle e => raise err
        val _ = assert "is_single_constructor" [("Recursive variable is of type: " ^ type_to_string (type_of var) ^
                " however the predicate is of type: " ^ type_to_string (type_of isP),
                curry op= (type_of var) o fst o dom_rng o type_of)] isP
in
        not (free_in (beta_conv (mk_comb (isP,var))) r) orelse
        not (free_in (beta_conv (mk_comb (left,var))) r orelse free_in (beta_conv (mk_comb (right,var))) r)
        handle e => wrapException "is_single_constructor" e
end;

fun RFUN_CONV rewrites term =
let     val all_funs = mk_set (map (rator o lhs o snd o strip_forall) (strip_conj term))
        fun conv clause =
                ONCE_DEPTH_CONV (fn term =>
                        if      exists (C free_in (rand term))
                                        (op:: (strip_comb (rand (lhs (snd (strip_forall clause))))))
                                andalso null (find_terms (same_const conditional) term)
                        then    ONCE_DEPTH_CONV (FIRST_CONV (map REWR_CONV rewrites)) term
                        else    NO_CONV term)
                clause
in
        EVERY_CONJ_CONV conv term
end;

local
fun assert' x = assert "SPLIT_HFUN_CONV" x
val func_exn = mkDebugExn "SPLIT_HFUN_CONV" "HO Function supplied is of the form \"(f x = A x) /\\ (g x =...\"";

fun wrap e = wrapException "SPLIT_HFUN_CONV" e
in
fun SPLIT_HFUN_CONV hfun_def fvs term =
let     val _ = type_trace 3 "->SPLIT_HFUN_CONV\n"
        val _  = (assert' [
                        ("Term is not a conjunction of equalities",is_conjunction_of (is_eq o snd o strip_forall)),
                        ("Term is not a conjunction of function (not constant) definitions",
                                is_conjunction_of (can dest_comb o lhs o snd o strip_forall))] term)
        val function_terms = (mk_set o map (rator o lhs o snd o strip_forall) o strip_conj o concl) hfun_def
        val _ = if exists (C free_in ((list_mk_conj o map (snd o strip_forall) o strip_conj) term)) function_terms
                        then () else raise UNCHANGED
        val _ = assert' [("Function list is not a list of variables",all is_var)] fvs
        val _ = assert' [("Constants specified in higher order function: " ^ thm_to_string hfun_def,
                         all (can dom_rng o type_of))] function_terms;

        val (fvs',new_consts) =
                foldr (fn (x,(fvs,consts)) =>
                        let     val (arg_type,res_type) = dom_rng (type_of x)
                                val ftvs = set_diff (free_varsl (snd (strip_comb x))) fvs
                                val nc = variant fvs (mk_var("split",
                                        list_mk_fun (map type_of ftvs,arg_type --> res_type)))
                        in
                                (nc::fvs,(ftvs,list_mk_comb(nc,ftvs))::consts)
                        end) (fvs,[]) function_terms handle e => wrap e

        val concl_assumptions = map2 (fn (a,b) => curry list_mk_forall a o curry mk_eq b) new_consts function_terms
                                        handle e => wrap e;
        val hyp_assumption = list_mk_conj (map (fn x =>
                                        list_mk_forall(free_vars_lr (rand (lhs x)),
                                        list_mk_forall(mk_set (flatten (map fst new_consts)),
                                                subst (map2 (curry op|->) function_terms (map snd new_consts)) x)))
                                        ((map (snd o strip_forall) o strip_conj o concl) hfun_def))
                                handle e => wrap e
        val rewrites = map (SYM o SPEC_ALL) (CONJUNCTS (UNDISCH_ONLY
                                (ASSUME (mk_imp(hyp_assumption,list_mk_conj concl_assumptions)))))
                                handle e => wrap e
in
        (rewrites,fvs',check_standard_conv "SPLIT_HFUN_CONV" (term,
                (RIGHT_CONV_RULE (ADDR_AND_CONV hyp_assumption THENC PURE_REWRITE_CONV [GSYM CONJ_ASSOC])
                (RFUN_CONV rewrites term)) handle e => wrap e))
end
end;

local
val debug_exn = mkDebugExn "SPLIT_PAIR_CONV"
val func_exn = debug_exn "Term is not a conjunction of equalities";
val pair_exn = debug_exn "Pair theorem is not of the form \"pair f g x = A (f x) (g x)\""
fun wrap UNCHANGED = raise UNCHANGED | wrap e = wrapException "SPLIT_PAIR_CONV" e
fun wrapd UNCHANGED = raise UNCHANGED | wrapd e = wrapException "SPLIT_PAIR_CONV (fix_double_term)" e

fun FUN_EQ_RULE thm =
let     val (vars,body) = (strip_forall o concl) thm
        val a = (rand o lhs) body
in
        GENL (set_diff vars [a]) (CONV_RULE (REWR_CONV (GSYM FUN_EQ_THM)) (GEN a (SPEC_ALL thm)))
end handle e => wrapException "SPLIT_PAIR_CONV (FUN_EQ_RULE)" e

fun fix_double_term fvs funcs pair_def term =
let     val (l_thm,px) = with_exn dest_comb term pair_exn
        val vars = set_diff (free_vars l_thm) funcs
        val new_term = list_mk_comb(variant fvs (mk_var("split",
                                foldr (fn (a,t) => type_of a --> t) (type_of l_thm) vars)),vars) handle e => wrapd e

        val pvar1 = with_exn (rand o lhs o concl) pair_def pair_exn
        val pvar2 = subst (fst (foldl (fn (v,(s,fvs)) => let val x = variant fvs v in ((v |-> x) :: s,x::fvs) end)
                                ([],vars) (free_vars pvar1))) pvar1 handle e => wrapd e;
        val pvar3 = inst (match_type (type_of pvar2) (fst (dom_rng (type_of l_thm)))) pvar2 handle e => wrapd e;

        val func =  snd (EQ_IMP_RULE (STRIP_QUANT_CONV (RAND_CONV (REWR_CONV pair_def))
                        (list_mk_forall(free_vars_lr pvar3 @ vars,mk_eq(mk_comb(new_term,pvar3),mk_comb(l_thm,pvar3))))))
                        handle e => wrapd e

        val rewrite = if is_pair pvar3
                        then FUN_EQ_RULE (HO_MATCH_MP (TypeBase.induction_of (mk_prod(alpha,beta)))
                                        (UNDISCH_ONLY func) handle e => wrapd e)
                        else FUN_EQ_RULE (UNDISCH_ONLY func handle e => wrapd e)
in
        (repeat rator new_term :: fvs,(GSYM rewrite,fst (dest_imp_only (concl func)))) handle e => wrapd e
end;

in
fun SPLIT_PAIR_CONV is_double_term fvs pair_def term =
let     val _ = type_trace 3 "->SPLIT_PAIR_CONV\n"
        val _ = type_trace 4 ("Term: " ^ term_to_string term ^ "\n")
        val _ = type_trace 4 ("FVS:  " ^ xlist_to_string term_to_string fvs ^ "\n")
        val pair_def_spec = SPEC_ALL pair_def
        val pair_left = with_exn (rator o lhs o concl) pair_def_spec pair_exn
        val clauses = with_exn strip_conj term func_exn
        val funcs = with_exn (mk_set o map (repeat rator o lhs o snd o strip_forall)) clauses func_exn
        val split_terms = flatten (map (fn c => map (pair c)
                        (find_terms (fn x => is_comb x andalso exists (C free_in x) (free_vars (rand (lhs (snd (strip_forall c)))))
                                andalso can (match_term pair_left) (rator x)) c)) clauses);
        val double_terms = mk_set (map snd (filter (uncurry (is_double_term funcs)) split_terms)) handle e => wrap e

        val (fvs',(rewrites,new_funcs)) =
                foldl (fn (double,(fvs,(RWS,NFS))) =>
                        (I ## (C cons RWS ## C cons NFS))
                                (fix_double_term fvs funcs pair_def_spec double))
                (fvs,([],[])) double_terms
                handle e => wrap e
in
        (rewrites,fvs',check_standard_conv "SPLIT_PAIR_CONV" (term,
                foldr (fn (a,thm) =>
                                RIGHT_CONV_RULE (ADDR_AND_CONV a THENC PURE_REWRITE_CONV [GSYM CONJ_ASSOC]) thm)
                        (RFUN_CONV rewrites term) new_funcs)
        handle e => wrap e)
end
end;


local
val debug_exn = mkDebugExn "SPLIT_FUNCTION_CONV"
val func_exn = debug_exn "Term is not a conjunction of equalities";
fun wrap e = wrapException "SPLIT_FUNCTION_CONV" e

fun SFC (is_double_term,pair_def) [] (fvs,thm) =
        (let    val (rewrites,fvs',thm') = SPLIT_PAIR_CONV is_double_term fvs pair_def ((rhs o concl) thm)
        in      SFC (is_double_term,pair_def) [] (fvs',TRANS thm thm')
        end     handle UNCHANGED => (fvs,thm))
  | SFC (is_double_term,pair_def) hfuns (fvs,thm) =
        (let    val ((rewrites,fvs',thm'),hfuns') = pick_e
                        UNCHANGED (fn hfun => SPLIT_HFUN_CONV hfun fvs ((rhs o concl) thm)) hfuns
         in     SFC (is_double_term,pair_def)
                        (map (CONV_RULE (ONCE_DEPTH_CONV (FIRST_CONV (map REWR_CONV rewrites)))) hfuns')
                        (fvs',TRANS thm thm')
         end) handle UNCHANGED =>
        (let    val (rewrites,fvs',thm') = SPLIT_PAIR_CONV is_double_term fvs pair_def ((rhs o concl) thm)
         in     SFC (is_double_term,pair_def)
                        (map (CONV_RULE (ONCE_DEPTH_CONV (FIRST_CONV (map REWR_CONV rewrites)))) hfuns)
                        (fvs',TRANS thm thm')
         end) handle UNCHANGED =>
        raise (debug_exn        ("Unable to split function, neither conv applies to term:\n " ^
                                ((term_to_string o rhs o concl) thm) ^
                                "\n remaining function defs: " ^
                                (xlist_to_string thm_to_string hfuns)))
        | e => wrap e
in
fun SPLIT_FUNCTION_CONV pair_double ho_function_defs term =
let     val _ = type_trace 2 "->SPLIT_FUNCTION_CONV\n";
        val _ = assert "SPLIT_FUNCTION_CONV" [(
                        "The term:\n" ^ term_to_string term ^
                        "\nis not a valid source or target function",
                        fn x => is_source_function x orelse is_target_function x)] term
        val result = check_standard_conv "SPLIT_FUNCTION_CONV" (term,snd (SFC pair_double ho_function_defs
                ((with_exn (mk_set o map (repeat rator o lhs o snd o strip_forall) o strip_conj) term func_exn),
                REFL term)))
        val _ = assert "SPLIT_FUNCTION_CONV" [(
                        "Result of splitting:\n" ^ term_to_string ((rhs o concl) result) ^
                        "\nis not a fully expanded source or target function,\n" ^
                        "perhaps higher functions are missing from the function definitions given?",
                        fn x => (is_source_function x orelse is_target_function x) andalso is_expanded_function x)]
                ((rhs o concl) result)
in
        result
end
end;

fun is_double_term_target (scheme:translation_scheme) funcs clause term =
let     val l = guarenteed (snd o dest_abs o #left) scheme
        val r = guarenteed (snd o dest_abs o #right) scheme
        val (b1,x) = dest_comb term handle e => wrapException "is_double_term_target" e
        val (b2,rcall) = dest_comb b1 handle e => wrapException "is_double_term_target" e
        val (_,lcall) = dest_comb b2 handle e => wrapException "is_double_term_target" e
        fun is_lr_term x = is_comb x andalso
                (can (match_term l) x orelse can (match_term r) x)
in
        ((exists (C free_in rcall) funcs) orelse (exists (C free_in lcall) funcs)) andalso
        (is_single_constructor scheme clause orelse is_lr_term x) handle e => wrapException "is_double_term_target" e
end


fun is_double_term_source funcs (clause:term) term =
let     val (b1,x) = dest_comb term handle e => wrapException "is_double_term_source" e
        val (b2,rcall) = dest_comb b1 handle e => wrapException "is_double_term_source" e
        val (_,lcall) = dest_comb b2 handle e => wrapException "is_double_term_source" e
in
        not (pairLib.is_pair x) andalso (exists (C free_in rcall) funcs orelse exists (C free_in lcall) funcs)
        handle e => wrapException "is_double_term_source" e
end;

(*****************************************************************************)
(* prove_recind_thms_mutual: translation_scheme -> term -> thm * thm         *)
(*                                                                           *)
(*     prove_recind_thms_mutual proves the existence of mutually recursive   *)
(*     functions when given a recursion theorem of the form:                 *)
(*                                                                           *)
(*       |- ?fn. fn x =                                                      *)
(*               if P x then f (L x) (R x) (fn (L x)) (fn (R x)) else c      *)
(*                                                                           *)
(*     and a theorem of induction given a theorem of the form:               *)
(*                                                                           *)
(*       |- !P0. (!x. isP x /\ P0 (L x) /\ P0 (R x) ==> P0 x) /\             *)
(*                                      (!x. ~isP x ==> P0 x) ==> !x. P0 x   *)
(*                                                                           *)
(* build_call_graph : term * term -> term list ->                            *)
(*                                     (int * (int list * int list)) list    *)
(*     Given a list of function clauses returns a list of mapping functions  *)
(*     to those recursively called using L x and R x                         *)
(*                                                                           *)
(* create_mutual_theorem: (int * (int list * int list)) list -> thm -> thm   *)
(*     Given a call graph from build_call_graph and theorem of the type      *)
(*     specified earlier proves a mutually recursive function of the form:   *)
(*                                                                           *)
(*      |- ?fn0 fn1 fn2. fn0 x =                                             *)
(*                 (if P x then f0 (L x) (R x) (fi (L x)) (fj (R x)) else c) *)
(*              /\ (if P x then f1 ...                                       *)
(*                                                                           *)
(* instantiate_mutual_theorem: thm -> term list -> thm                       *)
(*     Given a mutually recursive theorem of the form output by the function *)
(*     create_mutual_theorem and a set of clauses instantiates the theorem   *)
(*     to prove the existence of the functions as defined by the clauses     *)
(*                                                                           *)
(* create_ind_theorem: (int * (int list * int list)) list ->                 *)
(*                                            translation_scheme -> thm      *)
(*     Creates a theorem of induction from a call graph and a theorem of the *)
(*     form given earlier.                                                   *)
(*                                                                           *)
(*****************************************************************************)

local
        fun e_rev_assoc L [] = []
          | e_rev_assoc L (x::xs) =
                ((rev_assoc (repeat rator x) L) :: e_rev_assoc L xs) handle e => e_rev_assoc L xs

        val type_exn = mkDebugExn "build_call_graph"
                        "The type of the L/R operators does not match the argument of type of one of the clauses"

        fun snd_rand x = if is_comb x then (if not (is_comb (rand x)) then x else snd_rand (rand x)) else x;
in
fun build_call_graph (left,right) clauses =
let     val _ = type_trace 3 "->build_call_graph\n"
        val (names,ho_funcs) = unzip (map (strip_comb o fst o dest_comb o lhs o snd o strip_forall)
                        (assert "build_call_graph" [
                                ("Second argument is not a list of function clauses",all (is_eq o snd o strip_forall)),
                                ("Second argument is not a list of function (not constant) definitions",
                                        all (can dest_comb o lhs o snd o strip_forall))] clauses))
        val bl = with_exn (snd o dest_abs) left (mkDebugExn "build_call_graph" "Left term is not of the form: \\x.P x")
        val br = with_exn (snd o dest_abs) right (mkDebugExn "build_call_graph" "Right term is not of the form: \\x.P x")
        val fdefs = map (dest_eq o snd o strip_forall) clauses;

        fun is_lr tm = can (match_term bl) tm orelse can (match_term br) tm

        fun find_names_of X (func,def) =
        let     val var = rand func
                val isX = curry op= (with_exn (beta_conv o mk_comb) (X,var) type_exn)
                fun t1 x = is_comb x andalso not (is_lr x) andalso is_lr (rand x) andalso isX (snd_rand x)
        in
                find_terms t1 def
        end

in
        map2    (fn (n,fdef) => fn hf => (n,(   e_rev_assoc (enumerate 0 names) (find_names_of left fdef),
                                                e_rev_assoc (enumerate 0 names) (find_names_of right fdef))))
                (enumerate 0 fdefs) ho_funcs
end
end;

local
fun wrap "" e = wrapException "create_mutual_theorem" e
  | wrap s  e = wrapException ("create_mutual_theorem (" ^ s ^ ")") e

fun make_out [] n tm = raise Empty
  | make_out ((x,ft)::fts) n tm =
        if x = n
                then (if can (sumSyntax.dest_sum o type_of) tm then sumSyntax.mk_outl tm else tm)
                else make_out fts n (sumSyntax.mk_outr tm)
fun make_outp a b c = make_out a b c handle e => wrap "make_out" e;

fun make_in [] n tm = raise Empty
  | make_in [(x,ft)] n tm = if x = n then tm else raise Empty
  | make_in ((x,ft)::fts) n tm =
        if x = n
                then sumSyntax.mk_inl (tm,sumSyntax.list_mk_sum(map snd fts))
                else sumSyntax.mk_inr (make_in fts n tm,ft)
fun make_inp a b c = make_in a b c handle e => wrap "make_in" e;

fun make_out_thm [] n thm = raise Empty
  | make_out_thm ((x,ft)::fts) n thm =
let     val l = (lhs o concl) thm
in
        if x = n
                then (if can (sumSyntax.dest_sum o type_of) l then
                        AP_TERM (rator (sumSyntax.mk_outl l)) thm else thm)
                else make_out_thm fts n
                        (AP_TERM (rator (sumSyntax.mk_outr l)) thm)
end
fun make_out_thmp a b c = make_out_thm a b c handle e => wrap "make_out_thm" e;

fun make_rec_term func_types rt n = make_outp func_types n (mk_comb(rt,term_of_int n) handle e => wrap "make_rec_term" e);

fun make_single_term func_types mk_var x_var (rlt,rrt) (n,(xs,ys)) =
        make_inp func_types n (list_mk_comb(mk_var("f"^(int_to_string n),
                        (type_of x_var) -->
                        (foldr (fn (a,t) => assoc a func_types --> t)
                                (foldr (fn (a,t) => assoc a func_types --> t) (assoc n func_types) ys) xs)),
                x_var::(map (make_rec_term func_types rlt) xs @ map (make_rec_term func_types rrt) ys))
                handle e => wrap "make_single_term" e);

fun make_f_term func_types mk_var var x_var rlr [] = raise Empty
  | make_f_term func_types mk_var var x_var rlr [x] = make_single_term func_types mk_var x_var rlr x
  | make_f_term func_types mk_var var x_var rlr ((n,(x,y))::xs) =
let     val r = make_single_term func_types mk_var x_var rlr (n,(x,y))
        val f = make_f_term func_types mk_var var x_var rlr xs
in
        mk_cond(mk_eq(var,term_of_int n),r,f) handle e => wrap "make_f_term" e
end

fun extract_f_term exn fterm =
        case (strip_comb fterm)
        of (f0,[x_var,rlt,rrt]) => (f0,x_var,rlt,rrt)
        |  _ => raise exn;

fun check_call_graph cg =
        all (fn (n,(xs,ys)) =>
                all (fn x => exists (fn a => fst a = x) cg) xs andalso
                all (fn y => exists (fn a => fst a = y) cg) ys) cg

fun make_c_term func_types mk_var x_var n =
        make_in func_types n
                (mk_comb(mk_var("c" ^ (int_to_string n),type_of x_var --> assoc n func_types),x_var)
                handle e => wrap "make_c_term" e)

fun FTERM_CONV func_types func var term =
let     val (outs,tm) = repeat (fn (l,x) =>
                                if      can (match_term sumSyntax.outl_tm) (rator x) orelse
                                        can (match_term sumSyntax.outr_tm) (rator x)
                                then (rator x::l,rand x) else raise Empty) ([],term)
in
        if mem (type_of term) (map snd func_types) andalso can (match_term func) tm then
                (UNBETA_CONV ((rand o rator) tm) THENC RATOR_CONV (RENAME_VARS_CONV [(fst (dest_var var))])) term
                handle UNCHANGED => raise UNCHANGED | e => wrap "FTERM_CONV" e
        else NO_CONV term
end

in
fun create_mutual_theorem call_graph thm =
let     val _ = type_trace 3 "->create_mutual_theorem\n"
        val _ = assert "create_mutual_theorem" [("Bad call graph!",check_call_graph)] call_graph
        val exn = mkDebugExn "create_mutual_theorem"
                        ("thm supplied for mutual recursion is not of the form: " ^
                         "\"?fn. !x. fn x = if P x then f0 (L x) (R x) (fn (L x)) (fn (R x)) else c0\"")
        val (fterm,body) = with_exn Psyntax.dest_exists (concl thm) exn;
        val res_t = type_of (with_exn (rhs o snd o dest_forall) body exn);
        val func_types = map (I ## gen_tyvar o K ()) call_graph
        val sum_t = sumSyntax.list_mk_sum (map snd func_types);

        val inst_it = inst [res_t |-> ``:num`` --> sum_t]
        val var = with_exn (rand o lhs o snd o dest_forall) body exn;

        val fvs = ref (free_varsl (fterm :: body :: hyp thm))
        fun mk_var (name,t) =
        let     val nv = variant (!fvs) (Term.mk_var (name,t)) in (fvs := nv :: (!fvs) ; nv) end

        val (_,f_term,c_term) = with_exn (dest_cond o rhs o snd o dest_forall) (inst_it body) exn;
        val (f0,x_var,rlt,rrt) = extract_f_term exn f_term;
        val c0 = rator c_term

        val (x_var',rlt',rrt') = (genvar (type_of x_var),genvar (type_of rlt),genvar (type_of rrt))

        val v = mk_var("v",``:num``);
        val f0term =    let     val ft = make_f_term func_types mk_var v x_var' (rlt',rrt') call_graph
                        in      list_mk_abs([x_var',rlt',rrt',v],ft) handle e => wrap "" e end
        val c0term =    mk_abs(x_var',mk_abs(v,foldr (fn (a,t) => mk_cond(mk_eq(v,term_of_int (fst a)),
                                                        make_c_term func_types mk_var x_var' (fst a),t))
                                (make_c_term func_types mk_var x_var' (fst (last call_graph)))
                                (butlast call_graph))) handle e => wrap "" e;

        val thm1 = RIGHT_CONV_RULE (REWRITE_CONV [COND_RAND,COND_RATOR]) (AP_THM (SPEC_ALL (ASSUME (inst_it body))) v)
                                handle e => wrap "" e
        val thm2 = BETA_RULE (INST [f0 |-> f0term, c0 |-> c0term] thm1) handle e => wrap "" e
        val thm3 = LIST_CONJ (map
                        (fn (n,_) =>    (GEN var o RIGHT_CONV_RULE PUSH_COND_CONV o
                                        make_out_thm func_types n o
                                        (REWR_CONV thm2 THENC ONCE_DEPTH_CONV REDUCE_CONV) o
                                        curry mk_comb (mk_comb(inst_it fterm,var)) o term_of_int) n) call_graph)
                        handle e => wrap "" e
        val thm4 = CONV_RULE (  DEPTH_CONV (REWR_CONV sumTheory.OUTL ORELSEC REWR_CONV sumTheory.OUTR) THENC
                                ONCE_DEPTH_CONV (FTERM_CONV func_types (list_mk_comb(inst_it fterm,[var,v])) var)) thm3
                        handle e => wrap "" e;

        fun make_var n = mk_var(fst (dest_var fterm) ^ (int_to_string n),type_of var --> assoc n func_types);
        fun make_term n = mk_abs(var,make_out func_types n (mk_comb(mk_comb(inst_it fterm,var),term_of_int n)));

        val thm5 = foldr (fn (a,thm) =>
                        let     val var = make_var (fst a)
                        in      EXISTS (Psyntax.mk_exists(var,subst [make_term (fst a) |-> var] (concl thm)),
                        make_term (fst a)) thm
                end) thm4 call_graph  handle e => wrap "" e
in
        CHOOSE (inst_it fterm,INST [f0 |-> f0term, c0 |-> c0term]
                (INST_TYPE [res_t |-> ``:num`` --> sum_t] thm)) thm5  handle e => wrap "" e
end
end;

local
fun debug_exn s = mkDebugExn "instantiate_mutual_theorem" s;

val exn1 = debug_exn "Function clauses are not all of the form \"!x x0 .. xn. f x = A x0 ... xn\""
val exn2 = debug_exn (  "Recursive theorem is not of the form: " ^
                        "\"?fn0 ... fnm. (!x. fn0 x = A (fn1 (L x)) ... (fnm (R x))) /\\ ... \"")

fun wrap "" e = wrapException "instantiate_mutual_theorem" e
  | wrap s  e = wrapException ("instantiate_mutual_theorem (" ^ s ^ ")") e

fun convit [] term = (DEPTH_CONV BETA_CONV term handle UNCHANGED => REFL term)
  | convit list term = (DEPTH_CONV BETA_CONV THENC UNBETA_LIST_CONV list) term;

fun instantiate_clause term_subst ((n,(func,body)),(thm,mthm)) =
let     val thm_clause = with_exn List.nth ((strip_conj (concl thm)),n)
                (debug_exn "Recursion theorem has a different number of clauses than the function clauses supplied")
        val (_,thm_rec,thm_const) = with_exn (dest_cond o rhs o snd o strip_forall) thm_clause exn2
        val (_,term_rec,term_const) = with_exn (dest_cond o subst term_subst) body exn1

        fun DCBC x = DEPTH_CONV BETA_CONV x handle UNCHANGED => REFL x

        val term_const_thm = convit (snd (strip_comb thm_const)) term_const;
        fun drop x = List.drop x handle e => []
        val term_rec_thm = convit
                (assert "instantiate_mutual_theorem" [
                        ("Recursive call missing from mutual recursion theorem",
                        (all (C free_in ((rhs o concl o DCBC) (subst term_subst body))) o
                        C (curry drop) 2))] ((snd o strip_comb) thm_rec)) term_rec;

        val _ = assert "instantiate_mutual_theorem"
                        [("x is free in the function body, should be either R x or L x, in function clause:\n" ^
                                (term_to_string (mk_eq (func,body))),
                         (not o free_in (rand func) o repeat rator o rhs o concl))] term_rec_thm

        val insttt =    INST_TY_TERM (match_term thm_const ((rhs o concl) term_const_thm)) o
                        INST_TY_TERM (match_term thm_rec ((rhs o concl) term_rec_thm))
                        handle e => wrap "instantiate_clause" e

in
        (CONV_RULE (NTH_CONJ_CONV n (
                        STRIP_QUANT_CONV (FORK_CONV (UNBETA_LIST_CONV (snd (strip_comb func)),
                                RAND_CONV (REWR_CONV (GSYM term_const_thm)) THENC
                                RATOR_CONV (RAND_CONV (REWR_CONV (GSYM term_rec_thm)))))))
                (insttt thm),
                insttt mthm) handle e => wrap "instantiate_clause" e
end;

in
fun instantiate_mutual_theorem mthm clauses =
let     val _ = type_trace 3 "->instantiate_mutual_theorem\n"
        val split_term = with_exn (map (dest_eq o snd o strip_forall)) clauses exn1
        val (fterms_thm,thm_body) = with_exn (strip_exists o concl) mthm exn2;
        val thm_clauses = map SPEC_ALL (CONJUNCTS (ASSUME thm_body))
        val arg_types = with_exn (map (type_of o rand o (fn (a,b,c) => a) o dest_cond o snd)) split_term exn1;
        val arg_type = hd (assert "instantiate_mutual_theorem"
                                [("Function term is mutually recursive on different types",
                                all (curry op= (hd arg_types)))] arg_types);
        val thm_arg_types = with_exn (map (type_of o rand o lhs o concl)) thm_clauses exn2
        val thm_arg_type = hd (assert "instantiate_mutual_theorem"
                                [("Recursion thm is mutually recursive on different types",
                                all (curry op= (hd thm_arg_types)))] thm_arg_types);

        val (type_subst,args) =
                unzip (map2 (fn tc => fn (func,body) =>
                        let     val args = with_exn (snd o strip_comb o rator) func exn1
                                val res_t = with_exn (type_of o lhs o concl) tc exn2
                        in
                                (res_t |-> list_mk_fun(map type_of args,type_of func),args)
                        end) thm_clauses
                (assert "instantiate_mutual_theorem"
                        [("Recursion theorem has a different number of clauses than the function clauses supplied",
                        curry op= (length thm_clauses) o length)] split_term));

        val thm_clauses' =
                map2 (fn a => RIGHT_CONV_RULE (REWRITE_CONV [COND_RATOR]) o
                                C (foldl (uncurry (C AP_THM))) a o INST_TYPE ((thm_arg_type |-> arg_type)::type_subst))
                args thm_clauses handle e => wrap "" e;

        val term_subst =
                map2 (fn tc => fn (func,body) =>
                        let     val args = snd (strip_comb (lhs (concl tc)))
                        in
                                (repeat rator func |-> list_mk_abs(tl args,(mk_abs(hd args,lhs (concl tc))))) end)
                thm_clauses' split_term handle e => wrap "" e;

        val (thm1,mthm') = foldl (instantiate_clause term_subst)
                        (LIST_CONJ (map2 (fn x => GEN_THM ((fst o strip_forall) x)) clauses thm_clauses'),
                                INST_TYPE ((thm_arg_type |-> arg_type)::type_subst) mthm)
                        (enumerate 0 split_term);


        val thm2 = foldr (fn ((func1,func2),thm) =>
                        EXISTS (mk_exists(func1,subst [func2 |-> func1] (concl thm)),func2) thm) thm1
                        (zip    (map (repeat rator o fst) split_term)
                                (map (repeat rator o lhs o snd o strip_forall) (strip_conj (concl thm1))))
                handle e => wrap "" e

in
        CHOOSE_L (fst (strip_exists (concl mthm')),mthm') thm2 handle e => wrap "" e
end
end;

local
        fun mkDebug e = mkDebugExn "create_ind_theorem" e
        fun wrap e = wrapException "create_ind_theorem" e
in
fun create_ind_theorem call_graph (scheme:translation_scheme) =
let     val _ = type_trace 3 "->create_ind_theorem\n"
        val ind_thm = #induction scheme
        val isP   = #predicate scheme
        val left  = #left scheme
        val right = #right scheme
        val target = #target scheme

        val x = mk_var("x",target)
        val isPcomb = beta_conv (mk_comb(isP,x)) handle e =>
                        raise (mkDebug ("Predicate for translation scheme " ^ type_to_string target ^
                                        " is not of the form: \\x.P x"))
        fun mkP y p = mk_comb(mk_var("P" ^ (int_to_string p),target --> ``:bool``),beta_conv (mk_comb(y,x)))
        fun mkP_var n = mk_comb(mk_var("P" ^ (int_to_string n),target --> ``:bool``),x)

        val ind_terms_pre =
                map (fn (n,(l,r)) =>
                        (n,isPcomb :: (foldr (fn (a,l) => mkP left a :: l) (map (mkP right) r) l)))
                call_graph handle e => wrap e
        val non_ind_terms =
                map (fn (n,_) => mk_forall(x,mk_imp(mk_neg(isPcomb),mkP_var n))) call_graph handle e => wrap e

        val full_ind_thm = BETA_RULE (SPEC (mk_abs(x,list_mk_conj(map (mkP_var o fst) call_graph))) ind_thm)
                                handle e => wrap e

        val (thm1,ind_terms) =
                (LIST_CONJ ## I) (unzip (map (fn (n,tms) =>
                                let     val tmf = mk_forall(x,mk_imp(list_mk_conj tms,mkP_var n))
                                in      (MATCH_MP (ASSUME tmf) (LIST_CONJ (map ASSUME tms)),tmf) end)
                        ind_terms_pre)) handle e => wrap e
        val fi_term = (fst o dest_imp_only o snd o strip_forall o fst o dest_conj o fst o
                        dest_imp_only o concl o SPEC_ALL) full_ind_thm handle e => wrap e

        val thm2 = CONJ (GEN x (DISCH fi_term (foldl (uncurry PROVE_HYP) thm1 (CONJUNCTS (ASSUME fi_term)))))
                        (GEN x (DISCH (mk_neg (isPcomb))
                                (LIST_CONJ (map (UNDISCH_ONLY o SPEC_ALL o ASSUME) non_ind_terms))))
                handle e => wrap e
in
        GENL (map (fn (n,_) => mk_var("P" ^ (int_to_string n),target --> ``:bool``)) call_graph)
                (PURE_REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
                (foldr (uncurry DISCH) (foldr (uncurry DISCH)
                        (CONV_RULE (TOP_DEPTH_CONV FORALL_AND_CONV) (MP full_ind_thm thm2)) non_ind_terms) ind_terms))
        handle e => wrap e
end
end;

fun prove_recind_thms_mutual (scheme:translation_scheme) term =
let     val _ = type_trace 3 "->prove_recind_thms_mutual\n"
        val rec_thm = #recursion scheme
        val ind_thm = #induction scheme
        val left = #left scheme
        val right = #right scheme
        val conjuncts = strip_conj term
        val call_graph = build_call_graph (left,right) conjuncts handle e => wrapException "prove_recind_thms_mutual" e
        val mthm = create_mutual_theorem call_graph rec_thm
        val _ = type_trace 2 ("Generated recursion theorem:\n" ^ thm_to_string mthm)
in
        (instantiate_mutual_theorem mthm conjuncts,
         create_ind_theorem call_graph scheme) handle e => wrapException "prove_recind_thms_mutual" e
end;

(*****************************************************************************)
(* LEQ_REWRITES : term -> term -> thm list -> thm                            *)
(*                                                                           *)
(* Rewrites the first term to match the second using the list of rewrites    *)
(* given.                                                                    *)
(*                                                                           *)
(*****************************************************************************)

local
fun insert x [] = [[x]]
  | insert x (y::ys) = (x::y::ys) :: (map (cons y) (insert x ys));
fun perm [] = [[]]
  | perm (x::xs) = flatten (map (insert x) (perm xs))
fun LEQSTEP 0 _ _ _ = raise Match
  | LEQSTEP n term1 term2 rewrites =
        if aconv term1 term2 then ALPHA term1 term2
        else (tryfind_e Match (fn r =>
                let val thm1 = REWR_CONV r term1
                in  TRANS thm1 (LEQSTEP (n - 1) ((rhs o concl) thm1) term2 rewrites) end) rewrites)
        handle Match =>
                if is_forall term1 andalso is_forall term2 then
                        tryfind_e Match (fn x =>
                                let     val thm1 = ORDER_FORALL_CONV x term1
                                        val thm2 = RIGHT_CONV_RULE (RENAME_VARS_CONV (map (fst o dest_var) (fst (strip_forall term2)))) thm1
                                        val r = LEQSTEP n (snd (strip_forall (rhs (concl thm2)))) (snd (strip_forall term2)) rewrites
                                in
                                        RIGHT_CONV_RULE (STRIP_BINDER_CONV (SOME universal) (REWR_CONV r)) thm2
                                end)
                                (filter (fn x => (map type_of x) = (map type_of (fst (strip_forall term2)))) (perm (fst (strip_forall term1))))
                else if is_comb term1 andalso is_comb term2 then
                        MK_COMB (LEQSTEP n (rator term1) (rator term2) rewrites,LEQSTEP n (rand term1) (rand term2) rewrites)
                else if is_abs term1 andalso is_abs term2 then
                let     val v1 = bvar term1
                        val v2 = bvar term2
                        val nvar = genvar (type_of v1)
                in
                        CONV_RULE (FORK_CONV (RENAME_VARS_CONV [fst (dest_var v1)],RENAME_VARS_CONV [fst (dest_var v2)]))
                                (MK_ABS (GEN nvar (LEQSTEP n (beta_conv (mk_comb(term1,nvar))) (beta_conv (mk_comb(term2,nvar))) rewrites)))
                end else raise Match
fun itdeep f n = f n handle Match => itdeep f (n + 1)
in
fun LEQ_REWRITES term1 term2 rwrs =
let     val thm1 = (PURE_REWRITE_CONV [FUN_EQ_THM] THENC DEPTH_CONV BETA_CONV) term1 handle e => REFL term1
        val thm2 = (PURE_REWRITE_CONV [FUN_EQ_THM] THENC DEPTH_CONV BETA_CONV) term2 handle e => REFL term2
        val rewrites = map (BETA_RULE o PURE_REWRITE_RULE [FUN_EQ_THM]) rwrs
in
        TRANS (TRANS thm1 (itdeep (fn n => LEQSTEP n (rhs (concl thm1)) (rhs (concl thm2)) rewrites) 0)) (GSYM thm2)
end
end;

(*****************************************************************************)
(* prove_induction_recursion_thms:                                           *)
(*              translation_scheme -> term -> thm * (term * term) list * thm *)
(*                                                                           *)
(*     Given a function definition term with some clauses that are simply:   *)
(*     fn x = A x, with no recursive calls, rewrites the other clauses with  *)
(*     the non-recursive ones, if necessary proves the existence of the      *)
(*     mutual recursion theorem. Once complete, it rewrites the clauses back,*)
(*     and adds a proof of their existence to the overall proof.             *)
(*                                                                           *)
(*     Also returns a theorem of mutual induction, using (!x. P0 x ==> P1 x) *)
(*     when no recursion takes place, and provides a mapping from            *)
(*     predicates to clauses.                                                *)
(*                                                                           *)
(*****************************************************************************)

local
fun debug_exn s = mkDebugExn "prove_induction_recursion_thms" s;
val fun_exn = debug_exn
        (       "Term supplied is not of the form: \n" ^
                "   |- ... (fni f0..fn x = \n" ^
                "               if isP x then fi x (decode (L x)) (decode (R x)) else ci)\n" ^
                "      ... (fnj f0..fn x = A (fn0 x) ... (fnm x))\n");

val ind_mutual_exn = debug_exn
        (       "Returned induction theorem is not of the form: \n" ^
                "   |- !P0 .. Pn.\n" ^
                "        ... (!x. isP x /\\ P0 (L x) ... /\\ Pn (R x) ==> Pi x) /\\ \n" ^
                "        ... (!x. ~isP x ==> Pn x) ==> \n" ^
                "        (!x. P0 x) ... !x. Pn x\n");
fun wrap e = wrapException "prove_induction_recursion_thms" e;

fun fix_nr_term tm =
let     val tm' = (snd o strip_forall) tm
        val vars = with_exn (snd o strip_comb o lhs) tm' fun_exn
in
        (STRIP_QUANT_CONV (RAND_CONV (UNBETA_LIST_CONV vars)) THENC
                PURE_REWRITE_CONV [GSYM FUN_EQ_THM]) (list_mk_forall (vars,tm'))
        handle e => wrapException "prove_induction_recursion_thms (fix_nr_term)" e
end

fun UCONV conv term = (conv term) handle UNCHANGED => REFL term

fun exists_nr_term thm =
let     val right = (rhs o concl) thm
        val var = lhs right
        val _ = if free_in var (rhs right) then
                raise (mkDebugExn "prove_induction_recursion_thms (exists_nr_term)"
                        ("Direct call term: " ^ term_to_string right ^
                         "\n directly refers to itself!")) else ()
in
        EXISTS (mk_exists(var,right),rhs right) (REFL (rhs right))
                handle e => wrapException "prove_induction_recursion_thms (exists_nr_term)" e
end

fun wrapari e = wrapException "prove_induction_recursion_thms (add_redundant_ind)" e
fun add_redundant_ind clauses (scheme:translation_scheme) NONE =
let     val target_type = #target scheme
        val var = mk_var("x",target_type)
        val mkf = curry mk_forall var
        val l1 = map (fn (n,c) => (mk_comb(mk_var("P" ^ (int_to_string n),target_type --> ``:bool``),var),c))
                (enumerate 0 clauses)
        val isP = beta_conv(mk_comb(#predicate scheme,var))
        val l2 = map (UNDISCH_ONLY o SPEC var o ASSUME o mkf o curry mk_imp isP o fst) l1
        val l3 = map (UNDISCH_ONLY o SPEC var o ASSUME o mkf o curry mk_imp (mk_neg isP) o fst) l1
        val mapping = map (rator ## rator o lhs o snd o strip_forall) l1
in
        (GENL (map fst mapping) (PURE_REWRITE_RULE [AND_IMP_INTRO]
                (DISCH_ALL (LIST_CONJ (map2 (fn x => (GEN var o DISJ_CASES (SPEC isP EXCLUDED_MIDDLE) x)) l2 l3)))),
        mapping)
        handle e => wrapari e
end
  | add_redundant_ind clauses scheme (SOME ind) =
let     val rec_thm = #recursion scheme
        val Ptype = with_exn (type_of o fst o dest_forall o concl) ind ind_mutual_exn
        val islist = map (is_single_constructor scheme) clauses handle e => wrapari e
        val termsL = map (fn (n,b) => (b,mk_var("P" ^ (int_to_string n),Ptype))) (enumerate 0 islist)
        val mapping = map2 (curry (snd ## rator o lhs o snd o strip_forall)) termsL clauses

        val ind1 = with_exn (SPECL (map snd (filter (not o fst) termsL))) ind ind_mutual_exn;
        val zipped = with_exn (zip termsL o map ((repeat rator ## I) o dest_eq o snd o strip_forall)) clauses fun_exn

        val x = mk_var("x",fst (dom_rng Ptype));

        (* Extra terms for inclusion from single constructed terms, ie: !x. P0 x ==> P1 x *)
        val extra_terms =
                foldr (fn (((single,pt),(_,right)),l) =>
                        if single then
                                mk_forall(x,mk_imp(list_mk_conj(map (fn p => mk_comb((snd o fst) p,x))
                                        (filter (C free_in right o fst o snd) zipped)),mk_comb(pt,x)))::l
                        else l) [] zipped handle e => wrapari e

        (* Extra theorems, ie: [!x. P0 x ==> P1 x,!x. P1 x ==> P2 x] |- !x. P0 x ==> P2x *)
        val extra_thms = TC_THMS (map ASSUME extra_terms)

        val all_clauses = (strip_conj o fst o dest_imp_only o concl) ind1
        val all_fns = map (fst o snd) zipped

        (* Given theorems of the form: [..] |- Pi (f x) ==> Pj (f x) and a clause, *)
        (* replaces the term Pj (f x) with Pi (f x) in the induction theorem.      *)
        fun fix_thms [] clause induction = raise Empty
          | fix_thms thms clause induction =
        let     val (ante,conc) = (dest_imp_only o snd o strip_forall) clause
                val terms = strip_conj ante
                val var = rand conc

                val thms' = map (fn t => tryfind_e Empty (C (PART_MATCH (fst o dest_imp_only)) t) thms handle Empty =>
                                DISCH_ALL (ASSUME t)) terms
                val final = foldr (fn (a,t) => MATCH_MP MONO_AND (CONJ a t)) (last thms') (butlast thms')
                val rthm = (GEN_ALL (IMP_TRANS final (SPEC var
                                (ASSUME (mk_forall(var,mk_imp(snd (dest_imp_only (concl final)),conc)))))))
        in
                if hyp rthm = [concl rthm] then raise Empty else PROVE_HYP_CHECK rthm induction
        end     handle Empty => raise Empty | e => wrapException
                        "prove_induction_recursion_thms (add_redundant_ind (fix_thms))" e

        (* Finds all terms in the clause such that there is a function call:          *)
        (* f (lr x) where f corresponds to Pi but the induction contains the          *)
        (* predicate Pj (lr x), and uses the theorem [..] |- Pi (lr x) ==> Pj (lr x)  *)
        (* to replace it.                                                             *)
        fun check_replace clause induction =
        let     val pred = guarenteed (rator o snd o dest_imp_only o snd o strip_forall) clause
                val ((single,_),(name,body)) = guarenteed (first (curry op= pred o snd o fst)) zipped
                val vars = find_terms (C mem all_fns o repeat rator) body
                val vars_fixed = filter (fn t => not (exists (fn t' => not (t = t') andalso free_in t t') vars)) vars
                val rv = mapfilter (fn vf => SPEC (rand vf) (
                        first (curry op= (snd (fst (first (curry op= (repeat rator vf) o fst o snd) zipped)))
                                o rator o snd o dest_imp_only o snd o strip_forall o concl) extra_thms)) vars_fixed
        in
                fix_thms rv clause induction
        end     handle Empty => raise Empty | e => wrapException
                        "prove_induction_recursion_thms (add_redundant_ind (check_replace))" e

        fun tf f [] = raise Empty
          | tf f (x::xs) = (f x) handle Empty => tf f xs

        fun replace_all induction =
                replace_all (tf (C check_replace induction) (hyp induction)) handle Empty => induction

        val induction = replace_all (CONV_HYP (PURE_REWRITE_CONV [AND_IMP_INTRO,GSYM CONJ_ASSOC])
                                (UNDISCH_ALL_ONLY (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] ind1)))

        fun assoc_list i_thms [] = i_thms
          | assoc_list i_thms list =
        let     val (imps,not_imps) = partition (is_imp_only o concl) list
                val (mped,not_mped) = mappartition (fn th => tryfind (MP th o guarenteed SPEC x) i_thms) imps
        in
                if null mped andalso not (null imps) andalso null not_imps then
                        raise (mkDebugExn "add_redundant_ind"
                                ("Extra terms cannot be resolved, no theorem in the set:\n  " ^
                                xlist_to_string thm_to_string not_mped ^
                                "\ncan be resolved by a conclusion in the set:\n  " ^
                                xlist_to_string thm_to_string i_thms))
                else assoc_list (map (GEN x) not_imps @ i_thms) (mped @ not_mped)
        end

        val all_thms = LIST_CONJ (assoc_list (CONJUNCTS induction)
                        (map (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] o SPEC x o ASSUME) extra_terms))

        val cneg = exists is_neg o strip_conj o fst o dest_imp_only  o snd o strip_forall
        val p = rator o snd o dest_imp_only o snd o strip_forall
        fun order h1 h2 =
                (not (cneg h1) andalso (cneg h2)) orelse
                (cneg h1 = cneg h2) andalso
                fst (valOf (assoc2 (p h1) (enumerate 0 (map snd termsL)))) <
                fst (valOf (assoc2 (p h2) (enumerate 0 (map snd termsL))))
in
        (GENL (map snd termsL) (PURE_REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
                (foldr (uncurry DISCH) all_thms (sort order (hyp all_thms)))),
        mapping)
end

in
fun prove_induction_recursion_thms (scheme:translation_scheme) term =
let     val _ = type_trace 2 "->prove_induction_recursion_thms\n"
        val rec_thm = #recursion scheme
        val ind_thm = #induction scheme

        val clauses = with_exn strip_conj term fun_exn
        val f_terms = with_exn (mk_set o map (repeat rator o lhs o snd o strip_forall)) clauses fun_exn
        val (non_rec_terms,rec_terms) = partition (is_single_constructor scheme) clauses handle e => wrap e

        val non_rec_terms' = map fix_nr_term non_rec_terms handle e => wrap e
        val nr_rewrites = with_exn (map (ASSUME o rhs o concl)) non_rec_terms' fun_exn
        val rec_terms' = map (UCONV (   REDEPTH_CONV (FIRST_CONV (map REWR_CONV nr_rewrites))
                                        THENC DEPTH_CONV BETA_CONV)) rec_terms;

        val nr_terms_exist = map exists_nr_term non_rec_terms'
        val (all_exists,induction1) = case (map (rhs o concl) rec_terms')
                of [] => (nr_terms_exist,NONE)
                |  L  => (C cons nr_terms_exist ## SOME) (prove_recind_thms_mutual scheme (list_mk_conj L))
                handle e => wrap e
        val (induction,mapping) = add_redundant_ind clauses scheme induction1 handle e => wrap e

        val all_clauses =
                map (fn f_term =>
                        first_e (mkDebugExn     "prove_induction_recursion_thms"
                                                "Function term missing from existence proof")
                                (curry op= f_term o repeat rator o lhs o snd o strip_forall o concl)
                                (flatten (map (CONJUNCTS o ASSUME o snd o strip_exists o concl) all_exists))) f_terms;

        fun NR_TERM_CONV term =
        let     val poss = filter (curry op= ((repeat rator o lhs o snd o strip_forall) term) o
                                repeat rator o lhs o rhs o concl) non_rec_terms'
        in
                (TRY_CONV (FIRST_CONV (map (REWR_CONV o GSYM) poss))) term
        end

        fun NR_TERM_CONV term =
        let     val poss = filter (curry op= ((repeat rator o lhs o snd o strip_forall) term) o
                                repeat rator o lhs o rhs o concl) non_rec_terms'
        in
                (TRY_CONV (FIRST_CONV (map (REWR_CONV o GSYM) poss))) term
        end

        val thm1 = LIST_CONJ (map2 (fn c => fn a => CONV_RULE (REWR_CONV (GSYM (LEQ_REWRITES c (concl a) nr_rewrites))) a) clauses all_clauses)

        val thm2 = foldr (fn (v,thm) => SIMPLE_EXISTS v thm) thm1 f_terms handle e => wrap e

        val lset = map (repeat rator o lhs o snd o strip_forall) o strip_conj;
        fun remove_witnesses thm list [] = thm
          | remove_witnesses thm list hs =
        let     val h = first_e
                        (mkDebugExn "prove_induction_recursion_thms"
                                ("Hypothesis set:\n  " ^ xlist_to_string term_to_string hs ^
                                 "\ncontains circular dependancies!"))
                        (fn h => all (fn h' => h = h' orelse not (exists (C free_in h') (lset h))) hs) hs
                val match = first_e
                        (mkDebugExn "prove_induction_recursion_thms"
                                ("Could not find a match for hypothesis:\n  " ^ term_to_string h ^
                                 "\nin the witness set: " ^ xlist_to_string thm_to_string list))
                         (curry op= h o snd o strip_exists o concl) list
        in
                remove_witnesses (CHOOSE_L ((fst o strip_exists o concl) match,match) thm) list
                        (set_diff hs [h])
        end
in
        (induction,mapping,remove_witnesses thm2 all_exists (hyp thm2))
        handle e => wrap e
end
end;

(*****************************************************************************)
(* The data structure holding the type translations                          *)
(*                                                                           *)
(* Note: The precise versions of functions will match the exact type given,  *)
(*       whilst the imprecise versions will return a precise version if it   *)
(*       exists, but the imprecise version if it does not.                   *)
(*                                                                           *)
(* exists_translation[_precise] : hol_type -> hol_type -> bool               *)
(* add_translation[_precise]    : hol_type -> hol_type -> unit               *)
(* get_translation[_precise]    : hol_type -> hol_type ->                    *)
(*                                                (string,function) dict ref *)
(* get_theorems[_precise]       : hol_type -> hol_type ->                    *)
(*                                                (string, thm) dict ref     *)
(*     Tests for the existence of a translations, creates a new translation  *)
(*     and returns dictionarys of translating functions or theorems          *)
(*                                                                           *)
(* exists_coding_function[_precise] : hol_type -> hol_type -> string -> bool *)
(* add_coding_function : hol_type -> hol_type -> string -> function -> unit  *)
(* get_coding_function[_precise]_def : hol_type -> hol_type -> string -> thm *)
(* get_coding_function[_precise]_const :                                     *)
(*                                    hol_type -> hol_type -> string -> term *)
(* get_coding_function[_precise]_induction :  hol_type -> hol_type ->        *)
(*                           string -> thm * (term * (term * hol_type)) list *)
(*     Tests for the existence of a coding function, adds a new coding       *)
(*     function and returns a function's definition, constant and principle  *)
(*     of induction.                                                         *)
(*                                                                           *)
(* exists_coding_theorem[_precise] : hol_type -> hol_type -> string -> bool  *)
(* add_coding_theorem[_precise] : hol_type -> hol_type ->                    *)
(*                                                     string -> thm -> unit *)
(* get_coding_theorem[_precise] : hol_type -> hol_type -> string -> thm      *)
(*     Tests for the existence of a coding theorem, adds a new coding        *)
(*     theorem and returns a coding theorem.                                 *)
(*                                                                           *)
(* exists_source_function[_precise] : hol_type -> string -> bool             *)
(* add_source_function : hol_type -> string -> function -> unit              *)
(* get_source_function[_precise]_def : hol_type -> string -> thm             *)
(* get_source_function[_precise]_const : hol_type -> string -> term          *)
(* get_source_function[_precise]_induction :  hol_type -> string ->          *)
(*                                     thm * (term * (term * hol_type)) list *)
(*     Tests for the existence of a source function, adds a new source       *)
(*     function and returns a function's definition, constant and principle  *)
(*     of induction.                                                         *)
(*                                                                           *)
(* exists_source_theorem[_precise] : hol_type -> string -> bool              *)
(* add_source_theorem[_precise] : hol_type -> string -> thm -> unit          *)
(* get_source_theorem[_precise] : hol_type -> string -> thm                  *)
(*     Tests for the existence of a source theorem, adds a new source        *)
(*     theorem and returns a source theorem.                                 *)
(*                                                                           *)
(* add_translation_scheme : hol_type -> thm -> thm -> unit                   *)
(*     Given a theorems of the form:                                         *)
(*         |- P a ==> measure (L a) < measure a /\ measure (R a) < measure a *)
(*         |- P nil = F                                                      *)
(*     adds a translation scheme creating theorems of recursion and          *)
(*     induction from the theorem.                                           *)
(*                                                                           *)
(*****************************************************************************)

val type_less = Type.compare;

val codingBase = ref (mkDict type_less) : translations ref;
val sourceBase = (ref (mkDict type_less),ref (mkDict type_less)) : (functions ref * theorems ref);

fun clearCoding () = (codingBase := mkDict type_less);
fun clearSource () = (fst sourceBase := mkDict type_less ; snd sourceBase := mkDict type_less);

local
fun translation_not_found t1 t2 =
        mkStandardExn "get_translation"
        ("The translation " ^ type_to_string (base_type t1) ^ " --> " ^
          type_to_string t2 ^ " was not found in the database");
fun translation_scheme_not_found t =
        mkStandardExn "get_translation_scheme" ("There is no translation scheme for type " ^ type_to_string t);
fun get_translations target =
        Binarymap.find (!codingBase,target) handle NotFound => (raise (translation_scheme_not_found target))
fun vbase_type t = base_type t handle _ => t
in
fun get_translation_scheme target = snd (get_translations target)
fun exists_translation_precise target t =
        case (Binarymap.peek(!((fst o fst) (get_translations target)),cannon_type t))
        of NONE => false
        |  SOME x => true
fun exists_translation target t = exists_translation_precise target (vbase_type t)
fun add_translation target t =
        if exists_translation target t then
                raise (mkStandardExn "add_translation"
                        ("The translation " ^ type_to_string target ^ " --> " ^ type_to_string t ^
                         " already exists."))
        else    let     val ((fbase,tbase),_) = get_translations target
                in      (fbase := Binarymap.insert(!fbase,vbase_type t,
                                        ref (mkDict String.compare : (string,function) dict)) ;
                         tbase := Binarymap.insert(!tbase,vbase_type t,
                                        ref (mkDict String.compare : (string,thm) dict)))
                end
fun add_translation_precise target t =
        if exists_translation_precise target t then
                raise (mkStandardExn "add_translation"
                        ("The translation " ^ type_to_string target ^ " --> " ^ type_to_string t ^
                         " already exists."))
        else    let     val ((fbase,tbase),_) = get_translations target
                in      (fbase := Binarymap.insert(!fbase,cannon_type t,
                                        ref (mkDict String.compare : (string,function) dict)) ;
                         tbase := Binarymap.insert(!tbase,cannon_type t,
                                        ref (mkDict String.compare : (string,thm) dict)))
                end
fun get_translation_precise target t =
        case (Binarymap.peek(!((fst o fst) (get_translations target)), cannon_type t))
        of NONE => raise (translation_not_found target t)
        |  SOME x => x
fun get_translation target t = get_translation_precise target (vbase_type t)
fun get_theorems_precise target t =
        case (Binarymap.peek(!((snd o fst) (get_translations target)),cannon_type t))
        of NONE => raise (translation_not_found target t)
        |  SOME x => x
fun get_theorems target t = get_theorems_precise target (vbase_type t)
fun get_translation_types target =
    map fst (Binarymap.listItems (! (fst (fst (get_translations target)))));
end;

(*****************************************************************************)
(* This function performs a breadth-first search, finding the most precise   *)
(* type with an entry in the database.                                       *)
(*****************************************************************************)

fun all_lists [] = [[]]
  | all_lists (x::xs) =
    foldr (fn (a,t) => map (cons a) (all_lists xs) @ t) [] x;

fun explode_type t =
    if is_vartype t
       then [gen_tyvar()]
       else gen_tyvar()::
                map (curry mk_type (fst (dest_type t)))
                    (all_lists (map explode_type (snd (dest_type t))));

fun ordered_list t =
    map cannon_type (rev (explode_type t));

fun most_precise_type exists_function t =
    first_e (mkStandardExn "most_precise_type"
               "No sub-type exists such that the function given holds")
            exists_function
            (ordered_list t);

(*-- functions --*)

fun exists_coding_function_precise target t name =
        if (exists_translation_precise target t)
        then
        (case (Binarymap.peek(!(get_translation_precise target t),name))
        of NONE => false
        |  SOME x => true)
        else false;

fun exists_coding_function target t name =
    can (most_precise_type
            (C (exists_coding_function_precise target) name)) t

fun inst_function {const,definition,induction} t =
    {const = safe_inst (match_type (cannon_type t) t) const,
     definition = SAFE_INST_TYPE (match_type (cannon_type t) t) definition,
     induction =
         Option.map
            (SAFE_INST_TYPE (match_type (cannon_type t) t) ##
             map (safe_inst (match_type (cannon_type t) t) ##
                   (safe_inst (match_type (cannon_type t) t) ##
                    safe_type_subst (match_type (cannon_type t) t)))) induction}

fun get_coding_function_precise target t name =
    case (Binarymap.peek(!(get_translation_precise target t),name))
    of NONE => raise (mkStandardExn "get_coding_function_precise"
                ("The function " ^ name ^
                 " was not found for the translation " ^
                 type_to_string target ^ " --> " ^ type_to_string t))
    |  SOME function => inst_function function t;

fun get_coding_function target t name =
    inst_function (get_coding_function_precise target
        (most_precise_type
            (C (exists_coding_function_precise target) name) t) name) t
    handle _ => raise (mkStandardExn "get_coding_function"
                ("The function " ^ name ^
                 " was not found for the translation " ^
                 type_to_string target ^ " --> " ^ type_to_string t))

fun get_coding_function_def target t name =
        #definition (get_coding_function target t name)
fun get_coding_function_const target t name =
        #const (get_coding_function target t name)
fun get_coding_function_induction target t name =
        case (#induction (get_coding_function target t name))
        of NONE => raise (mkStandardExn "get_coding_function_induction"
                ("The function " ^ name ^ "(" ^ type_to_string t ^
                 " --> " ^ type_to_string target ^
                 ") does not have an induction principle defined for it."))
        |  SOME x => x
fun get_coding_function_precise_def target t name =
        #definition (get_coding_function_precise target t name)
fun get_coding_function_precise_const target t name =
        #const (get_coding_function_precise target t name)
fun get_coding_function_precise_induction target t name =
        case (#induction (get_coding_function_precise target t name))
        of NONE => raise (mkStandardExn "get_coding_function_precise_induction"
                ("The function " ^ name ^ "(" ^ type_to_string t ^
                 " --> " ^ type_to_string target ^
                 ") does not have an induction principle defined for it."))
        |  SOME x => x

fun add_coding_function_precise target t name {const,definition,induction} =
let     val _ = type_trace 1 ("Adding coding function, " ^ name ^ ", for type: "
                                ^ (type_to_string (cannon_type t)) ^ "\n")
        val base = get_translation_precise target t handle e => wrapException "add_coding_function_precise" e
        val sub = match_type t (cannon_type t)
in
        base := Binarymap.insert(!base,name,{const = inst sub const,definition = SAFE_INST_TYPE sub definition,
                induction =  Option.map (SAFE_INST_TYPE sub ##
                        map (safe_inst sub ## (safe_inst sub ##
                                safe_type_subst sub))) induction})
end;

fun add_coding_function target t name function = add_coding_function_precise target (base_type t handle _ => t) name function


(*-- theorems --*)

fun exists_coding_theorem_precise target t name =
        if exists_translation_precise target t then
                case (Binarymap.peek(!(get_theorems_precise target t),name))
                of NONE => false
                |  SOME x => true
        else false;
fun exists_coding_theorem target t name =
        exists_coding_theorem_precise target t name orelse
        exists_coding_theorem_precise target (base_type t handle _ => t) name

fun add_coding_theorem_precise target t name thm =
let     val _ = type_trace 1 ("Adding coding theorem, " ^ name ^ ", for type: " ^
                        (type_to_string (cannon_type t)) ^ "\n")
        val _ = if exists_translation_precise target t then () else add_translation_precise target t
        val base = get_theorems_precise target t handle e => wrapException "add_coding_theorem_precise" e
in
        base := Binarymap.insert(!base,name,SAFE_INST_TYPE (match_type t (cannon_type t)) thm)
end;

fun add_coding_theorem target t name thm = add_coding_theorem_precise target (base_type t handle _ => t) name thm

fun get_coding_theorem_precise target t name =
        case (Binarymap.peek(!(get_theorems_precise target t),name))
        of NONE => raise (mkStandardExn "get_coding_theorem_precise"
                ("The theorem " ^ name ^ " does not exists for the translation " ^ type_to_string target ^ " --> " ^
                type_to_string t))
        |  SOME x => SAFE_INST_TYPE (match_type (cannon_type t) t) x

fun get_coding_theorem target t name =
    get_coding_theorem_precise target
        (most_precise_type (C (exists_coding_theorem_precise target) name) t)
        name

(*-- source functions and theorems --*)

fun exists_source_function_precise t name =
        case (Binarymap.peek(!(fst sourceBase),cannon_type t))
        of NONE => false | SOME x =>
                case (Binarymap.peek (!x,name))
                of NONE => false | SOME x => true;
fun exists_source_function t name =
    can (most_precise_type (C exists_source_function_precise name)) t

fun get_source_function_precise t name =
        case (Binarymap.peek(!(fst sourceBase),cannon_type t))
        of NONE => raise (mkStandardExn "get_source_function"
                        ("No source functions found for type " ^ type_to_string t))
        |  SOME x =>
                case (Binarymap.peek(!x,name))
                of NONE => raise (mkStandardExn "get_source_function_precise"
                                ("The function " ^ name ^ " has not been defined for the type " ^ type_to_string t))
                |  SOME function => inst_function function t

(*              {const = safe_inst (match_type (cannon_type t) t) const,
                 definition = SAFE_INST_TYPE (match_type (cannon_type t) t) definition,
                 induction = Option.map (SAFE_INST_TYPE (match_type (cannon_type t) t) ##
                        map (safe_inst (match_type (cannon_type t) t) ## (safe_inst (match_type (cannon_type t) t) ##
                                safe_type_subst (match_type (cannon_type t) t)))) induction}*)
fun get_source_function t name =
    inst_function (get_source_function_precise
        (most_precise_type (C exists_source_function_precise name) t) name) t
    handle e => raise (mkStandardExn "get_source_function"
    ("The function " ^ name ^ " has not been defined for any sub-type of " ^
      type_to_string t))

fun get_source_function_def t name =
        #definition (get_source_function t name)
fun get_source_function_const t name =
        #const (get_source_function t name)
fun get_source_function_induction t name =
        case (#induction (get_source_function t name))
        of NONE => raise (mkStandardExn "get_source_function_induction"
                ("The function " ^ name ^ "(" ^ type_to_string t ^
                 ") does not have an induction principle defined for it."))
        |  SOME x => x
fun get_source_function_precise_def t name =
        #definition (get_source_function_precise t name)
fun get_source_function_precise_const t name =
        #const (get_source_function_precise t name)
fun get_source_function_precise_induction t name =
        case (#induction (get_source_function_precise t name))
        of NONE => raise (mkStandardExn "get_source_function_precise_induction"
                ("The function " ^ name ^ "(" ^ type_to_string t ^
                 ") does not have an induction principle defined for it."))
        |  SOME x => x

fun add_source_function_precise t name {const,definition,induction} =
let     val sub = match_type t (cannon_type t)
        val _  = type_trace 1 ("Adding source function, " ^ name ^ ", for type: " ^
                                        (type_to_string (cannon_type t)) ^ "\n")
        val _ = case (Binarymap.peek(!(fst sourceBase),cannon_type t))
                of NONE => ((fst sourceBase) := Binarymap.insert(!(fst sourceBase),cannon_type t,ref (mkDict String.compare)))
                |  SOME x => ()
        val base = Binarymap.find(!(fst sourceBase),cannon_type t)
        val sub = match_type t (cannon_type t)
in
        base := Binarymap.insert(!base,name,{const = inst sub const,definition = SAFE_INST_TYPE sub definition,
                induction =  Option.map (SAFE_INST_TYPE sub ##
                        map (safe_inst sub ## (safe_inst sub ##
                                safe_type_subst sub))) induction})
end
fun add_source_function t name x = add_source_function_precise (base_type t handle _ => t) name x

fun exists_source_theorem_precise t name =
        case (Binarymap.peek(!(snd sourceBase),cannon_type t))
        of NONE => false
        |  SOME x => (  case (Binarymap.peek(!x,name))
                        of NONE => false
                        |  SOME x => true);

fun exists_source_theorem t name =
        exists_source_theorem_precise t name orelse
        exists_source_theorem_precise (base_type t handle _ => t) name

fun get_source_theorem_precise t name =
let     val err = mkStandardExn "get_source_theorem_precise"
                        ("Theorem: " ^ name ^ " does not exist for type " ^ type_to_string t)
in
        case (Binarymap.peek(!(snd sourceBase),cannon_type t))
        of NONE => raise err
        |  SOME x => (  case (Binarymap.peek(!x,name))
                        of NONE => raise err
                        |  SOME x => SAFE_INST_TYPE (match_type (cannon_type t) t) x)
end

fun get_source_theorem t name =
    get_source_theorem_precise
        (most_precise_type (C exists_source_theorem_precise name) t) name

fun add_source_theorem_precise t name thm =
        (type_trace 1 ("Adding source theorem, " ^ name ^ ", for type: " ^
                                (type_to_string (cannon_type t)) ^ "\n") ;
        (case (Binarymap.peek(!(snd sourceBase),cannon_type t))
        of NONE => ((snd sourceBase) := Binarymap.insert(!(snd sourceBase),cannon_type t,ref (mkDict String.compare)))
        |  SOME x => ())
        ;
        let     val base = Binarymap.find(!(snd sourceBase),cannon_type t)
        in
                base := Binarymap.insert(!base,name,SAFE_INST_TYPE (match_type t (cannon_type t)) thm)
        end)

fun add_source_theorem t name thm = add_source_theorem_precise (base_type t handle _ => t) name thm;

fun remove_coding_theorem_precise target t name =
let     val base = get_theorems_precise target t handle e => wrapException "remove_coding_theorem_precise" e
in
        base := fst (Binarymap.remove(!base,name))
end;

fun remove_source_theorem_precise t name =
        case (Binarymap.peek(!(snd sourceBase),t))
        of NONE => ()
        |  SOME x =>
        let     val base = Binarymap.find(!(snd sourceBase),t)
        in
                base := fst (Binarymap.remove(!base,name))
        end;


(*-- the translation base itself --*)

local
val imp1 = CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) (SPEC_ALL IMP_CONG)
val eqt = fst (dest_imp_only (concl imp1))
val IMP_THM = MP (INST [(uncurry (C (curry op|->)) o dest_eq) eqt] imp1) (REFL (lhs eqt))
val size_format =
        "size_thm should be of the form: \n" ^
        "|- P x ==> size (left x) < size x /\\ size (right x) < size x"
fun size_err s = mkStandardExn "add_translation_scheme" (size_format ^ "\nhowever " ^ s)
fun wrap1 e = wrapException "add_translation_scheme (make_recursion)" e
fun wrap2 e = wrapException "add_translation_scheme (make_induction)" e
fun split_size_thm target size_thm =
let     val specced = SPEC_ALL size_thm
        val (p_term,rest) = with_exn (dest_imp_only o concl) specced (size_err "theorem is not an implication")
        val ((l,lmeasure),(r,rmeasure)) = with_exn ((numLib.dest_less ## numLib.dest_less) o dest_conj) rest
                (size_err "result of theorem is not a conjunction of a < b terms")
        val ((ml,left),(mr,right)) = with_exn (dest_comb ## dest_comb) (l,r)
                (size_err "left of < terms are not measures '(size x)'")
        val ((mlr,_),(mrr,_)) = with_exn (dest_comb ## dest_comb) (lmeasure,rmeasure)
                (size_err "right of < terms are not measures '(size x)'")
        val all_vars = free_vars p_term
        val xvar = hd all_vars
        val _ = if all (curry op= ml) [mlr,mrr,mr] then () else raise (size_err
                ("measures '" ^ term_to_string ml ^ "' and '" ^
                        term_to_string (first (not o curry op= ml) [mlr,mrr,mr]) ^ "' are not equal"))
        val _ = if length all_vars = 1 then () else raise (size_err
                ("the antecedant " ^ term_to_string p_term ^ " does not depend on only one variable"))
        val _ = if type_of xvar = target then () else raise (size_err
                        ("variable in antecedent is of type " ^ type_to_string (type_of xvar) ^
                         " and not " ^ type_to_string target))
in
        (specced,ml,left,right,p_term,xvar)
end
fun make_recursion (specced,ml,left,right,p_term,xvar) target size_thm =
let     val f = mk_var("f",target --> beta) handle e => wrap1 e
        val f0 = mk_var("f0",target --> beta --> beta --> beta)  handle e => wrap1 e
        val template = list_mk_abs([f,xvar],mk_cond(p_term,
                        list_mk_comb(f0,[xvar,mk_comb(f,left),mk_comb(f,right)]),
                                mk_comb(mk_var("c0",target --> beta),xvar))) handle e => wrap1 e
        val measure = mk_comb(mk_const("measure",(target --> num) --> target --> target --> bool),ml)
                handle e => wrap1 e
        val decode_var = mk_var("decode",target --> beta) handle e => wrap1 e
        val rec_term = list_mk_comb(mk_const("WFREC",
                                type_of measure --> type_of template --> target --> beta),
                                [measure,template]) handle e => wrap1 e
        val def = mk_eq(decode_var,rec_term) handle e => wrap1 e
        val th0 = GEN xvar (SPEC xvar (MP (MATCH_MP relationTheory.WFREC_COROLLARY (ASSUME def))
                        (PART_MATCH rand prim_recTheory.WF_measure measure))) handle e => wrap1 e
        val th1 = CONV_RULE (REDEPTH_CONV BETA_CONV)
                        (PURE_REWRITE_RULE [relationTheory.RESTRICT_DEF, prim_recTheory.measure_thm] th0)
                handle e => wrap1 e
        val term = snd (strip_forall (concl th1)) handle e => wrap1 e
        val th2 = (REWR_CONV COND_RAND THENC REWR_CONV COND_EXPAND THENC
                        (NTH_CONJ_CONV 0 (HO_REWR_CONV (GSYM IMP_DISJ_THM)))) term handle e => wrap1 e
        val half = MATCH_MP IMP_THM (DISCH p_term ((PURE_REWRITE_CONV [ASSUME p_term,UNDISCH_ONLY specced] THENC
                                DEPTH_CONV (REWR_CONV (fst (CONJ_PAIR (SPEC_ALL COND_CLAUSES)))))
                        (snd (dest_imp_only (fst (dest_conj (rhs (concl th2)))))))) handle e => wrap1 e
        val th_l = CONV_RULE (STRIP_QUANT_CONV (REWR_CONV
                        (RIGHT_CONV_RULE (NTH_CONJ_CONV 0 (REWR_CONV half THENC REWR_CONV IMP_DISJ_THM) THENC
                                REWR_CONV (GSYM COND_EXPAND) THENC (REWR_CONV (GSYM COND_RAND))) th2))) th1
        val th_r = EXISTS (Psyntax.mk_exists(decode_var,def),rec_term) (REFL rec_term) handle e => wrap1 e
in
        SPEC_ALL (DISCH_ALL (GEN_ALL (CHOOSE (decode_var,th_r) (SIMPLE_EXISTS decode_var th_l)))) handle e => wrap1 e
end
fun make_induction (specced,ml,left,right,p_term,xvar) target size_thm =
let     val pred = mk_var("P",target --> bool) handle e => wrap2 e
        val ante_true = mk_forall(xvar,mk_imp(
                list_mk_conj [p_term,mk_comb(pred,left),mk_comb(pred,right)],mk_comb(pred,xvar))) handle e => wrap2 e
        val ante_false = mk_forall(xvar,mk_imp(mk_neg p_term,mk_comb(pred,xvar))) handle e => wrap2 e
        val measure = mk_comb(mk_const("measure",(target --> num) --> target --> target --> bool),ml)
                handle e => wrap1 e
        val th1 = SPEC_ALL (PURE_REWRITE_RULE [prim_recTheory.measure_thm]
                        (MP     (ISPEC measure relationTheory.WF_INDUCTION_THM)
                                (ISPEC ml prim_recTheory.WF_measure)))
                        handle e => wrap2 e
        val (th_true,th_false) = (CONJ_PAIR (ASSUME (mk_conj(ante_true,ante_false)))) handle e => wrap2 e
        val (wvar,pt1) = dest_forall(fst (dest_imp_only (concl th1))) handle e => wrap2 e
        val proof_term = subst [wvar |-> xvar] (fst (dest_imp_only pt1)) handle e => wrap2 e
        val th_false2 = DISCH proof_term (UNDISCH (SPEC_ALL th_false)) handle e => wrap2 e
        val th_true2 = DISCH proof_term (MP (REWRITE_RULE [AND_IMP_INTRO]
                (UNDISCH (REWRITE_RULE [GSYM AND_IMP_INTRO] (SPEC_ALL th_true))))
                        (CONJ
                                (MP (SPEC left (ASSUME proof_term)) (fst (CONJ_PAIR (UNDISCH specced))))
                                (MP (SPEC right (ASSUME proof_term)) (snd (CONJ_PAIR (UNDISCH specced))))))
                handle e => wrap2 e
in
        GEN_ALL (DISCH (mk_conj(ante_true,ante_false))
                (MP th1 (GEN xvar (DISJ_CASES (SPEC p_term EXCLUDED_MIDDLE) th_true2 th_false2)))) handle e => wrap2 e
end
in
fun add_translation_scheme target size_thm dead_thm =
let     val (specced,ml,left,right,p_term,xvar) = split_size_thm target size_thm
        val dead_term = hd (map #residue (fst (match_term p_term (lhs (concl dead_thm)))))
in
        codingBase :=
        Binarymap.insert (!codingBase,target,
                ((ref (mkDict type_less) : functions ref,
                  ref (mkDict type_less) : theorems ref),
                {target = target,
                 induction = make_induction (specced,ml,left,right,p_term,xvar) target size_thm,
                 recursion = make_recursion (specced,ml,left,right,p_term,xvar) target size_thm,
                 bottom_thm = dead_thm,
                 bottom = dead_term,
                 left = mk_abs(xvar,left),
                 right = mk_abs(xvar,right),
                 predicate = mk_abs(xvar,p_term)}))
end
end

(*****************************************************************************)
(* Loop checking for function generators                                     *)
(*                                                                           *)
(* Simply provides a function 'check_loop' that when giving an identifying   *)
(* string for a function can detect whether the function is looping.         *)
(*                                                                           *)
(* Looping is defined to occur if:                                           *)
(*     a) Exactly the same type is visited twice                             *)
(*     b) Types which are equal up to renaming of type variables visited     *)
(*        more than twice.                                                   *)
(*                                                                           *)
(*****************************************************************************)

local
val stores = ref (mkDict String.compare);
fun get s =
        case (Binarymap.peek(!stores,s))
        of NONE => (stores := Binarymap.insert(!stores,s,ref []) ; Binarymap.find(!stores,s))
        |  SOME x => x
fun cons s t = let val x = get s in x := t :: (!x) end
fun head s = let val x = get s in case (!x) of [] => NONE | y::ys => (x := ys ; SOME y) end
fun tail s = let val x = get s in case (!x) of [] => NONE | y::ys => (x := ys ; SOME ys) end
fun mem s t = let val x = get s in Lib.mem t (!x) end
in
val cstores = stores
fun check_loop s t f fail =
        if mem s (cannon_type t)
        then fail (!(get s))
        else let val result = (cons s (cannon_type t) ; f t handle e => (tail s ; raise e)) in (tail s ; result) end
end;

(*****************************************************************************)
(* Function generators:                                                      *)
(*                                                                           *)
(* Allow the recursive definition of functions for a whole type              *)
(*                                                                           *)
(*****************************************************************************)

val coding_function_generators =
        ref (Binarymap.mkDict type_less) :
  (hol_type,
   (string,
    ((hol_type -> bool) *
     (hol_type -> function)) list ref) dict ref) dict ref

fun add_coding_function_generator target (name:string) (predicate:hol_type -> bool)  (generator:hol_type -> function) =
let     val _ = case (Binarymap.peek (!coding_function_generators,target))
                of NONE => coding_function_generators := Binarymap.insert(!coding_function_generators,target,ref (mkDict String.compare))
                |  SOME _ => ()
        val generators = Binarymap.find (!coding_function_generators,target)
        val _ = case(Binarymap.peek(!generators,name))
                of NONE => generators := Binarymap.insert(!generators,name,ref [])
                |  SOME _ => ()
        val list = Binarymap.find(!generators,name)
in
        list := (predicate,generator) :: (!list)
end;

val source_function_generators =
        ref (Binarymap.mkDict String.compare) :
  (string,
   ((hol_type -> bool) *
    (hol_type -> function)) list ref) dict ref

fun add_source_function_generator name (predicate:hol_type -> bool) (generator : hol_type -> function) =
let     val _ = case(Binarymap.peek(!source_function_generators,name))
                of NONE => source_function_generators := Binarymap.insert(!source_function_generators,name,ref [])
                |  SOME _ => ()
        val list = Binarymap.find(!source_function_generators,name)
in
        list := (predicate,generator) :: (!list)
end;

local
fun err name target t = mkStandardExn "get_coding_function_generator"
        ("No coding function generator exists for functions named " ^ name ^
         " in the translation: " ^ type_to_string target ^
         " --> " ^ type_to_string t)
fun get_coding_function_generator target name t =
        case (Binarymap.peek(!coding_function_generators,target))
        of NONE => raise (err name target t)
        |  SOME x => case (Binarymap.peek(!x,name))
                of NONE => raise (err name target t)
                |  SOME x => (snd (first_e (err name target t) (fn (x,y) => x t) (!x)))
fun gcf target name t =
let     val function = if exists_coding_function_precise target t name
                then get_coding_function_precise target t name
                else (type_trace 1 (
                        "Generating function " ^ name ^ " for translation " ^
                        (type_to_string target) ^ " --> " ^ type_to_string t ^ "\n") ;
                        (get_coding_function_generator target name t) t)
in
        if exists_coding_function_precise target t name
        then ()
        else add_coding_function_precise target t name function
end
in
fun generate_coding_function target name t =
        check_loop ("gcf" ^ name ^ type_to_string (cannon_type target)) t (gcf target name)
                (fn list => raise (mkDebugExn "generate_coding_function"
                        ("Experienced a loop whilst generating the coding function " ^ name ^
                         " for type " ^ type_to_string target ^
                         "\nTrace: " ^ xlist_to_string type_to_string list)))
end;

local
fun err name t = mkStandardExn "get_source_function_generator"
        ("No source function generator exists for functions named " ^ name ^
         " and the type " ^ type_to_string t)
fun get_source_function_generator name t =
        case (Binarymap.peek(!source_function_generators,name))
        of NONE => raise (err name t)
        |  SOME x => (snd (first_e (err name t) (fn (x,y) => x t) (!x)))
fun gsf name t =
let     val function = if exists_source_function_precise t name
                then get_source_function_precise t name
                else (type_trace 1 (
                        "Generating function " ^ name ^ " for type " ^ type_to_string t ^ "\n") ;
                        (get_source_function_generator name t) t)
in
        if exists_source_function_precise t name
        then ()
        else add_source_function_precise t name function
end
in
fun generate_source_function name t =
        check_loop ("gsf"^name) t (gsf name)
                (fn list => raise (mkDebugExn "generate_source_function"
                        ("Experienced a loop whilst generating the source function " ^ name ^
                         "\nTrace: " ^ xlist_to_string type_to_string list)))
end;

(*****************************************************************************)
(* Theorem generators:                                                       *)
(*                                                                           *)
(* Allow the proof of theorems recursively                                   *)
(*                                                                           *)
(*****************************************************************************)

val coding_theorem_generators =
        ref (Binarymap.mkDict type_less) :
  (hol_type,
   (string,((hol_type -> term) option ref *
    ((hol_type -> bool) *
     (hol_type -> thm)) list ref)) dict ref) dict ref

local
fun setup target name =
let     val _ = case (Binarymap.peek (!coding_theorem_generators,target))
                of NONE => coding_theorem_generators := Binarymap.insert(!coding_theorem_generators,target,ref (mkDict String.compare))
                |  SOME _ => ()
        val generators = Binarymap.find (!coding_theorem_generators,target)
        val _ = case(Binarymap.peek(!generators,name))
                of NONE => generators := Binarymap.insert(!generators,name,(ref NONE,ref []))
                |  SOME _ => ()
in
        Binarymap.find(!generators,name)
end
in
fun set_coding_theorem_conclusion target name mk_conc =
let     val (conc,list) = setup target name
in
        conc := SOME mk_conc
end
fun exists_coding_theorem_conclusion target name = isSome(!(fst(setup target name)))
fun get_coding_theorem_conclusion target name = valOf(!(fst(setup target name)))
fun add_coding_theorem_generator target (name:string) (predicate:hol_type -> bool)  (generator:hol_type -> thm) =
let     val (conc,list) = setup target name
in
        list := (predicate,generator) :: (!list)
end
end;

val source_theorem_generators =
        ref (Binarymap.mkDict String.compare) :
  (string,((hol_type -> term) option ref *
   ((hol_type -> bool) *
    (hol_type -> thm)) list ref)) dict ref

local
fun setup name =
let     val _ = case(Binarymap.peek(!source_theorem_generators,name))
                of NONE => source_theorem_generators :=
                        Binarymap.insert(!source_theorem_generators,name,(ref NONE,ref []))
                |  SOME _ => ()
in      Binarymap.find(!source_theorem_generators,name)
end
in
fun set_source_theorem_conclusion name mk_conc =
let     val (conc,list) = setup name
in      conc := SOME mk_conc
end
fun exists_source_theorem_conclusion name = isSome(!(fst(setup name)))
fun get_source_theorem_conclusion name = valOf(!(fst(setup name)))
fun add_source_theorem_generator name predicate generator =
let     val (conc,list) = setup name
in
        list := (predicate,generator) :: (!list)
end
end;

fun MATCH_CONC thm conc =
let val thm' = SPEC_ALL thm
    val (vars,body) = strip_forall conc
in
    GENL vars (INST_TY_TERM (match_term (concl thm') body) thm')
end;

local
fun err name target t = mkStandardExn "get_coding_theorem_generator"
        ("No coding theorem generator exists for theorems named " ^ name ^
         " in the translation: " ^ type_to_string target ^
         " --> " ^ type_to_string t)
fun get_coding_theorem_generator target name t =
    case (Binarymap.peek(!coding_theorem_generators,target))
    of NONE => raise (err name target t)
    |  SOME x => case (Binarymap.peek(!x,name))
       of NONE => raise (err name target t)
       |  SOME x => (snd (first_e (err name target t)
                                  (fn (x,y) => x t) (!(snd x))))
fun gct target name t =
let val _ = type_trace 2 ("->generate_coding_theorem(" ^ name ^ "," ^
                         (type_to_string t) ^ ")\n")
    val _ = if base_type t = t orelse
               exists_coding_theorem_precise target t name
               then () else (gct target name (base_type t) ; ())
    val theorem = if exists_coding_theorem_precise target t name
                then get_coding_theorem_precise target t name
                else (get_coding_theorem_generator target name t) t
    val mtheorem = if exists_coding_theorem_conclusion target name
                then MATCH_CONC theorem (get_coding_theorem_conclusion target name t)
                        handle e => raise (mkStandardExn "generate_coding_theorem"
("Generator for " ^ name ^
 " returned the theorem:\n " ^ thm_to_string theorem ^
 "\nThis does not match the specified conclusion for type: " ^
 type_to_string t ^ ":\n" ^
 term_to_string (get_coding_theorem_conclusion target name t)))
                else theorem
        val _ = if exists_coding_theorem_precise target t name
                then ()
                else add_coding_theorem_precise target t name mtheorem
   val _ = if null (hyp mtheorem) then ()
              else raise (mkStandardExn "generate_coding_theroem"
                   ("Generator for " ^ name ^
                    " returned the theorem:\n " ^ thm_to_string theorem ^
                    "\nwhich has the non-empty hypothesis set:\n" ^
                    xlist_to_string term_to_string (hyp mtheorem)))
in
        mtheorem
end
in
fun generate_coding_theorem target name t =
        check_loop ("gct" ^ name ^ type_to_string (cannon_type target)) t (gct target name)
                (fn list => raise (mkDebugExn "generate_coding_theorem"
                        ("Experienced a loop whilst generating the coding theorem " ^ name ^
                         " for type " ^ type_to_string target ^
                         "\nTrace: " ^ xlist_to_string type_to_string list)))
end;

local
fun err name t = mkStandardExn "get_source_theorem_generator"
        ("No source theorem generator exists for theorems named " ^ name ^
         " and the type " ^ type_to_string t)
fun get_source_theorem_generator name t =
        case (Binarymap.peek(!source_theorem_generators,name))
        of NONE => raise (err name t)
        |  SOME x => (snd (first_e (err name t) (fn (x,y) => x t) (!(snd x))))
fun gst name t =
let     val _ = type_trace 2 ("->generate_source_theorem(" ^ name ^ "," ^ (type_to_string t) ^ ")\n")
        val _ = if base_type t = t orelse
                   (exists_source_theorem_precise t name)
                   then () else (gst name (base_type t) ; ())
        val theorem = if exists_source_theorem_precise t name
                then get_source_theorem_precise t name
                else (get_source_theorem_generator name t) t
        val mtheorem = if exists_source_theorem_conclusion name
                then MATCH_CONC theorem (get_source_theorem_conclusion name t)
                        handle e => raise (mkStandardExn "generate_source_theorem"
("Generator for " ^ name ^
 " returned the theorem:\n " ^ thm_to_string theorem ^
 "\nThis does not match the specified conclusion for type: " ^
 type_to_string t ^ ":\n" ^
 term_to_string (get_source_theorem_conclusion name t)))
                else theorem
        val _ = if null (hyp mtheorem) then ()
              else raise (mkStandardExn "generate_source_theroem"
                   ("Generator for " ^ name ^
                    " returned the theorem:\n " ^ thm_to_string theorem ^
                    "\nwhich has the non-empty hypothesis set:\n" ^
                    xlist_to_string term_to_string (hyp mtheorem)))
        val _ = if exists_source_theorem_precise t name
                then ()
                else add_source_theorem_precise t name mtheorem
in
        mtheorem
end
in
fun generate_source_theorem name t =
        check_loop ("gst" ^ name) t (gst name)
                (fn list => raise (mkDebugExn "generate_source_theorem"
                        ("Experienced a loop whilst generating the source theorem " ^ name ^
                         "\nTrace: " ^ xlist_to_string type_to_string list)))
end;

(*****************************************************************************)
(* Polytypic generation of functions:                                        *)
(*                                                                           *)
(* All the following higher order functions expect functions from the set:   *)
(*      make_term : Makes a function term of type :target -> 'a              *)
(*      get_def   : Returns the definition of a previously defined function  *)
(*      get_func  : Returns a term to be applied for the given type          *)
(*      conv      : Converts a term from 'make_term' to the acceptable form  *)
(*      get_ind   : Returns the induction theorem for a type                 *)
(* these will be used as abbreviations in the type signatures.               *)
(*                                                                           *)
(* inst_function_def       : get_def -> get_func -> hol_type -> thm          *)
(* expanded_function_def   : conv -> get_def -> hol_type -> term list -> thm *)
(*     Each function returns a fully instantiated definition, however        *)
(*     'expanded_function_def' returns one that applies to all types in the  *)
(*     recursive set and also applies 'conv' to them                         *)
(*                                                                           *)
(* mk_split_source_function :                                                *)
(*         make_term -> get_def -> get_func -> conv -> hol_type -> thm * thm *)
(* mk_split_target_function :                                                *)
(*         make_term -> get_def -> get_func -> conv -> translation_scheme -> *)
(*                        hol_type -> (thm * (term * term) list * thm) * thm *)
(*    These two functions return a theorem of mutual recursion, and an       *)
(*    equality theorem that maps this onto the term given by make_term.      *)
(*    Both functions use SPLIT_FUNCTION_CONV to split the term, 'source'     *)
(*    uses 'prove_rec_fn_exists' to form the mutual recursive function and   *)
(*    'target' uses 'prove_induction_recursion_thms', and as such also       *)
(*    returns a mapping and theorem of induction over the target type.       *)
(*                                                                           *)
(* MATCH_IND_TERM    : term -> thm -> thm                                    *)
(*     Matches a theorem to a term from the antecedents of an induction      *)
(*     theorem                                                               *)
(*                                                                           *)
(* strengthen_proof_term  : thm list -> term -> thm                          *)
(*      Takes a term of the form:                                            *)
(*           (f ... = a) /\ ... ==> (f = h)                                  *)
(*      and returns a theorem strengthened by adding in the rest of the      *)
(*      mutually recursive definitions:                                      *)
(*      |- (f ... = a) /\ ... /\ (g ... = b) /\ ... ==> (f = h) /\ (g = h')  *)
(*            ==> (f ... = a) /\ ... ==> (f = h)                             *)
(*                                                                           *)
(* prove_split_term      : (term * (term * hol_type)) list ->                *)
(*                                                 thm -> thm -> term -> thm *)
(*     Given a mapping from predicates to function constants and types,      *)
(*     a [mutual] induction theorem and a set of mutually recursive          *)
(*     functions, proves a term of the form:                                 *)
(*         |- (split (C a .. z) = A a .. z) /\ .... ==> (split = fn x y)     *)
(*                                                                           *)
(* prove_all_split_terms : get_ind * get_def * conv ->                       *)
(*                         (term * hol_type) list -> thm -> thm list * thm   *)
(*     Given a list mapping function terms to types and a theorem            *)
(*     prove_all_split_terms removes all split terms from the hypothese      *)
(*     of the theorem and returns them as a list                             *)
(*                                                                           *)
(* remove_hyp_terms      : thm -> thm list -> thm list * thm -> thm          *)
(*     Given a pair function, the list of proved split terms and a the       *)
(*     conjunctions from the theorem of mutual recursion, remove_hyp_terms   *)
(*     removes all hypothesis from the final mutual recursion theorem        *)
(*                                                                           *)
(* match_mapping         : thm -> (term * term) list -> get_func -> thm ->   *)
(*                               hol_type -> (term * (term * hol_type)) list *)
(*     Given an equality theorem and a mapping as returned by mk_split...    *)
(*     and an induction theorem, match_mapping attempts to construct a full  *)
(*     mapping from predicates to functions constants and types.             *)
(*                                                                           *)
(* unsplit_function      : get_ind -> get_def -> get_func -> conv ->         *)
(*                                              hol_type -> thm * thm -> thm *)
(*     Given a pair '(eq_thm,mrec_thm)' representing the equality theorem    *)
(*     and mutual recursion theorem returned by the mk_split_... functions   *)
(*     'unsplit_function' returns a theorem of mutual recursion that matches *)
(*     that given by eq_thm.                                                 *)
(*     Uses 'prove_all_split_terms' and 'remove_hyp_terms' to remove any     *)
(*     condition imposed by the equality theorem.                            *)
(*                                                                           *)
(* mk_source_functions : string -> mk_term -> get_func -> conv ->            *)
(*                                                          hol_type -> unit *)
(* mk_coding_functions, mk_target_functions : string -> mk_term ->           *)
(*                          get_func -> conv -> hol_type -> hol_type -> unit *)
(*    These functions combine 'unsplit_function' and 'mk_split_..._function' *)
(*    to generate functions, these functions are then defined through        *)
(*    'new_specification' and the relevant theorems and definitions are      *)
(*    stored in the coding base.                                             *)
(*                                                                           *)
(*****************************************************************************)

fun inst_function_def get_def get_func (t:hol_type) =
let     val _ = type_trace 3 "->inst_function_def\n"
in
        LIST_CONJ (map (C (PART_MATCH (rator o lhs)) (get_func t))
                (CONJUNCTS (get_def t)))
        handle e => wrapException "inst_function_def" e
end

local
fun wrap "" e = wrapException ("expanded_function_def") e
  | wrap s  e = wrapException ("expanded_function_def (" ^ s ^ ")") e;
fun gen1 vars thm =
let     val rvars = free_vars_lr ((rand o lhs o concl) thm)
        val vars' = intersect vars (free_vars (concl thm))
in
        GENL rvars (GENL vars' thm)
end
fun GEN_RAND vars thm =
        LIST_CONJ (map (gen1 vars o SPEC_ALL) (CONJUNCTS thm)) handle e => wrap "GEN_RAND" e

fun inst_it vars thm term =
        GEN_RAND vars (LIST_CONJ (map (C (PART_MATCH (rator o lhs)) term) (CONJUNCTS thm)) handle e => wrap "inst_it" e)
fun single_inst recfns vars main enc =
let     val current = strip_conj (concl main)
        val next = mapfilter
                (inst_it vars enc)
                (find_terms (can (match_term
                        ((rator o lhs o snd o strip_forall o hd o strip_conj o concl) enc)))
                (concl main) handle e => wrap "single_inst" e)
        val candidates = filter (fn x => (not o C mem current o concl) x andalso exists (C free_in (concl x)) recfns) next
in
        CONJ main (hd candidates)
end
fun inst_all recfns vars main [] = main
  | inst_all recfns vars main list =
        uncurry (inst_all recfns vars)
                (pick_e (mkDebugExn
                        ("expanded_function_def")
                        ("Sub-function returned by expanded_function_def not used in main function"))
                (single_inst recfns vars main) list)
fun inst_pairs recfns vars main pair = repeat (C (single_inst recfns vars) pair) main
fun fix_function recfns conv pair (main,sub) =
let     val vars = flatten (
                        map (fn c => set_diff ((fst o strip_forall) c) ((free_vars o rand o lhs o snd o strip_forall) c))
                                ((strip_conj o concl) main))
in
        inst_pairs recfns vars (inst_all recfns vars (CONV_RULE conv main)
                                        (map (CONV_RULE conv) sub)) (CONV_RULE conv pair)
end
fun subset x y = set_eq x (intersect x y);
in
fun expanded_function_def conv create_conv get_def t term_list =
let     val _ = type_trace 3 "->expanded_function_def\n"
        val base_types = split_nested_recursive_set (base_type t) handle e => wrap "" e
        val functions = map (get_def ## map get_def o fst) base_types handle e => wrap "" e
        val pair = get_def (mk_prod(alpha,beta))

        val matched = map (fn (main,sub) => (tryfind_e
                        (mkDebugExn "expanded_function_def"
                                ("Could not find a match for the function:\n" ^ thm_to_string main ^
                                 "\nin the term list: " ^ xlist_to_string term_to_string term_list))
                        (fn t => LIST_CONJ (map (C (PART_MATCH (rator o lhs)) t) (CONJUNCTS main))) term_list,sub)) functions
        val recfns = map (repeat rator o lhs o snd o strip_forall o hd o strip_conj o concl o fst) matched
        val full = PURE_REWRITE_RULE [GSYM CONJ_ASSOC] (LIST_CONJ (map (fix_function recfns conv pair) matched))
in
        CONV_RULE create_conv full
end
end;

local
fun wrap_conv source func conv term =
let     val name = ("conv (supplied function)")
        val mkExn = mkStandardExn name
        val result = conv term handle e => wrapException name e
        val _ = if can (match_term term) (lhs (concl result)) then () else
                        raise (mkExn (  "Left hand side of result theorem:\n" ^ thm_to_string result ^
                                        "\ndoes not match the term given:\n" ^ term_to_string term))
        val _ = if not source orelse source andalso is_source_function ((rhs o concl) result) then () else
                        raise (mkExn (  "Right hand side of result theorem:\n" ^ thm_to_string result ^
                                        "\nis not a correct source function, see help for details"))
        val _ = if source orelse not source andalso is_target_function ((rhs o concl) result) then () else
                        raise (mkExn (  "Right hand side of result theorem:\n" ^ thm_to_string result ^
                                        "\nis not a correct target function, see help for details"))
in
        result
end
fun mk_eq_thm func mk_term get_def get_func conv t =
let     fun wrap e = wrapException ("mk_split_" ^ func ^ "_function (mk_eq_thm)") e
        val recursive_types = (map (I ## fst) (split_nested_recursive_set t))
        val tm = mk_prod(alpha,beta)
        val terms = map (mk_term o fst) recursive_types handle e => wrap e
        val pair = CONV_RULE conv (get_def tm) handle e => wrap e
        val get_hfuns = map (inst_function_def (CONV_RULE conv o get_def) get_func) o filter (not o can (match_type tm))
        val hfuns = get_hfuns (mk_set (flatten (map snd recursive_types)))
        val term = list_mk_conj (flatten (map strip_conj terms)) handle e => wrap e
        val _ = type_trace 3 ("Target function: \n" ^ term_to_string term ^ "\n")
        val eq_thm =
                (conv THENC
                 SPLIT_FUNCTION_CONV (is_double_term_source,pair) hfuns) term handle e => wrap e
        val _ = type_trace 3 ("Equivalence theorem: \n" ^ thm_to_string eq_thm ^ "\n");
in
        eq_thm
end
fun wraps e = wrapException "mk_split_source_function" e
fun wrapt e = wrapException "mk_split_target_function" e
in
fun mk_split_source_function mk_term get_def get_func conv create_conv t =
let     val _ = type_trace 2 "->mk_split_source_function\n"
        val eq_thm1 = mk_eq_thm "source" mk_term get_def get_func (wrap_conv true "source" conv) t
        val eq_thm2 = create_conv (rhs (concl eq_thm1)) handle e => wraps e
        val r_thm = prove_rec_fn_exists (TypeBase.axiom_of t) ((rhs o concl) eq_thm2) handle e => wraps e
        val _ = assert "mk_split_source_function" [
                ("prove_rec_fn_exists returned a theorem with a non-empty hypothesis set!",
                 null o hyp)] r_thm
in
        (CONV_RULE (STRIP_QUANT_CONV (REWR_CONV (GSYM eq_thm2))) r_thm,eq_thm1) handle e => wraps e
end
fun mk_split_target_function mk_term get_def get_func conv create_conv (scheme:translation_scheme) t =
let     val _ = type_trace 2 "->mk_split_target_function\n"
        val eq_thm1 = mk_eq_thm "target" mk_term get_def get_func (wrap_conv false "target" conv) t
        val eq_thm2 = create_conv (rhs (concl eq_thm1)) handle e => wrapt e
        val (i_thm,mapping,r_thm) = prove_induction_recursion_thms scheme ((rhs o concl) eq_thm2)
in
        ((i_thm,mapping,CONV_RULE (STRIP_QUANT_CONV (REWR_CONV (GSYM eq_thm2))) r_thm),eq_thm1) handle e => wrapt e
end
end


(* Matches a thm to a term:
Terms are:
        Either: !a...z. f (C a .. z) = g (C a .. z)
        Or    : !a...z. (a = b) /\ (c = d) /\ (e = f) ==> !a'...z'. f (C a' .. z') = g (C a' .. z')
Thms will then be:
        Either: [.] |- f (C a .. z) = g (C a .. z)
        Or    : [.,a = b,c = d,e = f] |- f (C a .. z) = g (C a .. z)
*)
local
fun disch_and_conj_list thm [] = thm
  | disch_and_conj_list thm [a] = DISCH a thm
  | disch_and_conj_list thm (a::b::rest) =
        CONV_RULE (REWR_CONV AND_IMP_INTRO) (DISCH a (disch_and_conj_list thm (b::rest)))
fun SPECL_GEN thm =
        SPECL (map (genvar o type_of) (fst (strip_forall (concl thm)))) thm
in
fun MATCH_IND_TERM term assum =
let     val (gen1,body1) = strip_forall term
        val split2 = total ((strip_conj ## strip_forall) o dest_imp) body1;
        val assum' = SPECL_GEN assum
in
        GENL gen1 (case split2
                        of SOME (a,(b,term)) =>
                                (disch_and_conj_list
                                        (GENL b (INST_TY_TERM (match_term (concl assum')
                                                term) assum'))
                                        a
                                handle e =>
                                INST_TY_TERM (match_term (concl assum') body1) assum')
                        |  NONE => INST_TY_TERM (match_term (concl assum') body1) assum')
end     handle e => wrapException "MATCH_IND_TERM" e
end

local
fun wrap "" e = wrapException "strengthenProof" e
  | wrap s e = wrapException ("strengthenProof (" ^ s ^ ")") e

(* Anything in l1 is free in l2                                                     *)
fun any_free_in [] l2 = false
  | any_free_in (x::xs) l2 = exists (free_in x) l2 orelse any_free_in xs l2;

(* A function *not* in funcs is supplied with one in funcs                          *)
fun undef_hofs funcs term =
        find_terms (both o (not o C mem funcs ## any_free_in funcs) o strip_comb) ((rhs o snd o strip_forall) term)
        handle e => wrap "undef_hofs" e;

(* Generalise a theorem with arguments of the constructor                           *)
fun gen_const thm =
        GENL ((free_vars_lr o rand o lhs o snd o strip_forall o concl) thm) thm
        handle e => wrap "gen_const" e;

(* Match a term such as, enc1 (enc2 ...) with a theorem                             *)
fun match_term_func term thm =
        LIST_CONJ (map (gen_const o C (PART_MATCH (rator o lhs)) term) (CONJUNCTS thm))
        handle e => wrap "match_term" e;

(* Finds HO calls in a term and adds in the functions to the set of conjunctions    *)
fun add_defs_conv fvs functions (funcs,thm) =
let     val term = (rhs o concl) thm
        val hofs = flatten (map (undef_hofs funcs) (strip_conj term))
        val defs = mapfilter (fn h => tryfind_e Empty (match_term_func h) functions) hofs
        val defs' = map (fn d => LIST_CONJ (map (GENL (intersect (free_vars (concl d)) fvs)) (CONJUNCTS d))) defs
        val sdefs = map (fn d => (d,(rator o lhs o snd o strip_forall o hd o strip_conj o concl) d)) defs'
        val adefs = filter (not o C mem funcs o snd) sdefs
        val _ = if null adefs then raise Empty else ()
        val (new_funcs,defs'') = foldr (fn ((a,b),(nf,d)) => (b :: nf,a :: d)) (funcs,[]) adefs
in
        (new_funcs @ funcs,TRANS thm (foldr (uncurry PROVE_HYP)
                ((foldr (fn (a,b) => ADDR_AND_CONV (concl a) THENC b) ALL_CONV defs'') term) defs''))
end     handle e => wrap "add_defs_conv" e;
in
fun strengthen_proof_term functions term =
let     val _ = type_trace 3 "->strengthen_proof_term\n"
        val _ = type_trace 3 ("Strengthening proof term: " ^ term_to_string term)
        val _ = assert "strengthen_proof_term" [
                ("Proof term is not an implication from a function definition to a conjunction of function equalities",
                 is_implication_of
                        (is_conjunction_of (is_eq o snd o strip_forall))
                        (is_conjunction_of (fn x => (is_eq o snd o strip_forall) x
                                        andalso (can dom_rng o type_of o lhs o snd o strip_forall) x)))] term
        val (ante,conc) = guarenteed dest_imp_only term handle e => wrap "" e;
        val clauses = strip_conj ante handle e => wrap "" e;
        val funcs = map (rator o lhs o snd o strip_forall) clauses handle e => wrap "" e;
        val fvs = mk_set (flatten (map (fst o strip_forall) (strip_conj conc)))
        val thm1 = snd (EQ_IMP_RULE ((LAND_CONV (REWR_CONV
                        (snd (repeat (add_defs_conv fvs functions) (funcs,REFL ante)))) THENC
                         PURE_REWRITE_CONV [GSYM CONJ_ASSOC]) term))
                        handle e => wrap "" e
        val new_term = guarenteed (fst o dest_imp_only o concl) thm1 handle e => wrap "" e
        val _ = assert "strengthen_proof_term" [
                ("Strengthen proof term is not of the correct form, should be impossible!",
                 is_implication_of (is_conjunction_of (is_eq o snd o strip_forall))
                                ((fn x => (is_eq o snd o strip_forall) x
                                        andalso (can dom_rng o type_of o lhs o snd o strip_forall) x)))] new_term
        val all_rators = mk_set ((map (rator o lhs o snd o strip_forall) o strip_conj o fst o dest_imp_only) new_term)
                        handle e => wrap "" e
        val subs = subst (map (op|-> o dest_eq o snd o strip_forall) (strip_conj conc)) handle e => wrap "" e
        val conc' = (strip_conj conc) @ (map (fn x => list_mk_forall(intersect fvs (free_vars (subs x)),mk_eq(x,subs x)))
                        (filter (not o C mem (map (lhs o snd o strip_forall) (strip_conj conc))) all_rators))
                        handle e => wrap "" e
        val final_term = mk_imp(fst (dest_imp_only new_term),list_mk_conj conc') handle e => wrap "" e
in
        DISCH_ALL (MP thm1 (DISCH (fst (dest_imp_only new_term))
                (LIST_CONJ (map (fn c => first (curry op= c o concl) (CONJUNCTS (UNDISCH_ONLY (ASSUME final_term))))
                (strip_conj conc))))) handle e => wrap "" e
end
end

fun prove_split_term mapping induction function (dead_thm,dead_value) term =
let     val _ = type_trace 3 "->prove_split_term\n"
        val _ = type_trace 3 ("Attempting to prove split term: " ^ term_to_string term ^ "\n")
        fun wrap e = wrapException "prove_split_term" e

        val _ = assert "prove_split_term" [
                ("Proof term is not an implication from a function definition to a conjunction of function equalities",
                 is_implication_of (is_conjunction_of (is_eq o snd o strip_forall))
                        (is_conjunction_of (fn x => (is_eq o snd o strip_forall) x
                                        andalso (can dom_rng o type_of o lhs o snd o strip_forall) x)))] term

        val equivs = (map ((I ## dest_eq) o strip_forall) o strip_conj o snd o dest_imp_only) term handle e => wrap e

        val tt = mk_forall(mk_var("t",alpha),mk_comb(mk_var("P",alpha --> bool),mk_var("t",alpha))) handle e => wrap e
        val _ = assert "prove_split_term" [
                ("Induction theorem is not an implication to a conjunction of generalised predicates",
                 is_conjunction_of (can (match_term tt)) o snd o dest_imp_only o snd o strip_forall o concl)] induction
        val predicates =
                (map (rator o snd o strip_forall) o strip_conj o snd o dest_imp_only o snd o strip_forall o concl)
                induction handle e => wrap e

        val all_fns = bucket_alist (map ((rator ## I) o dest_eq o snd o strip_forall)
                                (strip_conj (fst (dest_imp_only term)))) handle e => wrap e;

        val _ = assert "prove_split_term" [
                ("Number of predicates, " ^ int_to_string (length predicates) ^
                 ", does not match number of functions, " ^ int_to_string (length all_fns),
                 curry op= (length predicates) o length)] all_fns

        val _ = (raise (mkDebugExn "prove_split_term"
                ("Free variables occur in the predicate term: " ^ term_to_string
                        (first_e Empty (fn t => not (null (set_diff (free_vars t)
                                (flatten (map (op:: o strip_comb o fst) all_fns) @ set_diff (free_vars (rhs t)) (snd (strip_comb (lhs t)))))))
                                ((strip_conj o snd o dest_imp_only o snd o strip_forall) term))))) handle Empty => ();

        val match = map (fn (a:term,(b,t:hol_type)) => (a,first (can (match_term b) o snd o snd) equivs)) mapping

        val predicate = RIGHT_CONV_RULE (EVERY_CONJ_CONV (fn term =>
                                ORDER_FORALL_CONV (((fn a => last a :: butlast a) o fst o strip_forall) term) term))
                        (LIST_MK_CONJ ((map (fn (_,(a,b)) => STRIP_QUANT_CONV (REWR_CONV FUN_EQ_THM)
                                (list_mk_forall(a,mk_eq b))) match))) handle e => wrap e

        (* The instantiated predicate, rewritten to match the conclusion of the term *)
        val inst = CONV_RULE (RAND_CONV (REWR_CONV (GSYM predicate)))
                (HO_PART_MATCH (snd o dest_imp_only) induction ((rhs o concl) predicate))
                handle _ => raise (mkDebugExn "prove_split_term"
                                ("Term conclusion, " ^ (term_to_string o lhs o concl) predicate ^
                                 " does not match induction conclusion: " ^
                                        (term_to_string o snd o dest_imp_only o snd o strip_forall o concl) induction));

        (* [!a .. z. split_n (C a .. z) = body a .. z] |- split_n (C a .. z) = body a .. z *)
        val assums = map (SPEC_ALL o ASSUME) ((strip_conj o fst o dest_imp_only) term) handle e => wrap e

        (* Converts a rewrite with the assumption [split_n x = f_n a_n .. x] |- split_n x = f_n a_n .. x *)
        fun fix_rewrite thm =
        let     val terms = find_terms (fn t => (exists (curry op= (rator t) o snd o snd) equivs handle _ => false))
                        (rhs (concl thm));
                val rwrs = map (fn t => (list_mk_forall o (I ## (mk_eq o
                                (C (curry mk_comb) (rand t) ## C (curry mk_comb) (rand t)))))
                        (first (curry op= (rator t) o snd o snd) equivs)) terms

        in      PURE_REWRITE_RULE (map (SPEC_ALL o GSYM o ASSUME) rwrs) thm
        end     handle e => wrapException "prove_split_term (fix_rewrite)" e

        val clauses = (CONJUNCTS o SPEC_ALL) function
        val missing_exn =
                mkDebugExn "prove_split_term"
                "The function given does not exactly match the induction theorem"

        (* Rewrite theorems: should match the assumptions on the left and the antecedents of inst on the right *)
        val rewrites = map (GSYM o fix_rewrite o (fn x => tryfind_e missing_exn (C REWR_CONV x) clauses) o
                                rhs o snd o strip_forall o snd o strip_imp o snd o strip_forall)
                        ((strip_conj o fst o dest_imp_only o concl) inst)

        (* Rewritten assumptions using the rewrites, output should match inst *)
        val assums' = map (CONV_RULE (STRIP_QUANT_CONV (RAND_CONV (FIRST_CONV (map MATCH_CONV rewrites))))) assums
                handle _ =>     raise (mkDebugExn "prove_split_term"
                                "The term given does not match the induction theorem and function")

        (* Antecedents of the instantiation we wish to match *)
        val terms = (strip_conj o fst o dest_imp_only o concl) inst handle e => wrap e

        (* Extra theorems when P x is false (not required for encoding) *)
        fun mk_all_extra [] = []
          | mk_all_extra thms =
        case (total (first is_neg) (mapfilter (fst o dest_imp_only o snd o strip_forall) (strip_conj (fst (dest_imp_only (concl inst))))))
        of SOME assum => map (RIGHT_CONV_RULE (REPEATC (CHANGED_CONV (PURE_ONCE_REWRITE_CONV [dead_thm,ASSUME assum,COND_CLAUSES] THENC PURE_ONCE_REWRITE_CONV thms)))) thms
        |  NONE => []

        fun ttrans [] _ = []
          | ttrans (x::xs) ys =
        let val (y,ysr) = pluck (can (TRANS x)) ys
        in      TRANS x y::ttrans xs ysr end;

        val extra_assums =
                if can (tryfind (dest_neg o fst o dest_imp_only o snd o strip_forall)) terms
                then ttrans (mk_all_extra (filter (is_cond o rhs o snd o strip_forall o concl) assums))
                                (map SYM (mk_all_extra (map SPEC_ALL
                                        (filter (is_cond o rhs o snd o strip_forall o concl) clauses))))
                else []

        (* Dead value theorems (only used in making target functions) *)
        val dead_terms = flatten (map (filter (fn x => (curry op= dead_value o rand o lhs o snd o strip_forall) x handle e => false) o hyp) assums');
        val dead_thms = case (mappartition
                        (CONV_RULE bool_EQ_CONV o (REPEATC (ONCE_REWRITE_CONV (map GEN_ALL assums) THENC ONCE_REWRITE_CONV clauses THENC REWRITE_CONV [dead_thm]))) dead_terms)
                        of (x,[]) => x
                        |  (_,x::xs) => raise (mkDebugExn "prove_split_term"
                                ("Could not resolve the 'dead' term: " ^ (term_to_string x)))

        val final_assums = map (C (foldl (uncurry PROVE_HYP)) dead_thms) assums';

        (* Make sure we have exactly the same form as the term we were given *)
        val inst' = CONV_RULE (RAND_CONV (REWR_CONV (CONV_RULE bool_EQ_CONV (AC_CONV (CONJ_ASSOC,CONJ_COMM)
                (mk_eq((snd o dest_imp_only o concl) inst,(snd o dest_imp_only) term)))))) inst handle e => wrap e

        (* Final proof of the term *)
        val final = PURE_REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC] (foldr (uncurry DISCH) (MP inst' (LIST_CONJ (map (fn t =>
                        tryfind_e (     mkDebugExn "prove_split_term"
                                        ("No matching antecedent found to match induction term " ^ term_to_string t))
                        (MATCH_IND_TERM t) (final_assums @ extra_assums)) terms)))
                ((strip_conj o fst o dest_imp_only) term))
in
        if null (hyp final) then final else
                raise (mkDebugExn "prove_split_term" ("The exception: " ^ term_to_string (hd (hyp final)) ^ " exists in the final proof!"))

end

local
fun wrap "" e = wrapException "prove_all_split_terms" e
  | wrap s e = wrapException ("prove_all_split_terms (" ^ s ^ ")") e

(* Prove a single split term by strengthening then inductive proof           *)
fun full_prove_split_term (get_ind,get_def,conv,create_conv,dead_thm,dead_value) t h =
let     val functions = flatten (map (map (CONV_RULE conv o get_def) o fst o snd)
                                (split_nested_recursive_set (base_type t)));
        val sh = strengthen_proof_term (CONV_RULE conv (get_def (mk_prod(alpha,beta))) :: functions) h
                handle e => raise (mkDebugExn "prove_all_split_terms (full_prove_split_term)"
                        ("Could not strengthen uniqueness proof: " ^ (term_to_string h) ^
                        "\nusing the function set: " ^ xlist_to_string thm_to_string functions ^
                        "\noriginal exception: " ^ exn_to_string e));
        val sh' = CONV_RULE (LAND_CONV (LAND_CONV create_conv)) sh
        val function = expanded_function_def conv create_conv get_def t
                                ((map (rhs o snd o strip_forall) o strip_conj o snd o dest_imp_only) h)
                handle e => wrap "full_prove_split_term" e
        val (induction,mapping) = get_ind t handle e => wrap "full_prove_split_term" e
        val th = prove_split_term mapping induction function (dead_thm,dead_value) ((fst o dest_imp_only o concl) sh')
                handle e => raise (mkDebugExn "prove_all_split_terms (full_prove_split_term)"
                        ("Could not prove uniqueness proof: " ^ ((term_to_string o fst o dest_imp_only o concl) sh') ^
                         "\nusing the expanded function definition: " ^ (thm_to_string function) ^
                         "\nand the induction theorem: " ^ (thm_to_string induction) ^
                         "\noriginal exception: " ^ exn_to_string e));
in
        MP sh' th handle e => raise (mkDebugExn "prove_all_split_terms (full_prove_split_term)"
                ("Proof returned by 'prove_split_term' does not exactly match its input term, " ^
                 "\ninput term: " ^ ((term_to_string o fst o dest_imp_only o concl) sh') ^
                 "\noutput thm: " ^ (thm_to_string th)))
end

(* Find the type of a term in the match list                                 *)
fun get_type term list =
let     val rs = guarenteed (map (rhs o snd o strip_forall) o strip_conj o snd o dest_imp_only) term
in      tryfind_e Empty (C assoc list) rs
end
in
fun prove_all_split_terms gets matches thm =
let     val _ = type_trace 3 "->prove_all_split_terms\n"
        val terms = filter is_imp_only (hyp thm)

        val _ = map (fn term => assert "prove_all_split_terms" [
                (("Proof term: " ^ term_to_string term ^
                 "is not an implication from a function definition to a conjunction of function equalities"),
                 is_implication_of (is_conjunction_of (is_eq o snd o strip_forall))
                        (fn x => (is_eq o snd o strip_forall) x
                                andalso (can dom_rng o type_of o lhs o snd o strip_forall) x))] term) terms

        fun do_all matches [] = (type_trace 1 "0\n" ; [])
          | do_all matches terms =
        let     val (found,notfound) = mappartition (fn t => (get_type t matches,t)) terms
                val done = map (uncurry (full_prove_split_term gets)) found
                val _ = type_trace 1 (int_to_string (length terms) ^ "-")
                val _ = hd done
                val rwrs = map (op|-> o uncurry (C pair) o dest_eq o snd o
                        strip_forall o snd o dest_imp_only o concl) done
        in
                done @ do_all (map (subst rwrs ## I) matches) notfound
        end;

        val proofs =
                if null terms then [] else
                (type_trace 1 "Proving uniqueness terms: " ;
                 do_all matches terms
                        handle Empty =>
                        raise (mkDebugExn "prove_all_split_terms"
                                ("The type of one or more of the uniqueness proofs: " ^
                                 xlist_to_string term_to_string terms ^
                                 "\ncould not be matched to the list: " ^
                                 xlist_to_string (xpair_to_string term_to_string type_to_string) matches)))
in
        (proofs,foldl (uncurry PROVE_HYP_CHECK) thm proofs)
        handle e => wrap "" e
end
end

local
fun wrap "" e = wrapException "remove_hyp_terms" e
  | wrap s e = wrapException ("remove_hyp_terms (" ^ s ^ ")") e

(* Performs a fold, but retains lists of passes and failures                 *)
fun filter_fold f a [] = (a,([],[]))
         | filter_fold f a (x::xs) = (I ## (cons x ## I)) (filter_fold f (f x a) xs)
        handle Empty => (I ## (I ## cons x)) (filter_fold f a xs)

(* Given a pair thm: 'split (a,b) = f a b' returns a rewrite 'split = f'     *)
fun fix_pair1 pair_thm thm =
let     val thm' = SPEC_ALL (CONV_RULE (STRIP_QUANT_CONV (RAND_CONV (REWR_CONV (GSYM pair_thm)))) thm)
        val thm'' = GENL ((strip_pair o rand o rhs o concl) thm') thm'
in
        MATCH_MP (snd (EQ_IMP_RULE (SPEC_ALL FUN_EQ_THM))) (MP (HO_PART_MATCH (fst o dest_imp_only)
                (TypeBase.induction_of (mk_prod(alpha,beta))) (concl thm'')) thm'')
end handle e => wrap "fix_pair1" e
fun fix_pair2 pair_thm thm =
let     val thm' = SPEC_ALL (CONV_RULE (STRIP_QUANT_CONV (RAND_CONV (REWR_CONV (GSYM pair_thm)))) thm)
        val thm'' = GENL ((strip_pair o rand o rhs o concl) thm') thm'
in
        CONV_RULE (REWR_CONV (GEN_ALL (SYM (SPEC_ALL FUN_EQ_THM)))) thm''
end handle e => wrap "fix_pair2" e
fun fix_pair pair_thm thm =
        if (can (match_type (mk_prod(alpha,beta))) ((type_of o rand o lhs o snd o strip_forall o concl) thm))
        then    fix_pair1 pair_thm thm
        else    fix_pair2 pair_thm thm

fun PROVE_HYP_CONJ thm1 thm2 =
let     val thm' = EQ_MP (CONV_RULE bool_EQ_CONV
                        (tryfind_e Empty (AC_CONV (CONJ_ASSOC,CONJ_COMM) o curry mk_eq (concl thm1)) (hyp thm2))) thm1
in
        if mem (concl thm') (hyp thm2) then PROVE_HYP_CHECK thm' thm2 else raise Empty
end     handle Empty => raise Empty | e => wrap "PROVE_HYP_CONJ" e
fun remove_hyp_terms_pre min pair_thm proofs (mthms,thm) =
let     val _ = type_trace 3 "->remove_hyp_terms\n"
        val to_remove = length mthms - min
        val _ = if to_remove = 0 then type_trace 1 "0\n" else type_trace 1 (int_to_string (length mthms - min) ^ "-")
        val (thm',(removed,kept)) = filter_fold PROVE_HYP_CONJ thm mthms
        val pair_rewrites = mapfilter (GEN_ALL o fix_pair pair_thm) removed
        val nonpair_rewrites = mapfilter (fn m => tryfind (C MP m) proofs) removed
        val _ = if length pair_rewrites + length nonpair_rewrites = length removed then ()
                else raise (mkDebugExn "remove_hyp_terms"
                        "Not all the hypotheses removed could be matched to a pair_theorem or a proved split term")
        fun conv term =
                if term = hd (hyp (hd mthms)) then ALL_CONV term
                else (PURE_REWRITE_CONV pair_rewrites THENC PURE_REWRITE_CONV nonpair_rewrites) term
in
        if null removed orelse null kept then
                if to_remove <= length removed then thm
                else raise (mkDebugExn "remove_hyp_terms"
                        ("The terms: " ^ xlist_to_string (term_to_string o concl) kept ^
                         " do not match terms in the hypothesis set"))
        else
        remove_hyp_terms_pre min pair_thm proofs (map (CONV_RULE conv) kept,PROVE_HYP TRUTH (CONV_HYP conv thm'))
end
in
fun remove_hyp_terms pair_thm proofs ([],thm) = thm
  | remove_hyp_terms pair_thm proofs (mthms,thm) =
let     val total = (length o mk_set o map (repeat rator o lhs o snd o strip_forall) o strip_conj o concl) thm
in
        if length mthms = total then
                foldl (uncurry PROVE_HYP) thm mthms
        else
                (type_trace 1 "Removing splits: " ;
                remove_hyp_terms_pre total pair_thm proofs (mthms,thm))
end
end;

local
fun full_subst subs term =
        if subst subs term = term then term else full_subst subs (subst subs term)
in
fun match_mapping ethm mapping get_func pair_def t =
let     val all_types = flatten (map (op:: o (I ## op@)) (split_nested_recursive_set t))
        val alist = map (fn t => (get_func t,t)) all_types
        val eq_fns1 = mapfilter (dest_eq o snd o strip_forall o snd o dest_imp_only) (hyp ethm)
        val eq_fns2 = mapfilter ((rator ## rator) o dest_eq o snd o strip_forall o rhs o
                        concl o STRIP_QUANT_CONV (RAND_CONV (REWR_CONV (GSYM pair_def)))) (hyp ethm)
        val mapping' = map ((I:term -> term) ## full_subst (map op|-> (eq_fns1 @ eq_fns2))) mapping

        val pt = (rator o lhs o snd o strip_forall o concl) pair_def

        fun find_type func =
                case (assoc1 func alist)
                of NONE => if can (match_term pt) func
                                then list_mk_prod(mapfilter find_type (snd (strip_comb func)))
                                else raise (mkDebugExn "match_mapping"
                                                ("Could not find type for function: " ^ term_to_string func))
                |  SOME (a,t) => t
in
        map (fn (a,b) => (a,(b,find_type b))) mapping'
end
end

local
fun wrap e = wrapException "unsplit_function" e
fun err1 thm = "Mutual recursion theorem must be of the form: \n" ^
        "|- ?fn0 ... fnK. (!a... fn0 ... = A0) /\\ ... /\\ (!a ... fnK ... = AK)\n" ^
        "theorem supplied has the form: \n" ^
        thm_to_string thm
fun wrap_ind get_ind t =
let     fun mkExn s = raise (mkStandardExn "get_ind (supplied function)" s)
        val result = get_ind t
        val all_types = flatten (map (op:: o (I ## fst)) (split_nested_recursive_set (base_type t)))
        val preds = fst (strip_forall (concl result))
        val _ = if null (hyp result) then ()
                else mkExn ("Induction theorem returned contains a non-empty hypothesis set")
        val _ = if all (can (match_type (alpha --> bool)) o type_of) preds then ()
                else mkExn ("Not all predicates of returned induction theorem are of type :'a -> bool")
        val _ = if length preds = length all_types then ()
                else mkExn ("Induction theorem specifies " ^ int_to_string (length preds) ^
                            " predicates but type " ^ type_to_string t ^ " is a set of " ^
                            int_to_string (length all_types) ^ " mutually recursive types")
        val _ = if is_imp_only (snd (strip_forall (concl result))) then ()
                else mkExn ("Induction theorem returned is not an implication: " ^ thm_to_string result)
        val (hyps,conc) = (strip_conj ## strip_conj) (dest_imp_only (snd (strip_forall (concl result))))
        val my_conc = map (fn p => mk_forall(mk_var("x",fst (dom_rng (type_of p))),
                                mk_comb(p,mk_var("x",fst (dom_rng (type_of p)))))) preds
        val _ = if all (fn c => exists (aconv c) my_conc) conc andalso all (fn c => exists (aconv c) conc) my_conc then ()
                else mkExn ("Conclusion of induction theorem does not use exactly the predicates: " ^
                            xlist_to_string term_to_string my_conc)
in
        result
end
in
fun unsplit_function get_ind get_def get_func conv create_conv (dead_thm,dead_value) t (mthm,ethm) =
let     val _ = type_trace 2 "->unsplit_function\n"
        val mterm = (snd o strip_exists) (
                assert "unsplit_function" [
                        (err1 mthm,boolSyntax.is_exists),
                        (err1 mthm,is_conjunction_of (is_eq o snd o strip_forall) o snd o strip_exists),
                        (err1 mthm,fn t => set_eq       ((map (repeat rator o lhs o snd o strip_forall) o
                                                        strip_conj o snd o strip_exists) t)
                                                ((fst o strip_exists) t))] (concl mthm));
        val mthms = map (LIST_CONJ o snd)
                        (bucket_alist (map (fn x => ((repeat rator o lhs o snd o strip_forall o concl) x,x))
                                (CONJUNCTS (ASSUME mterm)))) handle e => wrap e
        val thm = CONV_RULE (REWR_CONV (GSYM ethm)) (ASSUME mterm)
                        handle e => raise (mkDebugExn "unsplit_function"
                                "Equivalence theorem does not match theorem of mutual recursion")
        val prod = pairLib.mk_prod(alpha,beta) handle e => wrap e
        val htypes = mk_set (filter (not o can (match_type prod))
                (flatten (map (fst o snd) (split_nested_recursive_set t))))
        val pair_thm = get_def prod handle e => wrap e
        val matches = zip (map get_func htypes) htypes handle e => wrap e
        val (proofs,thm') = prove_all_split_terms (get_ind,get_def,conv,create_conv,dead_thm,dead_value) matches thm handle e => wrap e
        val thm'' = remove_hyp_terms pair_thm proofs (mthms,thm') handle e => wrap e
        val _ = if length (hyp thm'') = 1 then () else
                        raise (mkDebugExn "unsplit_function"
                        "remove_hyp_terms returned a theorem with more than one hypothesis")
        val hyp_vars = fst (strip_exists (concl mthm)) handle e => wrap e
        val thm_vars = mk_set (map (repeat rator o lhs o snd o strip_forall) (strip_conj (concl thm'')))
                handle e => wrap e
in
        CHOOSE_L (hyp_vars,mthm) (foldl (uncurry SIMPLE_EXISTS) thm'' thm_vars)
        handle e => wrap e
end
end

local
fun complete_function name mk_term get_ind get_def get_func conv create_conv (dead_thm,dead_value) t (mthm,ethm) =
let     val unsplit = unsplit_function get_ind get_def get_func conv create_conv (dead_thm,dead_value) t (mthm,ethm)
        val all_types = map fst (split_nested_recursive_set t)
        val func_names = map (fst o dest_var o repeat rator o get_func) all_types
        val def = new_specification (name ^ "_" ^ (fst (dest_type t)),map (fst o dest_var) (fst (strip_exists (concl unsplit))),unsplit)
        val all_theorems = map (I ## LIST_CONJ) (bucket_alist
                        (map (fn x => ((repeat rator o lhs o snd o strip_forall o concl) x,x)) (CONJUNCTS def)))
        val all_consts = map2 (curry mk_const) func_names (map (type_of o repeat rator o get_func) all_types)
in
        map2 (fn t => fn ac => (t,assoc1 ac all_theorems)) all_types all_consts
end
fun check_defs func get_def t =
let     val all_types = split_nested_recursive_set t
        val required = filter (not o is_vartype) (flatten (map (op@ o snd) all_types))
in
        (raise (mkStandardExn func
                ("Can't create function for type " ^ type_to_string t ^ " as this is dependent upon type " ^
                type_to_string (first_e Empty (not o can get_def) required) ^
                " for which no function is returned by get_def"))) handle Empty => ()
end
fun store_funcs name store err [] = ()
  | store_funcs name store err ((t,NONE)::xs) = raise (mkDebugExn err ("Functions were not created for type: " ^ type_to_string t))
  | store_funcs name store err ((t,SOME x)::xs) = (overload_on(name,(fst x)) ; store t x ; store_funcs name store err xs) handle e => wrapException err e;
fun get_source_ind get_func t =
let     val thm = TypeBase.induction_of t
in
        (thm,zip_on_types (fst o dom_rng o type_of) snd
                ((fst o strip_forall o concl) thm) (map (fn t => (get_func t,t))
                        ((map (fst o dom_rng o type_of) o fst o strip_forall o concl) thm)))
end
fun check_const result tm =
        if is_const tm then tm
        else
                fst (valOf (snd (first (fn (_,(SOME (c,_))) =>
                        (fst (dest_const c) = fst (dest_var tm)) andalso
                        (type_of c = type_of tm) | _ => false) result))) handle e => tm
fun fix_ind result (thm,mapping) =
        (thm,map (fn (P,(tm,t)) =>
                (P,(list_mk_comb((check_const result ## I) (strip_comb tm)),t))) mapping)
in
fun mk_source_functions name mk_term get_func conv create_conv t =
let     val get_def = C get_source_function_def name
        fun wrap e = wrapException "mk_source_functions" e
        val _ = check_defs "mk_source_functions" get_def t
        val (mthm,ethm) = mk_split_source_function mk_term get_def get_func conv create_conv t handle e => wrap e
        val ind = get_source_ind get_func t
        val result = complete_function name mk_term (C get_source_function_induction name)
                        get_def get_func conv create_conv (TRUTH,mk_arb alpha) t (mthm,ethm) handle e => wrap e
in
        store_funcs name (fn t => fn (c,d) => add_source_function t name {const = c,definition = d,induction = SOME (fix_ind result ind)})
                "mk_source_functions (store)" result

end
fun mk_coding_functions name mk_term get_func conv create_conv target t =
let     val get_def = C (get_coding_function_def target) name
        fun wrap e = wrapException "mk_coding_functions" e
        val _ = check_defs "mk_coding_functions" get_def t
        val (mthm,ethm) = mk_split_source_function mk_term get_def get_func conv create_conv t handle e => wrap e
        val ind = get_source_ind get_func t
        val dead_thm = #bottom_thm (get_translation_scheme target)
        val dead_value = #bottom (get_translation_scheme target)
        val result = complete_function name mk_term (C (get_coding_function_induction target) name)
                        get_def get_func conv create_conv (dead_thm,dead_value) t (mthm,ethm) handle e => wrap e
in
        store_funcs name (fn t => fn (term,thm) => add_coding_function target t name
                        {const = term,definition = thm,induction = SOME (fix_ind result ind)})
                "mk_coding_functions (store)"
                result
end
fun mk_target_functions name mk_term get_func conv create_conv target t =
let     val get_def = C (get_coding_function_def target) name
        val get_ind = C (get_coding_function_induction target) name
        fun wrap e = wrapException "mk_target_functions" e
        val _ = check_defs "mk_target_functions" get_def t
        val dead_thm = #bottom_thm (get_translation_scheme target)
        val dead_value = #bottom (get_translation_scheme target)
        val ((ithm,mapping,mthm),ethm) = mk_split_target_function mk_term get_def get_func conv create_conv
                                                (get_translation_scheme target) t handle e => wrap e
        val complete_mapping = match_mapping ethm mapping get_func (CONV_RULE conv (get_def (mk_prod(alpha,beta)))) t
        val result = complete_function name mk_term get_ind get_def get_func conv create_conv (dead_thm,dead_value) t (mthm,ethm) handle e => wrap e
in
        store_funcs name (fn t => fn (term,thm) => add_coding_function target t name
                                {const = term,definition = thm,induction = SOME (fix_ind result (ithm,complete_mapping))})
                "mk_target_functions (store)"
                result
end
end


(*****************************************************************************)
(* Function generators                                                       *)
(*****************************************************************************)

fun add_compound_coding_function_generator name mk_term get_func conv create_conv target =
        add_coding_function_generator target name (can TypeBase.constructors_of)
        (fn t =>
                (let    val all_types = split_nested_recursive_set t
                        val required = filter (not o is_vartype) (flatten (map (op@ o snd) all_types))
                        val _ = map (generate_coding_function target name o base_type) required
                in
                        mk_coding_functions name mk_term get_func conv create_conv target t
                end     ;
                        get_coding_function_precise target t name));
fun add_compound_target_function_generator name mk_term get_func conv create_conv target =
        add_coding_function_generator target name (can TypeBase.constructors_of)
        (fn t =>
                (let    val all_types = split_nested_recursive_set t
                        val required = filter (not o is_vartype) (flatten (map (op@ o snd) all_types))
                        val _ = map (generate_coding_function target name o base_type) required
                in
                        mk_target_functions name mk_term get_func conv create_conv target t
                end     ;
                        get_coding_function_precise target t name));
fun add_compound_source_function_generator name mk_term get_func conv create_conv =
        add_source_function_generator name (can TypeBase.constructors_of)
        (fn t =>
                (let    val all_types = split_nested_recursive_set t
                        val required = filter (not o is_vartype) (flatten (map (op@ o snd) all_types))
                        val _ = map (generate_source_function name o base_type) required
                in
                        mk_source_functions name mk_term get_func conv create_conv t
                end     ;
                        get_source_function_precise t name));

(*****************************************************************************)
(* Polytypic inductive proofs about functions                                *)
(*                                                                           *)
(* make_predicate_map thm -> (term * term list) list                         *)
(*     Given an induction theorem returns a mapping from predicates to the   *)
(*     predicates it relies upon.                                            *)
(*                                                                           *)
(* prove_inductive_source_theorem[_precise] : string -> string ->            *)
(*            (hol_type -> term) -> hol_type -> (term -> thm) ->             *)
(*            (hol_type * hol_type list -> thm list -> tactic) -> unit       *)
(* prove_inductive_coding_theorem[_precise] : string -> string ->            *)
(*            (hol_type -> term) -> hol_type -> hol_type -> (term -> thm) -> *)
(*            (hol_type * hol_type list -> thm list -> tactic) -> unit       *)
(*    Given the name of the function the induction is based around, the name *)
(*    of the theorem being proved, a function to generate conclusions, the   *)
(*    main type, a conversion to be applied to the conclusions to make their *)
(*    form induction and a tactic these functions prove the conclusions for  *)
(*    the type given using induction.                                        *)
(*                                                                           *)
(* prove_source_theorem[_precise]                                            *)
(*                      : string -> (hol_type -> term) -> hol_type ->        *)
(*                        (term -> thm) -> (hol_type * hol_type list ->      *)
(*                                          thm list -> tactic) -> unit      *)
(* prove_coding_theorem : string -> (hol_type -> term) -> hol_type ->        *)
(*               hol_type -> (term -> thm) -> (hol_type * hol_type list ->   *)
(*                                          thm list -> tactic) -> unit      *)
(*    Simply prove functions given a function to generate conclusions, a     *)
(*    conversion and a tactic.                                               *)
(*                                                                           *)
(*****************************************************************************)

local
fun mstrip_imp term = if is_imp_only term then (strip_conj ## I) (dest_imp_only term) else ([],term);
in
fun make_predicate_map induction =
let     val predicates = fst (strip_forall (concl induction))
        val mapping1 = (map (uncurry (C pair) o (filter (C mem predicates) o mapfilter rator
                                        ## rator o snd o strip_forall) o
                                mstrip_imp o snd o strip_forall) o strip_conj o fst o
                                dest_imp_only o snd o strip_forall o concl) induction
in
        map (I ## flatten) (bucket_alist mapping1)
end
end

fun delete_matching_types rset t =
        if op_mem (fn a => fn b => can (match_type a) b) t rset then gen_tyvar()
        else if can dest_type t then (mk_type o (I ## map (delete_matching_types rset)) o dest_type) t
        else t

fun all_types t = filter (not o is_vartype) (mk_set (t :: map snd (reachable_graph uncurried_subtypes t)));

fun relevant_types t =
let     val all_types = all_types t
        val rset = map fst (split_nested_recursive_set t)
in
        filter (not o is_vartype) (map (delete_matching_types rset) all_types)
end

local
fun check_concs targ target [] = ()
  | check_concs targ target ((_,(_,(t,thm)))::rest) =
let     val var = type_of (hd (fst (strip_forall (rhs (concl thm)))))
in
        if (not targ andalso (var = t)) orelse (targ andalso (var = target))
                then check_concs targ target rest
                else raise (mkStandardExn "inductive_proof"
                        ("Conclusion returned does not match the form: \"!a" ^
                         type_to_string (if targ then target else t) ^ ".P a\""))
end
fun mk_thm (induction,mapping) mk_conc conv =
let     val all_concs = map (I ## (I ## (fn t => (t,UNDISCH_ALL_EQ (conv (mk_conc t)))))) mapping
        val _ = type_trace 3 ("Conclusions:\n" ^ xlist_to_string
                        (thm_to_string o snd o snd o snd) all_concs ^ "\n")
        val preds = map (rator o snd o strip_forall)
                        ((strip_conj o snd o dest_imp_only o
                                snd o strip_forall o concl) induction)
        val all_types = map (fst o dom_rng o type_of) preds;
        val _ = check_concs (length (mk_set all_types) = 1) (hd (all_types)) all_concs
        val ithm = LIST_MK_CONJ (map (fn p => snd (snd (assoc p all_concs))) preds)
in
        (all_concs,ithm,foldl (fn (a,b) => UNDISCH_ONLY (DISCH a b))
                        (UNDISCH_ONLY (repeat (UNDISCH_ONLY o CONV_RULE
                                        (REWR_CONV (GSYM AND_IMP_INTRO)))
                        (HO_PART_MATCH (snd o dest_imp_only) induction
                                ((rhs o concl) ithm)))) (hyp ithm))
end
fun mkgoal (induction,mapping) mk_conc conv =
let     val (all_concs,ithm,thm) = mk_thm (induction,mapping) mk_conc conv
in
        (proofManagerLib.set_goal (hyp ithm,(lhs o concl) ithm) ;
         proofManagerLib.expand(
                MATCH_MP_TAC (snd (EQ_IMP_RULE ithm)) THEN
                MATCH_MP_TAC (foldl (fn (x,t) =>
                        CONV_RULE (REWR_CONV AND_IMP_INTRO) (DISCH x t))
                                (DISCH (hd (hyp thm)) thm) (tl (hyp thm))) THEN
                REPEAT CONJ_TAC))
end
fun proveit (induction,mapping) mk_conc conv (tactic:hol_type -> tactic) get_theorem =
let     val (all_concs,ithm,thm) = mk_thm (induction,mapping) mk_conc conv
        val _ = type_trace 3
                        ("Instantiated induction theorem: " ^ thm_to_string thm ^ "\n")
        val to_provea = mapfilter ((strip_conj ## I) o dest_imp_only o
                                snd o strip_forall) (hyp thm)
        val to_proveb = map (pair (hyp ithm) o snd o strip_forall) (hyp thm)
        val typed = mapfilter
                (fn tp => ((fst o snd o snd o first_e Empty
                        (can (C match_term (snd (strip_forall (snd tp)))) o snd o
                        strip_forall o rhs o concl o snd o snd o snd)) all_concs,tp))
                (to_provea @ to_proveb)
        val _ = if length typed = length (hyp thm) - length (hyp ithm) then () else
                        raise (mkDebugExn "prove_inductive"
                                ("Some clauses in the instantiated theorem do not match " ^
                                "conclusions generated from the mapping"))

        val proofs = map (fn (t,(assums:term list,goal:term)) =>
                        let     val clause_err = mkStandardExn "prove_inductive_theorem" o
                                        curry op^ ("Could not prove the clause:\n" ^
                                                xpair_to_string (xlist_to_string term_to_string) term_to_string
                                                (assums,goal))
                        in
                                (case (tactic t (assums @ hyp ithm,goal))
                                of ([],func) => foldl (uncurry PROVE_HYP) (func []) (map ASSUME assums)
                                |  (x::xs,func) => raise (clause_err ""))
                                handle e => raise (clause_err ("\nOriginal exception: " ^ exn_to_string e))
                        end) typed

        val sorted = map (fn c => tryfind (C MATCH_IND_TERM c) (hyp thm)) proofs
in
        DISCH_ALL (CONV_RULE (REWR_CONV (GSYM ithm)) (foldr (uncurry PROVE_HYP_CHECK) thm sorted))
end
fun split_theorem thm mk_conc t =
let     val main_types = map fst (split_nested_recursive_set t)
        val conjuncts = CONJUNCTS thm
in
        map (fn t => (t,first (can (match_term (mk_conc t)) o concl) conjuncts)) main_types
end     handle e => wrapException "(split_theorem)" e
in
fun prove_inductive_coding_theorem fname name mk_conc target t conv tactic =
let     val _ = type_trace 1 ("Proving coding theorem: " ^ name ^ " for translation " ^
                        type_to_string target ^ " --> " ^ type_to_string t ^ "\n")
        val (induction,mapping) = get_coding_function_induction target t fname
            handle e => wrapException "prove_inductive_coding_theorem" e
        val tsub = tryfind (C match_type t o snd o snd) mapping
            handle e => wrapException "prove_inductive_coding_theorem" e
        val thm = proveit
                (INST_TYPE tsub induction,map (inst tsub ## (I ## type_subst tsub)) mapping)
                mk_conc conv tactic
                (CONV_RULE conv o C (get_coding_theorem target) name)
                handle e => wrapException "prove_inductive_coding_theorem" e
        val split_types = map (type_subst tsub o snd o snd) mapping
                handle e => wrapException "prove_inductive_coding_theorem" e
        val conjuncts = map DISCH_ALL (CONJUNCTS (UNDISCH_ALL thm))
        val (thms,failed) = mappartition (fn t =>
            (t,first (can (match_term (mk_conc t)) o concl) conjuncts))
            split_types
        val _ = if null failed then () else
            raise (mkStandardExn "prove_inductive_coding_theorem"
                  ("The type: " ^ type_to_string (hd failed) ^
                   "\nwith conclusion: " ^ term_to_string (mk_conc t) ^
                   "\nhas no corresponding theorem in the proved set:\n"
                          ^ xlist_to_string thm_to_string conjuncts))
in
        app (fn (t,thm) => add_coding_theorem_precise target t name thm) thms
        handle e => wrapException "prove_inductive_coding_theorem" e
end
fun inductive_coding_goal fname mk_conc target t (conv:term -> thm) =
let     val (induction,mapping) = get_coding_function_induction target t fname
        val tsub = tryfind (C match_type t o snd o snd) mapping
in
        mkgoal (INST_TYPE tsub induction,map (inst tsub ## (I ## type_subst tsub)) mapping)
                mk_conc conv
end handle e => wrapException "inductive_coding_goal" e
fun prove_inductive_source_theorem fname name mk_conc t conv tactic =
let     val _ = type_trace 1 ("Proving source theorem: " ^ name ^ " for type " ^ type_to_string t ^ "\n")
        val (induction,mapping) = get_source_function_induction t fname
        val tsub = tryfind (C match_type t o snd o snd) mapping
        val thm = proveit
                (INST_TYPE tsub induction,map (inst tsub ## (I ## type_subst tsub)) mapping)
                mk_conc conv tactic
                (CONV_RULE conv o C get_source_theorem name)
        val split_types = map (type_subst tsub o snd o snd) mapping
        val conjuncts = CONJUNCTS thm
        val thms = map (fn t => (t,first (can (match_term (mk_conc t)) o concl) (CONJUNCTS thm))) split_types;
        val (thms,failed) = mappartition (fn t =>
            (t,first (can (match_term (mk_conc t)) o concl) (CONJUNCTS thm)))
            split_types;
        val _ = if null failed then () else
            raise (mkStandardExn "prove_inductive_source_theorem"
                  ("The type: " ^ type_to_string (hd failed) ^
                   "\nwith conclusion: " ^ term_to_string (mk_conc t) ^
                   "\nhas no corresponding theorem in the proved set:\n"
                          ^ xlist_to_string thm_to_string conjuncts))

in
        app (fn (t,thm) => add_source_theorem_precise t name thm) thms
end     handle e => wrapException "prove_inductive_source_theorem" e
fun inductive_source_goal fname mk_conc t (conv:term -> thm) =
let     val (induction,mapping) = get_source_function_induction t fname
        val tsub = tryfind (C match_type t o snd o snd) mapping
in
        mkgoal
        (INST_TYPE tsub induction,map (inst tsub ## (I ## type_subst tsub)) mapping)
        mk_conc conv
end     handle e => wrapException "inductive_source_goal" e
end

fun add_inductive_coding_theorem_generator fname name target conv tactic =
        add_coding_theorem_generator target name (can TypeBase.constructors_of)
        (fn t =>
                (prove_inductive_coding_theorem fname name
                        (fn t => if exists_coding_theorem_conclusion target name
                                        then get_coding_theorem_conclusion target name t
                                        else raise (mkStandardExn ("inductive_coding_proof ("^name^")")
                                                ("The conclusion has not yet been set!")))
                        target t conv tactic ;
                        get_coding_theorem_precise target t name));

fun add_inductive_source_theorem_generator fname name conv tactic =
        add_source_theorem_generator name (can TypeBase.constructors_of)
                (fn t => (prove_inductive_source_theorem fname name
                        (fn t => if exists_source_theorem_conclusion name
                                        then get_source_theorem_conclusion name t
                                        else raise (mkStandardExn ("inductive_source_proof ("^name^")")
                                                ("The conclusion has not yet been set!")))
                                t conv tactic ;
                                get_source_theorem_precise t name));

fun add_tactic_coding_theorem_generator name test (tactic:hol_type -> tactic) target =
        add_coding_theorem_generator target name test
                (fn t => case (tactic t ([],get_coding_theorem_conclusion target name t))
                                of ([],func) => func []
                                |  (x::xs,func) =>
        (raise (mkStandardExn ("tactic_" ^ name ^ " (" ^ type_to_string t ^ ")") "Unsolved goals")))

fun add_tactic_source_theorem_generator name test (tactic:hol_type -> tactic) =
        add_source_theorem_generator name test
                (fn t => case (tactic t ([],get_source_theorem_conclusion name t))
                                of ([],func) => func []
                                |  (x::xs,func) =>
        (raise (mkStandardExn ("tactic_" ^ name ^ " (" ^ type_to_string t ^ ")") "Unsolved goals")))

fun add_rule_coding_theorem_generator name test rule target =
        add_coding_theorem_generator target name test
        (fn t => rule t handle e => wrapException ("rule:" ^ name ^ " (" ^ type_to_string t ^ ")") e);

fun add_rule_source_theorem_generator name test rule =
        add_source_theorem_generator name test
        (fn t => rule t handle e => wrapException ("rule:" ^ name ^ " (" ^ type_to_string t ^ ")") e);

end
