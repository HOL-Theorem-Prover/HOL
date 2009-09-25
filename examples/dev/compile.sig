(*****************************************************************************)
(* Very simple compiler, with programs represented as ML list of HOL         *)
(* definitions.                                                              *)
(*****************************************************************************)

signature compile =
sig

  include Abbrev

(*****************************************************************************)
(* Error reporting function                                                  *)
(*****************************************************************************)
val ERR : string -> string -> exn

(*****************************************************************************)
(* List of definitions (useful for rewriting)                                *)
(*****************************************************************************)
val SimpThms : thm list

(*****************************************************************************)
(* Destruct ``d1 ===> d2`` into (``d1``,``d2``)                              *)
(*****************************************************************************)
val dest_dev_imp : term -> term * term

(*****************************************************************************)
(* An expression is just a HOL term built using expressions defined earlier  *)
(* in a program (see description of programs below) and Seq, Par,            *)
(* Ite and Rec:                                                              *)
(*                                                                           *)
(*  expr := Seq expr expr                                                    *)
(*        | Par expr expr                                                    *)
(*        | Ite expr expr expr                                               *)
(*        | Rec expr expr expr                                               *)
(*                                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Convert_CONV ``\(x1,...,xn). tm[x1,...,xn]`` returns a theorem            *)
(*                                                                           *)
(*  |- (\(x1,...,xn). tm[x1,...,xn]) = p                                     *)
(*                                                                           *)
(* where p is a combinatory expression built from the combinators            *)
(* Seq, Par and Ite. An example is:                                          *)
(*                                                                           *)
(*  - Convert_CONV ``\(x,y). if x < y then y-x else x-y``;                   *)
(* > val it =                                                                *)
(*     |- (\(x,y). (if x < y then y - x else x - y)) =                       *)
(*        Ite (Seq (Par (\(x,y). x) (\(x,y). y)) (UNCURRY $<))               *)
(*            (Seq (Par (\(x,y). y) (\(x,y). x)) (UNCURRY $-))               *)
(*            (Seq (Par (\(x,y). x) (\(x,y). y)) (UNCURRY $-))               *)
(*                                                                           *)
(* Notice that curried operators are uncurried.                              *)
(*                                                                           *)
(*****************************************************************************)

val LET_SEQ_PAR_THM : thm
val SEQ_PAR_I_THM : thm

val Convert_CONV : term -> thm

(*****************************************************************************)
(* Predicate to test whether a term occurs in another term                   *)
(*****************************************************************************)
val occurs_in : term -> term -> bool

(*****************************************************************************)
(* Convert (|- f x = e) returns a theorem                                    *)
(*                                                                           *)
(*  |- f = p                                                                 *)
(*                                                                           *)
(* where p is a combinatory expression built from the combinators Seq, Par   *)
(* and Ite.                                                                  *)
(*****************************************************************************)
val Convert : thm -> thm

(*****************************************************************************)
(* RecConvert (|- f x = if f1 x then f2 x else f(f3 x)) (|- TOTAL(f1,f2,f3)) *)
(* returns a theorem                                                         *)
(*                                                                           *)
(*  |- f = Rec(p1,p2,p3)                                                     *)
(*                                                                           *)
(* where p1, p2 and p3 are combinatory expressions built from the            *)
(* combinators Seq, Par and Ite.                                             *)
(*                                                                           *)
(* For example, given:                                                       *)
(*                                                                           *)
(*  FactIter;                                                                *)
(*  > val it =                                                               *)
(*      |- FactIter (n,acc) =                                                *)
(*         (if n = 0 then (n,acc) else FactIter (n - 1,n * acc))             *)
(*                                                                           *)
(*  - FactIter_TOTAL;                                                        *)
(*  > val it =                                                               *)
(*      |- TOTAL                                                             *)
(*           ((\(n,acc). n = 0),                                             *)
(*            (\(n,acc). (n,acc)),                                           *)
(*            (\(n,acc). (n - 1,n * acc)))                                   *)
(*                                                                           *)
(* then:                                                                     *)
(*                                                                           *)
(*  - RecConvert FactIter FactIter_TOTAL;                                    *)
(* > val it =                                                                *)
(*     |- FactIter =                                                         *)
(*        Rec (Seq (Par (\(n,acc). n) (\(n,acc). 0)) (UNCURRY $=))           *)
(*            (Par (\(n,acc). n) (\(n,acc). acc))                            *)
(*            (Par (Seq (Par (\(n,acc). n) (\(n,acc). 1)) (UNCURRY $-))      *)
(*                (Seq (Par (\(n,acc). n) (\(n,acc). acc)) (UNCURRY $* )))   *)
(*                                                                           *)
(*****************************************************************************)
val RecConvert : thm -> thm -> thm

(*---------------------------------------------------------------------------*)
(* Extract totality predicate of the form TOTAL (f1,f2,f3) for a recursive   *)
(* function of the form f(x) = if f1(x) then f2(x) else f (f3(x))            *)
(*---------------------------------------------------------------------------*)

val total_tm : term

val mk_total : term * term * term -> term
val getTotal : thm -> term



(*****************************************************************************)
(* Check if term tm is a well-formed expression built out of Seq, Par, Ite,  *)
(* Rec or Let. If so return a pair (constructor, args), else return (tm,[])  *)
(*****************************************************************************)
val dest_exp : term -> term * term list

(*****************************************************************************)
(* A combinational term is one that only contains constants declared         *)
(* combinational by having their names included in the assignable list       *)
(* combinational_constants                                                   *)
(*****************************************************************************)
val combinational_constants : string list ref
val add_combinational : string list -> unit
val is_combinational : term -> bool
val is_combinational_const : term -> bool

(*****************************************************************************)
(* CompileExp exp                                                            *)
(* -->                                                                       *)
(* [REC assumption] |- <circuit> ===> DEV exp                                *)
(*****************************************************************************)
val CompileExp : term -> thm

(*****************************************************************************)
(* CompileProg prog tm --> rewrite tm with prog, then compiles the result    *)
(*****************************************************************************)
val CompileProg : thm list -> term -> thm

(*****************************************************************************)
(* Compile (|- f args = bdy) = CompileProg [|- f args = bdy] ``f``           *)
(*****************************************************************************)
val Compile : thm -> thm

(*****************************************************************************)
(*  ``(f = \(x1,x2,...,xn). B)``                                             *)
(*   -->                                                                     *)
(*   |- (f = \(x1,x2,...,xn). B) = !x1 x2 ... xn. f(x1,x2,...,xn) = B        *)
(*****************************************************************************)
val FUN_DEF_CONV : term -> thm
val FUN_DEF_RULE : thm -> thm

(*****************************************************************************)
(* Simp prog thm rewrites thm using definitions in prog                      *)
(*****************************************************************************)
val Simp : thm list -> thm -> thm

(*****************************************************************************)
(* SimpExp prog term expands term using definitions in prog                  *)
(*****************************************************************************)
val SimpExp : thm list -> term -> thm

(*****************************************************************************)
(*            |- TOTAL(f1,f2,f3)                                             *)
(*  -------------------------------------------                              *)
(*  |- TOTAL((\x. f1 x), (\x. f2 x), (\x. f3 x))                             *)
(*****************************************************************************)
val UNPAIR_TOTAL : thm -> thm

(*****************************************************************************)
(* Convert a non-recursive definition to an expression and then compile it   *)
(*****************************************************************************)
val CompileConvert : thm -> thm

(*****************************************************************************)
(* Convert a recursive definition to an expression and then compile it.      *)
(*****************************************************************************)
val RecCompileConvert : thm -> thm -> thm


(*---------------------------------------------------------------------------*)
(* For termination prover.                                                   *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Single entrypoint for definitions where proof of termination will succeed *)
(* Allows measure function to be indicated in same quotation as definition,  *)
(* or not.                                                                   *)
(*                                                                           *)
(*     hwDefine `(eqns) measuring f`                                         *)
(*                                                                           *)
(* will use f as the measure function and attempt automatic termination      *)
(* proof. If successful, returns (|- eqns, |- ind, |- dev)                   *)
(* NB. the recursion equations must be parenthesized; otherwise, strange     *)
(* parse errors result. Also, the name of the defined function must be       *)
(* alphanumeric.                                                             *)
(*                                                                           *)
(* One can also omit the measure function, as in Define:                     *)
(*                                                                           *)
(*     hwDefine `eqns`                                                       *)
(*                                                                           *)
(* which will accept either non-recursive or recursive specifications. It    *)
(* returns a triple (|- eqns, |- ind, |- dev) where the ind theorem should   *)
(* be ignored for now (it will be boolTheory.TRUTH).                         *)
(*                                                                           *)
(* The results of hwDefine are stored in a reference hwDefineLib.            *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

val hwDefineLib : (thm * thm * thm) list ref;
val hwDefine : term frag list -> thm * thm * thm

(*****************************************************************************)
(* Recognisers, destructors and constructors for harware combinatory         *)
(* expressions.                                                              *)
(*****************************************************************************)

(*****************************************************************************)
(* PRECEDE abstract syntax functions                                         *)
(*****************************************************************************)
val   is_PRECEDE : term -> bool
val dest_PRECEDE : term -> term * term
val   mk_PRECEDE : term * term -> term

(*****************************************************************************)
(* FOLLOW abstract syntax functions                                          *)
(*****************************************************************************)
val   is_FOLLOW : term -> bool
val dest_FOLLOW : term -> term * term
val   mk_FOLLOW : term * term -> term

(*****************************************************************************)
(* ATM                                                                       *)
(*****************************************************************************)
val   is_ATM : term -> bool
val dest_ATM : term -> term
val   mk_ATM : term -> term

(*****************************************************************************)
(* SEQ                                                                       *)
(*****************************************************************************)
val   is_SEQ : term -> bool
val dest_SEQ : term -> term * term
val   mk_SEQ : term * term -> term

(*****************************************************************************)
(* PAR                                                                       *)
(*****************************************************************************)
val   is_PAR : term -> bool
val dest_PAR : term -> term * term
val   mk_PAR : term * term -> term

(*****************************************************************************)
(* ITE                                                                       *)
(*****************************************************************************)
val   is_ITE : term -> bool
val dest_ITE : term -> term * term * term
val   mk_ITE : term * term * term -> term

(*****************************************************************************)
(* REC                                                                       *)
(*****************************************************************************)
val   is_REC : term -> bool
val dest_REC : term -> term * term * term
val   mk_REC : term * term * term -> term

(*****************************************************************************)
(* Dev                                                                       *)
(*****************************************************************************)
val   is_DEV : term -> bool
val dest_DEV : term -> term
val   mk_DEV : term -> term

(*****************************************************************************)
(* A refinement function is an ML function that maps a term ``DEV f`` to     *)
(* a theorem                                                                 *)
(*                                                                           *)
(*  |- DEV g ===> DEV f                                                      *)
(*                                                                           *)
(* it is a bit like a conversion, but for device implication (===>)          *)
(* instead of for equality (=)                                               *)
(*****************************************************************************)

(*****************************************************************************)
(* Refine a device to a combinational circuit (i.e. an ATM):                 *)
(*                                                                           *)
(* ATM_REFINE ``DEV f``  =  |- ATM f ===> DEV f : thm                        *)
(*                                                                           *)
(*****************************************************************************)
val ATM_REFINE : term -> thm

(*****************************************************************************)
(* LIB_REFINE                                                                *)
(*  [|- <circuit> ===> DEV f1,                                               *)
(*   |- <circuit> ===> DEV f2                                                *)
(*   ...                                                                     *)
(*   |- <circuit> ===> DEV fn]                                               *)
(*  ``DEV fi``                                                               *)
(*                                                                           *)
(* returns the first theorem <circuit> ===> DEV fi                           *)
(* that it finds in the supplied list (i.e. library).                        *)
(* Fails if no refining theorem found.                                       *)
(*****************************************************************************)
val LIB_REFINE : thm list -> term -> thm

(*****************************************************************************)
(* DEPTHR refine tm scans through a combinatory expression tm built          *)
(* from ATM, SEQ, PAR, ITE, REC and DEV and applies the refine to all        *)
(* arguments of DEV using                                                    *)
(*                                                                           *)
(*  |- !P1 P2 Q1 Q2. P1 ===> Q1 /\ P2 ===> Q2 ==> P1 ;; P2 ===> Q1 ;; Q2     *)
(*                                                                           *)
(*  |- !P1 P2 Q1 Q2. P1 ===> Q1 /\ P2 ===> Q2 ==> P1 || P2 ===> Q1 || Q2     *)
(*                                                                           *)
(*  |- !P1 P2 Q1 Q2.                                                         *)
(*       P1 ===> Q1 /\ P2 ===> Q2 /\ P3 ===> Q3 ==>                          *)
(*       ITE P1 P2 P3 ===> ITE Q1 Q2 Q3                                      *)
(*                                                                           *)
(*  |- !P1 P2 Q1 Q2.                                                         *)
(*       P1 ===> Q1 /\ P2 ===> Q2 /\ P3 ===> Q3 ==>                          *)
(*       REC P1 P2 P3 ===> REC Q1 Q2 Q3                                      *)
(*                                                                           *)
(* to generate a theorem                                                     *)
(*                                                                           *)
(*  |- tm' ===> tm                                                           *)
(*                                                                           *)
(* (if refine fails, then no action is taken, i.e. |- tm ===> tm used)       *)
(*****************************************************************************)
val DEPTHR : (term -> thm) -> term -> thm

(*****************************************************************************)
(* REFINE refine (|- <circuit> ===> Dev f) applies refine to <circuit>       *)
(* to generate                                                               *)
(*                                                                           *)
(*  |- <circuit'> ===> <circuit>                                             *)
(*                                                                           *)
(* and then uses transitivity of ===> to deduce                              *)
(*                                                                           *)
(*  |- <circuit'> ===> Dev f                                                 *)
(*****************************************************************************)
val REFINE : (term -> thm) -> thm -> thm

(*****************************************************************************)
(* Naively implemented refinement combinators                                *)
(*****************************************************************************)

(*****************************************************************************)
(*    |- t2 ===> t1                                                          *)
(*   --------------- refine t2 = |- t3 ===> t2                               *)
(*    |- t3 ===> t1                                                          *)
(*****************************************************************************)
val ANTE_REFINE : thm -> (term -> thm) -> thm

(*****************************************************************************)
(* Apply two refinements in succession;  fail if either does.                *)
(*****************************************************************************)
(*infixr 3 THENR;*)
val 'a THENR : ('a -> thm) * (term -> thm) -> 'a -> thm

(*****************************************************************************)
(* Apply refine1;  if it raises a HOL_ERR then apply refine2. Note that      *)
(* interrupts and other exceptions will sail on through.                     *)
(*****************************************************************************)
(*infixr 3 ORELSER;*)
val ('a, 'b) ORELSER : ('a -> 'b) * ('a -> 'b) -> 'a -> 'b

(*****************************************************************************)
(* Identity refinement    tm --> |- tm ===> tm                               *)
(*****************************************************************************)
val ALL_REFINE : term -> thm

(*****************************************************************************)
(* Repeat refine until no change                                             *)
(*****************************************************************************)
val REPEATR : (term -> thm) -> term -> thm

(*****************************************************************************)
(* Refine using hwDefineLib and then convert all remaining DEVs to ATMs      *)
(*****************************************************************************)
val REFINE_ALL : thm -> thm

(*****************************************************************************)
(* Some ancient code for normalising circuits (will need to be updated!)     *)
(*****************************************************************************)

(*****************************************************************************)
(* LIST_EXISTS_ALPHA_CONV s n ``?a b c ...`` =                               *)
(*  |- (?a b c ...) = ?sn sn+1 sn+2 ...                                      *)
(*****************************************************************************)
val LIST_EXISTS_ALPHA_CONV : string -> int -> term -> thm

(*****************************************************************************)
(* Standardise apart all quantified variables to ``v0``, ``v1``, ...         *)
(* where "v" is given as an argument                                         *)
(*****************************************************************************)
val OLD_STANDARDIZE_EXISTS_CONV : string -> term -> thm

(*---------------------------------------------------------------------------*)
(* A faster version of STANDARDIZE_EXISTS_CONV.                              *)
(*---------------------------------------------------------------------------*)
val STANDARDIZE_EXISTS_CONV : string -> term -> thm


(*****************************************************************************)
(* Hoist all existential quantifiers to the outside                          *)
(*                                                                           *)
(*   (?x. A) /\ B --> ?x. A /\ B  (check x not free in B)                    *)
(*   A /\ (?x. B) --> ?x. A /\ B  (check x not free in A)                    *)
(*                                                                           *)
(* returns a pair consisting of a list of existentially quantified vars      *)
(* and a list of conjuncts                                                   *)
(*****************************************************************************)
val EXISTS_OUT : term -> term list * term list

(*****************************************************************************)
(* PRUNE1_FUN(v,[t1,...,tp,v=u,tq,...,tn]) or                                *)
(* PRUNE1_FUN(v,[t1,...,tp,u=v,tq,...,tn])                                   *)
(* returns [t1[u/v],...,tp[u/v],tq[u/v],...,tn[u/v]]                         *)
(* has no effect if there is no equation ``v=u`` of ``u=v`` in the list      *)
(*****************************************************************************)
val PRUNE1_FUN : term * term list -> term list

val EXISTS_OUT_CONV : term -> thm

(*****************************************************************************)
(* BUS_CONCAT abstract syntax functions                                      *)
(*****************************************************************************)
val is_BUS_CONCAT : term -> bool
val dest_BUS_CONCAT : term -> term * term
val mk_BUS_CONCAT : term * term -> term

(*****************************************************************************)
(* Match a varstruct with a bus. For example:                                *)
(*                                                                           *)
(* BUS_MATCH ``(m,n,acc)`` ``v102 <> v101 <> v100``                          *)
(* -->                                                                       *)
(* [(``m``,``v102``), (``n``,``v101``), (``acc``, ``v100``)]                 *)
(*                                                                           *)
(*                                                                           *)
(* BUS_MATCH ``(p1 - 1,p1',p1' + p2)`` ``v165 <> v164 <> v163``              *)
(* -->                                                                       *)
(* [(``p1 - 1``,``v165``), (``p1'``,``v164``),(``p1' + p2``,``v163``)        *)
(*****************************************************************************)
val BUS_MATCH : term -> term -> (term * term) list

(*****************************************************************************)
(* Convert a varstruct to a matching bus                                     *)
(* Example: varstruct_to_bus ty ``(v1,(v2,v3),v4)`` = ``v1<>(v2<>v3)<>v4``   *)
(* (where types are lifted to functions from domain ty)                      *)
(*****************************************************************************)
val varstruct_to_bus : hol_type -> term -> term

(*****************************************************************************)
(* A pure abstraction has the form ``\<varstruct>. <body>`` where            *)
(* <body> is built out of variables in <varstruct> and combinational         *)
(* constants using pairing.                                                  *)
(*****************************************************************************)
val is_pure_abs : term -> bool

(*****************************************************************************)
(* Generate a bus made of fresh variables from the type of a term            *)
(*****************************************************************************)
val genbus : hol_type -> term -> term * term list

(*****************************************************************************)
(* Synthesise combinational circuits.                                        *)
(* Examples (derived from FactScript.sml):                                   *)
(*                                                                           *)
(*  COMB (\(m,n,acc). m) (v102 <> v101 <> v100, v134)                        *)
(*  -->                                                                      *)
(*  (v134 = v102)                                                            *)
(*                                                                           *)
(*  COMB (\(m,n,p). op <term>) (v102 <> v101 <> v100, v134)                  *)
(*  -->                                                                      *)
(*  ?v. COMB(\(m,n,p). <term>)(v102 <> v101 <> v100,v) /\ COMB op (v,v134)   *)
(*                                                                           *)
(*  COMB (\(m,n,p). (op <term1>) <term2>) (v102 <> v101 <> v100, v134)       *)
(*  -->                                                                      *)
(*  ?v1 v2. COMB(\(m,n,p). <term1>)(v102 <> v101 <> v100,v1) /\              *)
(*          COMB(\(m,n,p). <term2>)(v102 <> v101 <> v100,v2) /\              *)
(*          COMB (UNCURRY op) (v1 <> v2,v134)                                *)
(*                                                                           *)
(*  COMB (\(m,n,p). (<term1>, <term2>) (v102 <> v101 <> v100, v134 <> v135)  *)
(*  -->                                                                      *)
(*  ?v1 v2. COMB(\(m,n,p). <term1>)(v102 <> v101 <> v100,v1) /\              *)
(*          COMB(\(m,n,p). <term2>)(v102 <> v101 <> v100,v2) /\              *)
(*          (v134 = v1) /\ (v135 = v2)                                       *)
(*                                                                           *)
(*  COMB (\(p1,p1',p2). (p1 - 1,p1',p1' + p2))                               *)
(*       (v109 <> v108 <> v107, v165 <> v164 <> v163)                        *)
(*  -->                                                                      *)
(*  (?v. (CONSTANT 1 v /\ COMB (UNCURRY $-) (v109 <> v, v165)) /\            *)
(*  (v164 = v108) /\                                                         *)
(*  COMB (UNCURRY $+) (v108 <> v107, v163)                                   *)
(*****************************************************************************)
val comb_synth_goalref : term ref
val if_print_flag : bool ref
val if_print : string -> unit
val if_print_term : term -> unit

val COMB_SYNTH_CONV : term -> thm

(*****************************************************************************)
(* If                                                                        *)
(*                                                                           *)
(*   f tm --> |- tm' ==> tm                                                  *)
(*                                                                           *)
(* then DEPTH_IMP f tm descends recursively through existential              *)
(* quantifications and conjunctions applying f (or tm --> |- tm ==> tm) if   *)
(* f fails) and returning |- tm' ==> tm for some term tm'                    *)
(*                                                                           *)
(*****************************************************************************)
val DEPTH_IMP : (term -> thm) -> term -> thm

(*****************************************************************************)
(* AP_ANTE_IMP_TRANS f (|- t1 ==> t2) applies f to t1 to get |- t0 ==> t1    *)
(* and then, using transitivity of ==>, returns |- t0 ==> t2                 *)
(*****************************************************************************)
val AP_ANTE_IMP_TRANS : (term -> thm) -> thm -> thm

(*****************************************************************************)
(* DEV_IMP f (|- tm ==> d) applies f to tm to generate an implication        *)
(* |- tm' ==> tm and then returns |- tm' ==> d                               *)
(*****************************************************************************)
val DEV_IMP : (term -> thm) -> thm -> thm

(*****************************************************************************)
(* DFF_IMP_INTRO ``DFF p`` --> |- DFF_IMP p => DFF p                         *)
(*****************************************************************************)
val DFF_IMP_INTRO : term -> thm

(*****************************************************************************)
(* Test is a term is of the from ``s1 at p``                                 *)
(*****************************************************************************)
val is_at : term -> bool

(*****************************************************************************)
(* IMP_REFINE (|- tm1 ==> tm2) tm matches tm2 to tm and if a substitution    *)
(* sub is found such that sub tm2 = tm then |- sub tm1 ==> sub tm2 is        *)
(* returned; if the match fails IMP_REFINE_Fail is raised.                   *)
(*****************************************************************************)
exception IMP_REFINE_Fail
val IMP_REFINE : thm -> term -> thm

(*****************************************************************************)
(* IMP_REFINEL [th1,...,thn] tm applies IMP_REFINE th1,...,IMP_REFINE thn    *)
(* to tm in turn until one succeeds.  If none succeeds then |- tm => tm      *)
(* is returned. Never fails.                                                 *)
(*****************************************************************************)
val IMP_REFINEL : thm list -> term -> thm

(*****************************************************************************)
(*               |- !s1 ... sn. P s1 ... sn                                  *)
(*  ------------------------------------------------------- at_SPECL ``clk`` *)
(*  ([``s1``,...,``sn``], |- P (s1 at clk) ... (sn at clk))                  *)
(*****************************************************************************)
val at_SPEC_ALL : term -> thm -> term list * thm

(*****************************************************************************)
(*      |- P ==> Q                                                           *)
(*   ---------------- (x not free in Q)                                      *)
(*   |- (?x. P) ==> Q                                                        *)
(*****************************************************************************)
val ANTE_EXISTS_INTRO : term -> thm -> thm
val LIST_ANTE_EXISTS_INTRO : term list * thm -> thm

(*****************************************************************************)
(* ``: ty1 # ... # tyn`` --> [`:ty```, ..., :``tyn``]                        *)
(*****************************************************************************)
val strip_prodtype : hol_type -> hol_type list

(*****************************************************************************)
(* mapcount f [x1,...,xn] = [f 1 x1, ..., f n xn]                            *)
(*****************************************************************************)
val ('a, 'b) mapcount : (int -> 'a -> 'b) -> 'a list -> 'b list

(*****************************************************************************)
(* ``s : ty -> ty1#...#tyn``  -->  ``(s1:ty->ty1) <> ... <> (sn:ty->tyn)``   *)
(*****************************************************************************)
val bus_split : term -> term

(*****************************************************************************)
(*                  |- Cir ===> DEV f                                        *)
(*  ------------------------------------------------------                   *)
(*  |- Cir (load,(inp1<>...<>inpm),done,(out1<>...<>outn))                   *)
(*     ==>                                                                   *)
(*     DEV f (load,(inp1<>...<>inpm),done,(out1<>...<>outn))                 *)
(*****************************************************************************)
val IN_OUT_SPLIT : thm -> thm

(*****************************************************************************)
(* User modifiable library of combinational components.                      *)
(*****************************************************************************)
val combinational_components : thm list ref
val add_combinational_components : thm list -> unit

(*---------------------------------------------------------------------------*)
(* Building netlists                                                         *)
(*---------------------------------------------------------------------------*)
val monitor_netlist_construction : bool ref
val ('a, 'b) ptime : string -> ('a -> 'b) -> 'a -> 'b
val comb_tm : term
val CIRC_CONV : (term -> thm) -> term -> thm
val CIRC_RULE : (term -> thm) -> thm -> thm
val COMB_FN_CONV : (term -> thm) -> term -> thm
val variants : term list -> term list -> term list
val is_prod : hol_type -> bool
val bus_concat_tm : term
val mk_bus_concat : term * term -> term
val dest_bus_concat : term -> term * term
val bus_concat_of : hol_type -> term list -> term * term list

(*---------------------------------------------------------------------------*)
(* STEP 4                                                                    *)
(*---------------------------------------------------------------------------*)
val FUN_EXISTS_PROD_CONV : term -> thm
val OLD_STEP4a : thm -> thm
val STEP4a : thm -> thm
val STEP4b : thm -> thm
val STEP4c : thm -> thm
val STEP4d : thm -> thm
val STEP4e : thm -> thm
val STEP4f : thm -> thm
val STEP4 : thm -> thm

(*---------------------------------------------------------------------------*)
(* STEP 5 applies theorem                                                    *)
(*                                                                           *)
(*  BUS_CONCAT_ELIM = |- (\x1. P1 x1) <> (\x2. P2 x2) = (\x. (P1 x,P2 x))    *)
(*                                                                           *)
(* Contorted code because of efficiency hacks.                               *)
(*---------------------------------------------------------------------------*)
val LAMBDA_CONCAT_CONV : term -> thm
val STEP5_CONV : term -> thm

(*---------------------------------------------------------------------------*)
(* Translate a DEV into a netlist                                            *)
(*---------------------------------------------------------------------------*)
val MAKE_NETLIST : thm -> thm


(*****************************************************************************)
(* User modifiable list of Melham-style temporal abstraction theorem         *)
(*****************************************************************************)
val temporal_abstractions : thm list ref
val add_temporal_abstractions : thm list -> unit

(*****************************************************************************)
(* Compile a device implementation into a clocked circuit represented in HOL *)
(*****************************************************************************)
val MAKE_CIRCUIT : thm -> thm
val EXISTSL_CONV : term -> thm
val NEW_MAKE_CIRCUIT : thm -> thm
val NEW_MAKE_CIRCUIT' : thm -> thm
val NEW_MAKE_CIRCUIT'' : thm -> thm

(*****************************************************************************)
(* Expand occurrences of component names into their definitions              *)
(*****************************************************************************)
val EXPAND_COMPONENTS : thm -> thm

(*****************************************************************************)
(* Invoke hwDefine and then apply MAKE_CIRCUIT, EXPAND_COMPONENTS and        *)
(* REFINE_ALL to the device                                                  *)
(*****************************************************************************)
val cirDefine : term frag list -> thm * thm * thm
val newcirDefine : term frag list -> thm * thm * thm

(*---------------------------------------------------------------------------*)
(* Don't go all the way to circuits. Instead stop at netlists built from     *)
(* COMB, CONSTANT, DEL and DELT.                                             *)
(*---------------------------------------------------------------------------*)
val netDefine : term frag list -> thm * thm * thm

end (* sig *)
