structure acl2encodeLib :> acl2encodeLib =
struct

(*****************************************************************************)
(* Used to encode functions from HOL to ACL2                                 *)
(*****************************************************************************)

open Lib Parse Type Term Drule Thm Tactical bossLib
open Rewrite polytypicLib encodeLib functionEncodeLib
open translateTheory extendTranslateTheory wordsLib intLib

(*
app load ["intLib","wordsLib","extendTranslateTheory","functionEncodeLib"];
*)

(*****************************************************************************)
(* Abbreviations for types to avoid parsing later...                         *)
(*****************************************************************************)

val num = ``:num``;
val int = ``:int``;
val rat = ``:rat``;
val com = ``:complex_rational``;
val bool = ``:bool``;
val char = ``:char``;
val string = ``:string``;
val pair = ``:'a # 'b``;
val list = ``:'a list``;
val sexp = ``:sexp``;
val fcp = ``:'a ** 'b``;
val word = ``:'a word``;

(*****************************************************************************)
(* A rule to generate the theorem: |- X o I = X   for some X                 *)
(*****************************************************************************)

fun simple_encode_map_encode tm = CONJUNCT2 (ISPEC tm combinTheory.I_o_ID);

fun simple_map_compose t =
    CONJUNCT1 (ISPEC (mk_const("I",t --> t)) combinTheory.I_o_ID);

(*****************************************************************************)
(* Some required theorems and functions for which the whole package is       *)
(* uneccessary.                                                              *)
(*****************************************************************************)

val GSYM = Conv.GSYM;
val I_THM = combinTheory.I_THM;
val K_THM = combinTheory.K_THM;

(*****************************************************************************)
(* Keeping track of whats in ..                                              *)
(*****************************************************************************)

exception ExistsAlready;

val performed = ref ([]:string list);

fun perform string =
    if Lib.mem string (!performed) then raise ExistsAlready
       else (performed := string :: (!performed));

fun tryperform string =
    if Lib.mem string (!performed) then raise ExistsAlready else ();

(*****************************************************************************)
(* Add the type-translation theorems for natural numbers                     *)
(*****************************************************************************)

fun add_num_translations () =
let val _ = perform "add_num_translations"
    val _ = add_translation sexp num
    val _ = add_coding_function sexp num "encode"
	{const = ``nat``,definition = sexpTheory.nat_def,induction = NONE};
    val _ = add_coding_function sexp num "decode"
	{const = ``sexp_to_nat``,definition = translateTheory.sexp_to_nat_def,
	 induction = NONE};
    val _ = add_coding_function sexp num "detect"
	{const = ``sexp_to_bool o natp``,
         definition = hol_defaxiomsTheory.natp_def,
	 induction = NONE};

    val _ = add_source_function num "map"
	{const = ``I``,definition = I_THM,induction = NONE};
    val _ = add_source_function num "all"
	{const = ``K T``,definition = K_THM,induction = NONE};
    val _ = add_coding_function sexp num "fix"
	{const = ``nfix``,definition = hol_defaxiomsTheory.nfix_def,
	 induction = NONE};

    val _ = add_coding_theorem sexp num "encode_decode_map"
    	    translateTheory.ENCDECMAP_NAT;
    val _ = add_coding_theorem sexp num "encode_detect_all"
    	    translateTheory.ENCDETALL_NAT;
    val _ = add_coding_theorem sexp num "decode_encode_fix"
    	    translateTheory.DECENCFIX_NAT;
    val _ = add_coding_theorem sexp num "encode_map_encode"
    	    (simple_encode_map_encode ``nat``)
    val _ = add_coding_theorem sexp num "fix_id"
    	    translateTheory.FIXID_NAT;
    val _ = add_source_theorem sexp "map_compose" (simple_map_compose sexp);
    val _ = add_source_theorem num "map_compose" (simple_map_compose num);

    val _ = add_coding_theorem sexp num "detect_dead"
    	    translateTheory.DETDEAD_NAT;
    val _ = add_coding_theorem sexp num "general_detect"
    	    (DECIDE ``!x. (sexp_to_bool o natp) x ==>
	    	    	  (sexp_to_bool o natp) x``)
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Add the type-translation theorems for integers                            *)
(*****************************************************************************)

fun add_int_translations () =
let val _ = perform "add_int_translations"
    val _ = add_translation sexp int
    val _ = add_coding_function sexp int "encode"
	{const = ``int``,definition = sexpTheory.int_def,induction = NONE};
    val _ = add_coding_function sexp int "decode"
	{const = ``sexp_to_int``,definition = translateTheory.sexp_to_int_def,
	 induction = NONE};
    val _ = add_coding_function sexp int "detect"
	{const = ``sexp_to_bool o integerp``,
         definition = sexpTheory.integerp_def,
	 induction = NONE};

    val _ = add_source_function int "map"
	{const = ``I``,definition = I_THM,induction = NONE};
    val _ = add_source_function int "all"
	{const = ``K T``,definition = K_THM,induction = NONE};
    val _ = add_coding_function sexp int "fix"
	{const = ``ifix``,definition = hol_defaxiomsTheory.ifix_def,
	 induction = NONE};

    val _ = add_coding_theorem sexp int "encode_decode_map"
    	    translateTheory.ENCDECMAP_INT;
    val _ = add_coding_theorem sexp int "encode_detect_all"
    	    translateTheory.ENCDETALL_INT;
    val _ = add_coding_theorem sexp int "decode_encode_fix"
    	    translateTheory.DECENCFIX_INT;
    val _ = add_coding_theorem sexp int "encode_map_encode"
    	    (simple_encode_map_encode ``int``)
    val _ = add_coding_theorem sexp int "fix_id"
    	    translateTheory.FIXID_INT;
    val _ = add_source_theorem int "map_compose" (simple_map_compose int);

    val _ = add_coding_theorem sexp int "detect_dead"
    	    translateTheory.DETDEAD_INT;
    val _ = add_coding_theorem sexp int "general_detect"
    	    (DECIDE ``!x. (sexp_to_bool o integerp) x ==>
	    	    	  (sexp_to_bool o integerp) x``)
    val _ = set_bottom_value int ``0i``
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Add the type-translation theorems for booleans                            *)
(*****************************************************************************)

fun add_bool_translations () =
let val _ = perform "add_bool_translations"
    val _ = add_translation sexp bool
    val _ = add_coding_function sexp bool "encode"
	{const = ``bool``,definition = translateTheory.bool_def,
	 induction = NONE};
    val _ = add_coding_function sexp bool "decode"
	{const = ``sexp_to_bool``,definition = translateTheory.sexp_to_bool_def,
	 induction = NONE};
    val _ = add_coding_function sexp bool "detect"
	{const = ``sexp_to_bool o booleanp``,
         definition = hol_defaxiomsTheory.booleanp_def,
	 induction = NONE};

    val _ = add_source_function bool "map"
	{const = ``I``,definition = I_THM,induction = NONE};
    val _ = add_source_function bool "all"
	{const = ``K T``,definition = K_THM,induction = NONE};
    val _ = add_coding_function sexp bool "fix"
	{const = ``fix_bool``,definition = translateTheory.fix_bool_def,
	 induction = NONE};

    val _ = add_coding_theorem sexp bool "encode_decode_map"
    	    translateTheory.ENCDECMAP_BOOL;
    val _ = add_coding_theorem sexp bool "encode_detect_all"
    	    translateTheory.ENCDETALL_BOOL;
    val _ = add_coding_theorem sexp bool "decode_encode_fix"
    	    translateTheory.DECENCFIX_BOOL;
    val _ = add_coding_theorem sexp bool "encode_map_encode"
    	    (simple_encode_map_encode ``bool``)
    val _ = add_coding_theorem sexp bool "fix_id"
    	    translateTheory.FIXID_BOOL;
    val _ = add_source_theorem bool "map_compose" (simple_map_compose bool);

    val _ = add_coding_theorem sexp bool "detect_dead"
    	    translateTheory.DETDEAD_BOOL;
    val _ = add_coding_theorem sexp bool "general_detect"
    	    (DECIDE ``!x. (sexp_to_bool o booleanp) x ==>
	    	    	  (sexp_to_bool o booleanp) x``)
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Add the type-translation theorems for rational numbers                    *)
(*****************************************************************************)

fun add_rat_translations () =
let val _ = perform "add_rat_translations"
    val _ = add_translation sexp rat
    val _ = add_coding_function sexp rat "encode"
	{const = ``rat``,definition = sexpTheory.rat_def,induction = NONE};
    val _ = add_coding_function sexp rat "decode"
	{const = ``sexp_to_rat``,definition = translateTheory.sexp_to_rat_def,
	 induction = NONE};
    val _ = add_coding_function sexp rat "detect"
	{const = ``sexp_to_bool o rationalp``,
         definition = sexpTheory.rationalp_def,
	 induction = NONE};

    val _ = add_source_function rat "map"
	{const = ``I``,definition = I_THM,induction = NONE};
    val _ = add_source_function rat "all"
	{const = ``K T``,definition = K_THM,induction = NONE};
    val _ = add_coding_function sexp rat "fix"
	{const = ``fix_rat``,definition = translateTheory.fix_rat_def,
	 induction = NONE};

    val _ = add_coding_theorem sexp rat "encode_decode_map"
    	    translateTheory.ENCDECMAP_RAT;
    val _ = add_coding_theorem sexp rat "encode_detect_all"
    	    translateTheory.ENCDETALL_RAT;
    val _ = add_coding_theorem sexp rat "decode_encode_fix"
    	    translateTheory.DECENCFIX_RAT;
    val _ = add_coding_theorem sexp rat "encode_map_encode"
    	    (simple_encode_map_encode ``rat``)
    val _ = add_coding_theorem sexp rat "fix_id"
    	    translateTheory.FIXID_RAT;
    val _ = add_source_theorem rat "map_compose" (simple_map_compose rat);

    val _ = add_coding_theorem sexp rat "detect_dead"
    	    translateTheory.DETDEAD_RAT;
    val _ = add_coding_theorem sexp rat "general_detect"
    	    (DECIDE ``!x. (sexp_to_bool o rationalp) x ==>
	    	    	  (sexp_to_bool o rationalp) x``)
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Add the type-translation theorems for products                            *)
(*****************************************************************************)

fun add_product_translations () =
let val _ = perform "add_product_translations"
    val _ = add_translation sexp pair
    val _ = add_coding_function sexp pair "encode"
		{const = ``pair``,
		 definition = translateTheory.pair_thm,
                 induction = NONE};
    val _ = add_coding_function sexp pair "decode"
		{const = ``sexp_to_pair``,
		 definition = translateTheory.sexp_to_pair_def,
		 induction = NONE};
    val _ = add_coding_function sexp pair "detect"
	      	{const = ``pairp``,
		 definition = translateTheory.pairp_def,
		 induction = NONE};
    val _ = add_source_function pair "map"
	        {const = ``$##``,
		 definition = pairTheory.PAIR_MAP_THM,
		 induction = NONE};
    val _ = add_source_function pair "all"
	      {const = ``all_pair``,
	       definition = translateTheory.all_pair_def,
	       induction = NONE};
    val _ = add_coding_function sexp pair "fix"
	      {const = ``fix_pair``,definition = translateTheory.fix_pair_def,
	       induction = NONE};

    val _ = add_coding_theorem sexp pair "encode_decode_map"
    	    translateTheory.ENCDECMAP_PAIR;
    val _ = add_coding_theorem sexp pair "encode_detect_all"
    	    translateTheory.ENCDETALL_PAIR;
    val _ = add_coding_theorem sexp pair "decode_encode_fix"
    	    translateTheory.DECENCFIX_PAIR;
    val _ = add_coding_theorem sexp pair "encode_map_encode"
    	    translateTheory.ENCMAPENC_PAIR;

    val _ = add_coding_theorem sexp pair "fix_id"
    	    translateTheory.FIXID_PAIR;
    val _ = add_source_theorem pair "map_id"
    	    quotient_pairTheory.PAIR_MAP_I;
    val _ = add_source_theorem pair "all_id"
    	    translateTheory.ALLID_PAIR;

    val _ = add_source_theorem pair "map_compose"
    	    (prove(``(a ## b) o (c ## d) = ((a o c) ## (b o d))``,
	         REWRITE_TAC [boolTheory.FUN_EQ_THM] THEN Cases THEN
	         REWRITE_TAC [pairTheory.PAIR_MAP_THM,combinTheory.o_THM]));

    val _ = add_coding_theorem sexp pair "detect_dead"
    	    translateTheory.DETDEAD_PAIR;
    val _ = add_coding_theorem sexp pair "general_detect"
    	    translateTheory.GENERAL_DETECT_PAIR;
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Add the type translations for lists.                                      *)
(*****************************************************************************)

val list_ind = translateTheory.sexp_list_ind;

val decode_list_ind =
    (list_ind,[(``P0:sexp -> bool``,(``sexp_to_list f``,list)),
    	       (``P1:sexp -> bool``,(``sexp_to_pair f (sexp_to_list f)``,
	       		     			    ``:'a # 'a list``))]);
val detect_list_ind =
    (list_ind,[(``P0:sexp -> bool``,(``listp f``,list)),
    	       (``P1:sexp -> bool``,(``pairp f (listp f)``,
	       		     		       ``:'a # 'a list``))]);
val fix_list_ind =
    (list_ind,[(``P0:sexp -> bool``,(``fix_list f``,list)),
               (``P1:sexp -> bool``,(``fix_pair f (fix_list f)``,
	       		     			``:'a # 'a list``))]);

val encode_list_ind =
    (TypeBase.induction_of list,
    [(``P:'a list -> bool``,(``list f``,list))]);
val map_list_ind =
    (TypeBase.induction_of list,
    [(``P:'a list -> bool``,(``MAP f``,list))]);
val every_list_ind =
    (TypeBase.induction_of list,
    [(``P:'a list -> bool``,(``EVERY f``,list))]);

fun add_list_translations () =
let val _ = perform "add_list_translations"
    val _ = add_translation sexp list
    val _ = add_coding_function sexp list "encode"
		{const = ``list``,
		 definition = translateTheory.list_thm,
                 induction = SOME encode_list_ind};
    val _ = add_coding_function sexp list "decode"
		{const = ``sexp_to_list``,
		 definition = translateTheory.sexp_to_list_thm,
		 induction = SOME decode_list_ind};
    val _ = add_coding_function sexp list "detect"
	      	{const = ``listp``,
		 definition = translateTheory.listp_thm,
		 induction = SOME detect_list_ind};
    val _ = add_source_function list "map"
	        {const = ``MAP``,
		 definition = listTheory.MAP,
		 induction = SOME map_list_ind};
    val _ = add_source_function list "all"
	      {const = ``EVERY``,
	       definition = listTheory.EVERY_DEF,
	       induction = SOME every_list_ind};
    val _ = add_coding_function sexp list "fix"
	      {const = ``fix_list``,
	       definition = translateTheory.fix_list_thm,
	       induction = SOME fix_list_ind};

    val _ = add_coding_theorem sexp list "encode_decode_map"
    	    translateTheory.ENCDECMAP_LIST;
    val _ = add_coding_theorem sexp list "encode_detect_all"
    	    translateTheory.ENCDETALL_LIST;
    val _ = add_coding_theorem sexp list "decode_encode_fix"
    	    translateTheory.DECENCFIX_LIST;
    val _ = add_coding_theorem sexp list "encode_map_encode"
    	    translateTheory.ENCMAPENC_LIST;

    val _ = add_coding_theorem sexp list "fix_id"
    	    translateTheory.FIXID_LIST;
    val _ = add_source_theorem list "map_id"
    	    quotient_listTheory.LIST_MAP_I;
    val _ = add_source_theorem list "all_id"
    	    translateTheory.ALLID_LIST;

    val _ = add_source_theorem list "map_compose"
    	    (GSYM rich_listTheory.MAP_o);

    val _ = add_coding_theorem sexp list "detect_dead"
    	    translateTheory.DETDEAD_LIST;
    val _ = add_coding_theorem sexp list "general_detect"
    	    translateTheory.GENERAL_DETECT_LIST;
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Add the translations for FCPs                                             *)
(*****************************************************************************)

fun add_fcp_translations () =
let val _ = perform "add_fcp_translations"
    val _ = add_translation sexp fcp
    val _ = add_coding_function sexp fcp "encode"
	{const = ``fcp_encode``,
	 definition = extendTranslateTheory.fcp_encode_def,
	 induction = NONE};
    val _ = add_coding_function sexp fcp "decode"
	{const = ``fcp_decode``,
	 definition = extendTranslateTheory.fcp_decode_def,
	 induction = NONE};
    val _ = add_coding_function sexp fcp "detect"
	{const = ``fcp_detect : (sexp -> bool) -> 'b itself -> sexp -> bool``,
         definition = extendTranslateTheory.fcp_detect_def,
	 induction = NONE};

    val _ = add_source_function fcp "map"
	{const = ``FCP_MAP : ('a -> 'c) -> 'a ** 'b -> 'c ** 'b``,
	 definition = fcpTheory.FCP_MAP,induction = NONE};
    val _ = add_source_function fcp "all"
	{const = ``FCP_EVERY : ('a -> bool) -> 'a ** 'b -> bool``,
	 definition = fcpTheory.FCP_EVERY,induction = NONE};
    val _ = add_coding_function sexp fcp "fix"
	{const = ``fcp_fix : (sexp -> sexp) -> 'b itself -> sexp -> sexp``,
	 definition = extendTranslateTheory.fcp_fix_def,
	 induction = NONE};

    val _ = add_coding_theorem sexp fcp "encode_decode_map"
    	    extendTranslateTheory.ENCDECMAP_FCP;
    val _ = add_coding_theorem sexp fcp "encode_detect_all"
    	    extendTranslateTheory.ENCDETALL_FCP;
    val _ = add_coding_theorem sexp fcp "decode_encode_fix"
    	    extendTranslateTheory.DECENCFIX_FCP;
    val _ = add_coding_theorem sexp fcp "encode_map_encode"
    	    extendTranslateTheory.ENCMAPENC_FCP;
    val _ = add_coding_theorem sexp fcp "fix_id"
    	    extendTranslateTheory.FIXID_FCP;
    val _ = add_source_theorem fcp "map_compose"
    	    extendTranslateTheory.MAP_COMPOSE_FCP;
    val _ = add_source_theorem fcp "map_id"
    	    extendTranslateTheory.MAPID_FCP;
    val _ = add_source_theorem fcp "all_id"
    	    extendTranslateTheory.ALLID_FCP;


    val _ = add_coding_theorem sexp fcp "detect_dead"
    	    extendTranslateTheory.DETDEAD_FCP;
    val _ = add_coding_theorem sexp fcp "general_detect"
    	    extendTranslateTheory.GENERAL_DETECT_FCP;

    val _ = set_bottom_value ``:'a word`` ``\a. FCP i. a``;
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Add the translations for words                                            *)
(*****************************************************************************)

fun add_word_translations () =
let val _ = perform "add_word_translations"
    val _ = add_translation_precise sexp word handle _ => ()
    val _ = add_coding_function_precise sexp word "encode"
	{const = ``word_encode``,
	 definition = extendTranslateTheory.word_encode_def,
	 induction = NONE};
    val _ = add_coding_function_precise sexp word "decode"
	{const = ``word_decode``,
	 definition = extendTranslateTheory.word_decode_def,
	 induction = NONE};
    val _ = add_coding_function_precise sexp word "detect"
	{const = ``word_detect``,
         definition = extendTranslateTheory.word_detect_def,
	 induction = NONE};

    val _ = add_source_function_precise word "map"
	{const = ``I``,definition = I_THM,induction = NONE};
    val _ = add_source_function_precise word "all"
	{const = ``K T``,definition = K_THM,induction = NONE};
    val _ = add_coding_function_precise sexp word "fix"
	{const = ``word_fix``,
	 definition = extendTranslateTheory.word_fix_def,
	 induction = NONE};

    val _ = add_coding_theorem_precise sexp word "encode_decode_map"
    	    extendTranslateTheory.ENCDECMAP_WORD;
    val _ = add_coding_theorem_precise sexp word "encode_detect_all"
    	    extendTranslateTheory.ENCDETALL_WORD;
    val _ = add_coding_theorem_precise sexp word "decode_encode_fix"
    	    extendTranslateTheory.DECENCFIX_WORD;
    val _ = add_coding_theorem_precise sexp word "encode_map_encode"
    	    (simple_encode_map_encode ``word_encode (:'a)``)
    val _ = add_coding_theorem_precise sexp word "fix_id"
    	    extendTranslateTheory.FIXID_WORD;
    val _ = add_source_theorem_precise word "map_compose"
    	    (simple_map_compose word);

    val _ = add_coding_theorem_precise sexp word "detect_dead"
    	    extendTranslateTheory.DETDEAD_WORD;
    val _ = add_coding_theorem_precise sexp word "general_detect"
    	    (DECIDE ``!x. word_detect (:'b) x ==>
	    	    	  word_detect (:'b) x``)
    val _ = add_source_theorem_precise ``:'a word`` "map_id"
    	    (REFL ``I:'a word -> 'a word``);

    val _ = set_bottom_value ``:'a word`` ``0w``;
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Initialise the type encoding system for s-expressions                     *)
(*****************************************************************************)

fun initialise_sexp() =
let val _ = perform "initialise_sexp"
    val _ = add_translation_scheme sexp
                translateTheory.SEXP_REDUCE
	        translateTheory.SEXP_TERMINAL;
    val _ = add_product_translations();
    val _ = add_translation sexp sexp
    val _ = add_coding_theorem sexp sexp "decode_encode_fix"
    	    (prove(``I o I = I:sexp -> sexp``,
	    	   REWRITE_TAC [combinTheory.I_o_ID]));
    val _ = add_coding_theorem sexp sexp "fix_id"
    	    (prove(``!x. (K T) x ==> (I x = x)``,
	           REWRITE_TAC [combinTheory.I_THM,combinTheory.K_THM]));
    val _ = add_source_function ``:sexp`` "map"
    	    {const = ``I:sexp -> sexp``,
	     definition = combinTheory.I_THM,
	     induction = NONE};
    val _ = add_source_function ``:sexp`` "all"
    	    {const = ``(K T):sexp -> bool``,
	     definition = combinTheory.K_THM,
	     induction = NONE};

    val _ = initialise_source_function_generators ();
    val _ = initialise_coding_function_generators sexp;
    val _ = initialise_coding_theorem_generators sexp;
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Functions specialised for encoding to sexp                                *)
(*                                                                           *)
(* initialise_type : hol_type -> unit                                        *)
(*      Fully initialises the encoding of a type, encoding the type and      *)
(*      creating the standard rewriting functions                            *)
(*                                                                           *)
(* translate_simple_function                                                 *)
(*        : (term * string) list -> thm -> thm                               *)
(*    Translates a function which requires no additional theorems for the    *)
(*    function to encode.                                                    *)
(* translate_conditional_function                                            *)
(*        : (term * string) list -> thm list -> thm -> thm                   *)
(*    Translates a function which relies upon conditional propagation        *)
(*    theorems in a non-trivial way. The list of theorems supplied is given  *)
(*    to the forward and backward-chaining resolution mechanisms to solve    *)
(*    this. Eg. the following term and propagation theorem:                  *)
(*          nat (if ~(a = 0) then b DIV a else 0)                            *)
(*          |- 0 < a ==> nat (b DIV a) = ...                                 *)
(*    Require the theorem: |- 0 < a ==> ~(a = 0) to be added to the set.     *)
(* translate_limit_function                                                  *)
(*      : (term * string) list ->                                            *)
(*        (term * term list) list -> thm list -> thm -> thm                  *)
(*    Translates a function that has specific limits that must be placed     *)
(*    upon a valid translation, eg. the function LOG:                        *)
(*        translate_limit_function [(``LOG``,"translated_log")]              *)
(*                                 [(``LOG``,[``\a b. 1 < a /\ 0 < b``])]    *)
(*                                 [|- 1 < a ==> 0 < a]                      *)
(*              |- 1 < a ==> (LOG a b = if b < a then 1 else LOG a (b DIV a) *)
(*                                                                           *)
(*****************************************************************************)

fun set_destructors thms =
    (functionEncodeLib.set_destructors sexp thms)
    handle e => wrapException "set_destructors" e

fun initialise_type t =
    (encode_type sexp t ;
     add_standard_coding_rewrites sexp t)
    handle e => wrapException "initialise_type" e

fun translate_simple_function names thm =
    convert_definition sexp names [] [] thm
    handle e => wrapException "translate_simple_function" e

fun translate_conditional_function names extras thm =
    convert_definition sexp names [] extras thm
    handle e => wrapException "translate_conditional_function" e

fun translate_limit_function names limits extras thm =
    convert_definition sexp names limits extras thm
    handle e => wrapException "translate_limits_function" e

fun flatten_recognizers namef t =
    functionEncodeLib.flatten_recognizers namef sexp t
    handle e => wrapException "flatten_recognizers" e;

(*****************************************************************************)
(* Polymorphic functions specialised for encoding to sexp                    *)
(*                                                                           *)
(* translate_simple_polymorphic_function                                     *)
(*        : (term * string) list -> (term * thm) list -> thm -> thm          *)
(* translate_conditional_polymorphic_function                                *)
(*        : (term * string) list -> (term * thm) list ->                     *)
(*                                  thm list -> thm -> thm                   *)
(* translate_limit_polymorphic_function                                      *)
(*      : (term * string) list -> (term * term list) list ->                 *)
(*                        (term * thm) list -> thm list -> thm -> thm        *)
(*                                                                           *)
(*****************************************************************************)

fun translate_simple_polymorphic_function names map_thms thm =
    convert_polymorphic_definition sexp names [] map_thms [] thm
    handle e => wrapException "translate_simple_polymorphic_function" e

fun translate_conditional_polymorphic_function names map_thms extras thm =
    convert_polymorphic_definition sexp names [] map_thms extras thm
    handle e => wrapException "translate_conditional_polymorphic_function" e

fun translate_limit_polymorphic_function names map_thms limits extras thm =
    convert_polymorphic_definition sexp names limits map_thms extras thm
    handle e => wrapException "translate_limits_polymorphic_function" e

(*****************************************************************************)
(* Translations specialised for s-expressions and FCPs                       *)
(*                                                                           *)
(* translate_simple_fcp_function                                             *)
(*        : string -> thm -> thm                                             *)
(* translate_conditional_fcp_function                                        *)
(*        : string -> thm list -> thm -> thm                                 *)
(* translate_limit_fcp_function                                              *)
(*        : string -> term list -> thm list -> thm -> thm                    *)
(* translate_recursive_fcp_function                                          *)
(*        : string -> term list -> thm list -> thm ->                        *)
(*          thm list -> tactic -> (thm -> thm -> tactic) -> thm              *)
(*                                                                           *)
(* flatten_fcp_recognizers                                                   *)
(*       : (hol_type -> string) -> hol_type -> thm list                      *)
(*                                                                           *)
(*****************************************************************************)

fun translate_simple_fcp_function names thm =
    convert_abstracted_nonrec_definition
    (can (match_term ``dimindex (:'a)``))
    sexp names [] [] thm
    handle e => wrapException "translate_simple_fcp_function" e

fun translate_conditional_fcp_function names extras thm =
    convert_abstracted_nonrec_definition
    (can (match_term ``dimindex (:'a)``))
    sexp names [] extras thm
    handle e => wrapException "translate_conditional_fcp_function" e

fun translate_limit_fcp_function names limits extras thm =
    convert_abstracted_nonrec_definition
    (can (match_term ``dimindex (:'a)``))
    sexp names limits extras thm
    handle e => wrapException "translate_limit_fcp_function" e

fun translate_recursive_fcp_function names limits extras thm
        rewrites tactic1 tactic2 =
    convert_abstracted_definition
    (can (match_term ``dimindex (:'a)``))
    sexp names limits extras thm rewrites tactic1 tactic2
    handle e => wrapException "translate_recursive_fcp_function" e

fun flatten_fcp_recognizers namef t =
    flatten_abstract_recognizers
    namef (can (match_term ``dimindex (:'a)``)) sexp t
    handle e => wrapException "flatten_fcp_recognizers" e;

(*****************************************************************************)
(* Tactics which may, or may not, be useful in proving full definitions.     *)
(*****************************************************************************)

open Psyntax boolSyntax Tactic;

fun ENCODE_WF_REL_TAC R (a,g) =
let val RR = Parse.parse_in_context (g::a) R
    val r = fst (dest_exists g)
    val rtypes = pairSyntax.strip_prod (hd (fst (strip_fun (type_of r))))
    val ftypes = pairSyntax.strip_prod (hd (fst (strip_fun (type_of RR))))
    fun ftype t = type_subst (map (fn v => v |-> sexp) (type_vars t)) t

    val decoders = map (get_decode_function sexp o ftype) ftypes
    val func = foldr pairLib.mk_pair_map (last decoders) (butlast decoders)

    val at = gen_tyvar();
    val bt = gen_tyvar();
    val inv_image =
        mk_const("inv_image",
            (at --> at --> bool) --> (bt --> at) --> bt --> bt --> bool);

    val RRR = list_imk_comb(inv_image,[RR,func]);
in
    (EXISTS_TAC RRR THEN
    CONJ_TAC THENL [MATCH_MP_TAC (relationTheory.WF_inv_image),ALL_TAC] THEN
    REWRITE_TAC [relationTheory.inv_image_def,prim_recTheory.WF_measure] THEN
    pairLib.GEN_BETA_TAC THEN
    REWRITE_TAC [pairTheory.PAIR_MAP_THM,prim_recTheory.measure_thm,
        combinTheory.o_THM,pairTheory.FST,pairTheory.SND] THEN
    REPEAT STRIP_TAC) (a,g)
end

local
fun pop_tac ([],g) = ALL_TAC ([],g)
  | pop_tac (a::b,g) =
    (POP_ASSUM (SUBST_ALL_TAC o GSYM) THEN
    markerLib.ABBREV_TAC
    (mk_eq(variant (free_varsl (g::a::b))
              (mk_var(fst (dest_var (rhs a)),type_of (rand (lhs a)))),
           rand (lhs a)))) (a::b,g);
in
fun FULL_CHOOSE_DETECT_TAC (a,g) =
let val types = mapfilter (get_detect_type o rator) a
    val thms = map (FULL_DECODE_ENCODE_THM sexp) types
    val rewrites1 = map (FULL_ENCODE_DECODE_THM sexp) types
    val rewrites2 = map (FULL_ENCODE_DETECT_THM sexp) types
in
    (MAP_EVERY IMP_RES_TAC thms THEN
     TRY (NTAC (length thms) pop_tac) THEN
     REWRITE_TAC (rewrites1 @ rewrites2) THEN
     RULE_ASSUM_TAC (REWRITE_RULE (rewrites1 @ rewrites2))) (a,g)
end
end;

(*****************************************************************************)
(* Add rewrites for natural number functions.                                *)
(*****************************************************************************)

local
val tm = ``nat a``
in
fun is_encoded_num term =
    can (match_term tm) term
    andalso numLib.is_numeral (rand term)
end

fun add_num_rewrites () =
let val _ = tryperform "add_num_rewrites"
    val _ = add_standard_rewrite 1 "num =0" translateTheory.NAT_EQUAL_0;
    val _ = add_standard_rewrite 1 "num 0="
    	    (prove(``bool (0 = a) = zp (nat a)``,
	     REWRITE_TAC [GSYM translateTheory.NAT_EQUAL_0,
	     		  translateTheory.BOOL_CONG] THEN
	     DECIDE_TAC))
    val _ = add_standard_rewrite 1 "num 0 <" translateTheory.NAT_0_LT;
    val _ = add_standard_rewrite 0 "num <" translateTheory.NAT_LT;
    val _ = add_standard_rewrite 0 "num <=" translateTheory.NAT_LE;
    val _ = add_standard_rewrite 0 "num >=" translateTheory.NAT_GE;
    val _ = add_standard_rewrite 0 "num >" translateTheory.NAT_GT;
    val _ = add_standard_rewrite 0 "num +" translateTheory.NAT_ADD;
    val _ = add_standard_rewrite 0 "SUC" translateTheory.NAT_SUC;
    val _ = add_standard_rewrite 1 "SUC-PRE" translateTheory.NAT_SUC_PRE;
    val _ = add_standard_rewrite 0 "PRE" translateTheory.NAT_PRE;
    val _ = add_standard_rewrite 0 "num *" translateTheory.NAT_MULT;
    val _ = add_standard_rewrite 0 "num -fix" translateTheory.NAT_SUB;
    val _ = add_standard_rewrite 1 "num -" translateTheory.NAT_SUB_COND;
    val _ = add_standard_rewrite 0 "num encdec" translateTheory.DECENC_NAT;
    val _ = add_standard_rewrite 0 "natp" translateTheory.FLATTEN_NAT;
    val _ = add_standard_rewrite 0 "is SUC" translateTheory.NUM_CONSTRUCT;
    val _ = add_standard_rewrite 0 "num case" translateTheory.NUM_CASE;
    val _ = add_terminal ("nat ?",is_encoded_num);
    val _ = set_destructors [CONJUNCT2 (prim_recTheory.PRE)];
    val _ = add_standard_rewrite 0 "Num" translateTheory.NAT_NUM;

    val _ = add_standard_rewrite 0 "DIV" extendTranslateTheory.NAT_DIV;
    val _ = add_standard_rewrite 0 "MOD" extendTranslateTheory.NAT_MOD;
    val _ = add_standard_rewrite 0 "num **" extendTranslateTheory.NAT_EXPT;
    val _ = add_standard_rewrite 1 "num <<" extendTranslateTheory.NAT_ASH;
    val _ = add_standard_rewrite 0 "MAX" extendTranslateTheory.NAT_MAX;
    val _ = add_standard_rewrite 0 "MIN" extendTranslateTheory.NAT_MIN;

    val _ = add_standard_rewrite 0 "BIT" extendTranslateTheory.NAT_BIT;
    val _ = perform "add_num_rewrites"
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Add rewrites for boolean functions.                                       *)
(*****************************************************************************)

fun add_bool_rewrites () =
let val _ = tryperform "add_bool_rewrites"
    val _ = add_standard_rewrite 0 "booleanp" translateTheory.FLATTEN_BOOL;
    val _ = add_conditional_rewrite 0 "if" translateTheory.COND_REWRITE;
    val _ = add_standard_rewrite 1 "if T" translateTheory.COND_T;
    val _ = add_standard_rewrite 1 "if F" translateTheory.COND_F;
    val _ = add_conditional_rewrite 1 "/\\-left" translateTheory.BOOL_LEFT_AND;
    val _ = add_conditional_rewrite 0 "/\\-right"
    	    translateTheory.BOOL_RIGHT_AND;
    val _ = add_conditional_rewrite 1 "\\/-left" translateTheory.BOOL_LEFT_OR;
    val _ = add_conditional_rewrite 0 "\\/-right" translateTheory.BOOL_RIGHT_OR;
    val _ = add_conditional_rewrite 0 "==>implies" translateTheory.BOOL_IMPLIES;
    val _ = add_standard_rewrite 0 "bool ~" translateTheory.BOOL_NOT;
    val _ = add_standard_rewrite 0 "T" translateTheory.BOOL_T;
    val _ = add_standard_rewrite 0 "F" translateTheory.BOOL_F;

    val _ = add_standard_rewrite 0 "|= consp" translateTheory.BOOL_PAIR;
    val _ = add_standard_rewrite 0 "K T" translateTheory.BOOL_KT;
    val _ = perform "add_bool_rewrites"
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Add rewrites for list functions.                                          *)
(*****************************************************************************)

fun add_list_rewrites() =
let val _ = tryperform "add_list_rewrites"
    val _ = add_standard_rewrite 0 "HD" translateTheory.LIST_HD;
    val _ = add_standard_rewrite 0 "TL" translateTheory.LIST_TL;
    val _ = add_standard_rewrite 0 "NULL" translateTheory.LIST_NULL;
    val _ = add_standard_rewrite 0 "LENGTH" translateTheory.LIST_LENGTH;
    val _ = add_standard_rewrite 0 "list case" translateTheory.LIST_CASE;
    val _ = add_standard_rewrite 1 "is []" translateTheory.LIST_CONSTRUCT1;
    val _ = add_standard_rewrite 1 "is Cons" translateTheory.LIST_CONSTRUCT2;
    val _ = set_destructors [listTheory.HD,listTheory.TL];
    val _ = add_standard_coding_rewrites sexp list;
    val _ = perform "add_list_rewrites"
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Add rewrites for product functions.                                       *)
(*****************************************************************************)

fun add_pair_rewrites() =
let val _ = perform "add_pair_rewrites"
    val _ = set_destructors [pairTheory.FST,pairTheory.SND];
    val _ = add_standard_coding_rewrites sexp pair;
    val _ = add_standard_rewrite 0 "FST" translateTheory.PAIR_FST;
    val _ = add_standard_rewrite 0 "SND" translateTheory.PAIR_SND;
    val _ = add_standard_rewrite 0 "pair case" translateTheory.PAIR_CASE;
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Add the polytypic rewrites                                                *)
(*****************************************************************************)

fun add_polytypic_rewrites() =
let val _ = perform "add_polytypic_rewrites"
    val _ = add_standard_conversion 0 "nesting"
      				(nested_constructor_rewrite ``:sexp``);
    val _ = add_standard_rewrite 0 "=" translateTheory.BOOL_EQUALITY;
    val _ = add_polytypic_rewrite 0 "\\x." make_lambda_propagation_theorem;
    val _ = add_polytypic_rewrite 0 "dec enc" polytypic_decodeencode;
    val _ = add_polytypic_rewrite 0 "case" polytypic_casestatement;
    val _ = add_polytypic_rewrite 0 "construct" polytypic_encodes;
    val _ = add_polytypic_rewrite 0 "let" polytypic_let_conv
    val _ = add_standard_conversion 0 "I var" (target_function_conv ``:sexp``)
    val _ = add_standard_conversion 0 "I enc" (dummy_encoder_conv ``:sexp``);
    val _ = add_polytypic_rewrite 0 "PRED" polytypic_recognizer;
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Add the integer rewrites                                                  *)
(*****************************************************************************)

local
val tm = ``int (a:int)``
in
fun is_encoded_int term =
    can (match_term tm) term
    andalso numLib.is_numeral (rand (rand term)) handle _ => false
end;

fun add_int_rewrites() =
let val _ = perform "add_int_rewrites"
    val _ = add_standard_rewrite 0 "integerp" translateTheory.FLATTEN_INT;

    val _ = add_standard_rewrite 0 "int +" translateTheory.INT_ADD;
    val _ = add_standard_rewrite 0 "int *" translateTheory.INT_MULT;
    val _ = add_standard_rewrite 0 "int ~" translateTheory.INT_UNARY_MINUS;
    val _ = add_standard_rewrite 0 "int <" translateTheory.INT_LT;
    val _ = add_standard_rewrite 0 "int >" translateTheory.INT_GT;
    val _ = add_standard_rewrite 0 "int <=" translateTheory.INT_LE;
    val _ = add_standard_rewrite 0 "int >=" translateTheory.INT_GE;
    val _ = add_standard_rewrite 0 "int -" translateTheory.INT_SUB;
    val _ = add_standard_rewrite 0 "int &" (GSYM sexpTheory.nat_def);

    val _ = add_standard_rewrite 0 "int **" extendTranslateTheory.INT_EXPT;
    val _ = add_standard_rewrite 0 "int /" extendTranslateTheory.INT_DIV;
    val _ = add_standard_rewrite 0 "quot" extendTranslateTheory.INT_QUOT;
    val _ = add_standard_rewrite 0 "int %" extendTranslateTheory.INT_MOD;
    val _ = add_standard_rewrite 0 "rem" extendTranslateTheory.INT_REM;
    val _ = add_standard_rewrite 0 "SGN" extendTranslateTheory.INT_SGN;
    val _ = add_standard_rewrite 1 "int <<" extendTranslateTheory.INT_ASH;
    val _ = add_standard_rewrite 0 "max" extendTranslateTheory.INT_MAX;
    val _ = add_standard_rewrite 0 "min" extendTranslateTheory.INT_MIN;
    val _ = add_standard_rewrite 0 "ABS" extendTranslateTheory.INT_ABS;

    val _ = add_terminal ("int ?",is_encoded_int);
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Add the Rational rewrites                                                 *)
(*****************************************************************************)

local
val tm = ``rat (a:rat)``
in
fun is_encoded_rat term =
    can (match_term tm) term
    andalso numLib.is_numeral (rand (rand term)) handle _ => false
end;

fun add_rat_rewrites() =
let val _ = perform "add_rat_rewrites"
    val _ = add_standard_rewrite 0 "rationalp" translateTheory.FLATTEN_RAT;

    val _ = add_standard_rewrite 0 "rat +" translateTheory.RAT_ADD;
    val _ = add_standard_rewrite 0 "rat *" translateTheory.RAT_MULT;
    val _ = add_standard_rewrite 0 "rat ~" translateTheory.RAT_UNARY_MINUS;
    val _ = add_standard_rewrite 0 "rat <" translateTheory.RAT_LT;
    val _ = add_standard_rewrite 0 "rat >" translateTheory.RAT_GT;
    val _ = add_standard_rewrite 0 "rat <=" translateTheory.RAT_LE;
    val _ = add_standard_rewrite 0 "rat >=" translateTheory.RAT_GE;
    val _ = add_standard_rewrite 0 "rat -" translateTheory.RAT_SUB;
    val _ = add_standard_rewrite 0 "rat -" translateTheory.RAT_DIV;

    val _ = add_terminal ("rat ?",is_encoded_rat)
in
    ()
end handle ExistsAlready => ()

(*****************************************************************************)
(* Add the FCP rewrites                                                      *)
(*****************************************************************************)

fun add_fcp_rewrites() =
let val _ = perform "add_fcp_rewrites"
    val _ = add_conditional_rewrite 0 "%%" extendTranslateTheory.FCP_INDEX;
    val _ = add_standard_rewrite 0 ":+" extendTranslateTheory.FCP_UPDATE;
in
    ()
end handle ExistsAlready => ();

(*****************************************************************************)
(* Add the word rewrites                                                     *)
(*****************************************************************************)

fun add_word_rewrites() =
let val _ = perform "add_word_rewrites"
    val _ = add_standard_rewrite 0 "isword" extendTranslateTheory.WORD_FLATTEN;

    val _ = add_standard_rewrite 0 "&&" extendTranslateTheory.WORD_AND;
    val _ = add_standard_rewrite 0 "!!" extendTranslateTheory.WORD_OR;
    val _ = add_standard_rewrite 0 "??" extendTranslateTheory.WORD_XOR;
    val _ = add_standard_rewrite 0 "w~" extendTranslateTheory.WORD_NOT;
    val _ = add_standard_rewrite 1 "~!!" extendTranslateTheory.WORD_ORC1;
    val _ = add_standard_rewrite 1 "!!~" extendTranslateTheory.WORD_ORC2;
    val _ = add_standard_rewrite 1 "~&&" extendTranslateTheory.WORD_ANDC1;
    val _ = add_standard_rewrite 1 "&&~" extendTranslateTheory.WORD_ANDC2;
    val _ = add_standard_rewrite 1 "~(&&)" extendTranslateTheory.WORD_NAND;
    val _ = add_standard_rewrite 1 "~(??)" extendTranslateTheory.WORD_NXOR;
    val _ = add_standard_rewrite 1 "~(!!)" extendTranslateTheory.WORD_NOR;
    val _ = add_standard_rewrite 1 "word %%" extendTranslateTheory.WORD_BIT;
    val _ = add_standard_rewrite 0 ">>" extendTranslateTheory.WORD_ASR;
    val _ = add_standard_rewrite 0 "<<" extendTranslateTheory.WORD_LSL;
    val _ = add_standard_rewrite 0 "word_msb" extendTranslateTheory.WORD_MSB;

    val _ = add_standard_rewrite 0 "word +" extendTranslateTheory.WORD_ADD;
    val _ = add_standard_rewrite 0 "word -" extendTranslateTheory.WORD_SUB;
    val _ = add_standard_rewrite 0 "word *" extendTranslateTheory.WORD_MUL;
    val _ = add_standard_rewrite 0 "word $-" extendTranslateTheory.WORD_NEG;
    val _ = add_standard_rewrite 0 "word /" extendTranslateTheory.WORD_DIV;
    val _ = add_standard_rewrite 0 "word T" extendTranslateTheory.WORD_T;
    val _ = add_standard_rewrite 0 "word <" extendTranslateTheory.WORD_LT;
    val _ = add_standard_rewrite 0 "word >" extendTranslateTheory.WORD_GT;
    val _ = add_standard_rewrite 0 "word <=" extendTranslateTheory.WORD_LE;
    val _ = add_standard_rewrite 0 "word >=" extendTranslateTheory.WORD_GE;

    val _ = add_standard_rewrite 0 "n2w" extendTranslateTheory.WORD_N2W;
    val _ = add_standard_rewrite 0 "w2n" extendTranslateTheory.NAT_W2N;
    val _ = add_standard_rewrite 0 "int sw2i"
    	          (GSYM extendTranslateTheory.word_encode_def)
    val _ = add_standard_conversion 0 "index"
    	    	  (Conv.RAND_CONV wordsLib.SIZES_CONV);

    local
      open intLib integerTheory Tactic Tactical
      val i2n_lemma = prove(``0 <= (i + 1) rem 2 ** l - 1 + 2 ** l``,
        REWRITE_TAC [ARITH_PROVE ``0i <= a - 1 + b = ~a < b``] THEN
    	MATCH_MP_TAC
	  (ARITH_PROVE ``!a b c. a <= b /\ b < c ==> a < c:int``) THEN
        Q.EXISTS_TAC `ABS ((i + 1) rem 2 ** l)` THEN
    	METIS_TAC [INT_REMQUOT,INT_ABS_NUM,INT_EXP,INT_EXP_EQ0,
          ARITH_PROVE ``~(2 = 0i)``,INT_ABS,INT_NOT_LT,INT_NEGNEG,INT_LE_REFL,
	  INT_LE_NEGL]);
    in
       val i2n_thms = [INT_EXP_EQ0,ARITH_PROVE ``~(2 = 0i)``,
            REWRITE_CONV [integerTheory.INT_POS,integerTheory.INT_EXP]
                 ``0 <= 2 ** a``,
            prove(``~(b = 0) /\ 0i <= b ==> 0 <= a % b``,
		     METIS_TAC [INT_MOD_BOUNDS,INT_NOT_LT]),i2n_lemma]
    end;

    val _ = translate_conditional_function
    	    [(``i2n``,"translated_i2n")]
	    i2n_thms
	    signedintTheory.i2n_def;

    val _ = translate_simple_function
    	    [(``extend``,"translated_extend")]
	    signedintTheory.extend_def;
in
    ()
end handle ExistsAlready => ();

(*****************************************************************************)
(* Initialisation: run the above functions, checking for errors.             *)
(*****************************************************************************)

val _ = Feedback.set_trace "functionEncodeLib.Trace" 1;

val _ = (initialise_sexp() handle e =>
      	Raise (mkStandardExn "initialise_sexp"
	      ("Failed to add the translations for :sexp\n" ^
	       ("Original exception: \n" ^ exn_to_string e))));

fun add_translations f t =
    (trace 1 "Adding translations for the type: " ;
     trace 1 (type_to_string t) ; trace 1 "\n" ;
     f ()) handle e =>
      	Raise (mkStandardExn "Initialisation"
	      ("Failed to add the translations for " ^ type_to_string t ^
	       ("\nOriginal exception: \n" ^ exn_to_string e)));

val _ = add_translations add_num_translations num;
val _ = add_translations add_int_translations int;
val _ = add_translations add_rat_translations rat;
val _ = add_translations add_bool_translations bool;
val _ = add_translations add_list_translations list;
val _ = add_translations add_fcp_translations fcp;
val _ = add_translations add_word_translations word;

fun add_rewrites f t =
    (trace 1 "Adding rewrites for the type: " ;
     trace 1 (type_to_string t) ; trace 1 "\n" ;
     f ()) handle e =>
      	Raise (mkStandardExn "Initialisation"
	      ("Failed to add the rewrites for " ^ type_to_string t ^
	       ("\nOriginal exception: \n" ^ exn_to_string e)));

val _ = add_rewrites add_num_rewrites num;
val _ = add_rewrites add_bool_rewrites bool;
val _ = (trace 1 "Adding polytypic rewrites\n" ;
      	 add_polytypic_rewrites())
	handle e => Raise (mkStandardExn "Initialisation"
	       	    ("Failed to add polytypic rewrites"));
val _ = add_rewrites add_list_rewrites list;
val _ = add_rewrites add_pair_rewrites pair
val _ = add_rewrites add_int_rewrites int;
val _ = add_rewrites add_rat_rewrites rat;
val _ = add_rewrites add_fcp_rewrites fcp;
val _ = add_rewrites add_word_rewrites word;



(*****************************************************************************)
(* Output of definitions                                                     *)
(*    - Doesn't yet work for mutually recursive definitions...               *)
(*****************************************************************************)

open sexp;

fun tryfilter f [] = []
  | tryfilter f (x::xs) =
  if (f x handle _ => false) then x::tryfilter f xs else tryfilter f xs;

fun mapff f1 f2 [] = []
  | mapff f1 f2 (x::xs) = f1 x :: f2 x:: mapff f1 f2 xs;

val GCONST = map (fst o strip_comb o lhs o snd o strip_forall)
    	     o strip_conj o concl

fun order_defs [] = []
  | order_defs L =
let val (head,rest) =
    	with_exn
        (pluck (fn x =>
	     all (fn y => null (find_terms (C mem (GCONST x)) (concl y))
	     	       	  orelse (concl x = concl y)) L))
        L
        (mkStandardExn "order_defs"
	       ("Could not order the function list: " ^
	       	xlist_to_string thm_to_string L ^
		"\n as it appears to contain cycles..."))
in  head::order_defs rest
end;

fun acl2_var_map s = (implode o filter (not o curry op= #"'") o explode) s

fun acl2_prime s = s ^ "p";

fun acl2_variant vl v =
    if mem v vl then acl2_variant vl (acl2_prime v) else v;

local
fun conv1 term =
let val var = fst (dest_var (fst (dest_abs term)))
    val vars = free_vars term
    val newvar = acl2_var_map var
    val variant = acl2_variant (map (fst o dest_var) vars) newvar
in
    if variant = var
       then NO_CONV term
       else RENAME_VARS_CONV [variant] term
end;
in
fun ACL2_BVARS_CONV term = REDEPTH_CONV conv1 term
    handle UNCHANGED => REFL term
         | e => wrapException "ACL2_BVARS_CONV" e
end

fun mk_mlsexp_mbe_term body =
    mk_mlsexp_list
	    [mksym "ACL2" "MUST-BE-EQUAL",
	     term_to_mlsexp body,
	     term_to_mlsexp (rand (rator body))]

fun mk_mlsexp_guard body =
    mk_mlsexp_list
       [mksym "ACL2" "DECLARE",
        mk_mlsexp_list
	   [mksym "ACL2" "XARGS",
	    mksym "ACL2" ":GUARD",
            term_to_mlsexp (rand (rator (rator body)))]];

fun def_to_mlsexp_mbe_defun thm =
let val (asl,concl) = dest_thm (SPEC_ALL thm)
    val _ = if null asl then ()
    	       else raise (mkStandardExn "def_to_mlsexp_mbe_defun"
	       	    ("The theorem supplied:\n" ^ thm_to_string thm ^
		     "\nhas a non-empty hypothesis set."))
    val (opr,args) = strip_comb (lhs concl)
in
    mk_mlsexp_list
       [mksym "COMMON-LISP" "DEFUN",
        string_to_mlsym(get_name opr),
	mk_mlsexp_list(map term_to_mlsexp args),
	mk_mlsexp_guard (rhs concl),
	mk_mlsexp_mbe_term (rhs concl)]
end;

fun all_definitions (thm:thm) =
let val consts = GCONST thm
    val {Name,Thy,Ty} = dest_thy_const (hd consts)
    val consts = mk_set (find_terms (fn x => is_const x andalso
    	       	 	    	     (curry op= Thy o #Thy o dest_thy_const) x)
    	       	 	    (concl thm))
    val all_defs = DB.definitions Thy
    val filtered1 = tryfilter (not o null o intersect consts o GCONST o snd)
    		    	      all_defs
    val filtered2 = tryfilter (String.isPrefix "translated_" o fst) filtered1

    val recursive = map all_definitions
    		    	(op_set_diff (fn a => fn b => concl a = concl b)
				     (map snd filtered2) [thm]);
in
    op_mk_set (fn a => fn b => concl a = concl b)
    	      (thm::flatten recursive)
end;

fun print_all_defs filename print convert thm =
let val ordered = order_defs (all_definitions thm)
    val rewritten = map (REWRITE_RULE [sexpTheory.andl_def] o
    		         CONV_RULE ACL2_BVARS_CONV o GEN_ALL) ordered
    val preamble = mk_mlsexp_list
    	[mksym "ACL2" "IN-PACKAGE",
	 mlstr (!current_package)];
    fun post_def thm = mk_mlsexp_list
    	[mksym "ACL2" "VERIFY-GUARDS",
	 string_to_mlsym(get_name (hd (GCONST thm)))]

    fun mprint out x = (print out x ; out "\n\n")

    val outputs = preamble::mapff convert post_def (rev rewritten)
in
    print_lisp_file filename (fn out => map (mprint out) outputs)
end handle e => wrapException "print_all_defs" e

fun print_all_defs_standard filename thm =
    print_all_defs filename print_mlsexp def_to_mlsexp_defun thm
		   handle e => wrapException "print_all_defs_standard" e

fun can_mbe thm =
    can (C match_term (rhs (concl (SPEC_ALL thm)))) ``ite a b c`` andalso
    not (can (C match_term (rhs (concl (SPEC_ALL thm)))) ``ite (consp a) b c``);

(*****************************************************************************)
(* Very nasty hack to allow the use of the :guard keyword... this will be    *)
(* replaced with the proper symbol, or better code, at a later date.         *)
(*****************************************************************************)

fun print_allow_keyword (out:string->unit) (sym as mlsym(_,v))  =
     if String.isPrefix ":" v
     	then out v
     	else out (mlsym_to_string sym)
 | print_allow_keyword (out:string->unit) (mlstr s) =
     (out "\""; out s; out "\"")
 | print_allow_keyword (out:string->unit) (mlchr c) =
     (out "(code-char "; out(int_to_string(ord c)); out ")")
 | print_allow_keyword (out:string->unit) (mlnum(an,ad,bn,bd)) =
    if (bn = "0") andalso (bd = "1")
     then (out an; out "/"; out ad)
     else (out "(COMMON-LISP::COMPLEX ";
           out an; out "/"; out ad;
           out " ";
           out bn; out "/"; out bd;
           out ")")
 | print_allow_keyword (out:string->unit) (mlpair(p1,p2)) =
     (out "(";
      (if is_mlsexp_list p2
        then let val sl = dest_mlsexp_list p2
             in
              if null sl
               then print_allow_keyword out p1
               else (print_allow_keyword out p1;
                     map (fn p => (out " "; print_allow_keyword out p)) sl;
                     ())
             end
        else (print_allow_keyword out p1; out " . ";
	      print_allow_keyword out p2));
      out ")");

fun print_all_defs_mbe filename thm =
    print_all_defs filename print_allow_keyword
        (fn y => if can_mbe y then def_to_mlsexp_mbe_defun y else
		       	   	     	  def_to_mlsexp_defun y) thm
    handle e => wrapException "print_all_defs_mbe" e;

val Raise = polytypicLib.Raise;

end