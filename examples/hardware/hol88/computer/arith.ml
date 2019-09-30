%  MICROCODED COMPUTER PROOF : HOL                                      %
%                                                                       %
%  'arith.ml'                                                           %
%                                                                       %
%  Description                                                          % 
%                                                                       %
%     This theory provides some simple arithmetic theorems such as      %
%  "|- 1 + 2 = 3", which are required by the theory 'proof1'.           %
%                                                                       %
%  Author:  Jeff Joyce                                                  %
%  Date:    August 4, 1985                                              %

new_theory `arith`;;

SPEC "2" (GEN "n" (CONJUNCT1 ADD));;
let plus_0_2 = save_thm (`plus_0_2`,it);;

REFL "1 + 2";;
SUBS_OCCS [([2],(num_CONV "1"))] it;;
PURE_REWRITE_RULE [ADD] it;;
SUBS [SYM(num_CONV "3")] it;;
let plus_1_2 = save_thm (`plus_1_2`,it);;

REFL "2 + 2";;
SUBS_OCCS [([3],(num_CONV "2"))] it;;
SUBS_OCCS [([1],(num_CONV "1"))] it;;
PURE_REWRITE_RULE [ADD] it;;
SUBS [SYM(num_CONV "3")] it;;
SUBS [SYM(num_CONV "4")] it;;
let plus_2_2 = save_thm (`plus_2_2`,it);;

REFL "3 + 2";;
SUBS_OCCS [([2],(num_CONV "3"))] it;;
SUBS_OCCS [([2],(num_CONV "2"))] it;;
SUBS_OCCS [([1],(num_CONV "1"))] it;;
PURE_REWRITE_RULE [ADD] it;;
SUBS [SYM(num_CONV "3")] it;;
SUBS [SYM(num_CONV "4")] it;;
SUBS [SYM(num_CONV "5")] it;;
let plus_3_2 = save_thm (`plus_3_2`,it);;

SPEC "10" (GEN "n" (CONJUNCT1 ADD));;
let plus_0_10 = save_thm (`plus_0_10`,it);;

REFL "1 + 10";;
SUBS_OCCS [([2],(num_CONV "1"))] it;;
PURE_REWRITE_RULE [ADD] it;;
SUBS [SYM(num_CONV "11")] it;;
let plus_1_10 = save_thm (`plus_1_10`,it);;

REFL "2 + 10";;
SUBS_OCCS [([2],(num_CONV "2"))] it;;
SUBS [num_CONV "1"] it;;
PURE_REWRITE_RULE [ADD] it;;
SUBS [SYM(num_CONV "11")] it;;
SUBS [SYM(num_CONV "12")] it;;
let plus_2_10 = save_thm (`plus_2_10`,it);;

REFL "3 + 10";;
SUBS_OCCS [([2],(num_CONV "3"))] it;;
SUBS [num_CONV "2"] it;;
SUBS [num_CONV "1"] it;;
PURE_REWRITE_RULE [ADD] it;;
SUBS [SYM(num_CONV "11")] it;;
SUBS [SYM(num_CONV "12")] it;;
SUBS [SYM(num_CONV "13")] it;;
let plus_3_10 = save_thm (`plus_3_10`,it);;

REFL "4 + 10";;
SUBS_OCCS [([2],(num_CONV "4"))] it;;
SUBS [num_CONV "3"] it;;
SUBS [num_CONV "2"] it;;
SUBS [num_CONV "1"] it;;
PURE_REWRITE_RULE [ADD] it;;
SUBS [SYM(num_CONV "11")] it;;
SUBS [SYM(num_CONV "12")] it;;
SUBS [SYM(num_CONV "13")] it;;
SUBS [SYM(num_CONV "14")] it;;
let plus_4_10 = save_thm (`plus_4_10`,it);;

REFL "5 + 10";;
SUBS_OCCS [([2],(num_CONV "5"))] it;;
SUBS [num_CONV "4"] it;;
SUBS [num_CONV "4"] it;;
SUBS [num_CONV "3"] it;;
SUBS [num_CONV "2"] it;;
SUBS [num_CONV "1"] it;;
PURE_REWRITE_RULE [ADD] it;;
SUBS [SYM(num_CONV "11")] it;;
SUBS [SYM(num_CONV "12")] it;;
SUBS [SYM(num_CONV "13")] it;;
SUBS [SYM(num_CONV "14")] it;;
SUBS [SYM(num_CONV "15")] it;;
let plus_5_10 = save_thm (`plus_5_10`,it);;

REFL "6 + 10";;
SUBS_OCCS [([2],(num_CONV "6"))] it;;
SUBS [num_CONV "5"] it;;
SUBS [num_CONV "4"] it;;
SUBS [num_CONV "4"] it;;
SUBS [num_CONV "3"] it;;
SUBS [num_CONV "2"] it;;
SUBS [num_CONV "1"] it;;
PURE_REWRITE_RULE [ADD] it;;
SUBS [SYM(num_CONV "11")] it;;
SUBS [SYM(num_CONV "12")] it;;
SUBS [SYM(num_CONV "13")] it;;
SUBS [SYM(num_CONV "14")] it;;
SUBS [SYM(num_CONV "15")] it;;
SUBS [SYM(num_CONV "16")] it;;
let plus_6_10 = save_thm (`plus_6_10`,it);;

REFL "7 + 10";;
SUBS_OCCS [([2],(num_CONV "7"))] it;;
SUBS [num_CONV "6"] it;;
SUBS [num_CONV "5"] it;;
SUBS [num_CONV "4"] it;;
SUBS [num_CONV "4"] it;;
SUBS [num_CONV "3"] it;;
SUBS [num_CONV "2"] it;;
SUBS [num_CONV "1"] it;;
PURE_REWRITE_RULE [ADD] it;;
SUBS [SYM(num_CONV "11")] it;;
SUBS [SYM(num_CONV "12")] it;;
SUBS [SYM(num_CONV "13")] it;;
SUBS [SYM(num_CONV "14")] it;;
SUBS [SYM(num_CONV "15")] it;;
SUBS [SYM(num_CONV "16")] it;;
SUBS [SYM(num_CONV "17")] it;;
let plus_7_10 = save_thm (`plus_7_10`,it);;

close_theory ();;
