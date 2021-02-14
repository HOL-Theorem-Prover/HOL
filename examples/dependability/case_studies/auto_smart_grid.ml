app load
 ["bossLib", "metisLib", "realLib", "numLib", "listLib"];

open bossLib metisLib realLib numLib listLib;

app load ["combinTheory","RBDTheory","FT_deepTheory","VDCTheory",
"smart_gridTheory","ASN_gatewayTheory","realTheory","arithmeticTheory","boolTheory","listTheory"];

open combinTheory RBDTheory FT_deepTheory VDCTheory
smart_gridTheory ASN_gatewayTheory realTheory arithmeticTheory boolTheory listTheory;

(*-------------------------------*)

fun sml_of_hol_real_op t =
  if t = ``($*):real->real->real`` then Real.*
  else if t = ``($+):real->real->real`` then Real.+
  else if t = ``($/):real->real->real`` then Real./
  else if t = ``($-):real->real->real`` then Real.-
  else failwith "Unrecognized HOL operator";
(*-------------------------------*)
fun real_to_pos_arbrat tm =
      case Lib.total realSyntax.dest_injected tm of
         SOME a => Arbrat.fromNat (numLib.dest_numeral a)
       | NONE => raise ERR "real_to_pos_arbrat" "";
(*-------------------------------*)
fun real_to_signed_arbrat tm =
      case Lib.total realSyntax.dest_negated tm of
         SOME a => Arbrat.negate (real_to_pos_arbrat a)
       | NONE => real_to_pos_arbrat tm;
(*-------------------------------*)
fun real_to_arbrat tm =
      case Lib.total realSyntax.dest_div tm of
         SOME (a, b) =>
            Arbrat./ (real_to_signed_arbrat a, real_to_signed_arbrat b)
       | NONE => real_to_signed_arbrat tm;
fun arbrat_to_math_real x =
  Real./ (Real.fromInt (Arbint.toInt (Arbrat.numerator x)),
          Real.fromInt (Arbnum.toInt (Arbrat.denominator x)));

(*-------------------------------*)
val real_to_math_real = arbrat_to_math_real o real_to_arbrat;

(************************************)

fun sml_of_hol_real t =
  let val failstring = "Symbolic expression could not be translated in a number" in
    case strip_comb t of
       (f,[a1,a2]) => sml_of_hol_real_op f (sml_of_hol_real a1,sml_of_hol_real a2)
       | (f,[a]) =>
           if f = ``($&):num -> real``
           then Arbnum.toReal (dest_numeral a)
           else failwith failstring
       | _ => failwith failstring
  end;


(*------------------------------------------------------------*)
fun sml_of_hol_real_exp t =
 let val failstring = "Symbolic expression could not be translated in a number" in
    case strip_comb t of
       (f,[a1,a2]) =>
       sml_of_hol_real_op f (sml_of_hol_real_exp a1,sml_of_hol_real_exp a2)
       | (f,[a]) => if f = ``($&):num -> real``
           then Arbnum.toReal (dest_numeral a)
                else if f =  ``exp:real->real`` then Math.exp (real_to_math_real (a)) else failwith failstring
       |_ => failwith failstring
  end;


(*--------------------------------------*)
 sml_of_hol_real_exp
        ``1 - (1 - (1 - exp ((-5:real)/2) ) *
              (1 - exp (-3:real/2) )) *
              ((1 - (1 - exp ((-1:real)/2) ) * ((1 - exp(-2:real) )*
                  ((1 - exp (-3:real/2) ) * (1 - exp(-4:real) )))) *
                  exp((-9:real)/2) ) *
               ((1 - (1 - exp(-7:real/2) ) *
                (1 - exp(-3:real) ))* (1 - (1 - exp(-4:real) ) *
                (1 - exp(-3:real) )) *(exp(-4:real) *
                ((1 - (1 - exp(-1:real/2) ) * (1 - exp(-3:real) ))*
                 ((1 - (1 - exp(-1:real/2) ) *(1 - exp(-3:real) )) *
                 ((1 - (1 - exp(-1:real/2) ) *(1 - exp(-3:real) ))*
                (1 - (1 - exp(-1:real/2) ) *(1 - exp(-3:real) ))))) *
                 (exp(-321:real/20) *((1 - (1 - exp(-1:real/2) ) *
                 (1 - exp(-3:real) ))*((1 - (1 - exp(-1:real/2) ) *
                 (1 - exp(-3:real) )) *((1 - (1 - exp(-1:real/2) ) *
                 (1 - exp(-3:real) ))* (1 - (1 - exp(-1:real/2)) *
                 (1 - exp(-3:real) )))))) *
                ((1 - (1 - exp(-3:real/2) ) *(1 - exp(-2:real) ))*
                 ((1 - (1 - exp(-1:real/2) ) *(1 - exp(-2:real) )) *
                 (1 - (1 - exp(-1:real/2) ) *(1 - exp(-2:real) ))))) *
                exp(-7/2:real) *
                ((1 - (1 - exp(-7:real/2) ) *(1 - exp(-3:real) )) *
                 ((1 - (1 - exp(-3:real/2) ) *(1 - exp(-3:real) ))*
                 ((1 - (1 - exp(-1:real/2) ) *(1 - exp(-3:real) )) *
                 (1 - (1 - exp(-5:real/2) ) *(1 - exp(-3:real) )))))) + ((1 - (1 - exp(-7:real/2) ) *(1 - exp(-3:real) )) *
                 ((1 - (1 - exp(-3:real/2) ) *(1 - exp(-3:real) ))*
                 ((1 - (1 - exp(-1:real/2) ) *(1 - exp(-3:real) )) *
                 (1 - (1 - exp(-5:real/2) ) *(1 - exp(-3:real) ))))) ``;


(*---------------------------------------*)

fun smart_grid_RBD_EVAL L =
let
val specialization =
    (UNDISCH_ALL o REWRITE_RULE[of_DEF,o_THM,FLAT,MEM] o SPEC_ALL o Q.SPECL L)
     rel_redund_star_ringRBD
val computation =
       (CONV_RULE(SIMP_CONV real_ss[list_sum_def,REAL_SUB_RDISTRIB,REAL_SUB_LDISTRIB]) o CONV_RULE(SIMP_CONV list_ss[list_prod_def,one_minus_list_def,exp_func_def,exp_func_list_def,list_prod_def]) o REWRITE_RULE[list_prod_def,one_minus_list_def,exp_func_list_def,one_minus_exp_prod_def
        ] o BETA_RULE  o REWRITE_RULE[LENGTH,MAP
        ]) specialization
val value = sml_of_hol_real_exp (rhs (concl computation))
in
      print "Under the following assumptions:\n";
      print (String.concat (map (fn t => term_to_string t ^ "\n\n") (hyp computation)));
            print "\n\n";
      print (term_to_string (concl computation));
print "\n\n";
print (Real.toString ( value) ^ "\n\n")
end;

smart_grid_RBD_EVAL [`p:α event # α event event # (α event -> real)`,
                      `5.0:real`,
                       `PIED:'a->extreal`,
                        `X_ESW_list:('a->extreal) list list`,
                       `CIED:'a->extreal`,
                       `0.5:real`,
                       `[[0.5;0.6;(1.0:real)]]`,
                       `0.7:real`];


(*---------------------------------*)

fun smart_grid_RBD_EVAL1 L =
let
val specialization =
    (UNDISCH_ALL o SPEC_ALL o Q.SPECL L)
     rel_redund_star_ringRBD
val computation =
       (CONV_RULE (SIMP_CONV real_ss[]) o
        CONV_RULE(SIMP_CONV list_ss[list_sum_def,list_prod_def,one_minus_list_def,exp_func_def,exp_func_list_def,list_prod_def]) o
        BETA_RULE o REWRITE_RULE [of_DEF,o_THM]) specialization
val value = sml_of_hol_real_exp (rhs (concl computation))
in
      print "Under the following assumptions:\n";
      print (String.concat (map (fn t => term_to_string t ^ "\n\n") (hyp computation)));
            print "\n\n";
      print (term_to_string (concl computation));
      print "\n\n";
      print (Real.toString ( value) ^ "\n\n")
end;

(*-------------------------------*)
fun smart_grid_RBD_EVAL2 L thm thms =
let
val specialization =
    (UNDISCH_ALL o SPEC_ALL o Q.SPECL L)
     thm
val computation =
       (CONV_RULE (SIMP_CONV real_ss[]) o
        CONV_RULE(SIMP_CONV list_ss thms) o
        BETA_RULE o REWRITE_RULE thms) specialization
val value = sml_of_hol_real_exp (rhs (concl computation))
in
      print "Under the following assumptions:\n";
      print (String.concat (map (fn t => term_to_string t ^ "\n\n") (hyp computation)));
      print "\n\n";
      print "Simplified Reliability Expression of Redundant Star Ring:\n";
      print (term_to_string (concl computation));
      print "\n\n";
      print "Numerically Computed Reliability of Redundant Star Ring:\n";
      print (Real.toString (value) ^ "\n\n")
end;

(*-------------------------------*)
smart_grid_RBD_EVAL1 [`p:α event # α event event # (α event -> real)`,
                      `5.0:real`,
                       `PIED:'a->extreal`,
                        `X_ESW_list:('a->extreal) list list`,
                       `CIED:'a->extreal`,
                       `0.5:real`,
                       `[[0.5;0.6;(1.0:real)]]`,
                       `0.7:real`];

(*-------------------------------*)
smart_grid_RBD_EVAL2 [`p:α event # α event event # (α event -> real)`,
                      `5.0:real`,
                       `PIED:'a->extreal`,
                        `X_ESW_list:('a->extreal) list list`,
                       `CIED:'a->extreal`,
                       `0.5:real`,
                       `[[0.5;0.6;(1.0:real)]]`,
                       `0.7:real`]
                        rel_redund_star_ringRBD
                        [list_sum_def,list_prod_def,one_minus_list_def,exp_func_def,exp_func_list_def,list_prod_def,of_DEF,o_THM];


(*-------------------------------*)
smart_grid_RBD_EVAL2 [`p:α event # α event event # (α event -> real)`,
                      `5.0:real`,
                        `RV_list:('a->extreal) list list`,
                       `[[0.5;0.6;(1.0:real)]]`]
                       rel_series_parallel_RBD_exp_dist_fail_rate
                        [list_sum_def,list_prod_def,one_minus_list_def,exp_func_def,exp_func_list_def,list_prod_def,of_DEF,o_THM];
