signature Literal =
sig
 type term = HolKernel.term
 type num  = Arbnum.num

 val is_zero        : term -> bool
 val is_numeral     : term -> bool
 val dest_numeral   : term -> Arbnum.num
 val gen_mk_numeral : {mk_comb : 'a * 'a -> 'a,
                       ZERO    : 'a,
                       ALT_ZERO: 'a,
                       NUMERAL : 'a,
                       BIT1    : 'a,
                       BIT2    : 'a} -> Arbnum.num -> 'a

 val is_emptystring  : term -> bool
 val is_string_lit   : term -> bool
 val dest_string_lit : term -> String.string
 val mk_string_lit   : {mk_string   : 'a * 'a -> 'a,
                        emptystring : 'a,
                        fromMLchar  : char -> 'a} -> String.string -> 'a

 val is_char_lit     : term -> bool
 val dest_char_lit   : term -> Char.char

 val is_literal      : term -> bool
 val is_pure_literal : term -> bool
 val other_literals  : (term -> bool) ref

 val relaxed_dest_numeral : term -> Arbnum.num
 val relaxed_dest_string_lit : term -> String.string
end
