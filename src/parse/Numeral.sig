signature Numeral =
sig
 type term = HolKernel.term
 type num  = Arbnum.num

 val is_numeral     : term -> bool
 val dest_numeral   : term -> Arbnum.num
 val gen_mk_numeral : {mk_comb : 'a * 'a -> 'a,
                       ZERO    : 'a,
                       ALT_ZERO: 'a,
                       NUMERAL : 'a,
                       BIT1    : 'a, 
                       BIT2    : 'a} -> Arbnum.num -> 'a
end
