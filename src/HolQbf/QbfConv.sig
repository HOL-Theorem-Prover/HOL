signature QbfConv = sig
  type conv = Abbrev.conv

  (* put an arbitrary QBF into the required form *)
  (* specifically,
     input term:
       - has type bool
       - is closed
       - contains only:
         - first order connectives (/\,\/,==>,~)
            (TODO: allow equality?)
         - quantifiers (!,?)
         - variables
     output term:
       - of the form Q_1 x_1. ... Q_n x_n. phi
       - each Q_i is either ! or ?
       - Q_n is ?
       - each x_i appears in phi
       - phi is closed and in CNF
     alternatively, the output term might simply be 'T' or 'F'
  *)
  val qbf_prenex_conv : conv

  (* conversion that takes [!x:bool. t] where t is in CNF and may contain x and
  removes the quantifier and all occurrences of x *)
  val remove_forall : conv

  (* [last_quant_conv (fc,ec)] strips a quantifier (! and ? only) prefix down
  to the last quantifier then applies fc if the last quantifier is forall, or
  else ec if it is exists *)
  val last_quant_conv : (conv * conv) -> conv

end
