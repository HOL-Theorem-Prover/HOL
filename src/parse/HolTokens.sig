signature HolTokens =
sig

  type ('a,'b) token = ('a,'b) Token.token
  type svalue = HolMlyValue.svalue

  val EOF:  'a * 'a -> (svalue,'a) token
  val EOLEX:  'a * 'a -> (svalue,'a) token
  val string_: (string) *  'a * 'a -> (svalue,'a) token
  val of_:  'a * 'a -> (svalue,'a) token
  val in_:  'a * 'a -> (svalue,'a) token
  val and_:  'a * 'a -> (svalue,'a) token
  val let_:  'a * 'a -> (svalue,'a) token
  val bar:  'a * 'a -> (svalue,'a) token
  val type_plus:  'a * 'a -> (svalue,'a) token
  val type_hash:  'a * 'a -> (svalue,'a) token
  val arrow:  'a * 'a -> (svalue,'a) token
  val eq:  'a * 'a -> (svalue,'a) token
  val eq_gt:  'a * 'a -> (svalue,'a) token
  val semi_colon:  'a * 'a -> (svalue,'a) token
  val dot:  'a * 'a -> (svalue,'a) token
  val dcolon:  'a * 'a -> (svalue,'a) token
  val colon:  'a * 'a -> (svalue,'a) token
  val type_comma:  'a * 'a -> (svalue,'a) token
  val rbrace:  'a * 'a -> (svalue,'a) token
  val lbrace:  'a * 'a -> (svalue,'a) token
  val rbracket:  'a * 'a -> (svalue,'a) token
  val lbracket:  'a * 'a -> (svalue,'a) token
  val type_rparen:  'a * 'a -> (svalue,'a) token
  val type_lparen:  'a * 'a -> (svalue,'a) token
  val rparen:  'a * 'a -> (svalue,'a) token
  val lparen:  'a * 'a -> (svalue,'a) token
  val aq: (Term.term) *  'a * 'a -> (svalue,'a) token
  val qualified_binder: ( ( string*string ) ) *  'a * 'a -> (svalue,'a) token
  val binder: (string) *  'a * 'a -> (svalue,'a) token
  val type_var_ident: (string) *  'a * 'a -> (svalue,'a) token
  val qualified_type_ident: ( ( string*string ) ) *  'a * 'a -> (svalue,'a) token
  val type_ident: (string) *  'a * 'a -> (svalue,'a) token
  val qualified_ident: ( ( string*string ) ) *  'a * 'a -> (svalue,'a) token
  val symbolic_ident: (string) *  'a * 'a -> (svalue,'a) token
  val ident: (string) *  'a * 'a -> (svalue,'a) token

end;

