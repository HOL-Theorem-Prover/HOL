structure HolTokens :> HolTokens =
struct

type svalue = HolParserData.svalue
type ('a,'b) token = ('a,'b) Token.token

fun ident (i,p1,p2) = Token.TOKEN (LRTable.T 0,(HolMlyValue.ident i,p1,p2))
fun symbolic_ident(i,p1,p2) = Token.TOKEN(LRTable.T 1,
                                          (HolMlyValue.symbolic_ident i,p1,p2))
fun qualified_ident (i,p1,p2) = Token.TOKEN (LRTable.T 2,
                                         (HolMlyValue.qualified_ident i,p1,p2))
fun type_ident(i,p1,p2) = Token.TOKEN(LRTable.T 3,
                                      (HolMlyValue.type_ident i,p1,p2))
fun qualified_type_ident (i,p1,p2) = Token.TOKEN(LRTable.T 4,
                                   (HolMlyValue.qualified_type_ident i,p1,p2))
fun type_var_ident (i,p1,p2) = Token.TOKEN (LRTable.T 5,
                                         (HolMlyValue.type_var_ident i,p1,p2))
fun binder (i,p1,p2) = Token.TOKEN (LRTable.T 6,(HolMlyValue.binder i,p1,p2))
fun qualified_binder (i,p1,p2) = Token.TOKEN (LRTable.T 7,
                                       (HolMlyValue.qualified_binder i,p1,p2))
fun aq (i,p1,p2) = Token.TOKEN (LRTable.T 8,(HolMlyValue.aq i,p1,p2))
fun lparen (p1,p2) = Token.TOKEN (LRTable.T 9,(HolMlyValue.VOID,p1,p2))
fun rparen (p1,p2) = Token.TOKEN (LRTable.T 10,(HolMlyValue.VOID,p1,p2))
fun type_lparen (p1,p2) = Token.TOKEN (LRTable.T 11,(HolMlyValue.VOID,p1,p2))
fun type_rparen (p1,p2) = Token.TOKEN (LRTable.T 12,(HolMlyValue.VOID,p1,p2))
fun lbracket (p1,p2) = Token.TOKEN (LRTable.T 13,(HolMlyValue.VOID,p1,p2))
fun rbracket (p1,p2) = Token.TOKEN (LRTable.T 14,(HolMlyValue.VOID,p1,p2))
fun lbrace (p1,p2) = Token.TOKEN (LRTable.T 15,(HolMlyValue.VOID,p1,p2))
fun rbrace (p1,p2) = Token.TOKEN (LRTable.T 16,(HolMlyValue.VOID,p1,p2))
fun type_comma (p1,p2) = Token.TOKEN (LRTable.T 17,(HolMlyValue.VOID,p1,p2))
fun colon (p1,p2) = Token.TOKEN (LRTable.T 18,(HolMlyValue.VOID,p1,p2))
fun dcolon (p1,p2) = Token.TOKEN (LRTable.T 19,(HolMlyValue.VOID,p1,p2))
fun dot (p1,p2) = Token.TOKEN (LRTable.T 20,(HolMlyValue.VOID,p1,p2))
fun semi_colon (p1,p2) = Token.TOKEN (LRTable.T 21,(HolMlyValue.VOID,p1,p2))
fun eq_gt (p1,p2) = Token.TOKEN (LRTable.T 22,(HolMlyValue.VOID,p1,p2))
fun eq (p1,p2) = Token.TOKEN (LRTable.T 23,(HolMlyValue.VOID,p1,p2))
fun arrow (p1,p2) = Token.TOKEN (LRTable.T 24,(HolMlyValue.VOID,p1,p2))
fun type_hash (p1,p2) = Token.TOKEN (LRTable.T 25,(HolMlyValue.VOID,p1,p2))
fun type_plus (p1,p2) = Token.TOKEN (LRTable.T 26,(HolMlyValue.VOID,p1,p2))
fun bar (p1,p2) = Token.TOKEN (LRTable.T 27,(HolMlyValue.VOID,p1,p2))
fun let_ (p1,p2) = Token.TOKEN (LRTable.T 28,(HolMlyValue.VOID,p1,p2))
fun and_ (p1,p2) = Token.TOKEN (LRTable.T 29,(HolMlyValue.VOID,p1,p2))
fun in_ (p1,p2) = Token.TOKEN (LRTable.T 30,(HolMlyValue.VOID,p1,p2))
fun of_ (p1,p2) = Token.TOKEN (LRTable.T 31,(HolMlyValue.VOID,p1,p2))
fun string_ (i,p1,p2) = Token.TOKEN (LRTable.T 32,
                                     (HolMlyValue.string_ i,p1,p2))
fun EOLEX (p1,p2) = Token.TOKEN (LRTable.T 33,(HolMlyValue.VOID,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (LRTable.T 34,
                               (HolMlyValue.VOID,p1,p2))
end
