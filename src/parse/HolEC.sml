structure HolEC =
struct
open LRTable

val is_keyword = fn _ => false
val preferred_change = nil
val noShift = fn (T 34) => true | _ => false

val showTerminal = fn (T 0) => "ident"
                    | (T 1) => "symbolic_ident"
                    | (T 2) => "qualified_ident"
                    | (T 3) => "type_ident"
                    | (T 4) => "qualified_type_ident"
                    | (T 5) => "type_var_ident"
                    | (T 6) => "binder"
                    | (T 7) => "qualified_binder"
                    | (T 8) => "aq"
                    | (T 9) => "lparen"
                    | (T 10) => "rparen"
                    | (T 11) => "type_lparen"
                    | (T 12) => "type_rparen"
                    | (T 13) => "lbracket"
                    | (T 14) => "rbracket"
                    | (T 15) => "lbrace"
                    | (T 16) => "rbrace"
                    | (T 17) => "type_comma"
                    | (T 18) => "colon"
                    | (T 19) => "dcolon"
                    | (T 20) => "dot"
                    | (T 21) => "semi_colon"
                    | (T 22) => "eq_gt"
                    | (T 23) => "eq"
                    | (T 24) => "arrow"
                    | (T 25) => "type_hash"
                    | (T 26) => "type_plus"
                    | (T 27) => "bar"
                    | (T 28) => "let_"
                    | (T 29) => "and_"
                    | (T 30) => "in_"
                    | (T 31) => "of_"
                    | (T 32) => "string_"
                    | (T 33) => "EOLEX"
                    | (T 34) => "EOF"
                    | _ => "bogus-term"

local open HolHeader 
in val errtermvalue = fn _ => HolMlyValue.VOID
end

val terms = (T 9) :: (T 10) :: (T 11) :: (T 12) :: (T 13) :: (T 14)
 :: (T 15) :: (T 16) :: (T 17) :: (T 18) :: (T 19) :: (T 20) :: (T 21)
 :: (T 22) :: (T 23) :: (T 24) :: (T 25) :: (T 26) :: (T 27) :: (T 28)
 :: (T 29) :: (T 30) :: (T 31) :: (T 33) :: (T 34) :: nil

end
