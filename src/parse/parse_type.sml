open type_tokens HOLgrammars

open monadic_parse optmonad
infix >- ++ >> >->

datatype grammar_rule =
  SUFFIX of string list
| INFIX of {opname : string, parse_string : string} list * associativity

val std_suffix_precedence = 100

type grammar = (int * grammar_rule) list


datatype 'a pretype =
  pVartype of string | pType of (string * 'a pretype list) | pAQ of 'a


fun n_appls([], t) = t
  | n_appls(op1::ops, t) = n_appls(ops, pType(token_string op1, [t]))
fun n_appls_l([], t) = raise Fail "parse_type.n_appls_l: can't happen"
  | n_appls_l(op1::ops, args) = n_appls(ops, pType(token_string op1, args))

fun parse_type allow_unknown_suffixes G = let
  val lex = type_tokens.lex
  (* extra fails on next two definitions will effectively make the stream
     push back the unwanted token *)
  fun item t = (lex >- (fn t' => if t = t' then return t else fail)) ++ fail
  fun itemP P = (lex >- (fn t => if P t then return t else fail)) ++ fail

  fun parse_base_level f =
    (itemP is_ident >- (fn t => return (pType(token_string t, [])))) ++
    (itemP is_tvar >- (fn t => return (pVartype (token_string t)))) ++
    (itemP is_aq >- (fn t => return (pAQ (dest_aq t)))) ++
    (item LParen >> f >-> item RParen)

  fun parse_op slist =
    itemP (fn t =>
           is_ident t andalso
           (allow_unknown_suffixes orelse
            isSome (List.find (fn s => token_string t = s) slist)))
  fun parse_binop stlist = let
    fun doit t = let
      val result =
        List.find (fn r => (#parse_string r = token_string t)) stlist
    in
      case result of
        NONE => fail
      | SOME r => return (#opname r)
    end
  in
    (itemP is_ident ++ itemP is_typesymbol) >-  doit
  end


  fun parse_term current strm =
    (case current of
       [] => parse_base_level (parse_term G)
     | (x::xs) => parse_rule x xs) strm
  and parse_rule (r as (level, rule)) rs strm = let
    val next_level = parse_term rs
    val same_level = parse_rule r rs
    val tuple_arg =
      item LParen >>
      chainl1
      (parse_term G >- (fn t => return [t]))
      (item Comma >> return (fn tl1 => fn tl2 => tl1 @ tl2)) >-
      (fn args => item RParen >> return args)
  in
    (case rule of
       INFIX (stlist, NONASSOC) =>
         next_level >-                         (fn t1 =>
         (parse_binop stlist >-                (fn opname =>
          next_level >-                        (fn t2 =>
          return (pType(opname, [t1, t2]))))) ++
         (return t1))
     | INFIX (stlist, LEFT) =>
         chainl1 next_level
         (parse_binop stlist >-
          (fn opname => return (fn t1 => fn t2 => pType(opname, [t1, t2]))))
     | INFIX (stlist, RIGHT) =>
         chainr1 next_level
         (parse_binop stlist >-
          (fn opname => return (fn t1 => fn t2 => pType(opname, [t1, t2]))))
     | SUFFIX slist =>
         (next_level >-                             (fn t =>
          many (parse_op slist) >-                  (fn oplist =>
          return (n_appls(oplist, t))))) ++
         (tuple_arg >-                              (fn args =>
          many1 (parse_op slist) >-                 (fn oplist =>
          return (n_appls_l(oplist, args)))))) strm
  end
in
  parse_term G
end

fun merge r1 r2 =
  case (r1, r2) of
    (SUFFIX slist1, SUFFIX slist2) => SUFFIX(Lib.union slist1 slist2)
  | (INFIX(rlist1, a1), INFIX(rlist2, a2)) => let
    in
      if a1 = a2 then INFIX(Lib.union rlist1 rlist2, a1)
      else
        raise GrammarError
          "Attempt to merge two infix types with different associativities"
    end
  | _ => raise GrammarError "Attempt to merge suffix and infix type"

fun insert_sorted0 (k, v) [] = [(k, v)]
  | insert_sorted0 kv1 (wholething as (kv2::rest)) = let
      val (k1, v1) = kv1
      val (k2, v2) = kv2
    in
      if (k1 < k2) then kv1::wholething
      else
        if k1 = k2 then  (k1, merge v1 v2) :: rest
        else
          kv2 :: insert_sorted0 kv1 rest
    end

fun insert_sorted (k, v) G0 = let
  val G1 = insert_sorted0 (k,v) G0
  fun merge_adj_suffixes [] = []
    | merge_adj_suffixes [x] = [x]
    | merge_adj_suffixes (x1::x2::xs) = let
      in
        case (x1, x2) of
          ((p1, SUFFIX slist1), (p2, SUFFIX slist2)) =>
            merge_adj_suffixes ((p1, SUFFIX (Lib.union slist1 slist2))::xs)
        | _ => x1 :: merge_adj_suffixes (x2 :: xs)
      end
in
  merge_adj_suffixes G1
end



fun new_binary_tyop G {precedence, infix_form, opname, associativity} = let
  val rule1 =
    if isSome infix_form then
      (precedence, INFIX([{parse_string = valOf infix_form,
                           opname = opname}],
                         associativity))
    else (precedence, INFIX([{parse_string = opname, opname = opname}],
                            associativity))
  val rule2 = (std_suffix_precedence, SUFFIX[opname])
in
  insert_sorted rule1 (insert_sorted rule2 G)
end

fun new_tyop G name =
  insert_sorted (std_suffix_precedence, SUFFIX[name]) G




val empty_grammar = []

fun rules (G: grammar) = G
