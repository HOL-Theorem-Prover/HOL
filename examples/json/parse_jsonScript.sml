open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = new_theory "parse_json";

open stringTheory;

(* TODO: Cannot make object finite map due to HOL4 definitional mechanism... *)
(* TODO: Keeping this very readable (i.e. Object instead of json_obj) for now,
 * since you might actually want to look at the parser's output *)
Datatype:
 json_t =
    Object json_kv_map_t
  | Array (json_t list)
  | String string
  | Number num
  | Boolean bool
  | Null ;

 json_kv_map_t = Map ((string # json_t) list)
End

Definition kv_map_empty:
 kv_map_empty = Map []
End

Definition kv_map_add:
 kv_map_add (k,v) (Map l) = Map ((k,v)::l)
End

Definition kv_map_reverse:
 kv_map_reverse (Map l) = Map (REVERSE l)
End

Definition sym_list:
 sym_list = [#"["; #"]"; #","; #":"; #"{"; #"}"]
End

Definition is_sym:
 is_sym char =
  if MEM char sym_list
  then T
  else F
End

Datatype:
 json_token_t =
    token_id string
  | token_str string
  | token_sym char
  | token_num num
End

(*********)
(* LEXER *)

Definition lex_id:
 (lex_id [] (acc, i) token_l = SOME (((token_id (REVERSE acc))::token_l), i)) /\
 (lex_id (h::t) (acc, i) token_l =
  if (isAlphaNum h \/ (h = #"_"))
  then lex_id t ((h::acc), i+1) token_l
  else SOME (((token_id (REVERSE acc))::token_l), i))
End

Theorem lex_id_index_incr:
 !str acc i token_l token_l' i'.
 (lex_id str (acc, i) token_l = SOME (token_l', i')) ==>
 (i' >= i)
Proof
Induct_on ‘str’ >> (
 fs [lex_id]
) >>
REPEAT STRIP_TAC >>
Cases_on ‘isAlphaNum h ∨ h = #"_"’ >> (
 fs []
) >> (
 RES_TAC >>
 fs []
)
QED

Definition lex_str:
 (lex_str [] _ _ = NONE) /\
 (lex_str (h::t) (acc, i) token_l =
  if (h <> #"\"")
  then lex_str t ((h::acc), i+1) token_l
  else SOME (((token_str (REVERSE acc))::token_l), i))
End

Definition str_to_num':
 (str_to_num' [] acc _ = acc) /\
 (str_to_num' (h::t) acc i =
  str_to_num' t (acc+((ORD h - 48)*i)) (i*10))
End

Definition str_to_num:
 str_to_num str = str_to_num' (REVERSE str) 0 1
End

Definition lex_num:
 (lex_num [] (acc, i) token_l = SOME (((token_num (str_to_num acc))::token_l), i)) /\
 (lex_num (h::t) (acc, i) token_l =
  if isDigit h
  then lex_num t ((h::acc), i+1) token_l
  else SOME (((token_num (str_to_num acc))::token_l), i))
End

Theorem lex_num_index_incr:
 !str acc i token_l token_l' i'.
 (lex_num str (acc, i) token_l = SOME (token_l', i')) ==>
 (i' >= i)
Proof
Induct_on ‘str’ >> (
 fs [lex_num]
) >>
REPEAT STRIP_TAC >>
Cases_on ‘isDigit h’ >> (
 fs []
) >>
RES_TAC >>
fs []
QED

Theorem is_alpha_alphanum:
 !c.
 isAlpha c ==>
 isAlphaNum c
Proof
fs [isAlpha_def, isAlphaNum_def]
QED

(* TODO: Also discard line break and whitespace to give JSON format some slack? *)
val lex = TotalDefn.tDefine "lex" ‘
 (lex ([], token_l) = SOME (REVERSE token_l)) /\
 (lex ((h::t), token_l) =
  let res_opt =
   if isSpace h then SOME (t, token_l)
   else if is_sym h then SOME (t, ((token_sym h)::token_l))
   else if (isAlpha h \/ h = #"_") then
    (case lex_id (h::t) ([], 0) token_l of
     | SOME (token_l', i) => SOME (DROP i (h::t), token_l')
     | NONE => NONE)
   else if h = #"\"" then 
    (case lex_str t ([], 0) token_l of
     | SOME (token_l', i) => SOME (DROP (i+1) t, token_l')
     | NONE => NONE)
   else if isDigit h then 
    (case lex_num (h::t) ([], 0) token_l of
     | SOME (token_l', i) => SOME (DROP i (h::t), token_l')
     | NONE => NONE)
   else NONE
  in
  case res_opt of
  | SOME res => lex res
  | NONE => NONE)’ (
WF_REL_TAC `measure (\(str, token_l). STRLEN str)` >>
REPEAT STRIP_TAC >>
Cases_on ‘isSpace h’ >> (
 fs []
) >>
Cases_on ‘is_sym h’ >> (
 fs []
) >>
Cases_on ‘isAlpha h’ >> (
  fs [lex_id, is_alpha_alphanum]
) >| [
 Cases_on ‘lex_id t (STRING h "",1) token_l’ >> (
  fs []
 ) >>
 Cases_on ‘x’ >> (
  fs []
 ) >>
 IMP_RES_TAC lex_id_index_incr >>
 rw [],

 Cases_on ‘h = #"_"’ >> (
  fs [lex_id]
 ) >- (
  Cases_on ‘lex_id t ("_",1) token_l’ >> (
   fs []
  ) >>
  Cases_on ‘x’ >> (
   fs []
  ) >>
  IMP_RES_TAC lex_id_index_incr >>
  rw []
 ) >>
 Cases_on ‘h = #"\""’ >> (
  fs []
 ) >| [
  Cases_on ‘lex_str t ("",0) token_l’ >> (
   fs []
  ) >>
  Cases_on ‘x’ >> (
   fs []
  ) >>
  rw [],

  Cases_on ‘lex_num (STRING h t) ("",0) token_l’ >> (
   fs [lex_num]
  ) >>
  Cases_on ‘x’ >> (
   fs []
  ) >>
  rfs [] >>
  IMP_RES_TAC lex_num_index_incr >>
  rw []
 ]
]
);

(**********)
(* PARSER *)

Definition parse_token_id:
parse_token_id id =
 if id = "null"
 then SOME Null
 else if id = "true"
 then SOME (Boolean T)
 else if id = "false"
 then SOME (Boolean F)
 else NONE
End

Definition sum_size:
 (sum_size (INR (INR (INR (kv_map:json_kv_map_t, token_l:json_token_t list)))) = LENGTH token_l) /\
 (sum_size (INR (INR (INL (kv_map:json_kv_map_t, token_l:json_token_t list)))) = LENGTH token_l) /\
 (sum_size (INR (INL (jsons:json_t list, token_l:json_token_t list))) = LENGTH token_l) /\
 (sum_size (INL (jsons:json_t list, token_l:json_token_t list, expect_v:bool)) =
   LENGTH token_l)
End

(* TODO: This should ideally return NONE for malformed input in a lot more places *)
val [parse_json_def, parse_json_delim_def, parse_kv_def, parse_kv_delim_def] =
 CONJUNCTS $ TotalDefn.tDefine "parse_json_kv_def"
 ‘(parse_json jsons token_l expect_v =
    case token_l of
    | [] =>
     if expect_v
     then NONE
     else SOME (REVERSE jsons, [])
    | ((token_str str)::token_l') =>
     if expect_v
     then SOME ([String str], token_l')
     else parse_json_delim ((String str)::jsons) token_l'
    | ((token_id id)::token_l') =>
     (case parse_token_id id of
      | SOME json_id =>
       if expect_v
       then SOME ([json_id], token_l')
       else parse_json_delim (json_id::jsons) token_l'
      | NONE => NONE)
    | ((token_num n)::token_l') =>
     if expect_v
     then SOME ([Number n], token_l')
     else parse_json_delim ((Number n)::jsons) token_l'
    | ((token_sym #"[")::((token_sym #"]")::token_l')) =>
     if expect_v
     then SOME ([Array []], token_l')
     else parse_json_delim ((Array [])::jsons) token_l'
    | ((token_sym #"[")::token_l') =>
     (case parse_json [] token_l' F of
      | SOME (jsons', token_l'') =>
       (case (LENGTH token_l'' < LENGTH token_l') of
        | T =>
         if expect_v
         then SOME ([Array jsons'], token_l'')
         else parse_json_delim ((Array jsons')::jsons) token_l''
        | F => NONE)
      | _ => NONE)
    | ((token_sym #"{")::token_l') =>
     (case parse_kv kv_map_empty token_l' of
      | SOME (kvs, ((token_sym #"}")::token_l'')) =>
       (case (LENGTH token_l'' < LENGTH token_l') of
        | T =>
         if expect_v
         then SOME ([Object (kv_map_reverse kvs)], token_l'')
         else parse_json_delim ((Object (kv_map_reverse kvs))::jsons) token_l''
        | F => NONE)
      | _ => NONE)
    | _ => NONE) /\
 (parse_json_delim jsons token_l =
   case token_l of
   | ((token_sym #",")::token_l') =>
    parse_json jsons token_l' F
   | ((token_sym #"]")::token_l') =>
    SOME ((REVERSE jsons), token_l')
   | [] => SOME (REVERSE jsons, [])
   | _ => NONE) /\
 (parse_kv kv_map token_l =
   case token_l of
   | ((token_id k)::((token_sym #":")::token_l')) =>
    (case parse_json [] token_l' T of
     | SOME ([json], token_l'') =>
      (case (LENGTH token_l'' < LENGTH token_l') of
       | T =>
        parse_kv_delim (kv_map_add (k, json) kv_map) token_l''
       | F => NONE)
     | _ => NONE)
   | ((token_str k)::((token_sym #":")::token_l')) =>
    (case parse_json [] token_l' T of
     | SOME ([json], token_l'') =>
      (case (LENGTH token_l'' < LENGTH token_l') of
       | T =>
        parse_kv_delim (kv_map_add (k, json) kv_map) token_l''
       | F => NONE)
     | _ => NONE)
   | _ => SOME (kv_map, token_l)) /\
 (parse_kv_delim kv_map token_l =
   case token_l of
   | ((token_sym #",")::token_l') => parse_kv kv_map token_l'
   | ((token_sym #"}")::token_l') => SOME (kv_map,token_l)
   | _ => NONE)’
(WF_REL_TAC `measure sum_size` >>
fs [sum_size])
;

Definition json_of_string:
(json_of_string str = 
 case lex (str, []) of
 | SOME token_l =>
  (case parse_json [] token_l F of
   | SOME (json, []) => SOME json
   | _ => NONE)
 | _ => NONE
)
End

val _ = export_theory ();
