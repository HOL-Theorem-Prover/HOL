(*
 This JSON parser has been validated using the "Parsing JSON is a Minefield" test suite: https://github.com/nst/JSONTestSuite

 A few caveats apply:
 * Unicode characters are represented as their four-digit hexadecimal UTF-8 encoding prefixed by "\u". Backslashes are represented by \u005C, while quotation marks (") are represented by \".
 * "e" vs. "E" in exponential representation is not kept track of: "E" is always used in serialisation. Also, serialisation never prints an explicit "+" for positive exponents.
 * Leading zeroes in the exponent are not kept track of.
*)

open HolKernel boolLib Parse bossLib ;
open BasicProvers boolSimps markerLib optionTheory ;
open listTheory rich_listTheory ;
open stringTheory ASCIInumbersTheory arithmeticTheory ;
open integerTheory ratTheory;

val _ = new_theory "parse_json";

(* JSON numbers are arbitrary-precision numbers in the format s * 10 ^ e,
   where s is a rational number with finite decimal expansion and e is an integer.
   A few details about how JSON numbers are represented as strings:
   * No leading zeroes are used when representing s.
   * Leading zeroes in e are not disallowed (in both ECMA-404 and RFC 8259).
   * The decimal separator in s is a dot, with no other separators allowed.
   * The base 10-exponentiation is denoted using either "e" or "E".
   * The exponent e, if positive, may be prefixed with an explicit "+".

   When representing JSON numbers in HOL4, 0 and -0 must be kept distinct, since
   they may be treated differently by the external tools that read the JSON.
   Since 0 = -0 for int and rat, we must keep track of the sign explicitly.
   It is probably also a good idea to keep track of trailing zeroes in the decimal
   expansion, which may be eaten by HOL4 if rat is used (may be used to infer precision).

   Accordingly, json_num is defined as a tuple of
   the integer component of s: (sign # num);
   the decimal expansion of s: ((num # num) option), where the first number signifies
                               the number of leading zeroes;
   and the exponent e: ((sign # num) option). *)

(* TODO: json_num could be swapped out, in whole or in part, for a more generic
   number representation elsewhere in HOL4, so long as this conserves minus zero
   and trailing decimal zeroes. *)

Datatype:
  sign =
     Positive
   | Negative
End
Type json_num = “:((sign # num) # ((num # num) option) # ((sign # num) option))”

Definition sign_num_to_int_def:
  sign_num_to_int (sign, n) =
  case sign of
    Positive => int_of_num n
  | Negative => - int_of_num n
End

Definition json_num_to_int_def:
  json_num_to_int (((sign, n), frac_opt, exp_opt):json_num) =
  let i = sign_num_to_int (sign, n) in
    case frac_opt of
      NONE =>
        (case exp_opt of
           SOME (exp_sign, exp_n) =>
             (case exp_sign of
                Positive => SOME $ i * (&(10 ** exp_n))
              | Negative => SOME $ FUNPOW (\i'. i' / 10) exp_n i)
         | NONE => SOME i)
    | SOME _ => NONE
End

Definition zeroes_num_to_rat_def:
  (zeroes_num_to_rat (0:num, n:num) = rat_of_num n) /\
  (zeroes_num_to_rat (SUC n_zeroes, n) =
   zeroes_num_to_rat (n_zeroes, n DIV 10))
End

Definition json_num_to_rat_def:
  json_num_to_int (((sign, n), frac_opt, exp_opt):json_num) =
  let i = rat_of_int $ sign_num_to_int (sign, n) in
  let r = case frac_opt of
      NONE => 0
    | SOME (n_zeroes, f) => zeroes_num_to_rat (n_zeroes + (LOG 10 f + 1), f) in
    case exp_opt of
      SOME (exp_sign, exp_n) =>
        (case exp_sign of
           Positive =>
             FUNPOW (\i'. i' * 10) exp_n (i + r)
         | Negative =>
             FUNPOW (\i'. i' / 10) exp_n (i + r))
    | NONE => i + r
End

Datatype:
  json =
     Object ((string # json) list)
   | Array (json list)
   | String string
   | Number json_num
   | Bool bool
   | Null
End

val json_size_def = fetch "-" "json_size_def";

Theorem json_size_MEM1:
  !l a. MEM a l ==> json_size a < json3_size l
Proof
  Induct >> rw[json_size_def]
  >> res_tac
  >> fs[]
QED

Theorem json_size_MEM2:
  !l a. MEM a l ==> json_size (SND a) + list_size char_size (FST a) < json1_size l
Proof
  Induct >> fs[json_size_def]
  >> gen_tac >> PairCases
  >> rw[]
  >> res_tac >> fs[json_size_def]
QED

Definition concat_with_def:
  (concat_with [] c = []) /\
  (concat_with [s] c = s) /\
  (concat_with (s::ss) c = s ++ (c ++ concat_with ss c))
End

Theorem concat_with_CONS_eq:
  !ls x t. concat_with (x::ls) t
    = (if ~NULL ls then (x ++ t) else x) ++ (concat_with ls t)
Proof
  Cases >> fs[concat_with_def]
QED

Theorem concat_with_APPEND:
  !ls ls' t. concat_with (ls ++ ls') t = ((concat_with ls t) ++
    (if ~NULL ls /\ ~NULL ls' then t else []) ++ (concat_with ls' t))
Proof
  Induct
  >> rw[concat_with_def]
  >> fs[PULL_FORALL,iffLR NULL_EQ,concat_with_def,concat_with_CONS_eq]
  >> IF_CASES_TAC
  >> fs[NULL_EQ]
QED

Theorem concat_with_REVERSE:
  !ls t. REVERSE $ concat_with ls t = concat_with (REVERSE $ MAP REVERSE ls) (REVERSE t)
Proof
  Induct
  >> fs[concat_with_def]
  >> rpt gen_tac
  >> qmatch_goalsub_rename_tac `h::ls`
  >> Cases_on `ls`
  >> fs[concat_with_def]
  >> simp[concat_with_APPEND,concat_with_def]
QED

Definition printable_def:
  printable c <=> 32 <= ORD c /\ ORD c < 127 /\ c <> #"\"" /\ c <> #"\\"
End

Definition num_to_hex_digit_def:
  num_to_hex_digit n =
    if n < 10 then [CHR (48 + n)] else
    if n < 16 then [CHR (55 + n)] else []
End

Definition n_rev_hex_digs_def:
  n_rev_hex_digs 0 x = [] /\
  n_rev_hex_digs (SUC n) x = (num_to_hex_digit (x MOD 16) ++
    n_rev_hex_digs n (x DIV 16))
End

(* Replaces ASCIInumbersTheory.num_to_dec_string_def, since CakeML doesn't like
 * MAP HEX (n2l 10 n) *)
Definition map_hex_def:
  (map_hex [] = []) /\
  (map_hex (h::t) = HEX h :: map_hex t)
End

Definition num_to_dec_string'_def:
  toString' n =
    REVERSE (map_hex (n2l 10 n))
End

Definition encode_str_def:
  encode_str unicode s =
  let s2 = EXPLODE s in
  if EVERY printable s2 then s
  else FLAT $ MAP (λc.
    if printable c then [c]
    else if unicode then ("\\u" ++ (REVERSE $ n_rev_hex_digs 4 (ORD c)))
    else "\\" ++ (toString' (ORD c))
  ) s2
End

(*
Example:
EVAL ``json_to_string $ Object [("a", String "\t")]``
*)

Definition json_to_string_list_def:
  (json_to_string_list obj =
   case obj of
   | Object mems =>
       ["{"] ++ concat_with (MAP mem_to_string_list mems) [","] ++ ["}"]
   | Array obs =>
       ["["] ++ concat_with (MAP json_to_string_list obs) [","] ++ ["]"]
   | String s => [CONCAT ["\""; encode_str T s; "\""]]
   | Number ((sign, integer), frac_opt, exp_opt) =>
       [if sign = Negative then CONCAT ["-"; toString' integer] else toString' integer;
        (case frac_opt of
         | SOME (n_zeroes, fraction) =>
             CONCAT ["."; IMPLODE $ REPLICATE n_zeroes #"0"; toString' fraction]
         | NONE => "");
        (case exp_opt of
         | SOME (exp_sign, exp) =>
             if exp_sign = Negative
             then CONCAT ["E-"; toString' exp]
             else CONCAT ["E+"; toString' exp]
         | NONE => "")]
    | Bool b => if b then ["true"] else ["false"]
    | Null => ["null"])
  /\
  (mem_to_string_list n_obj =
   let (n, obj) = n_obj in
   [CONCAT ["\""; n; "\""]] ++ [":"] ++ json_to_string_list obj)
Termination
   WF_REL_TAC `measure (\x. case x of
       | INL obj => json_size obj
       | INR p => json2_size p)`
  >> rw[]
  >> imp_res_tac json_size_MEM1
  >> imp_res_tac json_size_MEM2
  >> fs[]
End
Definition json_to_string_def:
  json_to_string obj = CONCAT $ json_to_string_list obj
End

(* lexing *)

Datatype:
  token =
    OBJOPEN | OBJCLOSE | COLON
  | ARROPEN | ARRCLOSE | COMMA
  | NULL
  | BOOL bool
  | Str string
  | NUM json_num
End

Definition MEM'_def:
 (MEM' el [] = F) /\
 (MEM' el (h::t) =
  if el = h
  then T
  else MEM' el t)
End
(* Changed to avoid MEM, for CakeML *)
Definition is_whitespace_def:
  is_whitespace c = MEM' c "\u0020\u000A\u000D\u0009"
End

Definition lex_bool_def:
  lex_bool cs =
    case cs of
    | #"t"::#"r"::#"u"::#"e"::cs => SOME (BOOL T, cs)
    | #"f"::#"a"::#"l"::#"s"::#"e"::cs => SOME (BOOL F, cs)
    | _ => NONE
End

Theorem lex_bool_thm:
  !t cs. lex_bool cs = SOME t <=>
    (cs = "true" ++ SND t /\ FST t = BOOL T)
    \/ (cs = "false" ++ SND t /\ FST t = BOOL F)
Proof
  PairCases
  >> rw[lex_bool_def,IS_SOME_EXISTS]
  >> BasicProvers.every_case_tac
  >> fs[AC CONJ_ASSOC CONJ_COMM]
QED

Definition lex_null_def:
  lex_null cs =
    case cs of
    | #"n"::#"u"::#"l"::#"l"::cs => SOME (NULL, cs)
    | _ => NONE
End

Theorem lex_null_thm:
  !t cs. lex_null cs = SOME t <=> cs = "null" ++ SND t /\ FST t = NULL
Proof
  PairCases
  >> rw[lex_null_def,IS_SOME_EXISTS]
  >> BasicProvers.every_case_tac
  >> fs[AC CONJ_ASSOC CONJ_COMM]
QED

(* Changed to avoid MEM, for CakeML *)
Definition lex_escape_innards_def:
  (lex_escape_innards [] = NONE)
  /\ (lex_escape_innards (c::cs) =
    if MEM' c "\"\\/bfnrt" then SOME (c::#"\\"::[],cs) else
    if c <> #"u" then NONE else
    case cs of
    | a::b::c::d::cs =>
      if EVERY isHexDigit [a;b;c;d]
      then SOME (d::c::b::a::#"u"::#"\\"::[], cs)
      else NONE
    | _ => NONE)
End

Theorem lex_escape_innards_LENGTH:
  !cs v. lex_escape_innards cs = SOME v
  ==> IS_SUFFIX cs $ SND v /\ LENGTH $ SND v < LENGTH cs
Proof
  Cases
  >> rw[lex_escape_innards_def]
  >> fs[IS_SUFFIX_APPEND]
  >> BasicProvers.every_case_tac
  >> gvs[]
QED

Definition lex_str_def:
 (lex_str [] _ = NONE) /\
 (lex_str (c::cs) acc =
  if c <> #"\\" then
    if c = #"\"" then
      SOME (Str (REVERSE acc), cs)
    else lex_str cs (c::acc)
  else
    case lex_escape_innards cs of
    | NONE => NONE
    | SOME (esc, cs) => lex_str cs (esc ++ acc))
Termination
  WF_REL_TAC `measure $ LENGTH o FST` >> rw[]
  >> dxrule_then assume_tac lex_escape_innards_LENGTH
  >> fs[]
End

Theorem lex_str_LENGTH:
  !cs acc v. lex_str cs acc = SOME v
  ==> IS_SUFFIX cs $ SND v /\ LENGTH $ SND v < LENGTH cs
Proof
  gen_tac
  >> completeInduct_on `LENGTH cs`
  >> fs[PULL_FORALL,AND_IMP_INTRO]
  >> Cases
  >> fs[lex_str_def]
  >> rpt gen_tac >> strip_tac
  >> BasicProvers.every_case_tac >> fs[]
  >> imp_res_tac lex_escape_innards_LENGTH
  >> gvs[]
  >- gvs[IS_SUFFIX_APPEND]
  >- gvs[IS_SUFFIX_APPEND]
  >- (
    first_x_assum $ drule_at Any
    >> rw[IS_SUFFIX_APPEND]
    >> qmatch_goalsub_rename_tac `STRING h (STRCAT l _)`
    >> qexists_tac `h::l`
    >> fs[]
  )
  >- (
    first_x_assum $ drule_at Any
    >> rw[IS_SUFFIX_APPEND]
    >> qmatch_goalsub_rename_tac `STRING h (STRCAT l _)`
    >> qexists_tac `h::l`
    >> fs[]
  )
  >> first_x_assum $ drule_at Any
  >> fs[IS_SUFFIX_APPEND]
  >> rw[]
  >> qmatch_goalsub_rename_tac `STRCAT l (STRCAT l' _)`
  >> qexists_tac `STRCAT (#"\\"::l) l'`
  >> fs[]
QED

(*
Example:
EVAL ``lex_num "21149a" 0``
*)

Definition lex_num_def:
  lex_num [] acc = (acc,[]) /\
  (lex_num (c::cs) acc =
    if isDigit c then
      lex_num cs (acc * 10 + (ORD c - ORD #"0"))
    else (acc, c::cs))
End

Definition lex_int_def:
  lex_int [] = NONE /\
  (lex_int (c::cs) =
    let sign = if c = #"-" then Negative else Positive in
    let (nat_num, cs') = if sign = Negative then lex_num cs 0 else lex_num (c::cs) 0 in
    SOME ((sign, nat_num), cs'))
End


Definition lex_leading_zeroes_def:
  lex_leading_zeroes [] (acc:num) = (NONE, []) /\
  (lex_leading_zeroes (c::cs) acc =
    if c = #"0"
    then lex_leading_zeroes cs (acc+1)
    else
      (( \ (a, b). if a = 0 then (if acc > 0 then (SOME (acc-1, a), b) else (NONE, b)) else (SOME (acc, a), b)) (lex_num (c::cs) 0)))
End
Definition lex_frac_def:
  lex_frac [] = (NONE, []) /\
  (lex_frac (c::cs) =
    if c = #"." then
     lex_leading_zeroes cs 0
    else (NONE, c::cs))
End

Definition lex_plus_def:
  lex_plus [] = (NONE, []) /\
  (lex_plus (c::cs) =
    if c = #"+" then
     (case lex_int cs of
         | SOME (int, cs') => (SOME int, cs')
         | NONE => (NONE, c::cs))
    else
     (case lex_int (c::cs) of
         | SOME (int, cs') => (SOME int, cs')
         | NONE => (NONE, c::cs)))
End

Definition lex_exp_def:
  lex_exp [] = (NONE, []) /\
  (lex_exp (c::cs) =
    if (c = #"e" \/ c = #"E") then
     lex_plus cs
    else (NONE, c::cs))
End

Definition lex_sci_def:
  lex_sci [] = NONE /\
  (lex_sci (c::cs) =
    case lex_int (c::cs) of
    | SOME (integer, cs') =>
      let (frac_opt, cs'') = lex_frac cs' in
      let (exp_opt, cs''') = lex_exp cs'' in
        SOME ((integer, frac_opt, exp_opt), cs''')
    | NONE => NONE)
End

Theorem lex_num_SUFFIX:
  !cs n v. lex_num cs n = v ==> IS_SUFFIX cs $ SND v
Proof
  Induct
  >> rw[lex_num_def]
  >> fs[IS_SUFFIX_APPEND,lex_num_def]
  >> qmatch_goalsub_abbrev_tac `lex_num cs num`
  >> first_x_assum $ qspec_then `num` strip_assume_tac
  >> qexists_tac `h::l`
  >> fs[]
QED

Theorem lex_num_LENGTH:
  !cs n v. lex_num cs n = v /\ cs <> SND v ==> LENGTH $ SND v < LENGTH cs
Proof
  rpt strip_tac
  >> drule_then assume_tac lex_num_SUFFIX
  >> fs[IS_SUFFIX_APPEND]
  >> spose_not_then assume_tac
  >> fs[NOT_LESS]
QED

Theorem lex_int_SUFFIX:
  !cs n v. lex_int cs = SOME v ==> IS_SUFFIX cs $ SND v
Proof
  rpt strip_tac
  >> Cases_on `cs`
  >> (fs[lex_int_def])
  >> Cases_on `h = #"-"`
  >> (fs[])
  >- (
    Cases_on `lex_num t 0`
    >> imp_res_tac lex_num_SUFFIX
    >> gvs[IS_SUFFIX_APPEND])
  >> Cases_on `lex_num (STRING h t) 0`
  >> imp_res_tac lex_num_SUFFIX
  >> gvs[IS_SUFFIX_APPEND]
QED

Theorem lex_int_LENGTH:
  !cs v. lex_int cs = SOME v /\ cs <> SND v ==> LENGTH $ SND v < LENGTH cs
Proof
  rpt strip_tac
  >> Cases_on `cs`
  >> (fs[lex_int_def])
  >> Cases_on `h = #"-"`
  >> (fs[])
  >- (
    Cases_on `lex_num t 0`
    >> drule_then assume_tac lex_num_SUFFIX
    >> gvs[IS_SUFFIX_APPEND])
  >> Cases_on `lex_num (STRING h t) 0`
  >> imp_res_tac lex_num_LENGTH
  >> gvs[]
QED

Theorem lex_leading_zeroes_SUFFIX:
  !cs n v. lex_leading_zeroes cs n = v ==> IS_SUFFIX cs $ SND v
Proof
  Induct
  >> (rw[lex_leading_zeroes_def])
  >- (
    fs[IS_SUFFIX_APPEND,lex_leading_zeroes_def]
    >> Cases_on `cs`
    >- (fs[lex_leading_zeroes_def])
    >> first_x_assum $ qspec_then `n+1` strip_assume_tac
    >> qexists_tac ‘STRCAT "0" l’
    >> gvs[])
  >> fs[IS_SUFFIX_APPEND,lex_leading_zeroes_def]
  >> Cases_on ‘n > 0’
  >> (fs[])
  >> Cases_on `lex_num (STRING h cs) 0`
  >> imp_res_tac lex_num_SUFFIX
  >> gvs[IS_SUFFIX_APPEND]
  >> Cases_on ‘q = 0’
  >> (fs[])
QED

Theorem lex_leading_zeroes_LENGTH:
  !cs n v. lex_leading_zeroes cs n = v /\ cs <> SND v ==> LENGTH $ SND v < LENGTH cs
Proof
  rpt strip_tac
  >> drule_then assume_tac lex_leading_zeroes_SUFFIX
  >> fs[IS_SUFFIX_APPEND]
  >> spose_not_then assume_tac
  >> fs[NOT_LESS]
QED

Theorem lex_frac_SUFFIX:
  !cs v. lex_frac cs = v ==> IS_SUFFIX cs $ SND v
Proof
  rpt strip_tac
  >> Cases_on `cs`
  >> (fs[lex_frac_def])
  >> Cases_on `h = #"."`
  >- (
    fs[]
    >> imp_res_tac lex_leading_zeroes_SUFFIX
    >> fs[IS_SUFFIX_APPEND])
  >> gvs[]
QED

Theorem lex_frac_LENGTH:
  !cs v. lex_frac cs = v /\ cs <> SND v ==> LENGTH $ SND v < LENGTH cs
Proof
  rpt strip_tac
  >> Cases_on ‘v’
  >> Cases_on ‘q’
  >- (
    drule_then assume_tac lex_frac_SUFFIX
    >> gvs[IS_SUFFIX_APPEND]
    >> CCONTR_TAC
    >> gs[])
  >> imp_res_tac lex_frac_SUFFIX
  >> fs[IS_SUFFIX_APPEND]
  >> spose_not_then assume_tac
  >> fs[NOT_LESS]
QED

Theorem lex_plus_LENGTH:
  !cs v. lex_plus cs = v /\ cs <> SND v ==> LENGTH $ SND v < LENGTH cs
Proof
  rpt strip_tac
  >> Cases_on `cs`
  >> (gs[lex_plus_def])
  >> Cases_on `h = #"+"`
  >> (gs[])
  >- (
    Cases_on `lex_int t`
    >> (gvs[])
    >> Cases_on `x`
    >> imp_res_tac lex_int_SUFFIX
    >> gvs[IS_SUFFIX_APPEND])
  >> Cases_on `lex_int (STRING h t)`
  >> (gvs[])
  >> Cases_on `x`
  >> imp_res_tac lex_int_LENGTH
  >> gvs[IS_SUFFIX_APPEND]
QED

Theorem lex_exp_LENGTH:
  !cs v. lex_exp cs = v /\ cs <> SND v ==> LENGTH $ SND v < LENGTH cs
Proof
  rpt strip_tac
  >> Cases_on `cs`
  >> (gs[lex_exp_def])
  >> Cases_on `h = #"e" \/ h = #"E"`
  >> (gs[])
  >- (
    imp_res_tac lex_plus_LENGTH
    >> Cases_on ‘t = SND v’
    >> (gs[]))
  >- (
    imp_res_tac lex_plus_LENGTH
    >> Cases_on ‘t = SND v’
    >> (gs[]))
  >> gvs[]
QED

Theorem lex_sci_LENGTH:
  !cs n v. lex_sci cs = SOME v /\ cs <> SND v ==> LENGTH $ SND v < LENGTH cs
Proof
  rpt strip_tac
  >> Cases_on `cs`
  >> (fs[lex_sci_def])
  >> Cases_on `lex_int (STRING h t)`
  >> (fs[])
  >> Cases_on `x`
  >> fs[]
  >> Cases_on `lex_frac r`
  >> fs []
  >> Cases_on `lex_exp r'`
  >> gvs[]
  >> Cases_on `STRING h t <> r`
  >> (Cases_on `r <> r'`)
  >> (Cases_on `r' <> r''`)
  >> (
    imp_res_tac lex_int_LENGTH
    >> imp_res_tac lex_frac_LENGTH
    >> imp_res_tac lex_exp_LENGTH
    >> gvs[])
QED

Definition lex_def:
  (lex [] acc = INL acc) /\
  (lex (c::cs) acc =
   if is_whitespace c then lex cs acc
   else if c = #":" then lex cs (COLON::acc)
   else if c = #"," then lex cs (COMMA::acc)
   else if c = #"{" then lex cs (OBJOPEN::acc)
   else if c = #"}" then lex cs (OBJCLOSE::acc)
   else if c = #"[" then lex cs (ARROPEN::acc)
   else if c = #"]" then lex cs (ARRCLOSE::acc)
   else if c = #"\"" then
     case lex_str cs [] of
     | SOME (tok, cs) => lex cs (tok::acc)
     | NONE => INR $ "unbalanced string: " ++ TAKE 10 (c::cs)
   else if c = #"t" \/ c = #"f" then
     case lex_bool (c::cs) of
     | SOME (tok, cs) => lex cs (tok::acc)
     | NONE => INR $ "unexpected characters: " ++ TAKE 10 (c::cs)
   else if c = #"n" then
     case lex_null (c::cs) of
     | SOME (tok, cs) => lex cs (tok::acc)
     | NONE => INR ("unexpected characters: " ++ TAKE 10 (c::cs))
   else
     case lex_sci (c::cs) of
     | SOME (json_num, cs') =>
         if cs' = c::cs then
           INR $ "unexpected characters: " ++ TAKE 10 (c::cs)
         else lex cs' ((NUM json_num)::acc)
     | NONE => INR $ "unexpected characters: " ++ TAKE 10 (c::cs)
  )
Termination
  WF_REL_TAC `measure $ LENGTH o FST`
  >> (rw[]
      >> gs[lex_null_thm,lex_bool_thm])
  >- (imp_res_tac lex_sci_LENGTH >> gs[])
  >> (imp_res_tac lex_str_LENGTH >> gs[])
End

(*
 * stack of parsed items.
 *   OBJV is a json value that expects a key, and an object list
 *   OBJ is an object
 *   ARR is an array
*)
Datatype:
  parsestack = OBJV json ((string # json) list) | OBJ ((string # json) list) | ARR (json list)
End

(* parse arguments: token stream, nesting level, json value expected *)

Definition parse_def:
     parse [] _ T = INL "unexpected EOF"
  /\ parse (NULL::ts) ns T =
    (case ns of
    | (OBJ acc)::ns => parse ts ((OBJV Null acc)::ns) F
    | (ARR acc)::ns => parse ts ((ARR $ Null::acc)::ns) F
    | ns => INR (Null, ts, ns))
  /\ parse ((BOOL b)::ts) ns T =
    (case ns of
    | (OBJ acc)::ns => parse ts ((OBJV (Bool b) acc)::ns) F
    | (ARR acc)::ns => parse ts ((ARR $ (Bool b)::acc)::ns) F
    | ns => INR (Bool b, ts, ns))
  /\ parse ((Str s)::ts) ns T =
    (case ns of
    | (OBJ acc)::ns => parse ts ((OBJV (String s) acc)::ns) F
    | (ARR acc)::ns => parse ts ((ARR $ (String s)::acc)::ns) F
    | ns => INR (String s, ts, ns))
  /\ parse ((NUM json_num)::ts) ns T =
    (case ns of
    | (OBJ acc)::ns => parse ts ((OBJV (Number json_num) acc)::ns) F
    | (ARR acc)::ns => parse ts ((ARR $ (Number json_num)::acc)::ns) F
    | ns => INR (Number json_num, ts, ns))
  /\ parse (OBJCLOSE::OBJOPEN::ts) ((ARR acc)::ns) T
    = parse ts ((ARR $ (Object [])::acc)::ns) F
  /\ parse (OBJCLOSE::OBJOPEN::ts) ((OBJ acc)::ns) T
    = parse ts ((OBJV (Object []) acc)::ns) F
  /\ parse (OBJCLOSE::OBJOPEN::ts) ns T = INR (Object [], ts, ns)
  /\ parse (OBJCLOSE::ts) ns T = parse ts ((OBJ [])::ns) T
  /\ parse (ARRCLOSE::ARROPEN::ts) ((ARR acc)::ns) T
    = parse ts ((ARR $ (Array [])::acc)::ns) F
  /\ parse (ARRCLOSE::ARROPEN::ts) ((OBJ acc)::ns) T
    = parse ts ((OBJV (Array []) acc)::ns) F
  /\ parse (ARRCLOSE::ARROPEN::ts) ns T = INR (Array [], ts, ns)
  /\ parse (ARRCLOSE::ts) ns T = parse ts ((ARR [])::ns) T
  /\ parse (ARROPEN::ts) ((ARR aacc)::(OBJ oacc)::ns) F
    = parse ts ((OBJV (Array aacc) oacc)::ns) F
  /\ parse (ARROPEN::ts) ((ARR acc)::(ARR acc')::ns) F
    = parse ts ((ARR $ (Array acc)::acc')::ns) F
  /\ parse (ARROPEN::ts) ((ARR acc)::ns) F = INR (Array acc, ts, ns)
  /\ parse (COMMA::ts) ((ARR acc)::ns) F = parse ts ((ARR acc)::ns) T
  /\ parse (COLON::(Str s)::OBJOPEN::ts) ((OBJV v oacc)::(ARR aacc)::ns) F
    = parse ts ((ARR $ (Object $ (s,v)::oacc)::aacc)::ns) F
  /\ parse (COLON::(Str s)::OBJOPEN::ts) ((OBJV v acc)::(OBJ acc')::ns) F
    = parse ts ((OBJV (Object $ (s,v)::acc) acc')::ns) F
  /\ parse (COLON::(Str s)::OBJOPEN::ts) ((OBJV v acc)::ns) F
    = INR (Object $ (s,v)::acc, ts, ns)
  /\ parse (COLON::(Str s)::COMMA::ts) ((OBJV v acc)::ns) F
    = parse ts ((OBJ $ (s,v)::acc)::ns) T
  /\ parse _ _ _ = INL "error"
End

Definition json_to_tok_def:
  (json_to_tok obj =
   case obj of
   | Object mems =>
       [OBJCLOSE] ++
       (REVERSE $ concat_with (MAP mem_to_tok mems) [COMMA]) ++
       [OBJOPEN]
   | Array obs =>
       [ARRCLOSE] ++
       (REVERSE $ concat_with (MAP json_to_tok obs) [COMMA]) ++
       [ARROPEN]
   | String s => [Str s]
   | Number json_num => [NUM json_num]
   | Bool b => [BOOL b]
   | Null => [NULL])
  /\
  (mem_to_tok n_obj = let (n, obj) = n_obj in
   json_to_tok obj ++ [COLON; Str n])
Termination
   WF_REL_TAC `measure (\x. case x of
       | INL obj => json_size obj
       | INR p => json2_size p)`
  >> rw[]
  >> imp_res_tac json_size_MEM1
  >> imp_res_tac json_size_MEM2
  >> fs[]
End

(*
Theorem lex_json_to_string_eq_json_to_tok:
  !obj. lex (json_to_string obj) [] = INL $ json_to_tok obj
Proof
  TODO
QED

(* Correctness: serialise then parse *)

Theorem parse_json_to_tok_eq_ID:
  !obj. parse (json_to_tok obj) [] T = INR (obj,[],[])
Proof
  TODO
QED

Theorem parse_json_to_string_eq_ID:
  !obj ts. lex (json_to_string obj) [] = INL ts
  ==> parse ts [] T = INR (obj,[],[])
Proof
  fs[lex_json_to_string_eq_json_to_tok,parse_json_to_tok_eq_ID]
QED

(* Correctness: parse then serialise *)

Theorem json_to_tok_parse_eq_ID:
  !obj ts. parse ts [] T = INR (obj, [], [])
  ==> json_to_tok obj = ts
Proof
  TODO
QED
*)

(*
Examples:
EVAL ``lex "{}" []``
EVAL ``lex "\"\"\"" []``
EVAL ``lex "\"\"" []``
EVAL ``lex "{ \"a\" : -1 }" []``
EVAL ``lex "{ \"a\" : -1.3333 }" []``
EVAL ``lex "{ \"a\" : -1.3333e-10 }" []``
EVAL ``parse [OBJCLOSE; OBJOPEN] [] T``
EVAL ``parse [OBJCLOSE; OBJCLOSE; OBJOPEN] [] T``
EVAL ``parse (OUTL $ lex "{\"1\": {\"2\": {\"3\": [{\"4\": {}}]}}}" []) [] T``
EVAL ``json_to_string $ Object [("a",Array [])]``
EVAL ``json_to_string $ String "\u0022"``
*)

val _ = export_theory();
