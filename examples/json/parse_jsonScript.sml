open HolKernel boolLib Parse bossLib ;
open BasicProvers boolSimps markerLib optionTheory ;
open listTheory rich_listTheory ;
open stringTheory ASCIInumbersTheory arithmeticTheory ;

val _ = new_theory "parse_json";

Datatype:
  json =
     Object ((string # json ) list)
   | Array (json list)
   | String string
   | Number num
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

Definition encode_str_def:
  encode_str unicode s =
  let s2 = EXPLODE s in
  if EVERY printable s2 then s
  else FLAT $ MAP (λc.
    if printable c then [c]
    else if unicode then ("\\u" ++ (REVERSE $ n_rev_hex_digs 4 (ORD c)))
    else "\\" ++ (toString (ORD c))
  ) s2
End

(*
Example:
EVAL ``json_to_string $ Object [("a", String "\t")]``
*)

Definition json_to_string_def:
  (json_to_string obj =
    case obj of
        | Object mems => ["{"] ++
                concat_with (MAP mem_to_string mems) ([","]) ++
                ["}"]
        | Array obs => ["["] ++
                concat_with (MAP json_to_string obs) ([","]) ++
                ["]"]
       | String s => [CONCAT ["\""; encode_str T s; "\""]]
       | Number i => [toString i]
       | Bool b => if b then ["true"] else ["false"]
       | Null => ["null"])
  /\
  (mem_to_string n_obj = let (n, obj) = n_obj in
       [CONCAT ["\""; n; "\""]]
       ++ [":"] ++ json_to_string obj)
Termination
   WF_REL_TAC `measure (\x. case x of
       | INL obj => json_size obj
       | INR p => json2_size p)`
  >> rw[]
  >> imp_res_tac json_size_MEM1
  >> imp_res_tac json_size_MEM2
  >> fs[]
End

(* lexing *)

Datatype:
  token =
    OBJOPEN | OBJCLOSE | COLON
  | ARROPEN | ARRCLOSE | COMMA
  | NULL
  | BOOL bool
  | Str string
  | NUM num
End

Definition is_whitespace_def:
  is_whitespace c = MEM c "\u0020\u000A\u000D\u0009"
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

Definition lex_escape_innards_def:
  (lex_escape_innards [] = NONE)
  /\ (lex_escape_innards (c::cs) =
    if MEM c "\"\\/bfnrt" then SOME (c::#"\\"::[],cs) else
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
Examle:
EVAL ``lex_num "21149a" 0``
*)

Definition lex_num_def:
  lex_num [] acc = (acc,[])
  /\ (lex_num (c::cs) acc =
    if isDigit c then
      lex_num cs (acc * 10 + (ORD c - ORD #"0"))
    else (acc, c::cs))
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

Definition lex_def:
  (lex [] acc = INL acc)
  /\ (lex (c::cs) acc =
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
      | NONE => INR $ "unbalanced string" ++ TAKE 10 (c::cs)
    else if c = #"t" \/ c = #"f" then
      case lex_bool (c::cs) of
      | SOME (tok, cs) => lex cs (tok::acc)
      | NONE => INR $ "unexpected characters" ++ TAKE 10 (c::cs)
    else if c = #"n" then
      case lex_null (c::cs) of
      | SOME (tok, cs) => lex cs (tok::acc)
      | NONE => INR ("unexpected characters" ++ TAKE 10 (c::cs))
    else let (num, cs') = lex_num cs 0 in
      if cs' = cs then
        INR $ "unexpected characters" ++ TAKE 10 (c::cs)
      else lex cs' ((NUM num)::acc)
  )
Termination
  WF_REL_TAC `measure $ LENGTH o FST`
  >> rw[]
  >> gvs[lex_null_thm,lex_bool_thm]
  >> imp_res_tac lex_str_LENGTH
  >> gs[]
  >> drule $ GSYM lex_num_LENGTH
  >> fs[]
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
  /\ parse (NULL::ts) ((ARR acc)::ns) T     = parse ts ((ARR $ Null::acc)::ns) F
  /\ parse ((BOOL b)::ts) ((ARR acc)::ns) T = parse ts ((ARR $ (Bool b)::acc)::ns) F
  /\ parse ((Str s)::ts) ((ARR acc)::ns) T  = parse ts ((ARR $ (String s)::acc)::ns) F
  /\ parse ((NUM n)::ts) ((ARR acc)::ns) T  = parse ts ((ARR $ (Number n)::acc)::ns) F
  /\ parse (NULL::ts) ((OBJ acc)::ns) T     = parse ts ((OBJV Null acc)::ns) F
  /\ parse ((BOOL b)::ts) ((OBJ acc)::ns) T = parse ts ((OBJV (Bool b) acc)::ns) F
  /\ parse ((Str s)::ts) ((OBJ acc)::ns) T  = parse ts ((OBJV (String s) acc)::ns) F
  /\ parse ((NUM n)::ts) ((OBJ acc)::ns) T  = parse ts ((OBJV (Number n) acc)::ns) F
  /\ parse (NULL::ts) ns T     = INR (Null, ts, ns)
  /\ parse ((BOOL b)::ts) ns T = INR (Bool b, ts, ns)
  /\ parse ((Str s)::ts) ns T  = INR (String s, ts, ns)
  /\ parse ((NUM n)::ts) ns T  = INR (Number n, ts, ns)
  /\ parse (OBJCLOSE::OBJOPEN::ts) ((ARR acc)::ns) T
    = parse ts ((ARR $ (Object [])::acc)::ns) F
  /\ parse (ARRCLOSE::ARROPEN::ts) ((ARR acc)::ns) T
    = parse ts ((ARR $ (Array [])::acc)::ns) F
  /\ parse (OBJCLOSE::OBJOPEN::ts) ((OBJ acc)::ns) T
    = parse ts ((OBJV (Object []) acc)::ns) F
  /\ parse (ARRCLOSE::ARROPEN::ts) ((OBJ acc)::ns) T
    = parse ts ((OBJV (Array []) acc)::ns) F
  /\ parse (OBJCLOSE::OBJOPEN::ts) ns T = INR (Object [], ts, ns)
  /\ parse (ARRCLOSE::ARROPEN::ts) ns T = INR (Array [], ts, ns)
  /\ parse (COMMA::ts) ((ARR acc)::ns) F = parse ts ((ARR acc)::ns) T
  /\ parse (ARROPEN::ts) ((ARR aacc)::(OBJ oacc)::ns) F
    = parse ts ((OBJV (Array aacc) oacc)::ns) F
  /\ parse (ARROPEN::ts) ((ARR acc)::(ARR acc')::ns) F
    = parse ts ((ARR $ (Array acc)::acc')::ns) F
  /\ parse (ARROPEN::ts) ((ARR acc)::ns) F = INR (Array acc, ts, ns)
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
        | Object mems => [OBJOPEN] ++
                concat_with (MAP mem_to_tok mems) ([COMMA]) ++
                [OBJCLOSE]
        | Array obs => [ARROPEN] ++
                concat_with (MAP json_to_tok obs) ([COMMA]) ++
                [ARRCLOSE]
       | String s => [Str s]
       | Number i => [NUM i]
       | Bool b => [BOOL b]
       | Null => [NULL])
  /\
  (mem_to_tok n_obj = let (n, obj) = n_obj in
       [Str n]
       ++ [COLON] ++ json_to_tok obj)
Termination
   WF_REL_TAC `measure (\x. case x of
       | INL obj => json_size obj
       | INR p => json2_size p)`
  >> rw[]
  >> imp_res_tac json_size_MEM1
  >> imp_res_tac json_size_MEM2
  >> fs[]
End

(* TODO prove equality between json_to_tok and json_to_string *)

val json_size_def = fetch "-" "json_size_def";
val json_size_eq = fetch "-" "json_size_eq";

(*
Examples:
EVAL ``lex "{}" []``
EVAL ``parse [OBJCLOSE; OBJOPEN] [] T``
EVAL ``parse [OBJCLOSE; OBJCLOSE; OBJOPEN] [] T``
EVAL ``CONCAT $ json_to_string $ Object [("a",Array [])]``
EVAL ``CONCAT $ json_to_string $ String "\u0022"``
*)

val _ = export_theory();

