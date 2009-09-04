(* ========================================================================= *)
(* BASIC FIRST-ORDER LOGIC MANIPULATIONS                                     *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

structure mlibTerm :> mlibTerm =
struct

open mlibParser mlibUseful;

infixr 8 ++;
infixr 7 >>;
infixr 6 ||;
infixr |-> ::> @> oo ##;

(* ------------------------------------------------------------------------- *)
(* Datatypes for storing first-order terms and formulas.                     *)
(* ------------------------------------------------------------------------- *)

datatype term =
  Var of string
| Fn  of string * term list;

datatype formula =
  True
| False
| Atom   of term
| Not    of formula
| And    of formula * formula
| Or     of formula * formula
| Imp    of formula * formula
| Iff    of formula * formula
| Forall of string * formula
| Exists of string * formula;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

(* Variables *)

fun dest_var (Var v) = v
  | dest_var (Fn _) = raise Error "dest_var";

val is_var = can dest_var;

(* Functions *)

fun dest_fn (Fn f) = f
  | dest_fn (Var _) = raise Error "dest_fn";

val is_fn = can dest_fn;

val fn_name = fst o dest_fn;

val fn_args = snd o dest_fn;

val fn_arity = length o fn_args;

fun fn_function tm = (fn_name tm, fn_arity tm);

(* Constants *)

fun mk_const c = (Fn (c, []));

fun dest_const (Fn (c, [])) = c
  | dest_const _ = raise Error "dest_const";

val is_const = can dest_const;

(* Binary functions *)

fun mk_binop f (a, b) = Fn (f, [a, b]);

fun dest_binop f (Fn (x, [a, b])) =
  if x = f then (a, b) else raise Error "dest_binop: wrong binop"
  | dest_binop _ _ = raise Error "dest_binop: not a binop";

fun is_binop f = can (dest_binop f);

(* Atoms *)

fun dest_atom (Atom a) = a
  | dest_atom _ = raise Error "dest_atom";

val is_atom = can dest_atom;

(* Negations *)

fun dest_neg (Not p) = p
  | dest_neg _ = raise Error "dest_neg";

val is_neg = can dest_neg;

(* Conjunctions *)

fun list_mk_conj l = (case rev l of [] => True | h :: t => foldl And h t);

local
  fun conj cs (And (a, b)) = conj (a :: cs) b
    | conj cs fm = rev (fm :: cs);
in
  fun strip_conj True = []
    | strip_conj fm = conj [] fm;
end;

val flatten_conj =
  let
    fun flat acc []                  = acc
      | flat acc (And (p, q) :: fms) = flat acc (q :: p :: fms)
      | flat acc (True       :: fms) = flat acc fms
      | flat acc (fm         :: fms) = flat (fm :: acc) fms
  in
    fn fm => flat [] [fm]
  end;

(* Disjunctions *)

fun list_mk_disj l = (case rev l of [] => False | h :: t => foldl Or h t);

local
  fun disj cs (Or (a, b)) = disj (a :: cs) b
    | disj cs fm = rev (fm :: cs);
in
  fun strip_disj False = []
    | strip_disj fm = disj [] fm;
end;

val flatten_disj =
  let
    fun flat acc []                 = acc
      | flat acc (Or (p, q) :: fms) = flat acc (q :: p :: fms)
      | flat acc (False     :: fms) = flat acc fms
      | flat acc (fm        :: fms) = flat (fm :: acc) fms
  in
    fn fm => flat [] [fm]
  end;

(* Universal quantifiers *)

fun list_mk_forall ([], body) = body
  | list_mk_forall (v :: vs, body) = Forall (v, list_mk_forall (vs, body));

local
  fun dest vs (Forall (v, b)) = dest (v :: vs) b
    | dest vs tm = (rev vs, tm);
in
  val strip_forall = dest [];
end;

(* Existential quantifiers *)

fun list_mk_exists ([], body) = body
  | list_mk_exists (v :: vs, body) = Exists (v, list_mk_exists (vs, body));

local
  fun dest vs (Exists (v, b)) = dest (v :: vs) b
    | dest vs tm = (rev vs, tm);
in
  val strip_exists = dest [];
end;

(* ------------------------------------------------------------------------- *)
(* A datatype to antiquote both terms and formulas.                          *)
(* ------------------------------------------------------------------------- *)

datatype thing = mlibTerm of term | Formula of formula;

(* ------------------------------------------------------------------------- *)
(* Built-in infix operators and reserved symbols.                            *)
(* ------------------------------------------------------------------------- *)

val infixes : infixities ref = ref
  [(* ML style *)
   {tok = " / ",   prec = 7,  left_assoc = true},
   {tok = " div ", prec = 7,  left_assoc = true},
   {tok = " mod ", prec = 7,  left_assoc = true},
   {tok = " * ",   prec = 7,  left_assoc = true},
   {tok = " + ",   prec = 6,  left_assoc = true},
   {tok = " - ",   prec = 6,  left_assoc = true},
   {tok = " ^ ",   prec = 6,  left_assoc = true},
   {tok = " @ ",   prec = 5,  left_assoc = false},
   {tok = " :: ",  prec = 5,  left_assoc = false},
   {tok = " = ",   prec = 4,  left_assoc = true},    (* may be interpreted *)
   {tok = " == ",  prec = 4,  left_assoc = true},    (* won't be interpreted *)
   {tok = " <> ",  prec = 4,  left_assoc = true},
   {tok = " <= ",  prec = 4,  left_assoc = true},
   {tok = " < ",   prec = 4,  left_assoc = true},
   {tok = " >= ",  prec = 4,  left_assoc = true},
   {tok = " > ",   prec = 4,  left_assoc = true},
   {tok = " o ",   prec = 8,  left_assoc = true},    (* ML prec = 3 *)
   (* HOL style *)
   {tok = " % ",   prec = 9,  left_assoc = true},    (* function application *)
   {tok = " -> ",  prec = 2,  left_assoc = false},   (* HOL ty prec = 50 *)
   {tok = " : ",   prec = 1,  left_assoc = false},   (* not in HOL grammars *)
   {tok =  ", ",   prec = 0,  left_assoc = false},   (* HOL tm prec = 50 *)
   (* Convenient alternative symbols *)
   {tok = " ** ",  prec = 7,  left_assoc = true},
   {tok = " ++ ",  prec = 6,  left_assoc = true},
   {tok = " -- ",  prec = 6,  left_assoc = true}];

val connectives =
  [{tok = " /\\ ", prec = ~1, left_assoc = false},
   {tok = " \\/ ", prec = ~2, left_assoc = false},
   {tok = " ==> ", prec = ~3, left_assoc = false},
   {tok = " <=> ", prec = ~4, left_assoc = false}];

val reserved = ["!", "?", "(", ")", ".", "~"];

(* ------------------------------------------------------------------------- *)
(* Deciding whether a string denotes a variable or constant.                 *)
(* ------------------------------------------------------------------------- *)

local
  val initials = explode "_vwxyz";
in
  val var_string = ref (C mem initials o Char.toLower o hd o explode);
end;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

(* Purely functional pretty-printing *)

val pp_vname =
  pp_map (fn s => if !var_string s then s else "var->" ^ s ^ "<-var") pp_string;

fun pp_term' ops =
  let
    val ops = ops @ connectives
    val iprinter = pp_infixes ops
    val itoks = optoks ops
    fun specialf s = mem s itoks orelse !var_string s
    val pp_fname = pp_map (fn s=>if specialf s then "("^s^")" else s) pp_string
    fun idest (Fn (f, [a, b])) = SOME (f, a, b) | idest _ = NONE
    fun is_op t = case idest t of SOME (f, _, _) => mem f itoks | NONE => false
    fun is_q (Fn ("!", _)) = true | is_q (Fn ("?", _)) = true | is_q _ = false
    fun negs (Fn ("~", [a])) = (curry op+ 1 ## I) (negs a) | negs tm = (0, tm)
    fun binds s (tm as Fn (n, [Var v, b])) =
      if s = n then (cons v ## I) (binds s b) else ([], tm)
      | binds _ tm = ([], tm)
    open PP
    fun basic pp (Var v) = pp_vname pp v
      | basic pp (Fn (f, a)) =
      (pp_fname pp f; app (fn x => (add_break pp (1,0); argument pp x)) a)
    and argument pp tm =
      if is_var tm orelse is_const tm then basic pp tm else pp_btm pp tm
    and quant pp (tm, r) =
      let
        fun pr pp (Fn (q, [Var v, tm])) =
          let
            val (vs, body) = binds q tm
          in
            add_string pp q;
            pp_vname pp v;
            app (fn a => (add_break pp (1, 0); pp_vname pp a)) vs;
            add_string pp ".";
            add_break pp (1, 0);
            if is_q body then pr pp body else pp_tm pp (body, false)
          end
          | pr pp tm = raise Bug "pp_term: not a quantifier"
        fun pp_q pp t = (begin_block pp INCONSISTENT 2; pr pp t; end_block pp)
      in
        (if is_q tm then (if r then pp_bracket "(" ")" else I) pp_q
         else basic) pp tm
      end
    and molecule pp (tm, r) =
      let
        val (n, x) = negs tm
      in
        begin_block pp INCONSISTENT n;
        funpow n (fn () => add_string pp "~") ();
        if is_op x then pp_btm pp x else quant pp (x, r);
        end_block pp
      end
    and pp_btm pp tm = pp_bracket "(" ")" pp_tm pp (tm, false)
    and pp_tm pp tmr = iprinter idest molecule pp tmr
  in
    pp_map (C pair false) pp_tm
  end;

local
  fun demote True            = Fn ("T",   []                  )
    | demote False           = Fn ("F",   []                  )
    | demote (Not a)         = Fn ("~",   [demote a]          )
    | demote (And (a, b))    = Fn ("/\\", [demote a, demote b])
    | demote (Or  (a, b))    = Fn ("\\/", [demote a, demote b])
    | demote (Imp (a, b))    = Fn ("==>", [demote a, demote b])
    | demote (Iff (a, b))    = Fn ("<=>", [demote a, demote b])
    | demote (Forall (v, b)) = Fn ("!",   [Var v,    demote b])
    | demote (Exists (v, b)) = Fn ("?",   [Var v,    demote b])
    | demote (Atom t)        = t;
in
  fun pp_formula' ops = pp_map demote (pp_term' ops);
end;

fun term_to_string'    ops len tm = PP.pp_to_string len (pp_term'    ops) tm;
fun formula_to_string' ops len fm = PP.pp_to_string len (pp_formula' ops) fm;

(* Pretty-printing things is needed for parsing thing quotations *)

fun pp_thing ops pp (mlibTerm tm)    = pp_term'    ops pp tm
  | pp_thing ops pp (Formula fm) = pp_formula' ops pp fm;

fun pp_bracketed_thing ops pp th =
  (PP.begin_block pp PP.INCONSISTENT 1; PP.add_string pp "(";
   pp_thing ops pp th; PP.add_string pp ")"; PP.end_block pp);

(* Pretty-printing using !infixes and !LINE_LENGTH *)

fun pp_term        pp tm = pp_term'           (!infixes) pp             tm;
fun pp_formula     pp fm = pp_formula'        (!infixes) pp             fm;
fun term_to_string    tm = term_to_string'    (!infixes) (!LINE_LENGTH) tm;
fun formula_to_string fm = formula_to_string' (!infixes) (!LINE_LENGTH) fm;

(* ------------------------------------------------------------------------- *)
(* Parsing.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Lexing *)

val lexer =
  (fn ((_, (toks, _)), _) => toks) o
  (many (some space) ++
   (many
    ((((atleastone (some alphanum) ||
        (some (fn c => symbol c andalso c <> #"~") ++ many (some symbol)) >>
        op ::) >> implode
       || some (fn c => c = #"~" orelse punct c) >> str) ++
      many (some space)) >> fst)) ++
   finished);

val lex_str = lexer o mlibStream.from_list o explode;

(* Purely functional parsing *)

val vname_parser =
  some (fn tok => not (mem tok reserved) andalso !var_string tok);

fun term_parser ops =
  let
    val ops          = ops @ connectives
    val iparser      = parse_infixes ops
    val itoks        = optoks ops
    val avoid        = itoks @ reserved
    fun fname tok    = not (mem tok avoid) andalso not (!var_string tok)
    val fname_parser = some fname || (exact "("++any++exact ")") >> (fst o snd)
    fun bind s (v,t) = Fn (s, [Var v, t])
    fun basic inp    =
      (vname_parser >> Var ||
       fname_parser >> (fn f => Fn (f, [])) ||
       (exact "(" ++ tm_parser ++ exact ")") >> (fn (_, (t, _)) => t) ||
       (exact "!" ++ atleastone vname_parser ++ exact "." ++ tm_parser) >>
       (fn (_, (vs, (_, body))) => foldr (bind "!") body vs) ||
       (exact "?" ++ atleastone vname_parser ++ exact "." ++ tm_parser) >>
       (fn (_, (vs, (_, body))) => foldr (bind "?") body vs)) inp
    and molecule inp      =
      ((many (exact "~") ++ ((fname_parser ++ many basic) >> Fn || basic)) >>
       (fn (l, t) => funpow (length l) (fn x => Fn ("~", [x])) t)) inp
    and tm_parser inp  = iparser (fn (f, a, b) => Fn (f, [a, b])) molecule inp
  in
    tm_parser
  end;

local
  fun promote (Fn ("T",   []        )) = True
    | promote (Fn ("F",   []        )) = False
    | promote (Fn ("~",   [a]       )) = Not (promote a)
    | promote (Fn ("/\\", [a, b]    )) = And (promote a, promote b)
    | promote (Fn ("\\/", [a, b]    )) = Or  (promote a, promote b)
    | promote (Fn ("==>", [a, b]    )) = Imp (promote a, promote b)
    | promote (Fn ("<=>", [a, b]    )) = Iff (promote a, promote b)
    | promote (Fn ("!",   [Var v, b])) = Forall (v, promote b)
    | promote (Fn ("?",   [Var v, b])) = Exists (v, promote b)
    | promote tm                       = Atom tm;
in
  fun formula_parser ops = term_parser ops >> promote;
end;

fun string_to_term' ops =
  fst o ((term_parser ops ++ finished) >> fst) o mlibStream.from_list o lex_str;

fun string_to_formula' ops =
  fst o ((formula_parser ops ++ finished) >> fst) o mlibStream.from_list o lex_str;

fun parse_term' ops =
  quotation_parser (string_to_term' ops) (pp_bracketed_thing ops);

fun parse_formula' ops =
  quotation_parser (string_to_formula' ops) (pp_bracketed_thing ops);

(* Parsing using !infixes *)

fun string_to_term    s = string_to_term'    (!infixes) s;
fun string_to_formula s = string_to_formula' (!infixes) s;
fun parse_term        q = parse_term'        (!infixes) q;
fun parse_formula     q = parse_formula'     (!infixes) q;

(* ------------------------------------------------------------------------- *)
(* New variables.                                                            *)
(* ------------------------------------------------------------------------- *)

local
  val prefix  = "_";
  val num_var = Var o mk_prefix prefix o int_to_string;
in
  val new_var  = num_var o new_int;
  val new_vars = map num_var o new_ints;
end;

(* ------------------------------------------------------------------------- *)
(* Sizes of terms and formulas.                                              *)
(* ------------------------------------------------------------------------- *)

local
  fun szt n []                    = n
    | szt n (Var _        :: tms) = szt (n + 1) tms
    | szt n (Fn (_, args) :: tms) = szt (n + 1) (args @ tms);

  fun sz n []                     = n
    | sz n (True          :: fms) = sz (n + 1) fms
    | sz n (False         :: fms) = sz (n + 1) fms
    | sz n (Atom t        :: fms) = sz (szt (n + 1) [t]) fms
    | sz n (Not p         :: fms) = sz (n + 1) (p :: fms)
    | sz n (And (p, q)    :: fms) = sz (n + 1) (p :: q :: fms)
    | sz n (Or  (p, q)    :: fms) = sz (n + 1) (p :: q :: fms)
    | sz n (Imp (p, q)    :: fms) = sz (n + 1) (p :: q :: fms)
    | sz n (Iff (p, q)    :: fms) = sz (n + 1) (p :: q :: fms)
    | sz n (Forall (_, p) :: fms) = sz (n + 1) (p :: fms)
    | sz n (Exists (_, p) :: fms) = sz (n + 1) (p :: fms);
in
  val term_size    = szt 0 o sing;
  val formula_size = sz  0 o sing;
end;

(* ------------------------------------------------------------------------- *)
(* Total comparison functions for terms and formulas.                        *)
(* ------------------------------------------------------------------------- *)

local
  fun lex EQUAL f x = f x | lex x _ _ = x;

  fun cmt [] = EQUAL
    | cmt ((Var _, Fn _) :: _) = LESS
    | cmt ((Fn _, Var _) :: _) = GREATER
    | cmt ((Var v, Var w) :: l) = lex (String.compare (v, w)) cmt l
    | cmt ((Fn (f, a), Fn (g, b)) :: l) =
    (case lex (String.compare (f, g)) (Int.compare o Df length) (a, b) of EQUAL
       => cmt (zip a b @ l)
     | x => x);

  fun cm [] = EQUAL
    | cm ((True,          True         ) :: l) = cm l
    | cm ((True,          _            ) :: _) = LESS
    | cm ((_,             True         ) :: _) = GREATER
    | cm ((False,         False        ) :: l) = cm l
    | cm ((False,         _            ) :: _) = LESS
    | cm ((_,             False        ) :: _) = GREATER
    | cm ((Atom t,        Atom u       ) :: l) = lex (cmt [(t, u)]) cm l
    | cm ((Atom _,        _            ) :: _) = LESS
    | cm ((_,             Atom _       ) :: _) = GREATER
    | cm ((Not p,         Not q        ) :: l) = cm ((p, q) :: l)
    | cm ((Not _ ,        _            ) :: _) = LESS
    | cm ((_,             Not _        ) :: _) = GREATER
    | cm ((And (p1, q1),  And (p2, q2) ) :: l) = cm ((p1, p2) :: (q1, q2) :: l)
    | cm ((And _,         _            ) :: _) = LESS
    | cm ((_,             And _        ) :: _) = GREATER
    | cm ((Or (p1, q1),   Or (p2, q2)  ) :: l) = cm ((p1, p2) :: (q1, q2) :: l)
    | cm ((Or _,          _            ) :: _) = LESS
    | cm ((_,             Or _         ) :: _) = GREATER
    | cm ((Imp (p1, q1),  Imp (p2, q2) ) :: l) = cm ((p1, p2) :: (q1, q2) :: l)
    | cm ((Imp _,         _            ) :: _) = LESS
    | cm ((_,             Imp _        ) :: _) = GREATER
    | cm ((Iff (p1, q1),  Iff (p2, q2) ) :: l) = cm ((p1, p2) :: (q1, q2) :: l)
    | cm ((Iff _,         _            ) :: _) = LESS
    | cm ((_,             Iff _        ) :: _) = GREATER
    | cm ((Forall (v, p), Forall (w, q)) :: l) =
    lex (String.compare (v, w)) (cm o cons (p, q)) l
    | cm ((Forall _,      Exists _     ) :: _) = LESS
    | cm ((Exists _,      Forall _     ) :: _) = GREATER
    | cm ((Exists (v, p), Exists (w, q)) :: l) =
    lex (String.compare (v, w)) (cm o cons (p, q)) l;
in
  val term_compare    = cmt o sing;
  val formula_compare = cm o sing;
end;

(* ------------------------------------------------------------------------- *)
(* Basic operations on literals.                                             *)
(* ------------------------------------------------------------------------- *)

fun mk_literal (true,  a) = a
  | mk_literal (false, a) = Not a;

fun dest_literal (a as Atom _)       = (true,  a)
  | dest_literal (Not (a as Atom _)) = (false, a)
  | dest_literal _                   = raise Error "dest_literal";

val is_literal = can dest_literal;

val literal_atom = snd o dest_literal;

(* ------------------------------------------------------------------------- *)
(* Dealing with formula negations.                                           *)
(* ------------------------------------------------------------------------- *)

fun negative (Not p) = true
  | negative _       = false;

val positive = non negative;

fun negate (Not p) = p
  | negate p       = Not p;

(* ------------------------------------------------------------------------- *)
(* Functions and relations in a formula.                                     *)
(* ------------------------------------------------------------------------- *)

local
  fun fnc fs []                 = fs
    | fnc fs (Var _     :: tms) = fnc fs tms
    | fnc fs (Fn (n, a) :: tms) = fnc (insert (n, length a) fs) (a @ tms);

  fun func fs []                          = fs
    | func fs (True               :: fms) = func fs fms
    | func fs (False              :: fms) = func fs fms
    | func fs (Atom (Var _)       :: fms) = func fs fms
    | func fs (Atom (Fn (_, tms)) :: fms) = func (fnc fs tms) fms
    | func fs (Not p              :: fms) = func fs (p :: fms)
    | func fs (And (p, q)         :: fms) = func fs (p :: q :: fms)
    | func fs (Or  (p, q)         :: fms) = func fs (p :: q :: fms)
    | func fs (Imp (p, q)         :: fms) = func fs (p :: q :: fms)
    | func fs (Iff (p, q)         :: fms) = func fs (p :: q :: fms)
    | func fs (Forall (_, p)      :: fms) = func fs (p :: fms)
    | func fs (Exists (_, p)      :: fms) = func fs (p :: fms);
in
  val functions = func [] o sing;
end;

val function_names = map fst o functions;

local
  fun rel rs []                        = rs
    | rel rs (True             :: fms) = rel rs fms
    | rel rs (False            :: fms) = rel rs fms
    | rel rs (Atom (Var _)     :: fms) = rel rs fms
    | rel rs (Atom (f as Fn _) :: fms) = rel (insert (fn_function f) rs) fms
    | rel rs (Not p            :: fms) = rel rs (p :: fms)
    | rel rs (And (p, q)       :: fms) = rel rs (p :: q :: fms)
    | rel rs (Or  (p, q)       :: fms) = rel rs (p :: q :: fms)
    | rel rs (Imp (p, q)       :: fms) = rel rs (p :: q :: fms)
    | rel rs (Iff (p, q)       :: fms) = rel rs (p :: q :: fms)
    | rel rs (Forall (_, p)    :: fms) = rel rs (p :: fms)
    | rel rs (Exists (_, p)    :: fms) = rel rs (p :: fms);
in
  val relations = rel [] o sing;
end;

val relation_names = map fst o relations;

(* ------------------------------------------------------------------------- *)
(* The equality relation has a special status.                               *)
(* ------------------------------------------------------------------------- *)

val eq_rel = ("=", 2);

fun mk_eq (a, b) = Atom (Fn ("=", [a, b]));

fun dest_eq (Atom (Fn ("=", [a, b]))) = (a, b)
  | dest_eq _ = raise Error "dest_eq";

val is_eq = can dest_eq;

val refl = mk_eq o D;

val sym = mk_eq o swap o dest_eq;

val lhs = fst o dest_eq;

val rhs = snd o dest_eq;

val eq_occurs = mem eq_rel o relations;

(* ------------------------------------------------------------------------- *)
(* Free variables in terms and formulas.                                     *)
(* ------------------------------------------------------------------------- *)

local
  fun fvt av =
    let
      val seen =
        if null av then mem else (fn v => fn vs => mem v av orelse mem v vs)
      fun f vs [] = vs
        | f vs (Var v :: tms) = f (if seen v vs then vs else v :: vs) tms
        | f vs (Fn (_, args) :: tms) = f vs (args @ tms)
    in
      f
    end;

  fun fv vs []                           = vs
    | fv vs ((_ , True         ) :: fms) = fv vs fms
    | fv vs ((_ , False        ) :: fms) = fv vs fms
    | fv vs ((av, Atom t       ) :: fms) = fv (fvt av vs [t]) fms
    | fv vs ((av, Not p        ) :: fms) = fv vs ((av, p) :: fms)
    | fv vs ((av, And (p, q)   ) :: fms) = fv vs ((av, p) :: (av, q) :: fms)
    | fv vs ((av, Or  (p, q)   ) :: fms) = fv vs ((av, p) :: (av, q) :: fms)
    | fv vs ((av, Imp (p, q)   ) :: fms) = fv vs ((av, p) :: (av, q) :: fms)
    | fv vs ((av, Iff (p, q)   ) :: fms) = fv vs ((av, p) :: (av, q) :: fms)
    | fv vs ((av, Forall (x, p)) :: fms) = fv vs ((insert x av, p) :: fms)
    | fv vs ((av, Exists (x, p)) :: fms) = fv vs ((insert x av, p) :: fms);
in
  fun FVT    tm  = rev (fvt [] [] [tm]);
  fun FVTL l tms =      fvt [] l  tms;
  fun FV     fm  = rev (fv  [] [([], fm)]);
  fun FVL  l fms =      fv  l  (map (pair []) fms);
end;

val specialize = snd o strip_forall;

fun generalize fm = list_mk_forall (FV fm, fm);

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun subterm [] tm = tm
  | subterm (_ :: _) (Var _) = raise Error "subterm: Var"
  | subterm (h :: t) (Fn (_, args)) =
  subterm t (List.nth (args, h))
  handle Subscript => raise Error "subterm: bad path";

fun literal_subterm p = subterm p o dest_atom o literal_atom;

local
  fun update _ _ [] = raise Error "rewrite: bad path"
    | update f n (h :: t) = if n = 0 then f h :: t else h :: update f (n - 1) t;
in
  fun rewrite ([] |-> res) _ = res
    | rewrite _ (Var _) = raise Error "rewrite: Var"
    | rewrite ((h :: t) |-> res) (Fn (f, args)) =
    Fn (f, update (rewrite (t |-> res)) h args);
end;

local
  fun atom_rewrite r = Atom o rewrite r o dest_atom;
in
  fun literal_rewrite ([] |-> _) = raise Error "literal_rewrite: empty path"
    | literal_rewrite r = mk_literal o (I ## atom_rewrite r) o dest_literal;
end;

local
  fun f [] l = l | f ((p, t) :: w) l = g p t w ((rev p |-> t) :: l)
  and g _ (Var _) w l = f w l
    | g p (Fn (_, ts)) w l =
    let val a = map (fn (x,y) => (x::p,y)) (enumerate 0 ts) in f (a @ w) l end;
in
  fun subterms p tm = f [(p, tm)] [];
  fun literal_subterms lit = g [] (dest_atom (literal_atom lit)) [] [];
end;

end
