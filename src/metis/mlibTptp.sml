(* ========================================================================= *)
(* INTERFACE TO TPTP PROBLEM FILES                                           *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

(*
app load ["mlibStream", "mlibUseful", "mlibParser", "mlibTerm", "mlibSubst"];
*)

(*
*)
structure mlibTptp :> mlibTptp =
struct

open mlibParser mlibUseful mlibTerm;

infixr 9 >>++;
infixr 8 ++;
infixr 7 >>;
infixr 6 ||;
infix |-> ## ::>;

structure S = mlibStream; local open mlibStream in end;

val |<>| = mlibSubst.|<>|;
val op ::> = mlibSubst.::>;
val term_subst = mlibSubst.term_subst;

(* ------------------------------------------------------------------------- *)
(* Abbreviating relation and function names in TPTP problems.                *)
(* ------------------------------------------------------------------------- *)

type rename = {tptp : string, fol : string, arity : int};

val renaming : rename list ref = ref
  [(* Mapping TPTP functions to nice symbols *)
   {tptp = "equal",      fol = "=",  arity = 2},
   {tptp = "equalish",   fol = "==", arity = 2},
   {tptp = "less_equal", fol = "<=", arity = 2},
   {tptp = "multiply",   fol = "*",  arity = 2},
   {tptp = "divide",     fol = "/",  arity = 2},
   {tptp = "add",        fol = "+",  arity = 2},
   {tptp = "subtract",   fol = "-",  arity = 2},

   (* Mapping HOL symbols to TPTP alphanumerics *)
   {tptp = "bool",       fol = "$",  arity = 1},
   {tptp = "type",       fol = ":",  arity = 2},
   {tptp = "apply",      fol = "%",  arity = 2}]

(* ------------------------------------------------------------------------- *)
(* Reading from a TPTP file in CNF/FOF format: pass in a filename.           *)
(* ------------------------------------------------------------------------- *)

val comment = equal #"%" o hd o explode;

val input_lines = S.filter (non comment) o S.from_textfile;

val input_chars = S.flatten o S.map (S.from_list o explode);

datatype tok_type = Lower | Upper | Punct;

local
  fun f [] = raise Bug "exact_puncts"
    | f [x] = x | f (h :: t) = (h ++ f t) >> K ();
in
  val exact_puncts = f o map (fn c => exact (Punct, str c) >> K ()) o explode;
end;

val lexer =
  (many (some space) ++
   (((some lower || some digit) ++ many (some alphanum) >>
     (fn (a, b) => (Lower, implode (a :: b)))) ||
    (some upper ++ many (some alphanum) >>
     (fn (a, b) => (Upper, implode (a :: b)))) ||
    ((some symbol || some punct) >> (fn c => (Punct, str c))))) >> snd;

val lex = many lexer ++ (many (some space) ++ finished) >> fst;

val input_toks = S.from_list o fst o lex;

local
  fun mapped (f,a) (m : rename list) =
    let fun g {tptp, arity, fol = _} = tptp = f andalso arity = length a
    in case List.find g m of SOME {fol, ...} => (fol, a) | NONE => (f, a)
    end;
in
  fun Fn' A = Fn (mapped A (!renaming));
end;

val var_parser = some (equal Upper o fst) >> snd;

fun term_parser input =
  ((var_parser >> Var) ||
   ((some (equal Lower o fst) >> snd) ++
    (optional
     (exact (Punct, "(") ++ term_parser ++
      many ((exact (Punct, ",") ++ term_parser) >> snd) ++
      exact (Punct, ")")) >>
     (fn SOME (_,(t,(ts,_))) => t :: ts | NONE => [])) >>
    Fn')) input;

val atom_parser =
  term_parser >> (fn t => Atom (case t of Var v => Fn (v,[]) | _ => t));

val literal_parser =
  (((exact_puncts "++" >> K true) || (exact_puncts "--" >> K false)) ++
   atom_parser) >> mk_literal;

val clause_parser =
  (exact (Lower, "input_clause") ++ exact (Punct, "(") ++ any ++
   exact (Punct, ",") ++ any ++ exact (Punct, ",") ++ exact (Punct, "[") ++
   literal_parser ++ many ((exact (Punct, ",") ++ literal_parser) >> snd) ++
   exact (Punct, "]") ++ exact (Punct, ")") ++ exact (Punct, ".")) >>
  (fn (_,(_,(name,(_,(typ,(_,(_,(l,(ls,_))))))))) =>
   (snd name, snd typ, list_mk_disj (l :: ls)));

val varl_parser =
  (exact (Punct, "[") ++ var_parser ++
   many ((exact (Punct, ",") ++ var_parser) >> snd) ++ exact (Punct, "]")) >>
  (fn (_,(h,(t,_))) => h :: t);

fun form_parser inp =
  (qform_parser ++
   (iform_parser "|" Or ||
    iform_parser "&" And ||
    iform_parser "<=>" Iff ||
    iform_parser "<~>" (Not o Iff) ||
    iform_parser "=>" Imp ||
    iform_parser "<=" (Imp o swap) ||
    iform_parser "~|" (Not o Or) ||
    iform_parser "~&" (Not o And) ||
    (nothing >> (fn () => I))) >>
   (fn (a,f) => f a)) inp
and iform_parser sym con inp =
  (atleastone ((exact_puncts sym ++ qform_parser) >> snd)
   >> (fn l => fn i =>
       let val x = rev (i :: l) in foldl con (hd x) (tl x) end)) inp
and qform_parser inp =
  (((exact (Punct, "~") ++ qform_parser) >> (Not o snd)) ||
   ((exact (Punct, "!") ++ varl_parser ++ exact (Punct, ":") ++ qform_parser)
    >> (fn (_,(v,(_,b))) => list_mk_forall (v,b))) ||
   ((exact (Punct, "?") ++ varl_parser ++ exact (Punct, ":") ++ qform_parser)
    >> (fn (_,(v,(_,b))) => list_mk_exists (v,b))) ||
   ((exact (Punct, "(") ++ form_parser ++ exact (Punct, ")"))
    >> (fst o snd)) ||
   atom_parser) inp;

val fof_parser =
  (exact (Lower, "input_formula") ++ exact (Punct, "(") ++ any ++
   exact (Punct, ",") ++ any ++ exact (Punct, ",") ++ form_parser ++
   exact (Punct, ")") ++ exact (Punct, ".")) >>
  (fn (_,(_,(name,(_,(typ,(_,(f,_))))))) => (snd name, snd typ, f));

datatype problem = CNF | FOF;

val problem_parser =
  fst o
  (((many clause_parser ++ finished) >> (fn (a,_) => (CNF,a))) ||
   ((many fof_parser ++ finished) >> (fn (a,_) => (FOF,a))));

local
  val to_form = list_mk_conj o map (fn (_,_,a) => generalize a);
in
  val input_problem =
    (fn (CNF,(a,b)) => Imp (to_form a, Imp (to_form b, False))
      | (FOF,(a,b)) => Imp (to_form a, if null b then False else to_form b)) o
    (I ## List.partition (not o equal "conjecture" o #2)) o
    problem_parser;
end;

val read = input_problem o input_toks o input_chars o input_lines;

(* Quick testing
installPP mlibTerm.pp_formula;
val num1 = read "../../test/NUM001-1.tptp";
val lcl9 = read "../../test/LCL009-1.tptp";
val set11 = read "../../test/SET011+3.fof";
*)

(* ------------------------------------------------------------------------- *)
(* Writing to a TPTP file in CNF format: pass in a formula and filename.     *)
(* ------------------------------------------------------------------------- *)

local
  val separator =
    "%-------------------------------------" ^
    "-------------------------------------\n";

  fun name n = "% File     : " ^ n ^ "\n";

  fun varify s =
    case explode s of [] => raise Error "write_cnf: empty string variable"
    | x :: xs => if Char.isUpper x then s else implode (Char.toUpper x :: xs);

  fun funify r s =
    let
      fun g {fol, arity, tptp = _} = fol = s andalso arity = r
    in
      case List.find g (!renaming) of SOME {tptp, ...} => tptp
      | NONE =>
        case explode s of [] => raise Error "write_cnf: empty string function"
        | x :: y => if Char.isLower x then s else implode (Char.toLower x :: y)
    end;

  fun term pr =
    let
      fun tm (Var v) = pr (varify v)
        | tm (Fn (f, l)) = (pr (funify (length l) f); tms l)
      and tms [] = ()
        | tms (x :: y) = (pr "("; tm x; app (fn z => (pr ","; tm z)) y)
    in
      tm
    end

  fun literal pr (Not (Atom a)) = (pr "--"; term pr a)
    | literal pr (Atom a) = (pr "++"; term pr a)
    | literal _ _ = raise Error "write_cnf: not in CNF";

  fun clause pr ty (cl, n) =
    let
      val () = if n = 0 then () else pr "\n"
      val () = pr ("input_clause(clause" ^ int_to_string n ^ "," ^ ty ^ ",\n")
      val () = pr "    [";
      val () =
        case (strip_disj o snd o strip_forall) cl of [] => ()
        | x :: y => (literal pr x; app (fn z => (pr ",\n     ";literal pr z)) y)
      val () = pr "]).\n"
    in
      n + 1
    end;
in
  fun write {filename = n} (Imp (a, Imp (b, False))) =
    let
      open TextIO
      val h = openOut n
      fun pr x = output (h, x)
      val () = pr separator
      val () = pr (name n)
      val () = pr separator
      val n = foldl (clause pr "hypothesis") 0 (strip_conj a)
      val n = foldl (clause pr "conjecture") n (strip_conj b)
      val () = assert (0 < n) (Error "write: no clauses")
      val () = pr separator
      val () = closeOut h
    in
      ()
    end
    | write _ _ = raise Error "write: not in CNF format";
end;

(* Quick testing
val () = write num1 "../file";
*)

(* ------------------------------------------------------------------------- *)
(* Making TPTP formulas more palatable.                                      *)
(* ------------------------------------------------------------------------- *)

local
  fun cycle _ ([], _) = raise Bug "cycle"
    | cycle f (h :: t, avoid) =
    let val h' = f h avoid in (h', (t @ [h], h' :: avoid)) end;

  exception Too_many_vars;

  val vars = ["x", "y", "z", "v", "w"];

  val MAX_PRIME = 3 * length vars;

  fun f _ True = True
    | f _ False = False
    | f (s,_,_) (Atom tm) = Atom (term_subst s tm)
    | f x (Not a) = Not (f x a)
    | f x (And (a,b)) = And (f x a, f x b)
    | f x (Or (a,b)) = Or (f x a, f x b)
    | f x (Iff (a,b)) = Iff (f x a, f x b)
    | f x (Imp (a,b)) = Imp (f x a, f x b)
    | f x (Forall (v,b)) = g x Forall v b
    | f x (Exists (v,b)) = g x Exists v b
  and g (_,0,_) _ _ _ = raise Too_many_vars
    | g (s,n,x) quant v b =
    let
      val variant_fn = if 0 <= n then variant else variant_num
      val n = n - 1
      val (w,x) = cycle variant_fn x
      val s = (v |-> Var w) ::> s
    in
      quant (w, f (s,n,x) b)
    end;

  val prettify1 = f (|<>|, MAX_PRIME, (vars, []));
  val prettify2 = f (|<>|, ~1, (vars, []));
in
  fun prettify fm = prettify1 fm handle Too_many_vars => prettify2 fm;
end;

(* Quick testing
installPP mlibTerm.pp_formula;
val num1 = (prettify o read) "../../test/NUM001-1.tptp";
val lcl9 = (prettify o read) "../../test/LCL009-1.tptp";
val set11 = (prettify o read) "../../test/SET011+3.tptp";
*)

end
