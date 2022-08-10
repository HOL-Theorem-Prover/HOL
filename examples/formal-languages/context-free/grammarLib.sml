structure grammarLib :> grammarLib =
struct

open HolKernel Parse boolSyntax
open Abbrev

local open grammarTheory in end

datatype fs = datatype errormonad.fs
type ('a,'b,'c) m = 'a -> ('a * ('b,'c)fs)

fun return (a : 'a) : ('s,'a,'b)m = fn s => (s,Some a)
fun ok e = return () e
fun fail0 (m:string) e = (e, Error m)
fun (m >- f) : ('s,'b,'error) m = fn (s0:'s) =>
  let
    val (s1, r) = m s0
  in
    case r of
        Error x => (s1, Error x)
      | Some v => f v s1
  end
fun (m1 >> m2) = m1 >- (fn _ => m2)
fun mmap f [] = return []
  | mmap f (h::t) = f h >- (fn h' => mmap f t >- (fn t' => return (h'::t')))

infix >-* >>-* <-
fun (m >-* cf) = m >- (fn v1 => cf v1 >- (fn v2 => return (v1,v2)))
fun (m1 >>-* m2) = m1 >-* (fn _ => m2)
fun (m1 <- m2) = m1 >- (fn v => m2 >> return v)
fun get s = (s, Some s)

type posn = int * int
type posnmsg = posn * (posn * string) option
type 'a tt = (posnmsg * term frag list, 'a, string) m

fun ((m1 : 'a tt) ++ (m2 : 'a tt)) : 'a tt =
  fn (s0 as ((p0, m0), qb0)) =>
     case m1 s0 of
         (((p, m), qb), Error e) => m2 ((p0, m), qb0)
       | x => x

fun repeat (m : 'a tt) s = ((m >> repeat m) ++ ok) s

datatype stringt = S of string | TMnm of string
datatype sym = NT of string | TOK of stringt
datatype clause = Syms of sym list | TmAQ of term
type t = (string * clause list) list

datatype NTproblem = Unreachable of string | Undefined of string
val emptyNTset = HOLset.empty String.compare
fun clausesNTs (cs, acc) = let
  fun symcase (NT s, acc) = HOLset.add(acc, s)
    | symcase (TOK _, acc) = acc
  fun clausecase (Syms syms, acc) = List.foldl symcase acc syms
    | clausecase (TmAQ _, acc) = acc
in
  List.foldl clausecase acc cs
end
fun usedNTs (g:t) =
  List.foldl (fn ((_,cs), acc) => clausesNTs(cs,acc)) emptyNTset g
fun reachableNTs start (clauses : t) =
  let
    fun foldthis (c as (nt, cs), m) =
      Binarymap.insert(m,nt,clausesNTs(cs, emptyNTset))
    val ntmap = List.foldl foldthis (Binarymap.mkDict String.compare) clauses
    fun dfs visited tovisit =
      case tovisit of
          [] => visited
        | nt::rest => let
          val visited' = HOLset.add(visited, nt)
          val neighbours = case Binarymap.peek(ntmap, nt) of
                               NONE => emptyNTset
                             | SOME s => s
          fun foldthis (nt, acc) =
            if HOLset.member(visited', nt) then acc
            else nt::acc
          val tovisit' = HOLset.foldl foldthis rest neighbours
        in
          dfs visited' tovisit'
        end
  in
    dfs emptyNTset [start]
  end
fun definedNTs (clauses : t) =
  let
    fun clausescase ((nt, _), acc) = HOLset.add(acc, nt)
  in
    List.foldl clausescase emptyNTset clauses
  end

fun NTproblems start g =
  let
    val used = usedNTs g
    val reachable = reachableNTs start g
    val defined = definedNTs g
    val defined_less_reachable = HOLset.difference(defined, reachable)
    val used_less_defined = HOLset.difference(used, defined)
  in
    HOLset.foldl (fn (s, acc) => Unreachable s :: acc)
                 (HOLset.foldl (fn (s, acc) => Undefined s :: acc)
                               []
                               used_less_defined)
                 defined_less_reachable
  end

fun newline ((col, line), msg) = ((0, line + 1), msg)
fun add1col ((col, line), msg) = ((col + 1, line), msg)
fun advance c p = if c = #"\n" then newline p else add1col p
fun posn_toString (col, line) = Int.toString line ^ "." ^ Int.toString col
fun posn_compare(p1 : posn, p2 : posn) =
  case Int.compare (#2 p1, #2 p2) of
      EQUAL => Int.compare(#1 p1, #1 p2)
    | x => x
val startposn :posnmsg = ((0, 1), NONE)

fun fail s ((p0,m0), i) =
  let
    val msg0 = posn_toString p0 ^ ": " ^ s
    fun finish m = fail0 msg0 ((p0, SOME m), i)
  in
    case m0 of
        NONE => finish (p0,s)
      | SOME(m as (p2, _)) =>
        if posn_compare(p0,p2) <> LESS then finish (p0,msg0) else finish m
  end

fun setPosn (line,col) ((_, m), i) = ((((col,line), m), i), Some ())

fun aq0 error (st as (posn:posnmsg, frags)) =
    case frags of
      [] => (st, Error error)
    | QUOTE s :: rest => if s = "" then aq0 error (posn, rest)
                         else (st, Error error)
    | ANTIQUOTE t :: rest => ((posn, rest), Some t)

fun getc error (st as (posn, i0)) =
  case i0 of
    [] => fail error st
  | QUOTE s :: rest =>
    if s = "" then getc error (posn, rest)
    else let val i' = if size s = 1 then rest
                      else QUOTE (String.extract(s,1,NONE)) :: rest
             val c = String.sub(s,0)
             val posn' = advance c posn
         in
           ((posn', i'), Some (String.sub(s,0)))
         end
  | ANTIQUOTE _ :: _ => fail error st

fun dropP P = repeat (getc "" >- (fn c => if P c then ok
                                          else fail ""))

fun getP P =
  getc "getP: EOF" >-
  (fn c => if P c then return c else fail "getP: P false")

fun token0 s = let
  val sz = size s
  fun recurse i =
      if i = sz then ok
      else let
        val c = String.sub(s,i)
      in
        getc ("EOF while looking for "^str c^" of "^s) >-
        (fn c' => if c' = c then recurse (i + 1)
                  else fail ("token: didn't find "^str c^" of "^s))
      end
in
  recurse 0
end

fun mnot m s = let
  val (s',res) = m s
in
  case res of
    Some _ => fail "mnot" s
  | Error _ => ok s
end

(* needs to be eta-expanded to make it suitably polymorphic
    (ware the value restriction!)
*)
fun barecomment s =
    (token0 "(*" >> repeat (mnot (token0 "*)") >> getc "") >> token0 "*)") s

fun mrpt m =
  let
    fun recurse acc =
      (m >- (fn v => recurse (v::acc))) ++ return (List.rev acc)
  in
    recurse []
  end

fun mrpt1 m =
  (m >>-* mrpt m) >- (fn (x,xs) => return (x::xs))

val int = mrpt1 (getP Char.isDigit) >-
          (fn clist =>
              return (valOf (Int.fromString (String.implode clist))))

val posn_comment =
    token0 "(*#loc " >> (int >>-* (getP Char.isSpace >> int)) >- setPosn >>
    token0 "*)"

val comment = posn_comment ++ barecomment


fun lex m = repeat ((getP Char.isSpace >> ok) ++ comment) >> m
fun complete m = m <- repeat ((getP Char.isSpace >> ok) ++ comment)
fun token s = lex (token0 s)
fun aq s = lex (aq0 s)

fun ident_constituent c =
    Char.isAlphaNum c orelse c = #"'" orelse c = #"_"

fun ident0 s =
  (getP Char.isAlpha >-
   (fn c => mrpt (getP ident_constituent) >-
   (fn cs => return (String.implode (c::cs))))) s

fun ident s = lex ident0 s

fun escape #"n" = #"\n"
  | escape #"t" = #"\t"
  | escape c = c

fun slitchar s =
  ((getP (equal #"\\") >> getc "" >- (return o escape)) ++
   (getP (not o equal #"\""))) s

val slitcontent : string tt =
  mrpt slitchar >- (return o String.implode)

val slit0 : string tt =
  getP (equal #"\"") >>
  slitcontent >-
  (fn s => (getP (equal #"\"") >> return s) ++
           fail "Unterminated string literal")

val slit = lex slit0

fun sepby m sep =
    (m >>-* mrpt (sep >> m)) >- (return o op::)

(* clause = a sequence of tokens and non-terminals
            (one alternative of a set of productions)
                  OR
            an antiquoted term *)
val clause =
    (aq "" >- (return o TmAQ)) ++
    (mrpt ((ident >- (return o NT)) ++
           (slit >- (return o TOK o S)) ++
           ((token "<" >> ident <- token ">") >- (return o TOK o TMnm))) >-
     (return o Syms))


(* rulebody = a set of clauses, together specifying all possible
              expansions for a non-terminal. *)
val rulebody =
    sepby clause (token "|") <- token ";"

val grule = ident >>-* (token "::=" >> rulebody)
val grammar0 =
    complete (mrpt grule) <-
     (mnot (getc "") ++
      fail "Couldn't make sense of remaining input")

fun grammar fs =
    case grammar0 (startposn, fs) of
        (((_,SOME(p,m)), _), Error _) => raise Fail m
      | (((_, NONE), _), Error s) =>
          raise Fail ("Invariant failure, (and "^s^")")
      | (_, Some v) => v

fun allnts f (g: t) : string HOLset.set = let
  fun clausents acc [] = acc
    | clausents acc (TOK _ :: rest) = clausents acc rest
    | clausents acc (NT s :: rest) = clausents (HOLset.add(acc,f s)) rest
  fun bodynts acc [] = acc
    | bodynts acc (Syms h::t) = bodynts (clausents acc h) t
    | bodynts acc (TmAQ _ :: t) = bodynts acc t
  fun rulents acc (nt,b) = bodynts (HOLset.add(acc,f nt)) b
  fun recurse acc [] = acc
    | recurse acc (h::t) = recurse (rulents acc h) t
in
  recurse (HOLset.empty String.compare) g
end

type ginfo = {tokmap : string -> term, start : string,
              nt_tyname : string, tokty : hol_type,
              mkntname : string -> string, gname : string}

fun mk_symty (tokty, nty) =
    mk_thy_type {Thy = "grammar", Tyop = "symbol",
                 Args = [tokty, nty]}
fun mk_infty ty = sumSyntax.mk_sum(ty, numSyntax.num)

val TOK_t =
    mk_thy_const{Thy = "grammar", Name = "TOK",
                 Ty = alpha --> mk_symty(alpha,beta)}
val NT_t =
    mk_thy_const{Thy = "grammar", Name = "NT",
                 Ty = mk_infty alpha --> mk_symty(beta,alpha)}

fun injinf tm = sumSyntax.mk_inl(tm, numSyntax.num)

fun appletter ty =
    case total dest_thy_type ty of
        SOME {Tyop,...} => str (String.sub(Tyop,0))
      | NONE => str (String.sub(dest_vartype ty,1))

fun mkNT0 nty mkntname s = injinf (mk_const(mkntname s, nty))
fun mkNT nty ({tokty,mkntname,...}:ginfo) s =
    mk_comb(inst [alpha |-> nty, beta |-> tokty] NT_t, mkNT0 nty mkntname s)


fun sym_to_term nty (gi as {tokmap,tokty,mkntname,...}:ginfo) sym used = let
  val TOK_t' = inst [alpha |-> tokty, beta |-> nty] TOK_t
  fun mktok t = mk_comb(TOK_t', t)
  fun termsym_to_term t = let
    val (_, ty) = dest_const t handle HOL_ERR _ =>
                  raise mk_HOL_ERR "grammarLib" "mk_grammar_def"
                        ("Term " ^ Lib.quote (term_to_string t) ^
                         " is not a constant")
    val (args, r) = strip_fun ty
    fun var aty used = let
      val t = variant used (mk_var(appletter aty, aty))
    in
      (t::used, Some t)
    end
    val (used, vs) =
        case mmap var args used of
            (_, Error _) => raise Fail "Impossible"
          | (used, Some vs) => (used, vs)
  in
    (used, Some (mktok (list_mk_comb(t, vs))))
  end
in
  case sym of
      TOK (S s) => (used,  Some (mktok (tokmap s)))
    | TOK (TMnm n) => termsym_to_term (Parse.Term [QUOTE n])
    | NT n => (used, Some (mkNT nty gi n))
end

fun image f destty t = let
  open pred_setSyntax pairSyntax
  fun err() = mk_HOL_ERR "grammarLib" "mk_grammar_def"
                         ("Can't handle form of antiquoted term " ^
                          term_to_string t)
in
  if same_const t empty_tm then inst [alpha |-> destty] empty_tm
  else
    case Lib.total dest_insert t of
        SOME (e, rest) => mk_insert(f e, image f destty rest)
      | NONE =>
        let
        in
          case Lib.total dest_union t of
              SOME(s1,s2) => mk_union(image f destty s1, image f destty s2)
            | NONE =>
              let
              in
                case Lib.total dest_comb t of
                    SOME (g,x) => if same_const g gspec_tm then
                                    let val (v, body) = dest_pabs x
                                        val (e, cond) = dest_pair body
                                    in
                                      mk_icomb(gspec_tm,
                                               mk_pabs(v,mk_pair(f e, cond)))
                                    end
                                  else raise err()
                  | NONE => raise err()
              end
        end
end

fun clause_to_termSet nty (gi as {tokty,...}:ginfo) c = let
  val symty = mk_symty(tokty,nty)
  open pred_setSyntax pairSyntax listSyntax
in
  case c of
      Syms slist =>
      let
        val (used, ts) =
            case mmap (sym_to_term nty gi) slist [] of
                (used, Some ts) => (used, ts)
             |  _ => raise Fail "Can't happen"
        val body = mk_list(ts, symty)
      in
        case used of
            [] => mk_insert(body, inst [alpha |-> type_of body] empty_tm)
          | _ => mk_icomb(gspec_tm, mk_pabs(list_mk_pair used, mk_pair(body, T)))
      end
    | TmAQ t =>
      let
        val TOK_t' = inst [alpha |-> tokty, beta |-> nty] TOK_t
        val symlist_ty = mk_list_type symty
      in
        image (fn t => mk_list([mk_comb(TOK_t', t)], symty)) symlist_ty t
      end
end


val warn = HOL_WARNING "grammarLib" "grammar"
fun NTproblem_warn (Unreachable s) = warn ("Unused non-terminal: " ^ s)
  | NTproblem_warn (Undefined s) = warn ("Undefined non-terminal: " ^ s)
fun reportNTproblems top g = List.app NTproblem_warn (NTproblems top g)

fun mk_grammar_def0 (gi:ginfo) (g:t) = let
  val {tokmap,nt_tyname,mkntname,tokty,start,gname,...} = gi
  val _ = reportNTproblems start g
  val nt_names = allnts mkntname g
  val constructors =
      ParseDatatype.Constructors
        (HOLset.foldl (fn (nm,l) => (nm,[]) :: l) [] nt_names)
  val _ = Datatype.astHol_datatype [(nt_tyname,constructors)]
  val nty = mk_thy_type { Thy = current_theory(),
                          Tyop = nt_tyname, Args = []}
  val U = list_mk_lbinop (curry pred_setSyntax.mk_union) o List.concat
  val symty = mk_symty(tokty,nty)
  val gty = mk_thy_type {Thy = "grammar", Tyop = "grammar", Args = [tokty,nty]}
  fun foldthis ((ntnm, cs), rules_fm) = let
    val nt_t = mkNT0 nty (#mkntname gi) ntnm
    val rhs_sets = map (clause_to_termSet nty gi) cs
    val rhs_set = list_mk_lbinop (curry pred_setSyntax.mk_union) rhs_sets
  in
    finite_mapSyntax.mk_fupdate(rules_fm, pairSyntax.mk_pair(nt_t, rhs_set))
  end

  val rules = List.foldl foldthis
                         (finite_mapSyntax.mk_fempty
                            (mk_infty nty, listSyntax.mk_list_type symty --> bool))
                         g
  val grammar_t =
      TypeBase.mk_record (gty, [("start", mkNT0 nty mkntname start),
                                ("rules", rules)])
  val mesg = with_flag(MESG_to_string, Lib.I) HOL_MESG
  val defn_name = gname ^ "_def"
in
  new_definition (defn_name, mk_eq(mk_var(gname, gty), grammar_t)) before
  mesg ((if !Globals.interactive then
           "Grammar definition has been stored under "
         else
           "Saved definition __ ") ^
        Lib.quote defn_name ^ "\n")
end

fun mk_grammar_def r q = mk_grammar_def0 r (grammar q)


(*
local open stringTheory in end
val _ = Hol_datatype`tok = LparT | RparT | StarT | PlusT | Number of num | Ident of string`
val Number = ``Number``
val tmap =
  List.foldl (fn ((nm,t),m) => Binarymap.insert(m,nm,t))
             (Binarymap.mkDict String.compare)
             [("+", ``PlusT``), ("*", ``StarT``), ("(", ``LparT``),
              (")", ``RparT``)];
mk_grammar_def {tokmap = (fn s => valOf (Binarymap.peek(tmap,s))),
                nt_tyname = "nt", tokty = ``:tok``, gname = "exprG",
                mkntname = (fn s => "n" ^ s), start = "E"}
               `E ::= E "*" F' | F';
                F' ::= F' "+" T | T;
                T ::= <Number> | "(" E ")" | ^(``{ Ident s | s <> "" ∧ isAlpha (HD s)}``);`;

*)

end
