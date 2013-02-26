structure grammarLib :> grammarLib =
struct

open Abbrev
open errormonad

local open grammarTheory in end

infix >-* >>-* <-
fun (m >-* cf) = m >- (fn v1 => cf v1 >- (fn v2 => return (v1,v2)))
fun (m1 >>-* m2) = m1 >-* (fn _ => m2)
fun (m1 <- m2) = m1 >- (fn v => m2 >> return v)
fun get s = (s, Some s)

type 'a tt = (term frag list, 'a, string) t

datatype stringt = S of string | TMnm of string
datatype sym = NT of string | TOK of stringt
datatype clause = Syms of sym list | TmAQ of term
type t = (string * clause list) list

fun aq0 error frags =
    case frags of
      [] => (frags, Error error)
    | QUOTE s :: rest => if s = "" then aq0 error rest
                         else (frags, Error error)
    | ANTIQUOTE t :: rest => (rest, Some t)

fun getc error frags =
  case frags of
    [] => (frags, Error error)
  | QUOTE s :: rest =>
    if s = "" then getc error rest
    else let val i' = if size s = 1 then rest
                      else QUOTE (String.extract(s,1,NONE)) :: rest
         in
           (i', Some (String.sub(s,0)))
         end
  | ANTIQUOTE _ :: _ => (frags, Error error)

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
        getc "" >-
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

fun comment s =
    (token0 "(*" >> repeat (mnot (token0 "*)") >> getc "") >>
     token0 "*)") s

fun lex m = repeat ((getP Char.isSpace >> ok) ++ comment) >> m
fun complete m = m <- repeat ((getP Char.isSpace >> ok) ++ comment)
fun token s = lex (token0 s)
fun aq s = lex (aq0 s)

fun mrpt m = let
  fun recurse acc = (m >- (fn v => recurse (v::acc))) ++
                    return (List.rev acc)
in
  recurse []
end

fun ident0 s =
  (getP Char.isAlpha >-
   (fn c => mrpt (getP Char.isAlphaNum) >-
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
    case grammar0 fs of
        (_, Error s) => raise Fail s
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
          case Lib.total dest_comb t of
              SOME (g,x) => if same_const g gspec_tm then
                              let val (v, body) = dest_pabs x
                                  val (e, cond) = dest_pair body
                              in
                                mk_icomb(gspec_tm, mk_pabs(v,mk_pair(f e, cond)))
                              end
                            else raise err()
            | NONE => raise err()
        end
end

fun clause_to_termSet ntnm nty (gi as {tokty,...}:ginfo) c = let
  val symty = mk_symty(tokty,nty)
  val nt_t = mkNT0 nty (#mkntname gi) ntnm
  open pred_setSyntax pairSyntax listSyntax
in
  case c of
      Syms slist =>
      let
        val (used, ts) =
            case mmap (sym_to_term nty gi) slist [] of
                (used, Some ts) => (used, ts)
             |  _ => raise Fail "Can't happen"
        val body = mk_pair(nt_t, mk_list(ts, symty))
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
        image (fn t => mk_pair(nt_t, mk_list([mk_comb(TOK_t', t)], symty)))
              (mk_prod(mk_infty nty, symlist_ty))
              t
      end
end

fun mk_grammar_def0 (gi:ginfo) (g:t) = let
  val {tokmap,nt_tyname,mkntname,tokty,start,gname,...} = gi
  val nt_names = allnts mkntname g
  val constructors =
      ParseDatatype.Constructors
        (HOLset.foldl (fn (nm,l) => (nm,[]) :: l) [] nt_names)
  val _ = Datatype.astHol_datatype [(nt_tyname,constructors)]
  val nty = mk_thy_type { Thy = current_theory(),
                          Tyop = nt_tyname, Args = []}
  val U = list_mk_lbinop (curry pred_setSyntax.mk_union) o List.concat
  val gty = mk_thy_type {Thy = "grammar", Tyop = "grammar", Args = [tokty,nty]}
  val rules =
      U (map (fn (ntnm,cs) => map (clause_to_termSet ntnm nty gi) cs) g)
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
               `E ::= E "*" F | F;
                F ::= F "+" T | T;
                T ::= <Number> | "(" E ")" | ^(``{ Ident s | s <> "" ∧ isAlpha (HD s)}``);`;

*)

end
