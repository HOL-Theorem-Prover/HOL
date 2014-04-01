(*===========================================================================*)
(* EmitML: mapping HOL expressions to ML. The basic HOL theory hierarchy has *)
(* a loose analogue in the hierarchy of basic ML structures. Thus we have    *)
(* something like                                                            *)
(*                                                                           *)
(*    HOL Theory         ML Structure                                        *)
(*    ----------         ------------                                        *)
(*    boolTheory            Bool                                             *)
(*    numTheory             Arbnum                                           *)
(*    intTheory             Arbint                                           *)
(*    optionTheory          Option                                           *)
(*    listTheory            List                                             *)
(*    stringTheory          Char,String                                      *)
(*                                                                           *)
(* Missing from this list are pairs (pairTheory in HOL, builtin to ML),      *)
(* which are flat tuples in ML and nested pairs in HOL. Also there is the    *)
(* unit type, which exists in both HOL and ML. Other structures where there  *)
(* is a close relationship arise from Anthony Fox's parameterized theory of  *)
(* n-bit words.                                                              *)
(*                                                                           *)
(* The ideal, we assume, is to build formalizations in HOL and then "export" *)
(* them to ML, with the idea that the executable aspects of a HOL            *)
(* formalization can be faithfully copied down to ML. If this can be         *)
(* supported, then ground HOL expressions should be able to be copied to ML  *)
(* and executed there, with huge speed-ups. This can be used to provide a    *)
(* code generation facility and a testing environment for HOL definitions.   *)
(*                                                                           *)
(* Exporting HOL definitions of types and functions consists of 2 things:    *)
(* installing those definitions in ML and mapping HOL expressions into       *)
(* syntactically acceptable ML expressions. The latter operation is "just"   *)
(* prettyprinting, where the prettyprinter uses a table mapping HOL types    *)
(* and constants to their ML counterparts. This table needs to be extensible *)
(* as theories load.                                                         *)
(*                                                                           *)
(*===========================================================================*)

structure EmitML :> EmitML =
struct

open HolKernel boolSyntax Abbrev;

val ERR = mk_HOL_ERR "EmitML";
val WARN = HOL_WARNING "EmitML";

(*---------------------------------------------------------------------------*)
(* All ref cells.                                                            *)
(*---------------------------------------------------------------------------*)

val emitOcaml = ref false;
val sigSuffix = ref "ML.sig";
val structSuffix = ref "ML.sml";
val sigCamlSuffix = ref "ML.mli";
val structCamlSuffix = ref "ML.ml";

val is_int_literal_hook = ref (fn _:term => false);
val int_of_term_hook = ref
    (fn _:term => (raise ERR "EmitML" "integers not loaded") : Arbint.int)

(*---------------------------------------------------------------------------*)
(* Misc. syntax operations                                                   *)
(*---------------------------------------------------------------------------*)

val is_pair_type = Lib.can pairSyntax.dest_prod;
val is_num_literal = Lib.can Literal.relaxed_dest_numeral;

(*---------------------------------------------------------------------------*)
(* Version of dest_string that doesn't care if characters look like          *)
(*                                                                           *)
(*   CHAR (NUMERAL n)    or    CHAR n                                        *)
(*---------------------------------------------------------------------------*)

val is_string_literal = Lib.can Literal.relaxed_dest_string_lit;

fun strip_cons M =
 case total (listSyntax.dest_cons) M
  of SOME (h,t) => h::strip_cons t
   | NONE => [M];

fun is_fn_app tm = is_comb tm andalso not(pairSyntax.is_pair tm)
fun is_infix_app tm = is_conj tm orelse is_disj tm orelse is_eq tm ;

local
  val a = mk_var("a",bool)
  val b = mk_var("b",bool)
in
val andalso_tm = list_mk_abs([a,b],mk_conj(a,b))
val orelse_tm = list_mk_abs([a,b],mk_disj(a,b))
end

(*---------------------------------------------------------------------------*)
(* Peculiar names for fake record constructors. These help generate code for *)
(* projection and access functions automatically defined for records. The    *)
(* need for this comes from the fact that large records declarations are     *)
(* modelled differently than small records; the difference in representation *)
(* is vexatious when defining the ML projection and access functions, since  *)
(* we want the resulting ML to look the same, i.e., be readable, no matter   *)
(* how big the record is.                                                    *)
(*---------------------------------------------------------------------------*)

fun mk_record_vconstr (name,ty) = mk_var(name^"--Record Constr Var",ty)

fun dest_record_vconstr v =
 let open Substring
     val (name,ty) = dest_var v
     val (ss1,ss2) = position "--Record Constr Var" (full name)
 in if string ss2 = "--Record Constr Var"
     then (string ss1,ty)
     else raise ERR "dest_record_vconstr" ""
 end handle _ => raise ERR "dest_record_vconstr" "";

val is_fake_constructor = Lib.can dest_record_vconstr;

local
  val reserved_set = Redblackset.addList (Redblackset.empty String.compare,
    ["abstype", "datatype", "do", "end", "eqtype", "exception", "fn", "fun",
     "functor", "handle", "include", "infix", "infixr", "local", "nonfix", "op",
     "open", "raise", "rec", "sharing", "sig", "signature", "struct",
     "structure", "type", "val", "where", "withtype", "while"])
  fun is_reserved s = Redblackset.member (reserved_set, s)
in
  fun fix_reserved s = if is_reserved s then s ^ "_" else s
end

fun fix_symbol c =
  case c of
    #"#"  => #"^"
  | #"\\" => #"!"
  | #":"  => #"?"
  | #"~"  => #"$"
  | #"|"  => #"@"
  | _     => c;

fun capitalize s =
  if !emitOcaml then
    Char.toString (Char.toUpper (String.sub(s,0))) ^ String.extract(s,1,NONE)
  else
    s;

fun lowerize s =
  if !emitOcaml then
    Char.toString (Char.toLower (String.sub(s,0))) ^ String.extract(s,1,NONE)
  else
    s;

fun fix_name (prefix,is_type_cons,s) =
  let val c0 = String.sub(s,0)
      val s1 = if not (prefix = "") andalso c0 = #" " then
                 String.extract(s,1,NONE)
               else
                 s
  in
    if !emitOcaml then
      if s = "andalso" then
        "&&"
      else if s = "orelse" then
        "||"
      else if s = "SOME" then
        "Some"
      else if s = "NONE" then
        "None"
      else let val s1 = String.map fix_symbol s in
        if not (Char.isAlphaNum c0 orelse (s1 = "=")) then
          prefix ^ "(" ^ s1 ^ ")"
        else if is_type_cons then
          prefix ^ capitalize s1
        else
          prefix ^ (if Char.isUpper c0 then "_" ^ s1 else fix_reserved s1)
      end
    else
      prefix ^ (fix_reserved s1)
  end;

fun ML s = capitalize s ^ "ML";

fun full_name openthys (is_type_cons,s1,s2,_) =
  let val prefix = if mem s1 openthys orelse (s1="") then
                     ""
                   else
                     ML s1 ^ "."
  in
    fix_name (prefix,is_type_cons,s2)
  end;

fun const_map openthys c = full_name openthys (ConstMapML.apply c);

val COMMA_PREC = 50;
val CONS_PREC  = 450;

fun prec_of c =
  if same_const c boolSyntax.equality then 100 else
  if same_const c boolSyntax.disjunction then 300 else
  if same_const c boolSyntax.conjunction then 400 else
  if same_const c pairSyntax.comma_tm then COMMA_PREC else 0;

val minprec = ~1;
val maxprec = 9999;

datatype side = LEFT | RIGHT;

fun pick_name slist n (s1,s2) = if mem n slist then s1 else s2;

fun vars_of_types alist =
  map (fn (i,ty) => mk_var("v"^Int.toString i,ty)) (Lib.enumerate 0 alist);

(*---------------------------------------------------------------------------*)
(* Convert a constructor application (C t1 ... tn) to C'(t1,...,tn) where    *)
(* C' is a variable with the same name as C. This code only deals with       *)
(* pseudo-constructors, like INSERT for sets and BAG_INSERT for bags. These  *)
(* are *not* constructors, but we will generate programs in which they are   *)
(* constructors for abstract datatypes.                                      *)
(*                                                                           *)
(* Real constructors are detected in the term prettyprinter by testing       *)
(* TypeBase.is_constructor. In contrast, pseudo-constructors are dealt with  *)
(* in a pre-processing pass over the theorems that code is being generated   *)
(* from.                                                                     *)
(*---------------------------------------------------------------------------*)

local val emit_tag = "EmitML"
  val pseudo_constr_defs = ref [] : thm list ref;
in
fun pseudo_constr_rws() = map concl (!pseudo_constr_defs)
val reshape_thm_hook = ref (fn th =>
     pairLib.GEN_BETA_RULE (Rewrite.PURE_REWRITE_RULE (!pseudo_constr_defs) th))

fun new_pseudo_constr (c,a) =
 let fun nstrip_fun 0 ty = ([],ty)
       | nstrip_fun n ty =
         let val (d,r) = dom_rng ty
             val (f,b) = nstrip_fun (n-1) r
         in (d::f,b)
         end
     val (argtys,target) = nstrip_fun a (type_of c)
     val args = vars_of_types argtys
     val pvar = mk_var("^" ^ fst(dest_const c),
                       pairSyntax.list_mk_prod argtys --> target)
     val new = pairSyntax.list_mk_pabs
                 (args,mk_comb(pvar,pairSyntax.list_mk_pair args))
     val thm = mk_oracle_thm emit_tag ([],mk_eq(c,new))
 in
    pseudo_constr_defs := thm :: !pseudo_constr_defs
 end
end;

fun generic_type_of tm =
  if is_const tm
   then let val {Name,Thy,...} = dest_thy_const tm
        in type_of (prim_mk_const{Name=Name,Thy=Thy})
        end
   else type_of tm;

(*---------------------------------------------------------------------------*)
(* A prettyprinter from HOL to very simple ML, dealing with basic paired     *)
(* lambda calculus terms, plus literals (strings, nums, ints), notation for  *)
(* lists, and case expressions.                                              *)
(*---------------------------------------------------------------------------*)

fun term_to_ML openthys side ppstrm =
 let open Portable
     val {add_break,add_newline,
          add_string,begin_block,end_block,...} = with_ppstream ppstrm
     fun prec_paren p i j = if i >= j then add_string p else ()
     val lparen = prec_paren "("
     val rparen = prec_paren ")"
     val const_map = const_map openthys
     val numML = if !emitOcaml then "NumML." else "numML."
     val intML = if !emitOcaml then "IntML." else "intML."
     val fcpML = if !emitOcaml then "FcpML." else "fcpML."
     fun fix s = fix_name("", false, s)
  fun pp i tm =
     if is_var tm then pp_var tm else
     if is_cond tm then pp_cond i tm else
     if is_arb tm then pp_arb i else
     if is_num_literal tm then pp_num_literal i tm else
     if !is_int_literal_hook tm then pp_int_literal tm else
     if is_string_literal tm then pp_string tm else
     if listSyntax.is_list tm then pp_list tm else
     if listSyntax.is_cons tm then pp_cons i tm else
     if listSyntax.is_mem tm then pp_mem i (listSyntax.dest_mem tm) else
     if is_infix_app tm then pp_binop i tm else
     if pairSyntax.is_pair tm then pp_pair i tm else
     if boolSyntax.is_let tm then pp_lets i tm else
     if pairSyntax.is_pabs tm then pp_abs i tm else
     if combinSyntax.is_fail tm then pp_fail i tm else
     if oneSyntax.is_one tm  then pp_one tm else
     if TypeBase.is_record tm then pp_record i (TypeBase.dest_record tm) else
     if TypeBase.is_case tm then pp_case i (TypeBase.strip_case tm) else
     if is_the_value tm then pp_itself tm else
     if is_const tm then pp_const i tm else
     if is_comb tm then pp_comb i tm
     else raise ERR "term_to_ML"
                    ("Unknown syntax with term: "^Parse.term_to_string tm)
  and pp_cond i tm = let
    val (b,a1,a2) = dest_cond tm
    val parens = i >= (if !emitOcaml then minprec else 70)
    fun conddo b f = if b then f() else ()
  in
    conddo parens (fn () => (add_string "("; begin_block CONSISTENT 0));
      begin_block CONSISTENT 0;
        add_string"if";
        add_break(1,2);
        begin_block INCONSISTENT 0; pp 70 b; end_block();
        add_break(1,0);
        add_string"then";
      end_block();
      add_break(1,2);
      begin_block INCONSISTENT 0; pp 70 a1; end_block();
      add_break(1,0);
      begin_block CONSISTENT 0;
        add_string"else";
        add_break(1,2);
        pp minprec a2;
      end_block();
    conddo parens (fn () => (end_block(); add_string ")"))
  end
  and pp_num_from_string s =
        if s="0" then
          add_string (pick_name openthys "num" ("ZERO",numML ^ "ZERO"))
        else if s="1" then
          add_string (pick_name openthys "num" (fix "ONE",numML ^ fix "ONE"))
        else if s="2" then
          add_string (pick_name openthys "num" (fix "TWO",numML ^ fix "TWO"))
        else
          (begin_block INCONSISTENT 0
         ; add_string"("
         ; add_string (pick_name openthys "num"
                         ("fromString ", numML ^ "fromString "))
         ; add_break(0,0)
         ; add_string (quote s)
         ; add_string")"
         ; end_block())
  and pp_num_literal i tm =
      (*------------------------------------------------------------*)
      (* Numeric literals can be built from strings or constructors *)
      (*------------------------------------------------------------*)
      let val s = Arbnum.toString(Literal.relaxed_dest_numeral tm)
      in if side = RIGHT (* use fromString *)
         then
           pp_num_from_string s
         else (* side = LEFT, so use constructors *)
           if s = "0"
           then add_string (pick_name openthys "num" ("ZERO",numML ^ "ZERO"))
           else pp_comb i tm
      end
  and pp_int_literal tm =
         let val s = Arbint.toString(!int_of_term_hook tm)
         in begin_block CONSISTENT 0
          ; add_string"("; add_break(0,0)
          ; add_string (pick_name openthys "int"
              ("fromString", intML ^ "fromString"))
          ; add_break(0,0)
          ; add_string (mlquote s)
          ; add_break(0,0)
          ; add_string")"
          ; end_block()
         end
  and pp_string tm = add_string (mlquote (Literal.relaxed_dest_string_lit tm))
  and pp_list tm =
       let val els = fst (listSyntax.dest_list tm)
       in begin_block CONSISTENT 0
        ; add_string "["
        ; begin_block INCONSISTENT 0
        ; pr_list (pp minprec)
                  (fn () => add_string (if !emitOcaml then ";" else ","))
                  (fn () => add_break(0,0)) els
        ; end_block()
        ; add_string "]"
        ; end_block()
       end
  and pp_binop i tm =
      let val (c,t1,t2) = case strip_comb tm
                          of (c,[t1,t2]) => (c,t1,t2)
                           | _ => raise ERR "term_to_ML" ""
          val j = prec_of c
      in begin_block CONSISTENT 0
        ; lparen i j
        ; begin_block INCONSISTENT 0
        ; pp (j+1) t1
        ; add_break(1,0)
        ; add_string (const_map c)
        ; add_break(1,0)
        ; pp j t2
        ; end_block()
        ; rparen i j
        ; end_block()
      end
  and pp_cons i tm =
      let val alist = strip_cons tm
          val j = CONS_PREC
      in begin_block CONSISTENT 0
        ; lparen i j
        ; begin_block INCONSISTENT 0
        ; pr_list (pp j)
                  (fn () => add_string "::")
                  (fn () => add_break(0,0)) alist
        ; end_block()
        ; rparen i j
        ; end_block()
      end
  and pp_mem i (t1, t2) =
      let
      in
        begin_block INCONSISTENT 0
      ; lparen i maxprec
      ; add_string (full_name openthys (false,"list","MEM",bool))
      ; add_break(1,0)
      ; pr_list (pp maxprec) (fn () => add_break(1,0)) (fn () => ()) [t1, t2]
      ; rparen i maxprec
      ; end_block()
      end
  and pp_pair i tm =
      let val (t1,t2) = pairSyntax.dest_pair tm
          val j = COMMA_PREC
      in begin_block INCONSISTENT 0
        ; lparen maxprec i
        ; begin_block INCONSISTENT 0
        ; pp (j+1) t1
        ; add_string ","
        ; add_break(0,0)
        ; pp j t2
        ; end_block()
        ; rparen maxprec i
        ; end_block()
      end
  and pp_lets i tm = (* a sequence of lets *)
      let val (blists,body) = pairSyntax.strip_anylet tm
          fun pp_binding (k,(l,r)) =
               (begin_block INCONSISTENT 4;
                add_string k; add_break(1,0);
                pp minprec l; add_break(1,0);
                add_string "="; add_break(1,0);
                begin_block CONSISTENT 0;
                pp minprec r; end_block();
                end_block())
      in  begin_block CONSISTENT 0
        ; if !emitOcaml then
           (let
              fun keyword [] = raise ERR "term_to_ML" "pp_lets"
                | keyword l = ("let", hd l) :: (map (pair "and") (tl l))
              val blist' = map keyword blists
              fun droplast [] = []
                | droplast l = List.take(l, length l - 1)
            in
                lparen i minprec
              ; begin_block CONSISTENT 0
              ; app (fn l => (pr_list pp_binding (fn()=>()) add_newline l;
                     add_break(1,0); add_string "in"; add_break(1,0)))
                    (droplast blist')
              ; pr_list pp_binding (fn()=>()) add_newline (last blist')
              ; add_break(1,0)
              ; add_string "in"
              ; add_break(1,3)
              ; pp minprec body
              ; end_block()
              ; rparen i minprec
            end)
          else
           (let
              fun keyword1 (l,r) = (if is_fn_app l then "fun" else "val", (l,r))
              fun keyword [] = raise ERR "term_to_ML" "pp_lets"
                | keyword l = map keyword1 l
              val blist' = flatten (map keyword blists)
            in
                lparen i 5000
              ; begin_block CONSISTENT 0
              ; add_string "let "
              ; begin_block CONSISTENT 0
              ;   pr_list pp_binding (fn()=>()) add_newline blist'
              ;    end_block()
              ; add_break(1,0)
              ; add_string"in"
              ; add_break(1,3)
              ; pp minprec body
              ; add_break(1,0)
              ; add_string "end"
              ; end_block()
              ; rparen i 5000
            end)
        ; end_block()
      end
  and pp_case i (a,cases) =
      ( begin_block CONSISTENT 1
                   (* from HOL term grammar *)
        ; lparen i (if !emitOcaml then minprec else 7)
        ; begin_block INCONSISTENT 2
        ; add_string (if !emitOcaml then "match" else "case")
        ; add_break(1,0)
        ; pp minprec a
        ; end_block()
        ; add_break(1,0)
        ; begin_block CONSISTENT 1
        ; add_string (if !emitOcaml then "with " else "of ")
        ; pp_case_clause (hd cases)
        ; add_break(1,0)
        ; pr_list (fn cl => (add_string "| "; pp_case_clause cl))
                  (fn () => ())
                  (fn () => add_break(1,0)) (tl cases)
        ; end_block()
        ; rparen i (if !emitOcaml then minprec else 7)
        ; end_block())
  and pp_case_clause (pat,rhs) =
        (begin_block CONSISTENT 3
         ; pp minprec pat
         ; add_string (if !emitOcaml then " ->" else " =>")
         ; add_break (1,0)
         ; pp 7 rhs
         ; end_block()
        )
  and pp_record i (ty,flds) =
       pp_open_comb i (hd(TypeBase.constructors_of ty), map snd flds)
  and pp_fail i tm =
       let val (f,s,args) = combinSyntax.dest_fail tm
           val fname = fst(dest_const f)
       in begin_block CONSISTENT 3
         ; add_string "raise ("
         ; add_string (if !emitOcaml then "Failure" else "Fail")
         ; add_break (1,0)
         ; add_string (Lib.quote (fname^": "^s)^")")
         ; end_block()
       end
  and pp_arb i =
      (lparen i maxprec
       ; begin_block CONSISTENT 3
       ; add_string
           (if !emitOcaml then "raise (Failure \"ARB\")"
                          else "raise Fail \"ARB\"")
       ; end_block()
       ; rparen i maxprec)
  and pp_itself tm =
    let fun skip1 s = String.extract(s, 1, NONE)
        fun num_type typ =
              let val pp_n = !type_pp.pp_num_types
                  val _ = type_pp.pp_num_types := true
              in
                skip1 (Hol_pp.type_to_string typ) before
                type_pp.pp_num_types := pp_n
              end
        fun itself x =
               (begin_block INCONSISTENT 2
              ; add_string "("
              ; add_string
                  (pick_name openthys "fcp" ("ITSELF", fcpML ^ "ITSELF"))
              ; add_break (1,0)
              ; pp_num_from_string x
              ; add_string ")"
              ; end_block())
        fun pp_itself_type typ =
         if is_vartype typ then
           add_string (skip1 (dest_vartype typ))
         else
           case (dest_type typ) of
             ("one", [])   => itself "1"
           | ("num", [])   => itself "1"
           | ("int", [])   => itself "1"
           | ("list", [a]) => itself "1"
           | ("bool", [])  => itself "2"
           | ("bit0", [a]) => itself (num_type typ)
           | ("bit1", [a]) => itself (num_type typ)
           | ("string", []) => itself "1"
           | (tyop, [a, b]) =>
              (begin_block INCONSISTENT 0
               ; add_string ("(" ^
                  pick_name openthys "fcp"
                   (case tyop of
                      "sum"  => (fix "SUMi", fcpML ^ fix "SUMi")
                    | "prod" => (fix "MULi", fcpML ^ fix "MULi")
                    | "cart" => (fix "EXPi", fcpML ^ fix "EXPi")
                    | _ => raise ERR "term_to_ML" "pp_itself") ^ "(")
               ; begin_block INCONSISTENT 0
               ; pp_itself_type a
               ; add_string ", "
               ; add_break (0,0)
               ; pp_itself_type b
               ; end_block()
               ; add_string "))"
               ; end_block())
           | _ => raise ERR "term_to_ML" "pp_itself"
    in
      (pp_itself_type o hd o snd o dest_type o type_of) tm
    end
  and pp_var tm = let val s = fst(dest_var tm)
                      val c = String.sub(s,0)
                  in
                    if c = #"^" then
                      add_string (fix_reserved (String.extract(s,1,NONE)))
                    else if !emitOcaml andalso Char.isUpper c then
                      add_string ("_" ^ s)
                    else
                      add_string (fix_reserved s)
                  end
  and pp_const i tm =
      if same_const tm boolSyntax.conjunction
         then pp_abs i andalso_tm else
       if same_const tm boolSyntax.disjunction
         then pp_abs i orelse_tm
       else add_string (const_map tm)
  and pp_one tm = add_string "()"
  and pp_nil tm = add_string "[]"
  and pp_open_comb i (f,args) =
       let val is_constr = case Lib.total ConstMapML.apply f
                             of SOME (true,_,_,_) => true
                              | _ => false
       in begin_block CONSISTENT 0
        ; lparen i maxprec
        ; if TypeBase.is_constructor f andalso is_constr
               orelse is_fake_constructor f
            then
              (let val fname = fst(dest_const f) handle HOL_ERR _ =>
                               fst(dest_record_vconstr f)
               in add_string (fix_name ("", true, fname))
               end;   (* pp maxprec f; *)
               add_string "(";
               begin_block INCONSISTENT 0;
               pr_list (pp minprec)
                       (fn () => add_string ",")
                       (fn () => add_break(0,0)) args;
               end_block();
               add_string ")"
              )
            else (begin_block INCONSISTENT 2;
                  pr_list (pp maxprec) (fn () => ())
                          (fn () => add_break(1,0)) (f::args);
                  end_block())
        ; rparen i maxprec
        ; end_block()
       end
  and pp_comb i tm =
       let val (h,args) = strip_comb tm
           val (argtys,target) = strip_fun(generic_type_of h)
       in if length argtys < length args
          then let val (app,rst) = split_after (length argtys) args
               in
                 lparen i maxprec;
                 pp maxprec (list_mk_comb(h,app));
                 add_break (1,0);
                 pr_list (pp maxprec)
                       (fn () => ())
                       (fn () => add_break(1,0)) rst;
                 rparen i maxprec
               end
          else pp_open_comb i (h,args)
       end
  and pp_abs i tm =
       let val (vstruct,body) = pairSyntax.dest_pabs tm
       in lparen i (if !emitOcaml then minprec else 5000)
        ; add_string (if !emitOcaml then "function" else "fn")
        ; add_break (1,0)
        ; pp 50 vstruct
        ; add_break (1,0)
        ; add_string (if !emitOcaml then "->" else "=>")
        ; add_break (1,0)
        ; pp minprec body
        ; rparen i (if !emitOcaml then minprec else 5000)
       end

 in fn i => fn M =>
    (begin_block INCONSISTENT 0 ; pp i M ; end_block ())
 end;

fun pp_term_as_ML openthys side ppstrm M =
    term_to_ML openthys side ppstrm minprec M;

fun same_fn eq1 eq2 =
  same_const (fst(strip_comb(lhs eq1))) (fst(strip_comb(lhs eq2)));

(*---------------------------------------------------------------------------*)
(* Print a function definition as ML, i.e., fun f ... = ...                  *)
(*---------------------------------------------------------------------------*)

fun partitions P [] = []
  | partitions P (h::t) =
     case partition (P h) t
      of (L1,L2) => (h::L1) :: partitions P L2;

fun pp_defn_as_ML openthys ppstrm =
 let open Portable
     val {add_break,add_newline,
          add_string,begin_block,end_block,...} = with_ppstream ppstrm
     val toML = fn ppnumlit => term_to_ML openthys ppnumlit ppstrm
     fun pp_clause i eq =
         let val (L,R) = dest_eq eq
         in begin_block INCONSISTENT 2
          ; toML LEFT minprec L
          ; add_break(1,0)
          ; add_string "="
          ; add_break(1,0)
          ; toML RIGHT i R
          ; end_block()
         end
     fun pp_clauses (s,els) =
       let val s' = if is_fn_app(lhs(hd els)) then s else "val"
       in  begin_block CONSISTENT 2
         ; add_string (s'^" ")
         ; pp_clause (if length els = 1 then minprec else 100) (hd els)
         ; add_newline()
         ; case tl els
            of [] => ()
             | els' =>
                 (pr_list (fn c => (add_string "| "; pp_clause 100 c))
                    (fn () => ())
                    (fn () => add_newline()) els';
                  add_newline())
         ; end_block()
       end
     fun pp tm =
       let val eqns = map (snd o strip_forall)
                          (strip_conj (snd (strip_forall tm)))
           val clauses = partitions same_fn eqns (* term list list *)
           val clauses' = ("fun",hd clauses)::map (pair "and") (tl clauses)
       in begin_block CONSISTENT 0
        ; pr_list pp_clauses (fn () => ())
                  (fn () => (add_newline())) clauses'
        ; end_block()
       end
 in
    pp
 end;

fun pp_defn_as_OCAML openthys ppstrm =
 let open Portable
     val const_map = const_map openthys
     val {add_break,add_newline,
          add_string,begin_block,end_block,...} = with_ppstream ppstrm
     val toML = fn ppnumlit => term_to_ML openthys ppnumlit ppstrm
     fun pp_clause i eq =
         let val (L,R) = dest_eq eq
         in begin_block INCONSISTENT 2
          ; toML LEFT minprec L
          ; add_break(1,0)
          ; add_string "="
          ; add_break(1,0)
          ; toML RIGHT i R
          ; end_block()
         end
     fun pp_pattern i s (L,R) =
         (begin_block INCONSISTENT 0
          ; add_string (fix_reserved s)
          ; begin_block INCONSISTENT 2
          ; begin_block INCONSISTENT 0
          ; pr_list (toML LEFT minprec) (fn () => add_string ",")
              (fn () => add_break(0,0)) L
          ; end_block()
          ; add_string " ->"
          ; add_break(1,0)
          ; toML RIGHT i R
          ; end_block()
          ; add_newline()
          ; end_block())
     fun caml_strip_comb t = let
       val (t1, t2) = listSyntax.dest_mem t
     in
       (full_name openthys (false, "list", "MEM", bool), [t1, t2])
     end handle _ => apfst const_map (strip_comb t)
     fun clauses_to_patterns els = map (((snd o caml_strip_comb)##I) o dest_eq) els
     fun pp_clauses (s,els) =
         ( begin_block INCONSISTENT 2
         ; add_string (s^" ")
         ; if length els = 1 then
            (pp_clause minprec (hd els); add_newline())
           else
             let
               val (fname, args) = caml_strip_comb (lhs (hd els))
               val vs = vars_of_types (map type_of args)
               val pats = clauses_to_patterns els
             in
                 add_string fname
               ; add_break(1,0)
               ; pr_list (toML LEFT minprec) (fn () => add_break(1,0)) (fn () => ()) vs
               ; add_break(1,0)
               ; add_string "="
               ; add_break(1,0)
               ; add_string "match "
               ; begin_block INCONSISTENT 0
               ; pr_list (toML LEFT minprec) (fn () => add_string ",")
                   (fn () => add_break(0,0)) vs
               ; end_block()
               ; add_string " with"
               ; add_break(1,0)
               ; begin_block INCONSISTENT 0
               ; pp_pattern 100 "  " (hd pats)
               ; case tl pats
                   of [] => ()
                    | pats' =>
                        pr_list (pp_pattern 100 "| ") (fn () => ())
                           (fn () => ()) pats'
               ; end_block()
             end
         ; end_block())
     fun contains_const c t = can (find_term (same_const c)) t;
     fun contains_consts l t =
           isSome (List.find (fn c => contains_const c t) l);
     fun pp tm =
       let val eqns = map (snd o strip_forall)
                          (strip_conj (snd (strip_forall tm)))
           val clauses = partitions same_fn eqns (* term list list *)
           val rhsides = map rhs eqns
           val lhsides = eqns |> map lhs |> filter is_fn_app
                              |> map (fst o strip_comb)
                              |> filter (not o same_const IN_tm)
           val possibly_recursive =
                 isSome (List.find (contains_consts lhsides) rhsides)
           val s = if possibly_recursive then "let rec" else "let"
           val clauses' = (s,hd clauses)::map (pair "and") (tl clauses)
       in begin_block CONSISTENT 0
        ; pr_list pp_clauses (fn () => ())
                  (fn () => (add_newline())) clauses'
        ; end_block()
       end
 in
    pp
 end;

(*---------------------------------------------------------------------------*)
(* Now print datatype declarations in ML. First tweak the existing type      *)
(* prettyprinter so it generates syntactically correct ML types              *)
(*---------------------------------------------------------------------------*)

fun adjust_tygram tygram =
 let open type_grammar HOLgrammars
     val g0 = List.foldl (fn (s,g) => remove_binary_tyop g s)
                         tygram
                         ["+", "#", "|->", "**"]
 in
   new_binary_tyop g0 {precedence = 70, infix_form = SOME "*",
                       opname = "prod", associativity = NONASSOC}
 end;

fun prim_pp_type_as_ML tygram ppstrm =
   trace ("Greek tyvars",0)
      (type_pp.pp_type (adjust_tygram tygram) PPBackEnd.raw_terminal ppstrm)

fun pp_type_as_ML ppstrm = prim_pp_type_as_ML (Parse.type_grammar()) ppstrm;

(*---------------------------------------------------------------------------*)
(* Elements of a theory presentation.                                        *)
(*---------------------------------------------------------------------------*)

datatype elem
    = DEFN of thm
    | DEFN_NOSIG of thm
    | DATATYPE of hol_type quotation
    | EQDATATYPE of string list * hol_type quotation
    | ABSDATATYPE of string list * hol_type quotation
    | OPEN of string list
    | MLSIG of string
    | MLSTRUCT of string;

(*---------------------------------------------------------------------------*)
(* Fetch the constructors out of a datatype declaration                      *)
(*---------------------------------------------------------------------------*)

local open ParseDatatype
in
fun constructors [] = []
  | constructors ((s,Constructors clist)::rst) = clist@constructors rst
  | constructors ((s,Record flds)::rst) = [(s, map snd flds)]@constructors rst

fun constrl [] = []
  | constrl ((s,Constructors clist)::rst) = (s,clist)::constrl rst
  | constrl ((s,Record flds)::rst) = (s, [(s,map snd flds)])::constrl rst
end;

(*---------------------------------------------------------------------------*)
(* Internal version of elem (nearly identical, except that datatype          *)
(* declarations have been parsed) and some standard definitions from         *)
(* datatypes (e.g. size functions) and record types (accessor and field      *)
(* update functions) are automatically added.                                *)
(*---------------------------------------------------------------------------*)

datatype elem_internal
    = iDEFN of thm
    | iDEFN_NOSIG of thm
    | iDATATYPE of ParseDatatype.AST list
    | iEQDATATYPE of string list * ParseDatatype.AST list
    | iABSDATATYPE of string list * ParseDatatype.AST list
    | iOPEN of string list
    | iMLSIG of string
    | iMLSTRUCT of string;


(*---------------------------------------------------------------------------*)
(* A datatype declaration results in some extra HOL function definitions     *)
(* being automatically made. These are, usually, invisible to the user, but  *)
(* are important and usually need to have ML generated for them.  Currently, *)
(* only the access and update functions for records are generated. We used   *)
(* to also write out the size functions for datatypes as well, but they were *)
(* not used, so they are going for the time being.                           *)
(*                                                                           *)
(* In many cases suitable update and access functions are defined by the     *)
(* datatype package and stuck into the TypeBase. However, large records are  *)
(* modelled differently, for efficiency. The threshold number of fields is   *)
(* controlled by Datatype.big_record_size. A big record has a different      *)
(* shape, i.e., recursion theorem. To handle such records, we generate       *)
(* fake "theorems" of the right form. This should be OK, as they are only    *)
(* created for exporting the ML functions, and they are tagged. In fact, all *)
(* record declarations are handled by the following code.                    *)
(*---------------------------------------------------------------------------*)

fun diag vlist flist = tl
  (itlist2 (fn v => fn f => fn A =>
           case A of [] => [[v],[f v]]
                   | h::t => (v::h) :: (f v::h) :: map (cons v) t)
         vlist flist []);

fun gen_updates ty fields =
 let open pairSyntax
     val {Tyop,Thy,Args} = dest_thy_type ty
     fun mk_upd_const (fname,fty) =
        mk_thy_const{Name=Tyop^"_"^fname^"_fupd",Thy=Thy,
                     Ty = (fty --> fty) --> ty --> ty}
     val upds = map mk_upd_const fields
     val fns = map (fn (_,ty) => mk_var ("f", ty--> ty)) fields
     val fake_tyc = mk_record_vconstr(Tyop,list_mk_fun(map snd fields, ty))
     val vars = itlist
          (fn (n,(_,ty)) => fn acc =>
              mk_var("v"^int_to_string n,ty) :: acc)
          (enumerate 1 fields) []
     val pat = list_mk_comb(fake_tyc,vars)
     val lefts = map2 (fn upd => fn f => list_mk_comb(upd,[f,pat])) upds fns
     val diags = diag vars (map (curry mk_comb) fns)
     val rights = map (curry list_mk_comb fake_tyc) diags
     val eqns = rev(map2 (curry mk_eq) lefts rights)
     val mk_thm = mk_oracle_thm "EmitML fake thm"
 in
   map (curry mk_thm []) eqns
 end
 handle e => raise wrap_exn "EmitML" "gen_updates" e;

fun gen_accesses ty fields =
 let open pairSyntax
     val {Tyop,Thy,Args} = dest_thy_type ty
     fun mk_proj_const (fname,fty) =
         mk_thy_const{Name=Tyop^"_"^fname,Thy=Thy, Ty = ty --> fty}
     val projs = map mk_proj_const fields
     val fake_tyc = mk_record_vconstr(Tyop,list_mk_fun(map snd fields, ty))
     val vars = itlist
          (fn (n,(_,ty)) => fn acc =>
             mk_var("v"^int_to_string n,ty) :: acc)
          (enumerate 1 fields) []
     val pat = list_mk_comb(fake_tyc,vars)
     val lefts = map (fn proj => mk_comb(proj,pat)) projs
     val eqns = rev(map2 (curry mk_eq) lefts vars)
     val mk_thm = mk_oracle_thm "EmitML fake thm"
 in
   map (curry mk_thm []) eqns
 end
 handle e => raise wrap_exn "EmitML" "gen_accesses" e;

fun datatype_silent_defs tyAST =
 let val tyop = hd (map fst tyAST)
     val tyrecd = hd (Type.decls tyop)
 in
  if tyop = "num" then [] else
  case TypeBase.read tyrecd
   of NONE => (WARN "datatype_silent_defs"
                ("No info in the TypeBase for "^Lib.quote tyop); [])
   | SOME tyinfo =>
     let open TypeBasePure
          val size_def = [] (* [snd (valOf(size_of tyinfo))] handle _ => [] *)
          val (updates_defs, access_defs) =
            case fields_of tyinfo  (* test for record type *)
             of [] => ([],[])
              | fields => let val ty = ty_of tyinfo
                          in (gen_updates ty fields, gen_accesses ty fields)
                          end
     in
       map (iDEFN o !reshape_thm_hook)
           (size_def @ updates_defs @ access_defs)
     end
 end;

(*---------------------------------------------------------------------------*)
(* Map from external presentation to internal                                *)
(*---------------------------------------------------------------------------*)

(* Ocaml won't accept capitalized types            *)
(* Adds abbreviations with lowercase first letters *)

fun ocaml_type_abbrevs decls =
let
  val type_names = map fst decls
  val candidate_tyis =
        TypeBasePure.get (TypeBase.theTypeBase()) (hd type_names)
  val newtypes = if null candidate_tyis then [] else
                   Prim_rec.doms_of_tyaxiom
                     (TypeBasePure.axiom_of (hd candidate_tyis))
  fun do_abbrev(name, typ) =
        if Char.isUpper (String.sub(name,0)) then
          Parse.temp_type_abbrev(lowerize name, typ)
        else
          ()
in
  if length type_names = length newtypes then
    app do_abbrev (zip type_names newtypes)
  else
    ()
end;

fun elemi (DEFN th) (cs,il) = (cs,iDEFN (!reshape_thm_hook th) :: il)
  | elemi (DEFN_NOSIG th) (cs,il) = (cs,iDEFN_NOSIG (!reshape_thm_hook th)::il)
  | elemi (DATATYPE q) (cs,il) =
       let val tyAST = ParseDatatype.hparse q
           val _ = if !emitOcaml then ocaml_type_abbrevs tyAST else ()
           val defs = datatype_silent_defs tyAST
       in (cs, defs @ (iDATATYPE tyAST :: il))
       end
  | elemi (EQDATATYPE(sl,q)) (cs,il) =
       let val tyAST = ParseDatatype.hparse q
           val _ = if !emitOcaml then ocaml_type_abbrevs tyAST else ()
           val defs = datatype_silent_defs tyAST
       in (cs,defs @ (iEQDATATYPE(sl,tyAST) :: il))
       end
  | elemi (ABSDATATYPE(sl,q)) (cs,il) = (* build rewrites for pseudo constrs *)
     let open ParseDatatype
         val tyAST = hparse q
         val _ = if !emitOcaml then ocaml_type_abbrevs tyAST else ()
         val pconstrs = constrl tyAST
         val constr_names = flatten(map (map fst o snd) pconstrs)
         val constr_arities = flatten(map (map (length o snd) o snd) pconstrs)
         val constrs = map (hd o Term.decls) constr_names
         val constrs' = zip constrs constr_arities
         fun is_multi (_,n) = n >= 2
         val mconstrs = filter is_multi constrs'
         val _ = List.app new_pseudo_constr mconstrs
         (* val _ = schedule this call for exported theory *)
      in
        (mconstrs@cs, iABSDATATYPE(sl,tyAST) :: il)
      end
  | elemi (OPEN sl) (cs,il) = (cs,iOPEN sl :: il)
  | elemi (MLSIG s) (cs,il) = (cs,iMLSIG s :: il)
  | elemi (MLSTRUCT s) (cs,il) = (cs,iMLSTRUCT s :: il);

fun internalize elems =
  let val (cs, ielems) = rev_itlist elemi elems ([],[])
  in (rev cs, rev ielems)
  end;

local open ParseDatatype
fun replace f (v as dVartype _) = v
  | replace f (aq as dAQ _)     = aq
  | replace f (dTyop{Tyop,Thy,Args}) =
      f Tyop handle _ => dTyop{Tyop=Tyop,Thy=Thy,Args=map (replace f) Args}
in
fun replaceForm f (Constructors alist) =
                   Constructors (map (I##map (replace f)) alist)
  | replaceForm f other = other

fun pretype_of ty =
   dVartype(dest_vartype ty)
   handle _ =>
     let val (s,args) = dest_type ty
     in dTyop{Tyop=s,Thy=NONE,Args=map pretype_of args}
     end
end;

(*---------------------------------------------------------------------------*)
(* Initially, datatype descriptions do not have arguments to the type        *)
(* operators being defined. This function finds out what they should be      *)
(* and substitutes them through the rhs of the datatype declaration.         *)
(* The DATATYPE description requires looking info up in the type base, in    *)
(* order to see what order multiple type variables should be in. The         *)
(* EQDATATYPE clause expects the type variables to be given in the correct   *)
(* order in the first argument.                                              *)
(*---------------------------------------------------------------------------*)

fun repair_type_decls (iDATATYPE decls) =
     let val type_names = map fst decls
         val candidate_tyis =
             TypeBasePure.get (TypeBase.theTypeBase()) (hd type_names)
         val tyax = TypeBasePure.axiom_of (hd candidate_tyis)
         val newtypes = Prim_rec.doms_of_tyaxiom tyax
         val tyvars = map dest_vartype (snd (dest_type (hd newtypes)))
         val alist = map (fn x => (fst(dest_type x),pretype_of x)) newtypes
         fun alist_fn name = snd (valOf (assoc1 name alist))
     in
        (tyvars, map (I##replaceForm alist_fn) decls)
     end
  | repair_type_decls (iEQDATATYPE (tyvars,decls)) =
     let open ParseDatatype
         val tyvarsl = map dVartype tyvars
         val tynames = map fst decls
         val newtypes = map (fn s => dTyop{Tyop=s,Thy=NONE,Args=tyvarsl}) tynames
         val alist = zip tynames newtypes
         fun alist_fn name = snd (valOf (assoc1 name alist))
     in
       (tyvars, map (I##replaceForm alist_fn) decls)
     end
  | repair_type_decls (iABSDATATYPE stuff) = repair_type_decls (iEQDATATYPE stuff)
  | repair_type_decls arg = raise ERR "repair_type_decls" "unexpected input";

fun pp_datatype_as_ML ppstrm (tyvars,decls) =
 let open Portable ParseDatatype
     val {add_break,add_newline,
          add_string,begin_block,end_block,...} = with_ppstream ppstrm
     val fix_cons = fix_reserved o capitalize
     val fix_type = fix_reserved o lowerize
     val ppty = pp_type_as_ML ppstrm
     fun pp_comp_ty ty =
          if Lib.can dom_rng ty orelse is_pair_type ty
          then (add_string "("; ppty ty; add_string")")
          else ppty ty
     fun pp_tyl tyl =
        (begin_block INCONSISTENT 0
         ; pr_list pp_comp_ty (fn () => add_string" *")
                              (fn () => add_break(1,0)) tyl
         ; end_block())
     fun pp_tyvars [] = ()
       | pp_tyvars [v] = (add_string v; add_break(1,0))
       | pp_tyvars vlist =
          (begin_block CONSISTENT 0;
           add_string"(";
           pr_list add_string (fn () => add_string",") (fn ()=>()) vlist;
           add_string")";
           end_block())
     fun pp_clause r clause =
       (if !r then (add_string "= "; r:=false) else add_string "| ";
        case clause
         of (con,[]) => add_string (fix_cons con)
          | (con,args) =>
              (begin_block INCONSISTENT 0;
                 begin_block CONSISTENT 0;
                   add_string (fix_cons con);
                   add_string " of ";
                 end_block();
               pp_tyl (map ParseDatatype.pretypeToType args);
               end_block()))
     fun pp_decl (tyvars,r) (name,Constructors clauselist) =
         (begin_block CONSISTENT 5;
          begin_block CONSISTENT 0;
            if !r then
              (add_string (if !emitOcaml then "type" else "datatype"); r:=false)
            else
              ();
            add_break(1,0); pp_tyvars tyvars; add_string (fix_type name);
          end_block();
          add_break(1,0);
          begin_block CONSISTENT 0;
          pr_list (pp_clause (ref true))
                  (fn () => ())
                  (fn () => add_break(1,0)) clauselist;
          end_block(); end_block())
       | pp_decl (tyvars,_) (name,Record flist) =
           let open ParseDatatype
               val fields = map (I##pretypeToType) flist
           in begin_block CONSISTENT 0;
              add_string (if !emitOcaml then "type" else "datatype");
              add_break(1,0);
              pp_tyvars tyvars;
              add_string(fix_type name^" = ");
              add_string(fix_cons name^" of ");
              pp_tyl (map snd fields);
              end_block()
           end
 in
    begin_block CONSISTENT 0
  ; pr_list (pp_decl (tyvars,ref true))
            (fn () => (add_newline(); add_string "and"))
            add_newline
            decls
  ; end_block()
 end;

(*---------------------------------------------------------------------------*)
(* Get the name of all constants introduced by the definition. Probably      *)
(* won't work in general for constant specifications.                        *)
(*---------------------------------------------------------------------------*)

fun consts_of_def thm =
  let val eqns = strip_conj (snd (strip_forall (concl thm)))
      val allCs = map (fst o strip_comb o lhs o snd o strip_forall) eqns
  in op_mk_set same_const allCs
  end;

fun original_type name ty =
let val l = size name
    val s = if String.sub(name,0) = #" " andalso String.sub(name,l - 1) = #" "
            then String.substring(name,1,l - 2)
            else name
    val d = decls s
            handle Option => raise ERR "original_type"
               ("Cannot find " ^ quote name ^ Hol_pp.type_to_string ty)
    val tm = valOf (List.find (fn t => can (match_type ty) (type_of t)) d)
in
  type_of tm
end;

fun pp_sig strm (s,elems) =
 let open Portable
    val {add_break,add_newline, add_string,
         begin_block,end_block,flush_ppstream,...} = with_ppstream strm
    val ppty = pp_type_as_ML strm
    val pp_datatype = pp_datatype_as_ML strm
    fun pp_eqdatatype b (tyvars,astl) =
     let val tynames = map fst astl
         val tys = map (fn s => (tyvars,s)) tynames
         fun pp_tydec (tyvars,s) =
           (begin_block CONSISTENT 0;
             add_string (if b andalso not (!emitOcaml)
                         then "eqtype " else "type ");
             if null tyvars then add_string s else
             if List.length tyvars = 1
              then (add_string (hd tyvars); add_string(" "^s))
              else (add_string "(";
                    pr_list add_string (fn () => add_string",")
                                       (fn () => ()) tyvars;
                    add_string(") "^s));
            end_block())
     in begin_block CONSISTENT 0;
        pr_list pp_tydec (fn () => ()) add_newline (map (pair tyvars) tynames);
        end_block()
     end
    fun pp_valdec c =
     let val (is_type_cons,_,name,ty) = ConstMapML.apply c
         val ty = if !emitOcaml then original_type name ty else ty
     in begin_block CONSISTENT 3;
        add_string "val ";
        add_string (fix_name ("",is_type_cons,name)); add_break(1,0);
        add_string ": "; ppty ty;
        end_block()
     end
    fun pp_el (iDATATYPE astl) = pp_datatype (repair_type_decls (iDATATYPE astl))
      | pp_el (iEQDATATYPE (tyvarsl,astl)) = pp_eqdatatype true (tyvarsl,astl)
      | pp_el (iABSDATATYPE (tyvarsl,astl)) = pp_eqdatatype false (tyvarsl,astl)
      | pp_el (iDEFN thm) =
            pr_list pp_valdec (fn () => ()) add_newline (consts_of_def thm)
      | pp_el (iMLSIG s) = add_string s
      | pp_el (iDEFN_NOSIG thm) = ()
      | pp_el (iMLSTRUCT s) = ()
      | pp_el (iOPEN slist) = ()
 in
   begin_block CONSISTENT 0;
     add_string ((if !emitOcaml then "module type " else "signature ") ^
                 ML s ^ " =");
     add_newline();
     begin_block CONSISTENT 2;
       add_string "sig"; add_newline();
       begin_block CONSISTENT 0;
         pr_list pp_el (fn () => ()) add_newline
             (filter (fn (iDEFN_NOSIG _) => false
                       | (iOPEN _) => false
                       | (iMLSTRUCT _) => false
                       | otherwise => true) elems);
       end_block();
     end_block();
     add_newline();
     add_string "end"; add_newline();
   end_block();
   flush_ppstream()
 end
 handle e => raise wrap_exn "EmitML" "pp_sig" e;

val MLinfixes =
  String.fields Char.isSpace "* / div mod + - ^ @ <> > < >= <= := o before";

fun pp_struct strm (s,elems,cnames) =
 let open Portable
    val {add_break,add_newline, add_string,
         begin_block,end_block,flush_ppstream,...} = with_ppstream strm
    val openthys = ref []
    fun opens() = !openthys
    val pp_datatype = pp_datatype_as_ML strm
    fun pp_el (iDATATYPE astl) = pp_datatype (repair_type_decls (iDATATYPE astl))
      | pp_el (iEQDATATYPE (tyvarsl,astl)) =
           pp_datatype (repair_type_decls (iEQDATATYPE(tyvarsl,astl)))
      | pp_el (iABSDATATYPE (tyvarsl,astl)) =
           pp_datatype (repair_type_decls (iABSDATATYPE(tyvarsl,astl)))
      | pp_el (iDEFN thm) =
           (if !emitOcaml then pp_defn_as_OCAML else pp_defn_as_ML)
              (s::opens()) strm (concl thm)
      | pp_el (iDEFN_NOSIG thm) = pp_el (iDEFN thm)
      | pp_el (iMLSIG s) = ()
      | pp_el (iMLSTRUCT s) = add_string s
      | pp_el (iOPEN slist) = (openthys := union slist (!openthys);
                              begin_block CONSISTENT 0;
                              pr_list (add_string o curry String.^ "open " o ML)
                                 (fn ()=>()) (fn () => add_newline()) slist;
                              add_newline();
                              end_block())
    val (struct_mod, punct) = if !emitOcaml then
                                ("module ", " : ")
                              else
                                ("structure ", " :> ")
 in
   begin_block CONSISTENT 0;
     add_string (struct_mod ^ ML s ^ punct ^ ML s ^ " =");
     add_newline();
     begin_block CONSISTENT 2;
       add_string "struct"; add_newline();
       begin_block CONSISTENT 0;
       if !emitOcaml then () else
         (begin_block INCONSISTENT 7;
            add_string"nonfix ";
            pr_list add_string (fn()=>()) (fn()=> add_break(1,0))
                    (union cnames MLinfixes);
            add_string ";";
          end_block();
          add_newline());
       add_newline();
       pr_list pp_el (fn () =>()) add_newline
              (filter (fn (iMLSIG _) => false | otherwise => true) elems);
       end_block();
     end_block();
     add_newline();
     add_string"end"; add_newline();
   end_block();
   flush_ppstream()
 end
 handle e => raise wrap_exn "EmitML" "pp_struct" e;


(*---------------------------------------------------------------------------*)
(* Dealing with eqtypes. When a HOL function uses equality on the rhs, the   *)
(* type of the function does not reflect this. However, in ML, eqtypes       *)
(* are used to signal this. The compiler generates code for the equality     *)
(* test in that case. So we need to take a HOL definition and compute an ML  *)
(* type for it, which can include eqtypes. The strategy taken is to search   *)
(* the rhs for any constants whose generic type has eqtype constraints on    *)
(* some type variables. By matching the generic constant against the instance*)
(* we can find if any eqtype variables are bound to polymorphic types. If so,*)
(* the type variables in the polymorphic type get the eqtype attribute.      *)
(*---------------------------------------------------------------------------*)

fun is_eqtyvar ty =
  (case String.explode (dest_vartype ty)
    of #"'" :: #"'" ::rst => true
     | otherwise => false)
   handle HOL_ERR _ => raise ERR "is_eqtyvar" "not a type variable";

fun tyvar_to_eqtyvar ty =
 let val tyname = dest_vartype ty
 in
  case String.explode tyname
   of #"'" :: #"'" :: _ => raise ERR "tyvar_to_eqtyvar" "already an eqtyvar"
    | #"'" :: _ => with_flag (Feedback.emit_WARNING,false)
                     mk_vartype ("'"^tyname)
    | otherwise => raise ERR "tyvar_to_eqtyvar" "unexpected syntax"
 end;

fun const_eqtyvars genty c2 =
 let val bindings = match_type genty (type_of c2)
     val bindings' = Lib.filter (is_eqtyvar o #redex) bindings
     val bindings'' = Lib.filter (polymorphic o #residue) bindings'
 in
    Type.type_varsl (map #residue bindings'')
  end;

fun generic_const thy name = Term.prim_mk_const{Thy=thy,Name=name};

(*---------------------------------------------------------------------------*)
(* Gets possibly eq-style type from const map.                               *)
(*---------------------------------------------------------------------------*)

fun generic_type c =
   #4 (ConstMapML.apply c) handle HOL_ERR _ => type_of c;

fun term_eqtyvars tm =
 case dest_term tm
  of CONST _     => const_eqtyvars (generic_type tm) tm
   | VAR _       => []
   | COMB(t1,t2) => union (term_eqtyvars t1) (term_eqtyvars t2)
   | LAMB(_,tm)  => term_eqtyvars tm;

(*---------------------------------------------------------------------------*)
(* Translate the type of a defined constant to reflect any uses of equality  *)
(* in the body of the definition.                                            *)
(*---------------------------------------------------------------------------*)

fun munge_def_type def =
 let val (L,R) = unzip (map (dest_eq o snd o strip_forall)
                            (strip_conj (snd (strip_forall (concl def)))))
     val clist = op_mk_set same_const (map (fst o strip_comb) L)
     val tainted = U (map term_eqtyvars R)
     val theta = map (fn tyv => tyv |-> tyvar_to_eqtyvar tyv) tainted
 in
   map (inst theta) clist
 end
 handle e => raise wrap_exn "EmitML" "munge_def_type" e;

(*---------------------------------------------------------------------------*)
(* Get the newly introduced constants out of a list of function definitions  *)
(* and datatype definitions. We have to be aware that a constant may have    *)
(* been defined in an ancestor theory.                                       *)
(*---------------------------------------------------------------------------*)

fun add (is_constr, s) c =
    case ConstMapML.exact_peek c of
      NONE => let
        val {Name,Thy,Ty} = dest_thy_const c
      in
        ConstMapML.prim_insert(c,(is_constr,s,Name,Ty))
      end
    | SOME _ => ()

fun install_consts _ [] = []
  | install_consts s (iDEFN_NOSIG thm::rst) = install_consts s (iDEFN thm::rst)
  | install_consts s (iDEFN thm::rst) =
       let val clist0 = munge_def_type thm
           val clist =
               (* IN is only allowed to be defined in the setML module/structure;
                  due to the special-case of MEM, listML may appear to define it too
                *)
               if s <> "set" then filter (not o same_const IN_tm) clist0
               else clist0
           val _ = List.app (add (false, s)) clist
       in map (pair false) clist @ install_consts s rst
       end
  | install_consts s (iDATATYPE ty::rst) =
      let val consts = U (map (Term.decls o fst) (constructors ty))
          val _ = List.app (add (true, s)) consts
      in map (pair true) consts @ install_consts s rst
      end
  | install_consts s (iEQDATATYPE (tyvars,ty)::rst) =
      let val consts = U (map (Term.decls o fst) (constructors ty))
          val _ = List.app (add (true, s)) consts
      in map (pair true) consts @ install_consts s rst
      end
  | install_consts s (iABSDATATYPE (tyvars,ty)::rst) =
     install_consts s (iEQDATATYPE (tyvars,ty)::rst)
  | install_consts s (other::rst) = install_consts s rst;


(*---------------------------------------------------------------------------*)
(* Set up a ppstream to a file. Return the ppstream and the outstream. The   *)
(* latter has to be closed at the end of prettyprinting to the file.         *)
(*---------------------------------------------------------------------------*)

fun mk_file_ppstream file =
  let open Portable
      val ostrm = TextIO.openOut file
  in (ostrm,
      mk_ppstream{consumer = fn s => TextIO.output(ostrm,s),
                  linewidth = 72,
                  flush = fn () => TextIO.flushOut ostrm})
  end;

(*---------------------------------------------------------------------------*)
(* Append code to the theory file that will load the const map with the      *)
(* definitions and datatype constructors exported as ML.                     *)
(*---------------------------------------------------------------------------*)

fun emit_adjoin_call thy (consts,pcs) = let
  fun extern_pc (c,a) =
      let val {Thy=thy,Name=n,...} = dest_thy_const c
          val n' = mlquote n
          val thy' = mlquote thy
      in ("(prim_mk_const{Name="^n'^",Thy="^thy'^"},"^Int.toString a^")")
     end
  fun safetyprint ty = String.toString
                        (trace ("Unicode",0)
                           (HOLPP.pp_to_string 10000
                              (type_pp.pp_type (fst Parse.min_grammars)
                                 PPBackEnd.raw_terminal)) ty)

  fun pr3 pps ({Name,Thy,Ty}, (b,s2,ty)) = let
    open PP
    val S = add_string pps
    fun BB() = begin_block pps INCONSISTENT 0
    fun EB() = end_block pps
    fun brk n = add_break pps (1,n)
    fun ppty ty = (BB(); S "typ"; brk 0; S "\""; S (safetyprint Ty); S "\"";
                   EB())
  in
    S "("; BB();
     S "{"; BB();
       BB(); S "Name ="; brk 0; S (mlquote Name ^ ","); EB(); brk 0;
       BB(); S "Thy ="; brk 0; S (mlquote Thy ^","); EB(); brk 0;
       BB(); S "Ty ="; brk 2; ppty Ty; EB();
     EB(); S "},"; brk 0;
     S "("; BB();
       S (Bool.toString b ^ ","); brk 0;
       S (Lib.mlquote s2 ^ ","); brk 0;
       ppty ty;
     EB(); S ")";
   EB(); S ")"
  end
 in
  Theory.adjoin_to_theory
  {sig_ps = NONE,
   struct_ps = SOME (fn ppstrm =>
    let open PP
        val S = add_string ppstrm
        fun NL() = add_newline ppstrm
        val BR = add_break ppstrm
        fun getdata c = let
          val (b,pfx,s,ty) = ConstMapML.apply c
        in
          (b,s,ty)
        end
    in
     S "val _ = "; NL();
     S "   let open Parse"; NL();
     S "       fun doit (r,(b,s,ty)) = "; NL();
     S "         let val c = Term.mk_thy_const r"; NL();
     S ("         in ConstMapML.prim_insert(c,(b,"^Lib.quote thy^",s,ty))");
     NL();
     S "         end"; NL();
     S "       fun typ s = Feedback.trace (\"Vartype Format Complaint\", 0)\n\
       \                      (#1 (parse_from_grammars min_grammars))\n\
       \                      [QUOTE (\":\"^s)]"; NL();
     S "   in"; NL();
     S "     List.app doit ["; NL();
     S "       ";
     begin_block ppstrm INCONSISTENT 0;
     Portable.pr_list (pr3 ppstrm) (fn () => S",") (fn () => BR(1,0))
                      (map (fn (_, c) => (dest_thy_const c, getdata c))
                           consts);
     end_block ppstrm; NL();
     S "     ]"; NL();
     S "   end"; NL(); NL();
     if null pcs then ()
     else
     (S "val _ = List.app EmitML.new_pseudo_constr"; NL();
      S "                 [";
      begin_block ppstrm INCONSISTENT 0;
      Portable.pr_list S (fn () => S",")
                         (fn () => BR(1,0))
                         (map extern_pc pcs);
      end_block ppstrm;
     S"]";
     NL(); NL())
    end)}
   handle e => raise ERR "emit_adjoin_call" ""
 end;

(*---------------------------------------------------------------------------*)
(* Write the ML out to a signature and structure file. We first run over the *)
(* definitions and lift out the newly defined constants. These get inserted  *)
(* into the "const map", which is accessed when prettyprinting the           *)
(* definitions. We also have to detect eqtypes and ensure that the const map *)
(* is properly updated when the theory is loaded.                            *)
(*---------------------------------------------------------------------------*)

fun emit_xML (Ocaml,sigSuffix,structSuffix) p (s,elems_0) =
 let val _ = emitOcaml := Ocaml
     val (pcs,elems) = internalize elems_0  (* pcs = pseudo-constrs *)
     val path = if p="" then FileSys.getDir() else p
     val pathPrefix = Path.concat(path, capitalize s)
     val sigfile = pathPrefix^ sigSuffix
     val structfile = pathPrefix^ structSuffix
     fun trydelete s = OS.FileSys.remove s handle OS.SysErr _ => ()
     fun cleanFiles() = (trydelete sigfile; trydelete structfile)
 in
   let val (sigStrm,sigPPstrm) = mk_file_ppstream sigfile
       val (structStrm,structPPstrm) = mk_file_ppstream structfile
       val consts = install_consts s elems
   in
   (pp_sig sigPPstrm (s,elems);
    pp_struct structPPstrm (s,elems,map (fst o dest_const o snd) consts);
    TextIO.closeOut sigStrm;
    TextIO.closeOut structStrm;
    HOL_MESG ("emitML: " ^ s ^ "{" ^ sigSuffix ^ "," ^ structSuffix ^ "}\n\
              \ written to directory "^path);
    emit_adjoin_call s (consts,pcs)
   )
   handle e => (List.app TextIO.closeOut [sigStrm, structStrm];
                cleanFiles();
                raise wrap_exn "EmitML" "emitML" e)
   end handle Io _ =>
              raise mk_HOL_ERR "EmitML" "emitML"
                    ("I/O error prevented exporting files to "^Lib.quote path)
 end

val emit_xML =
    (fn info => fn p => fn stuff =>
                           Feedback.trace ("Unicode", 0)
                                          (emit_xML info p)
                                          stuff)

val emitML = emit_xML (false,!sigSuffix,!structSuffix);

val emitCAML = emit_xML (true,!sigCamlSuffix,!structCamlSuffix);

fun eSML d l = with_flag (type_pp.pp_array_types, false)
                 (emitML (!Globals.emitMLDir)) (d, l);
fun eCAML d l = with_flag (type_pp.pp_array_types, false)
                 (emitCAML (!Globals.emitCAMLDir)) (d, l);

fun MLSIGSTRUCT ll =
  foldr (fn (x,l) => MLSIG x :: MLSTRUCT x :: l) [] (ll @ [""]);

end (* struct *)
