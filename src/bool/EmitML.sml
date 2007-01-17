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
(* as theories load. The former operation requires an invocation of the ML   *)
(* compiler. In MoscowML, there is not a way to do this in the batch system  *)
(* which means that some deviousness is, unfortunately, required.            *)
(*                                                                           *)
(*===========================================================================*)

structure EmitML :> EmitML =
struct

open HolKernel boolSyntax Abbrev;

val ERR = mk_HOL_ERR "EmitML";
val WARN = HOL_WARNING "EmitML";

(*---------------------------------------------------------------------------*)
(* Forward references, to be patched up in the appropriate places.           *)
(*---------------------------------------------------------------------------*)

val is_num_literal_hook    = ref (K false)
val is_int_literal_hook    = ref (K false)
val is_list_hook           = ref (K false)
val is_comma_hook          = ref (K false)
val is_pair_hook           = ref (K false)
val is_let_hook            = ref (K false)
val is_pabs_hook           = ref (K false)
val is_one_hook            = ref (K false)
val is_fail_hook           = ref (K false)

val dest_num_literal_hook  = ref (fn _ => raise ERR "dest_num_literal" "undefined")
val dest_int_literal_hook  = ref (fn _ => raise ERR "dest_int_literal" "undefined")
val dest_cons_hook = ref (fn _ => raise ERR "dest_cons" "undefined")
val dest_list_hook = ref (fn _ => raise ERR "dest_list" "undefined")
val dest_pair_hook = ref (fn _ => raise ERR "dest_pair" "undefined")
val dest_pabs_hook = ref (fn _ => raise ERR "dest_pabs" "undefined")
val dest_fail_hook = ref (fn _ => raise ERR "dest_fail" "undefined")
val strip_let_hook = ref (fn _ => raise ERR "strip_let" "undefined")
val list_mk_prod_hook = ref (fn [x] => x
                              | _ => raise ERR "list_mk_prod" "undefined")
val list_mk_pair_hook = ref (fn _ => raise ERR "list_mk_pair" "undefined")
val list_mk_pabs_hook = ref (fn _ => raise ERR "list_mk_pabs" "undefined")

fun strip_cons M =
 case total (!dest_cons_hook) M
  of SOME (h,t) => h::strip_cons t
   | NONE => [M];

fun is_cons tm = Lib.can (!dest_cons_hook) tm;

fun is_fn_app tm = is_comb tm andalso not(!is_pair_hook tm)

fun is_infix_app tm = is_conj tm orelse is_disj tm orelse is_eq tm ;

fun is_pair_type ty =
 case total dest_thy_type ty
  of SOME{Tyop="prod",Thy="pair",...} => true
   | otherwise => false;

local val a = mk_var("a",bool)
      val b = mk_var("b",bool)
in
val andalso_tm = list_mk_abs([a,b],mk_conj(a,b))
val orelse_tm = list_mk_abs([a,b],mk_disj(a,b))
end

fun partitions P [] = []
  | partitions P (h::t) =
     case partition (P h) t
      of (L1,L2) => (h::L1) :: partitions P L2;

fun triml s =
  if String.sub(s,0) = #" "
  then String.substring(s,1,String.size(s)-1)
  else s;

fun full_name openthys (s1,s2,_) =
    if mem s1 openthys then s2 else
    if s1="" then s2 else s1^"ML."^triml s2;

fun const_map openthys c = full_name openthys (ConstMapML.apply c);

val COMMA_PREC = 50;
val CONS_PREC  = 450;

fun prec_of c =
  if same_const c boolSyntax.equality then 100 else
  if same_const c boolSyntax.disjunction then 300 else
  if same_const c boolSyntax.conjunction then 400 else
  if !is_comma_hook c then COMMA_PREC else 0;

val minprec = ~1;
val maxprec = 9999;

(*---------------------------------------------------------------------------*)
(* Version of dest_string that doesn't care if characters look like          *)
(*                                                                           *)
(*   CHAR (NUMERAL n)    or    CHAR n                                        *)
(*---------------------------------------------------------------------------*)

val is_string_literal = Lib.can Literal.relaxed_dest_string_lit;

datatype side = LEFT | RIGHT;

fun pick_name slist n (s1,s2) = if mem n slist then s1 else s2;

(*---------------------------------------------------------------------------
 * variants makes variables that are guaranteed not to be in avoid and
 * furthermore, are guaranteed not to be equal to each other. The names of
 * the variables will start with "v" and end in a number.
 *---------------------------------------------------------------------------*)

fun vars_of_types alist =
   map (fn (i,ty) => mk_var("v"^Int.toString i,ty))
       (Lib.enumerate 0 alist);

(*---------------------------------------------------------------------------*)
(* Convert a constructor application (C t1 ... tn) to C'(t1,...,tn) where    *)
(* C' is a variable with the same name as C. Uses mk_thm!                    *)
(*---------------------------------------------------------------------------*)

val pseudo_constructors = ref [] : thm list ref;

(*---------------------------------------------------------------------------*)
(*  The following reference cell gets set in pred_setTheory                  *)
(*---------------------------------------------------------------------------*)

val reshape_thm_hook = ref Lib.I : (thm -> thm) ref;

local val emit_tag = "EmitML"
   fun nstrip_fun 0 ty = ([],ty)
     | nstrip_fun n ty =
         let val (d,r) = dom_rng ty
             val (f,b) = nstrip_fun (n-1) r
         in (d::f,b)
         end
in
fun curried_const_equiv_tupled_var (c,a) =
 let val (argtys,target) = nstrip_fun a (type_of c)
     val args = vars_of_types argtys
     val pvar = mk_var(fst(dest_const c),!list_mk_prod_hook argtys --> target)
     val new = !list_mk_pabs_hook(args,mk_comb(pvar,!list_mk_pair_hook args))
     val thm = mk_oracle_thm emit_tag ([],mk_eq(c,new))
 in
    pseudo_constructors := thm :: !pseudo_constructors;
    thm
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
  fun pp i tm =
     if is_var tm then pp_var tm else
     if is_cond tm then pp_cond i tm else
     if is_arb tm then pp_arb i else
     if !is_num_literal_hook tm then pp_num_literal i tm else
     if !is_int_literal_hook tm then pp_int_literal tm else
     if is_string_literal tm then pp_string tm else
     if !is_list_hook tm then pp_list tm else
     if is_cons tm then pp_cons i tm else
     if is_infix_app tm then pp_binop i tm else
     if !is_pair_hook tm then pp_pair i tm else
     if !is_let_hook tm then pp_lets i tm else
     if !is_pabs_hook tm then pp_abs i tm else
     if !is_fail_hook tm then pp_fail i tm else
     if !is_one_hook tm  then pp_one tm else
     if TypeBase.is_record tm then pp_record i (TypeBase.dest_record tm) else
     if TypeBase.is_case tm then pp_case i (TypeBase.strip_case tm) else
     if is_the_value tm then pp_itself tm else
     if is_const tm then pp_const i tm else
     if is_comb tm then pp_comb i tm
     else raise ERR "term_to_ML"
                    ("Unknown syntax with term: "^Parse.term_to_string tm)
  and pp_cond i tm =
         let val (b,a1,a2) = dest_cond tm
         in begin_block CONSISTENT 0;
            lparen i 70;
            begin_block INCONSISTENT 2;
            add_string"if ";
            begin_block CONSISTENT 0; pp 70 b; end_block();
            add_break(1,0);
            add_string"then ";
            begin_block CONSISTENT 0; pp 70 a1; end_block();
            add_break(1,0);
            add_string"else ";
            begin_block CONSISTENT 0; pp minprec a2; end_block();
            end_block();
            rparen i 70;
            end_block()
         end
  and pp_num_literal i tm =
      (*------------------------------------------------------------*)
      (* Numeric literals can be built from strings or constructors *)
      (*------------------------------------------------------------*)
      let val s = Arbnum.toString(!dest_num_literal_hook tm)
      in if side = RIGHT (* use fromString *)
         then (if s="0" then add_string
                   (pick_name openthys "num" ("ZERO","numML.ZERO")) else
               if s="1" then add_string
                   (pick_name openthys "num" ("ONE","numML.ONE")) else
               if s="2" then add_string
                   (pick_name openthys "num" ("TWO","numML.TWO")) else
               (begin_block CONSISTENT 0
                ; add_string"("; add_break(0,0)
                ; add_string (pick_name openthys "num"
                             ("fromString","numML.fromString"))
                ; add_break(0,0)
                ; add_string (mlquote s)
                ; add_break(0,0)
                ; add_string")"
                ; end_block()))
         else (* side = LEFT, so use constructors *)
          if s = "0"
           then add_string (pick_name openthys "num" ("ZERO","numML.ZERO"))
           else pp_comb i tm
      end
  and pp_int_literal tm =
         let val s = Arbint.toString(!dest_int_literal_hook tm)
         in begin_block CONSISTENT 0
          ; add_string"("; add_break(0,0)
          ; add_string "intML.fromString"
          ; add_break(0,0)
          ; add_string (mlquote s)
          ; add_break(0,0)
          ; add_string")"
          ; end_block()
         end
  and pp_string tm = add_string (mlquote (Literal.relaxed_dest_string_lit tm))
  and pp_list tm =
       let val els = !dest_list_hook tm
       in begin_block CONSISTENT 0
        ; add_string "["
        ; begin_block INCONSISTENT 0
        ; pr_list (pp minprec)
                  (fn () => add_string",")
                  (fn () => add_break(0,0)) els
        ; end_block()
        ; add_string "]"
        ; end_block()
       end
  and pp_binop i tm =
      let val (c,[t1,t2]) = strip_comb tm
          val j = prec_of c
      in begin_block CONSISTENT 0
        ; lparen i j
        ; begin_block CONSISTENT 0
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
  and pp_pair i tm =
      let val (t1,t2) = !dest_pair_hook tm
          val j = COMMA_PREC
      in begin_block CONSISTENT 0
        ; lparen maxprec i
        ; begin_block CONSISTENT 0
        ; pp (j+1) t1
        ; add_string ","
        ; pp j t2
        ; end_block()
        ; rparen maxprec i
        ; end_block()
      end
  and pp_lets i tm = (* a sequence of lets *)
      let val (blists,body) = !strip_let_hook tm
          fun keyword1 (l,r) = ((if is_fn_app l then "fun" else "val"),(l,r))
          fun keyword [] = raise ERR "term_to_ML" "pp_lets"
            | keyword l = map keyword1 l
          val blist' = flatten (map keyword blists)
          fun pp_binding (k,(l,r)) =
               (begin_block INCONSISTENT 4;
                add_string k; add_break(1,0);
                pp minprec l; add_break(1,0);
                add_string "="; add_break(1,0);
                begin_block CONSISTENT 0;
                pp minprec r; end_block();
                end_block())
      in  begin_block CONSISTENT 0
        ; lparen i 5000
        ; begin_block CONSISTENT 0
        ; add_string "let "
        ; begin_block CONSISTENT 0
        ;    pr_list pp_binding (fn()=>()) add_newline blist'
        ;    end_block()
        ; add_break(1,0)
        ; add_string"in"
        ; add_break(1,3)
        ; pp minprec body
        ; add_break(1,0)
        ; add_string"end"
        ; end_block()
        ; rparen i 5000
        ; end_block()
      end
  and pp_case i (a,cases) =
      ( begin_block CONSISTENT 1
        ; lparen i 7  (* from HOL term grammar *)
        ; begin_block INCONSISTENT 2
        ; add_string "case"
        ; add_break(1,0)
        ; pp minprec a
        ; end_block()
        ; add_break(1,0)
        ; begin_block CONSISTENT 1
        ; add_string "of "
        ; pp_case_clause (hd cases)
        ; add_break(1,0)
        ; pr_list (fn cl => (add_string "| "; pp_case_clause cl))
                  (fn () => ())
                  (fn () => add_break(1,0)) (tl cases)
        ; end_block()
        ; rparen i 7
        ; end_block())
  and pp_case_clause (pat,rhs) =
        (begin_block CONSISTENT 3
         ; pp minprec pat
         ; add_string " =>"
         ; add_break (1,0)
         ; pp 7 rhs
         ; end_block()
        )
  and pp_record i (ty,flds) =
       pp_open_comb i (hd(TypeBase.constructors_of ty), map snd flds)
  and pp_fail i tm =
       let val (f,s,args) = !dest_fail_hook tm
           val fname = fst(dest_const f)
       in begin_block CONSISTENT 3
         ; add_string "raise Fail"
         ; add_break (1,0)
         ; add_string (Lib.quote (fname^": "^s))
         ; end_block()
       end
  and pp_arb i =
      (lparen i maxprec
       ; begin_block CONSISTENT 3
       ; add_string "raise Fail \"\""
       ; end_block()
       ; rparen i maxprec)
  and pp_itself tm =
    let fun abbrev_to_string t = String.extract(Hol_pp.type_to_string t,1,NONE)
        fun pp_itself_type typ =
      if is_vartype typ then
        add_string (String.extract(dest_vartype typ, 1, NONE))
      else case (dest_type typ) of
        ("bit0", els) =>
           add_string ("(Tyop (\"" ^ abbrev_to_string typ ^ "\", []))")
      | ("bit1", els) =>
           add_string ("(Tyop (\"" ^ abbrev_to_string typ ^ "\", []))")
      | (tyop, els) =>
           (begin_block Portable.CONSISTENT 0
          ; add_string ("(Tyop (\"" ^ tyop ^ "\", [")
          ; begin_block Portable.CONSISTENT 0
          ; Portable.pr_list pp_itself_type
                  (fn () => add_string",")
                  (fn () => add_break(0,0)) els
          ; end_block()
          ; add_string "]))"
          ; end_block())
    in
      (pp_itself_type o hd o snd o dest_type o type_of) tm
    end
  and pp_var tm = add_string(fst(dest_var tm))
  and pp_const i tm =
      if same_const tm boolSyntax.conjunction
         then pp_abs i andalso_tm else
       if same_const tm boolSyntax.disjunction
         then pp_abs i orelse_tm
       else add_string (const_map tm)
  and pp_one tm = add_string "()"
  and pp_nil tm = add_string "[]"
  and pp_open_comb i (f,args) =
       let
       in begin_block CONSISTENT 0
        ; lparen i maxprec
        ; if TypeBase.is_constructor f
            then
              (pp maxprec f; add_string "(";
               pr_list (pp minprec)
                       (fn () => add_string ",")
                       (fn () => add_break(0,0)) args;
               add_string ")")
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
       let val (vstruct,body) = !dest_pabs_hook tm
       in lparen i 5000
        ; add_string "fn"
        ; add_break (1,0)
        ; pp 50 vstruct
        ; add_break (1,0)
        ; add_string "=>"
        ; add_break (1,0)
        ; pp minprec body
        ; rparen i 5000
       end

 in fn i => fn M =>
    (begin_block INCONSISTENT 0 ; pp i M ; end_block ())
 end;

fun pp_term_as_ML openthys side ppstrm M =
    term_to_ML openthys side ppstrm minprec M;

fun same_fn eq1 eq2 = (fst(strip_comb eq1) = fst(strip_comb eq2));

(*---------------------------------------------------------------------------*)
(* Print a function definition as ML, i.e., fun f ... = ...                  *)
(*---------------------------------------------------------------------------*)

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
                  (fn () => (add_newline(); add_newline())) clauses'
        ; end_block()
       end
 in
    pp
 end;


(*---------------------------------------------------------------------------*)
(* Now print datatype declarations in ML. First tweak the existing type      *)
(* prettyprinter so it generates syntactically correct ML types              *)
(*---------------------------------------------------------------------------*)

local open type_grammar HOLgrammars
in
fun adjust_tygram tygram =
 let val g0 = List.foldl (fn (s,g) => remove_binary_tyop g s)
                         tygram
                         ["+", "#", "|->", "**"]
 in
    new_binary_tyop g0 {precedence = 70, infix_form = SOME "*",
                        opname = "prod", associativity = NONASSOC}
 end
end;

fun prim_pp_type_as_ML tygram tmgram ppstrm ty =
 let val (pp_type,_) = Parse.print_from_grammars
                              (adjust_tygram tygram, tmgram)
 in pp_type ppstrm ty
 end;

fun pp_type_as_ML ppstrm ty =
   prim_pp_type_as_ML (Parse.type_grammar()) (Parse.term_grammar())
                      ppstrm ty ;

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
(* Internal version (nearly identical, except that datatype declarations     *)
(* have been parsed) and some standard definitions from datatypes (e.g. size *)
(* functions) and record types (accessor and field update functions) are     *)
(* automatically added.                                                      *)
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
            val size_def = [snd (valOf(size_of tyinfo))] handle _ => []
            val updates_def = updates_of tyinfo handle HOL_ERR _ => []
            val access_def = accessors_of tyinfo handle HOL_ERR _ => []
        in
          map (iDEFN o !reshape_thm_hook)
              (size_def @ updates_def @ access_def)
        end
 end;

(*---------------------------------------------------------------------------*)
(* Map from external presentation to internal                                *)
(*---------------------------------------------------------------------------*)

fun elemi (DEFN th) (cs,il) = (cs,iDEFN (!reshape_thm_hook th) :: il)
  | elemi (DEFN_NOSIG th) (cs,il) = (cs,iDEFN_NOSIG (!reshape_thm_hook th)::il)
  | elemi (DATATYPE q) (cs,il) =
       let val tyAST = ParseDatatype.parse q
           val defs = datatype_silent_defs tyAST
       in (cs, defs @ (iDATATYPE tyAST :: il))
       end
  | elemi (EQDATATYPE(sl,q)) (cs,il) =
       let val tyAST = ParseDatatype.parse q
           val defs = datatype_silent_defs tyAST
       in (cs,defs @ (iEQDATATYPE(sl,tyAST) :: il))
       end
  | elemi (ABSDATATYPE(sl,q)) (cs,il) = (* build rewrites for pseudo constrs *)
     let open ParseDatatype
         val tyAST = parse q
         val pconstrs = constrl tyAST
         val constr_names = flatten(map (map fst o snd) pconstrs)
         val constr_arities = flatten(map (map (length o snd) o snd) pconstrs)
         val constrs = map (hd o Term.decls) constr_names
         val constrs' = zip constrs constr_arities
         fun is_multi (_,n) = n >= 2
         val mconstrs = filter is_multi constrs'
         val _ = List.map curried_const_equiv_tupled_var mconstrs
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

(*---------------------------------------------------------------------------*)
(* Perhaps naive in light of the recent stuff of MN200 to eliminate flab     *)
(* from big record types?                                                    *)
(*---------------------------------------------------------------------------*)

local open ParseDatatype
in
fun replace f (v as dVartype _) = v
  | replace f (aq as dAQ _)     = aq
  | replace f (dTyop{Tyop,Thy,Args}) =
      f Tyop handle _ => dTyop{Tyop=Tyop,Thy=Thy,Args=map (replace f) Args}

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
         of (con,[]) => add_string con
          | (con,args) =>
              (begin_block INCONSISTENT 0;
                 begin_block CONSISTENT 0; add_string con; add_string " of ";
                 end_block();
               pp_tyl (map ParseDatatype.pretypeToType args);
               end_block()))
     fun pp_decl (tyvars,r) (name,Constructors clauselist) =
         (begin_block CONSISTENT 5;
          begin_block CONSISTENT 0;
            if !r then (add_string "datatype"; r:=false) else ();
            add_break(1,0); pp_tyvars tyvars; add_string name;
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
              add_string "datatype";
              add_break(1,0);
              pp_tyvars tyvars;
              add_string(name^" = ");
              add_string(name^" of ");
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

fun ML s = s^"ML";

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
             add_string (if b then "eqtype " else "type ");
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
     let val (_,name,ty) = ConstMapML.apply c
     in begin_block CONSISTENT 3;
        add_string "val ";
        add_string name; add_break(1,0); add_string ": "; ppty ty;
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
   add_string ("signature "^ML s^" = "); add_newline();
   begin_block CONSISTENT 2;
   add_string"sig"; add_newline();
   begin_block CONSISTENT 0;
   pr_list pp_el (fn () => ()) add_newline
       (filter (fn (iDEFN_NOSIG _) => false
                 | (iOPEN _) => false
                 | (iMLSTRUCT _) => false
                 | otherwise => true) elems);
   end_block(); end_block();
   add_newline();
   add_string"end"; add_newline();
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
      | pp_el (iDEFN thm) = pp_defn_as_ML (s::opens()) strm (concl thm)
      | pp_el (iDEFN_NOSIG thm) = pp_el (iDEFN thm)
      | pp_el (iMLSIG s) = ()
      | pp_el (iMLSTRUCT s) = add_string s
      | pp_el (iOPEN slist) = (openthys := union slist (!openthys);
                              begin_block CONSISTENT 0;
                              add_string ("open ");
                              begin_block INCONSISTENT 6;
                              pr_list (add_string o ML)
                                 (fn ()=>()) (fn () => add_break(1,0)) slist;
                              add_string ";" ;
                              end_block();end_block())
 in
   begin_block CONSISTENT 0;
   add_string ("structure "^ML s^" :> "^ML s^" ="); add_newline();
   begin_block CONSISTENT 2;
   add_string"struct"; add_newline();
   begin_block CONSISTENT 0;
   begin_block INCONSISTENT 7;
      add_string"nonfix ";
      pr_list add_string (fn()=>()) (fn()=> add_break(1,0))
              (union cnames MLinfixes);
      add_string ";";
     end_block();
   add_newline(); add_newline();
   pr_list pp_el (fn () =>()) add_newline
          (filter (fn (iMLSIG _) => false | otherwise => true) elems);
   end_block(); end_block();
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
    | #"'" :: _ => mk_vartype ("'"^tyname)
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
   #3 (ConstMapML.apply c) handle HOL_ERR _ => type_of c;

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

fun add s c =
   let val {Name,Thy,Ty} = dest_thy_const c
   in ConstMapML.prim_insert(c,(s,Name,Ty))
   end;

fun install_consts _ [] = []
  | install_consts s (iDEFN_NOSIG thm::rst) = install_consts s (iDEFN thm::rst)
  | install_consts s (iDEFN thm::rst) =
       let val clist = munge_def_type thm
           val _ = List.app (add s) clist
       in clist @ install_consts s rst
       end
  | install_consts s (iDATATYPE ty::rst) =
      let val consts = U (map (Term.decls o fst) (constructors ty))
          val _ = List.app (add s) consts
      in consts @ install_consts s rst
      end
  | install_consts s (iEQDATATYPE (tyvars,ty)::rst) =
      let val consts = U (map (Term.decls o fst) (constructors ty))
          val _ = List.app (add s) consts
      in consts @ install_consts s rst
      end
  | install_consts s (iABSDATATYPE (tyvars,ty)::rst) =
     install_consts s (iEQDATATYPE (tyvars,ty)::rst)
  | install_consts s (other::rst) = install_consts s rst


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

fun emit_adjoin_call thy (consts,pcs) =
 let fun eqtyvars c = map dest_vartype(gather is_eqtyvar(type_vars_in_term c))
     fun name_thy c = let val {Name,Thy,...} = dest_thy_const c in (Name,Thy) end
     val sclist = map (fn c => (eqtyvars c,name_thy c)) consts
     fun listify slist = "["^String.concat (commafy slist)^"]"
     fun paren2 (a,b) = "("^a^","^b^")"
     fun paren3 (a,(b,c)) = "("^listify a^","^b^","^c^")"
     fun extern_pc (c,a) =
       let val (n,thy) = name_thy c
           val n' = mlquote n
           val thy' = mlquote thy
       in ("(prim_mk_const{Name="^n'^",Thy="^thy'^"},"^Int.toString a^")")
       end
 in
  Theory.adjoin_to_theory
  {sig_ps = NONE,
   struct_ps = SOME (fn ppstrm =>
    let open PP
        val S = add_string ppstrm
        fun NL() = add_newline ppstrm
        val BR = add_break ppstrm
    in
     S "val _ = "; NL();
     S "   let fun dconst thy c = "; NL();
     S "         let val {Name,Ty,...} = Term.dest_thy_const c"; NL();
     S "         in (c,(thy,Name,Ty))"; NL();
     S "         end"; NL();
     S "       val clist = map ConstMapML.iconst"; NL();
     S"         [";
     begin_block ppstrm INCONSISTENT 0;
     Portable.pr_list S (fn () => S",")
                        (fn () => BR(1,0))
          (map (paren3 o (map Lib.quote##Lib.mlquote##Lib.mlquote)) sclist);
     end_block ppstrm;
     S"]"; NL();
     S "   in "; NL();
     S ("     List.app ConstMapML.prim_insert (map (dconst "^Lib.quote thy^") clist)"); NL();
     S "   end"; NL(); NL();
     if null pcs then ()
     else
     (S "val _ = List.map EmitML.curried_const_equiv_tupled_var"; NL();
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

val sigSuffix = ref "ML.sig";
val structSuffix = ref "ML.sml";

fun emitML p (s,elems_0) =
 let val (pcs,elems) = internalize elems_0  (* pcs = pseudo-constrs *)
     val path = if p="" then FileSys.getDir() else p
     val pathPrefix = Path.concat(path,s)
     val sigfile = pathPrefix^ !sigSuffix
     val structfile = pathPrefix^ !structSuffix
 in
   let val (sigStrm,sigPPstrm) = mk_file_ppstream sigfile
       val (structStrm,structPPstrm) = mk_file_ppstream structfile
       val consts = install_consts s elems
   in
   (pp_sig sigPPstrm (s,elems);
    pp_struct structPPstrm (s,elems,map (fst o dest_const) consts);
    TextIO.closeOut sigStrm;
    TextIO.closeOut structStrm;
    HOL_MESG ("emitML: wrote files "^s^ !sigSuffix ^" and \n\
     \                                   "^s^ !structSuffix^" \n\
              \ in directory "^path);
    emit_adjoin_call s (consts,pcs)
   )
   handle e => (List.app TextIO.closeOut [sigStrm, structStrm];
                raise wrap_exn "EmitML" "emitML" e)
   end handle Io _ =>
             HOL_WARNING "EmitML" "emitML"
              ("I/O error prevented exporting files to "^Lib.quote path)
           | e => HOL_WARNING "EmitML" "emitML"
                     (exn_to_string e
                        ^" prevents writing ML files to "
                        ^Lib.quote path)
 end

end (* struct *)
