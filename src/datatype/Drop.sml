(*===========================================================================*)
(* Drop: mapping HOL expressions to ML. The basic HOL theory hierarchy has a *)
(* loose analogue in the hierarchy of basic ML structures. Thus we have      *)
(* something like                                                            *)
(*                                                                           *)
(*    HOL Theory         ML Structure                                        *)
(*    ----------         ------------                                        *)
(*    boolTheory            Bool                                             *)
(*    numTheory             Arbnum                                           *)
(*    intTheory             Arbint                                           *)
(*    optionTheory          Option                                           *)
(*    listTheory            List                                             *)
(*    stringTheory          Char, String                                     *)
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
(* mapping HOL expressions into syntactically acceptable ML expressions and  *)
(* installing those definitions in ML. The former operation is "just"        *)
(* prettyprinting, where the prettyprinter uses a table mapping HOL types    *)
(* and constants to their ML counterparts. This table needs to be extensible *)
(* as theories load. The latter operation requires an invocation of the ML   *)
(* compiler. In MoscowML, there is not a way to do this in the batch system  *)
(* which means that some deviousness is unfortunately required.              *)
(*                                                                           *)
(*===========================================================================*)

structure Drop :> Drop = 
struct

open HolKernel boolLib pairML;

val ERR = mk_HOL_ERR "Drop";

fun partitions P [] = []
  | partitions P (h::t) =
     case partition (P h) t 
      of (L1,L2) => (h::L1) :: partitions P L2;

fun full_name("",s2) = s2
  | full_name(s1,s2) = s1^"."^s2;

fun const_map c = full_name (ConstMapML.apply c);

fun prec_of c =
  if same_const c boolSyntax.equality then 100 else
  if same_const c boolSyntax.disjunction then 300 else
  if same_const c boolSyntax.conjunction then 400 else
  if same_const c pairSyntax.comma_tm then 50 else  0;

val minprec = ~1;
val maxprec = 9999;

val is_int_literal_hook    = ref (K false)
val is_string_literal_hook = ref (K false)
val is_cons_hook           = ref (K false)
val is_list_hook           = ref (K false)

val dest_int_literal_hook = ref (fn _ => raise ERR "dest_int_literal" "undefined")
val dest_string_literal_hook = ref (fn _ => raise ERR "dest_string_literal" "undefined")
val dest_list_hook  = ref (fn _ => raise ERR "dest_list" "undefined")

(*---------------------------------------------------------------------------*)
(* A prettyprinter from HOL to very basic ML, dealing with basic paired      *)
(* lambda calculus terms, plus literals (strings, nums, ints), notation for  *)
(* lists, and case expressions.                                              *)
(*---------------------------------------------------------------------------*)

fun term_to_ML ppstrm = 
 let open Portable
     val {add_break,add_newline,
          add_string,begin_block,end_block,...} = with_ppstream ppstrm
     fun prec_paren p i j = if i >= j then add_string p else ()
     val lparen = prec_paren "("
     val rparen = prec_paren ")"
  fun pp i tm =
     if is_var tm then pp_var tm else
     if is_const tm then pp_const tm else
     if is_cond tm then pp_cond i tm else
     if numSyntax.is_numeral tm then pp_num_literal tm else
     if !is_int_literal_hook tm then pp_int_literal tm else
     if !is_string_literal_hook tm then pp_string tm else
     if !is_list_hook tm then pp_list tm else
     if !is_cons_hook tm then pp_binop i tm else
     if boolSyntax.is_eq tm then pp_binop i tm else
     if boolSyntax.is_conj tm then pp_binop i tm else
     if boolSyntax.is_disj tm then pp_binop i tm else
     if pairSyntax.is_pair tm then pp_pair i tm else
     if pairSyntax.is_plet tm then pp_let i tm else
     if pairSyntax.is_pabs tm then pp_abs i tm else
     if TypeBase.is_case tm then pp_case i (TypeBase.dest_case tm) else
     if is_comb tm then pp_comb i tm 
     else raise ERR "term_to_ML" "Unknown syntax"

  and pp_cond i tm = 
         let val (b,a1,a2) = dest_cond tm
         in lparen i 5000;
            begin_block CONSISTENT 2;
            add_string"if "; 
            begin_block CONSISTENT 0; 
            pp minprec b; end_block(); add_break(1,0);
            add_string"then"; add_break(1,0); 
            begin_block CONSISTENT 0; 
            pp minprec a1; end_block(); add_break(1,0);
            add_string"else"; add_break(1,0); 
            begin_block CONSISTENT 0; 
            pp minprec a2; end_block(); add_break(0,0);
            end_block();
            rparen i 5000
         end
  and pp_num_literal tm = 
         let val s = numML.toString(numSyntax.dest_numeral tm)
         in add_string"("; add_break(0,0);
            add_string "numML.fromString";
            add_break(0,0);
            add_string (mlquote s);
            add_break(0,0);
            add_string")"
         end
  and pp_int_literal tm = 
         let val s = Arbint.toString(!dest_int_literal_hook tm)
         in add_string"("; add_break(0,0);
            add_string "intML.fromString";
            add_break(0,0);
            add_string (mlquote s);
            add_break(0,0);
            add_string")"
         end
  and pp_string tm = add_string (mlquote (!dest_string_literal_hook tm))
  and pp_list tm = 
       let val els = !dest_list_hook tm
       in add_string "["
        ; begin_block INCONSISTENT 0
        ; pr_list (pp minprec)
                  (fn () => add_string",") 
                  (fn () => add_break(0,0)) els
        ; end_block()
        ; add_string "]"
       end
  and pp_binop i tm = 
      let val (c,[t1,t2]) = strip_comb tm
          val j = prec_of c
      in lparen i j
        ; pp (j+1) t1
        ; add_break(1,0)
        ; pp_const c
        ; add_break(1,0)
        ; pp j t2
        ; rparen i j
      end
  and pp_pair i tm = 
      let val (t1,t2) = pairSyntax.dest_pair tm
          val j = prec_of pairSyntax.comma_tm
      in lparen maxprec i
        ; pp (j+1) t1
        ; add_break(1,0)
        ; pp_const pairSyntax.comma_tm
        ; add_break(1,0)
        ; pp j t2
        ; rparen maxprec i 
      end
  and pp_let i tm =
      let val (vstruct,rhs,body) = pairSyntax.dest_plet tm
      in  lparen i 5000
        ; add_string "let val"
        ; add_break(1,0)
        ; pp minprec vstruct
        ; add_break(1,0)
        ; add_string"="
        ; add_break(1,0)
        ; pp minprec rhs
        ; add_break(1,0)
        ; add_string"in"
        ; add_break(1,0)
        ; pp minprec body
        ; add_break(1,0)
        ; add_string"end"
        ; rparen i 5000
      end
  and pp_case i (c,a,cases) =
      (lparen i 5000
        ; begin_block INCONSISTENT 1
        ; add_string "case"
        ; add_break(1,0)
        ; pp minprec a
        ; add_newline()
        ; add_string"of" 
        ; add_break(1,0)
        ; pr_list pp_case_clause 
                   (fn () => (add_newline(); add_string "|"))
                   (fn () => add_break(1,0)) cases
        ; rparen i 5000
        ; end_block()
        ; rparen i 5000)
  and pp_case_clause (pat,rhs) =
        (begin_block CONSISTENT 0
         ; pp minprec pat
         ; add_break (1,0)
         ; add_string "=>"
         ; add_break (1,0)
         ; pp minprec rhs
         ; end_block()
        )
  and pp_var tm = add_string(fst(dest_var tm))
  and pp_const tm = add_string (const_map tm)
  and pp_comb i tm = 
       let val (f,args) = strip_comb tm
       in lparen i maxprec
        ; if TypeBase.is_constructor f 
            then 
              (pp maxprec f; add_string "(";
               pr_list (pp minprec) 
                       (fn () => add_string ",") 
                       (fn () => add_break(0,0)) args;
               add_string ")")
            else pr_list (pp maxprec) (fn () => ()) 
                         (fn () => add_break(1,0)) (f::args)
        ; rparen i maxprec
       end
  and pp_abs i tm = 
       let val (vstruct,body) = pairSyntax.dest_pabs tm
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
 end

fun pp_term_as_ML ppstrm M = term_to_ML ppstrm minprec M;

fun same_fn eq1 eq2 = (fst(strip_comb eq1) = fst(strip_comb eq2));

(*---------------------------------------------------------------------------*)
(* Print a function definition as ML, i.e., fun f ... = ...                  *)
(*---------------------------------------------------------------------------*)

fun pp_defn_as_ML ppstrm = 
 let open Portable
     val {add_break,add_newline,
          add_string,begin_block,end_block,...} = with_ppstream ppstrm
     val toMLprim = term_to_ML ppstrm
     val toML = pp_term_as_ML ppstrm
     fun pp_clause eq =
         let val (L,R) = dest_eq eq
         in begin_block INCONSISTENT 2
          ; toML L
          ; add_break(1,0)
          ; add_string "="
          ; add_break(1,0)
          ; toMLprim 100 R
          ; end_block()
         end
     fun pp_clauses (s,els) =
       let in 
           begin_block CONSISTENT 2
         ; add_string (s^" ")
         ; pr_list pp_clause 
                   (fn () => (add_newline(); add_string "|"))
                   (fn () => add_break(1,0)) els
         ; end_block()
       end
     fun pp tm =
       let val eqns = map (snd o strip_forall) (strip_conj tm)
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
(* prettyprinter so it generate syntactically correct ML types               *)
(*---------------------------------------------------------------------------*)

local open type_grammar HOLgrammars
      fun problem {opname="sum",  parse_string="+"} = true
        | problem {opname="prod", parse_string="#"} = true
        | problem otherwise = false
      fun elim (r as (i,INFIX(list,a))) A = 
            let val list' = gather (not o problem) list
            in if list' = list then (r::A)
               else if null list' then A else (i,INFIX(list',a))::A
            end
        | elim (r as (i,SUFFIX list)) A = r::A
      fun add_rule (i,SUFFIX strings) grm = itlist (C new_tyop) strings grm 
        | add_rule (i,INFIX (list,assoc)) grm = 
           itlist (fn {opname,parse_string} => fn grm' => 
                      new_binary_tyop grm'
                        {opname=opname,precedence=i,
                         infix_form=SOME parse_string,associativity=assoc})
              list grm
in
fun adjust_tygram tygram = 
 let val rules' = itlist elim (rules tygram) []
     val tygram' = 
          itlist add_rule rules' 
              (add_rule (70,INFIX([{opname="prod",parse_string = "*"}],RIGHT))
                         empty_grammar)
     val abbrevs = Binarymap.listItems (abbreviations tygram)
     val tygram'' = itlist (C new_abbreviation) abbrevs tygram'
 in 
    tygram''
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

fun pp_datatype_as_ML ppstrm decls = 
 let open Portable ParseDatatype
     val {add_break,add_newline,
          add_string,begin_block,end_block,...} = with_ppstream ppstrm
     val type_names = map fst decls
     val tyax = TypeBase.axiom_of (hd type_names)
     val newtypes = Prim_rec.doms_of_tyaxiom tyax
     val tyvars = map dest_vartype (snd (dest_type (hd newtypes)))
     val alist = map (fn x => (fst(dest_type x),pretype_of x)) newtypes
     fun alist_fn name = snd (valOf (assoc1 name alist))
     val decls' = map (I##replaceForm alist_fn) decls
     val ppty = pp_type_as_ML ppstrm
     fun pp_tyvars [] = ()
       | pp_tyvars [v] = add_string v
       | pp_tyvars vlist = 
          (begin_block CONSISTENT 0;
           add_string"(";
           pr_list add_string (fn () => add_string",") (fn ()=>()) vlist;
           add_string")";
           end_block())
     fun pp_clause r clause =
       (if !r then (add_string "= "; r:=false) 
              else add_string "| "; 
        case clause
         of (con,[]) => add_string con
          | (con,args) =>
              (begin_block INCONSISTENT 0; 
                 begin_block CONSISTENT 0; add_string con; add_string " of ";
                 end_block(); 
               begin_block INCONSISTENT 0;
               pr_list ppty
                   (fn () => add_string " *")
                   (fn () => add_break(1,0))
                   (map ParseDatatype.pretypeToType args);
               end_block(); end_block()))
     fun pp_decl (tyvars,r) (name,Constructors clauselist) =
         (begin_block CONSISTENT 5;
          begin_block CONSISTENT 0;
            if !r then (add_string "datatype"; r:=false) else ();
            add_break(1,0); pp_tyvars tyvars; add_break(1,0);
            add_string name; 
          end_block();
          add_break(1,0);
          begin_block CONSISTENT 0;
          begin_block CONSISTENT 0;
          pr_list (pp_clause (ref true))
                  (fn () => ())
                  (fn () => add_break(1,0)) clauselist;
          end_block();end_block())
       | pp_decl tyvars (name,Record flist) = raise ERR "pp_datatype_as_ML" 
                                         "Records not yet dealt with"
 in 
    begin_block CONSISTENT 0
  ; pr_list (pp_decl (tyvars,ref true))
            (fn () => (add_newline(); add_string "and")) 
            add_newline
            decls'
  ; end_block()
  ; end_block()
 end;


(*---------------------------------------------------------------------------*)
(* Generate ML signature and structure corresponding to executable portion   *)
(* of a theory.                                                              *)
(*---------------------------------------------------------------------------*)

datatype elem 
    = DEFN of thm
    | DATATYPE of ParseDatatype.AST list;

fun consts_of_def thm =
  let val eqns = strip_conj (concl thm)
      val allCs = map (fst o strip_comb o lhs o snd o strip_forall) eqns
  in op_mk_set aconv allCs
  end;

fun ML s = s^"ML";

fun pp_sig strm (s,elems) =
 let open Portable
    val {add_break,add_newline, add_string, 
         begin_block,end_block,flush_ppstream,...} = with_ppstream strm
    val ppty = pp_type_as_ML strm
    val pp_datatype = pp_datatype_as_ML strm
    fun pp_valdec c =
     let val (name,ty) = dest_const c
     in begin_block CONSISTENT 0;
        add_string "val ";
        add_string name; add_break(1,0); add_string ":"; add_break (1,0);
        ppty ty;
        end_block()
     end
    fun pp_el (DATATYPE astl) = pp_datatype astl
      | pp_el (DEFN thm) = 
         pr_list pp_valdec (fn () => ()) add_newline (consts_of_def thm)
 in 
   begin_block CONSISTENT 0;
   add_string ("signature "^ML s^" = "); add_newline();
   begin_block CONSISTENT 2;
   add_string"sig"; add_newline();
   begin_block CONSISTENT 0;
   pr_list pp_el (fn () => ()) add_newline elems;
   end_block(); end_block(); 
   add_newline();
   add_string"end"; add_newline();
   end_block();
   flush_ppstream()
 end;

fun pp_struct strm (s,elems) =
 let open Portable
    val {add_break,add_newline, add_string, 
         begin_block,end_block,flush_ppstream,...} = with_ppstream strm
    val pp_datatype = pp_datatype_as_ML strm
    val pp_defn = pp_defn_as_ML strm
    fun pp_el (DATATYPE astl) = pp_datatype astl
      | pp_el (DEFN thm) =  pp_defn (concl thm)
 in 
   begin_block CONSISTENT 0;
   add_string ("structure "^ML s^" :> "^ML s^" ="); add_newline();
   begin_block CONSISTENT 2;
   add_string"struct"; add_newline();
   begin_block CONSISTENT 0;
   pr_list pp_el (fn () =>()) (fn () => (add_newline();add_newline())) elems;
   end_block(); end_block(); 
   add_newline();
   add_string"end"; add_newline();
   end_block();
   flush_ppstream()
 end;


fun pp_theory_as_ML strm1 strm2 (s,elems) =
 (pp_sig strm1 (s,elems);
  pp_struct strm2 (s,elems)
 );

end
