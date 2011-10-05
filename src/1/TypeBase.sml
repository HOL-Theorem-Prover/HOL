(*---------------------------------------------------------------------------*
 * Building records of facts about datatypes.                                *
 *---------------------------------------------------------------------------*)

structure TypeBase :> TypeBase =
struct

open HolKernel TypeBasePure;

val ERR = mk_HOL_ERR "TypeBase";


(*--------------------------------------------------------------------------*
 * Create the database.                                                     *
 *--------------------------------------------------------------------------*)

fun list_compose [] x = x | list_compose (f :: fs) x = list_compose fs (f x);

local val dBase = ref empty
      val update_fns = ref ([]:(tyinfo list -> tyinfo list) list)
in
  fun theTypeBase() = !dBase

  fun register_update_fn f = (update_fns := !update_fns @ [f])
  fun write tyinfos =
    let
      fun write1 tyinfo =
        (dBase := insert (theTypeBase()) tyinfo;
         Parse.temp_overload_on("case", case_const_of tyinfo)
         handle HOL_ERR _ => ())
      val tyinfos = list_compose (!update_fns) tyinfos
      val () = app write1 tyinfos
    in
      tyinfos
    end;
end;

fun read {Thy,Tyop} = prim_get (theTypeBase()) (Thy,Tyop);

fun fetch ty = TypeBasePure.fetch (theTypeBase()) ty;

val elts = listItems o theTypeBase;

fun print_sp_type ty =
  let val {Thy,Tyop,Args} = dest_thy_type ty
  in Thy ^ "$" ^ Tyop
  end;

fun valOf2 ty t opt =
  case opt of
    NONE => raise ERR t ("No "^t^" information for type "^print_sp_type ty)
  | SOME x => x

fun pfetch s ty =
 case TypeBasePure.fetch (theTypeBase()) ty
  of SOME x => x
   | NONE => raise ERR s
              ("unable to find "^
               Lib.quote (print_sp_type ty)^" in the TypeBase");

fun axiom_of ty        = TypeBasePure.axiom_of (pfetch "axiom_of" ty)
fun axiom_rk_of ty     = TypeBasePure.axiom_rk_of (pfetch "axiom_rk_of" ty)
fun induction_of ty    = TypeBasePure.induction_of (pfetch "induction_of" ty)
fun constructors_of ty = TypeBasePure.constructors_of (pfetch "constructors_of" ty)
fun destructors_of ty  = TypeBasePure.destructors_of (pfetch "destructors_of" ty)
fun recognizers_of ty  = TypeBasePure.recognizers_of (pfetch "recognizers_of" ty)
fun case_const_of ty   = TypeBasePure.case_const_of (pfetch "case_const_of" ty)
fun case_cong_of ty    = TypeBasePure.case_cong_of (pfetch "case_cong_of" ty)
fun case_def_of ty     = TypeBasePure.case_def_of (pfetch "case_def_of" ty)
fun nchotomy_of ty     = TypeBasePure.nchotomy_of (pfetch "nchotomy_of" ty)
fun fields_of ty       = TypeBasePure.fields_of (pfetch "fields_of" ty)
fun accessors_of ty    = TypeBasePure.accessors_of (pfetch "accessors_of" ty)
fun updates_of ty      = TypeBasePure.updates_of (pfetch "updates_of" ty)
fun simpls_of ty       = TypeBasePure.simpls_of (pfetch "simpls_of" ty)
fun axiom_of0 ty       = TypeBasePure.axiom_of0 (pfetch "axiom_of" ty)
fun axiom_rk_of0 ty    = TypeBasePure.axiom_rk_of0 (pfetch "axiom_rk_of" ty)
fun induction_of0 ty   = TypeBasePure.induction_of0 (pfetch "induction_of0" ty)

fun distinct_of ty     = valOf2 ty "distinct_of"
                           (TypeBasePure.distinct_of (pfetch "distinct_of" ty))
fun one_one_of ty      = valOf2 ty "one_one_of"
                            (TypeBasePure.one_one_of (pfetch "one_one_of" ty))
fun size_of0 ty        = TypeBasePure.size_of0 (pfetch "size_of0" ty)
fun encode_of0 ty      = TypeBasePure.encode_of0 (pfetch "encode_of0" ty)
fun size_of ty         = valOf2 ty "size_of"
                           (TypeBasePure.size_of (pfetch "size_of" ty))
fun encode_of ty       = valOf2 ty "encode_of"
                            (TypeBasePure.encode_of (pfetch "encode_of" ty))



(*---------------------------------------------------------------------------*
 * Install datatype facts for booleans into theTypeBase.                     *
 *---------------------------------------------------------------------------*)
local open boolTheory Parse Drule boolSyntax
in
fun bool_case_thm_rk rk =
 let val a = ty_antiq (mk_var_type("'a", Kind.typ rk))
     val x = Term`e0:^a`
     val y = Term`e1:^a`
     val th1 = RIGHT_BETA (AP_THM bool_case_DEF x)
     val th2 = RIGHT_BETA (AP_THM th1 y)
     val th3 = RIGHT_BETA (AP_THM th2 (Term`T`))
     val th4 = RIGHT_BETA (AP_THM th2 (Term`F`))
     val th5 = SPEC y (SPEC x COND_CLAUSES)
     val th6 = TRANS th3 (CONJUNCT1 th5)
     val th7 = TRANS th4 (CONJUNCT2 th5)
 in
   CONJ (GEN x (GEN y th6)) (GEN x (GEN y th7))
 end

fun boolAxiom_rk rk =
 let val bool_case_thm = bool_case_thm_rk rk
     val th1 = CONJUNCT1 bool_case_thm
     val [e0,e1] = fst(strip_forall(concl th1))
     val th2 = SPEC e1 (SPEC e0 th1)
     val th3 = SPEC e1 (SPEC e0 (CONJUNCT2 bool_case_thm))
     val th4 = CONJ th2 th3
     val th5 = EXISTS (Term`?fn. (fn T = ^e0) /\ (fn F = ^e1)`,
                       Term`bool_case ^e0 ^e1`) th4
 in
    GEN e0 (GEN e1 th5)
 end
end (*local*);

val [bool_info] = TypeBasePure.gen_datatype_info_rk
                         {ax=boolTheory.boolAxiom,
                          ax_rk=boolAxiom_rk,
                          ind=boolTheory.bool_INDUCT,
                          case_defs = [boolTheory.bool_case_thm]};

val _ = write [bool_info];

(* and similarly for the itself type constructor *)
val [itself_info] = let
  open boolTheory Parse Drule
  fun itself_Axiom_rk rk = let
    val a = ty_antiq (mk_var_type("'a", Kind.typ rk))
    val witness = --`(\x:'b:'k itself. e : ^a)`--
    val fn_behaves = BETA_CONV  (mk_comb(witness, --`(:'b:'k)`--))
    val fn_exists = EXISTS (--`?f:'b:'k itself -> ^a. f (:'b) = e`--, witness)
                    fn_behaves
  in
    GEN_ALL fn_exists
  end
in
  TypeBasePure.gen_datatype_info_rk {ax = itself_Axiom,
                                     ax_rk = itself_Axiom_rk,
                                     ind = itself_induction,
                                     case_defs = [itself_case_thm]}
end
val _ = write [itself_info]

(* ---------------------------------------------------------------------- *
 * Install case transformation function for parser                        *
 * ---------------------------------------------------------------------- *)

val _ =
  let fun lookup s =
        case read s
         of SOME tyi => SOME {constructors = TypeBasePure.constructors_of tyi,
                              case_const = TypeBasePure.case_const_of tyi}
          | NONE => NONE
      open GrammarSpecials
  in
    set_case_specials (#functional o Pmatch.mk_functional lookup,
                       (fn s =>
                             case lookup s of
                               NONE => []
                             | SOME {constructors,...} => constructors))
  end

(*---------------------------------------------------------------------------*)
(* Is a term a constructor for some datatype.                                *)
(*---------------------------------------------------------------------------*)

fun is_constructor x = TypeBasePure.is_constructor (theTypeBase()) x;

(*---------------------------------------------------------------------------*)
(* Syntax operations on case expressions                                     *)
(*---------------------------------------------------------------------------*)

fun mk_case x   = TypeBasePure.mk_case (theTypeBase()) x
fun dest_case x = TypeBasePure.dest_case (theTypeBase()) x
fun is_case x   = TypeBasePure.is_case (theTypeBase()) x;
fun strip_case x = TypeBasePure.strip_case (theTypeBase()) x

(*---------------------------------------------------------------------------*)
(* Syntax operations on records                                              *)
(*---------------------------------------------------------------------------*)

fun mk_record x   = TypeBasePure.mk_record (theTypeBase()) x
fun dest_record x = TypeBasePure.dest_record (theTypeBase()) x
fun is_record x   = TypeBasePure.is_record (theTypeBase()) x;

(* ----------------------------------------------------------------------
    Initialise the case-split munger in the pretty-printer
   ---------------------------------------------------------------------- *)

val _ = term_pp.init_casesplit_munger strip_case

end
