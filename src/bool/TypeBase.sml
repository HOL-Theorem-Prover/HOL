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

local val dBase = ref empty
      val update_fns = ref ([]:(tyinfo -> unit) list)
in
  fun theTypeBase() = !dBase

  fun register_update_fn f = (update_fns := f :: !update_fns)
  fun write facts = (dBase := add (theTypeBase()) facts;
                     Parse.temp_overload_on("case", case_const_of facts);
                     app (fn f => f facts) (!update_fns));
end;

fun read s = get (theTypeBase()) s;
val elts = listItems o theTypeBase;

fun valOf s opt =
  case opt of
    NONE => raise ERR "read" ("No type of name "^s)
  | SOME x => x

fun valOf2 s t opt =
  case opt of
    NONE => raise ERR t ("No "^t^" information for type "^s)
  | SOME x => x

fun axiom_of s        = TypeBasePure.axiom_of (valOf s (read s))
fun induction_of s    = TypeBasePure.induction_of (valOf s (read s))
fun constructors_of s = TypeBasePure.constructors_of (valOf s (read s))
fun case_const_of s   = TypeBasePure.case_const_of (valOf s (read s))
fun case_cong_of s    = TypeBasePure.case_cong_of (valOf s (read s))
fun case_def_of s     = TypeBasePure.case_def_of (valOf s (read s))
fun nchotomy_of s     = TypeBasePure.nchotomy_of (valOf s (read s))
fun distinct_of s     = valOf2 s "distinct_of"
                            (TypeBasePure.distinct_of (valOf s (read s)))
fun one_one_of s      = valOf2 s "one_one_of"
                            (TypeBasePure.one_one_of (valOf s (read s)))
fun simpls_of s       = TypeBasePure.simpls_of (valOf s (read s))
fun size_of s         = valOf2 s "size_of"
                            (TypeBasePure.size_of (valOf s (read s)))
fun boolify_of s      = valOf2 s "boolify_of"
                            (TypeBasePure.boolify_of (valOf s (read s)))
fun axiom_of0 s       = TypeBasePure.axiom_of0 (valOf s (read s))
fun induction_of0 s   = TypeBasePure.induction_of0 (valOf s (read s))
fun size_of0 s        = TypeBasePure.size_of0 (valOf s (read s))
fun boolify_of0 s     = TypeBasePure.boolify_of0 (valOf s (read s))



(*---------------------------------------------------------------------------*
 * Install datatype facts for booleans into theTypeBase.                     *
 *---------------------------------------------------------------------------*)

val [bool_info] = TypeBasePure.gen_tyinfo {ax=boolTheory.boolAxiom,
                              ind=boolTheory.bool_INDUCT,
                              case_defs = [boolTheory.bool_case_thm]};

val _ = write bool_info;

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

end
