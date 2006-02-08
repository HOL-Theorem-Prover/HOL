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
        (dBase := add (theTypeBase()) tyinfo;
         Parse.temp_overload_on("case", case_const_of tyinfo))
      val tyinfos = list_compose (!update_fns) tyinfos
      val () = app write1 tyinfos
    in
      tyinfos
    end;
end;

fun read {Thy,Tyop} = prim_get (theTypeBase()) (Thy,Tyop);
fun fancyread (Thy,Tyop) =
    if Thy = "" then
      case get (theTypeBase()) Tyop of
        [] => raise ERR "read" ("No type of name "^Tyop)
      | [x] => x
      | x::_ => (HOL_WARNING "TypeBase" "read"
                             ("Multiple types of name "^Tyop);
                 x)
    else let
        val Thy = if Thy = "-" then current_theory() else Thy
      in
        case prim_get (theTypeBase()) (Thy,Tyop) of
          NONE => raise ERR "read" ("No such type: "^Thy^"$"^Tyop)
        | SOME tyi => tyi
      end

val elts = listItems o theTypeBase;

fun print_sp_type (thy,tyop) = if thy = "" then tyop
                               else thy ^ "$" ^ tyop

fun valOf2 sp t opt =
  case opt of
    NONE => raise ERR t ("No "^t^" information for type "^print_sp_type sp)
  | SOME x => x

fun axiom_of s        = TypeBasePure.axiom_of (fancyread s)
fun induction_of s    = TypeBasePure.induction_of (fancyread s)
fun constructors_of s = TypeBasePure.constructors_of (fancyread s)
fun case_const_of s   = TypeBasePure.case_const_of (fancyread s)
fun case_cong_of s    = TypeBasePure.case_cong_of (fancyread s)
fun case_def_of s     = TypeBasePure.case_def_of (fancyread s)
fun nchotomy_of s     = TypeBasePure.nchotomy_of (fancyread s)
fun fields_of s       = TypeBasePure.fields_of (fancyread s)
fun distinct_of s     = valOf2 s "distinct_of"
                            (TypeBasePure.distinct_of (fancyread s))
fun one_one_of s      = valOf2 s "one_one_of"
                            (TypeBasePure.one_one_of (fancyread s))
fun simpls_of s       = TypeBasePure.simpls_of (fancyread s)
fun size_of s         = valOf2 s "size_of"
                            (TypeBasePure.size_of (fancyread s))
fun encode_of s       = valOf2 s "encode_of"
                            (TypeBasePure.encode_of (fancyread s))
fun axiom_of0 s       = TypeBasePure.axiom_of0 (fancyread s)
fun induction_of0 s   = TypeBasePure.induction_of0 (fancyread s)
fun size_of0 s        = TypeBasePure.size_of0 (fancyread s)
fun encode_of0 s      = TypeBasePure.encode_of0 (fancyread s)



(*---------------------------------------------------------------------------*
 * Install datatype facts for booleans into theTypeBase.                     *
 *---------------------------------------------------------------------------*)

val [bool_info] = TypeBasePure.gen_tyinfo {ax=boolTheory.boolAxiom,
                              ind=boolTheory.bool_INDUCT,
                              case_defs = [boolTheory.bool_case_thm]};

val _ = write [bool_info];

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

fun mk_record x y   = TypeBasePure.mk_record (theTypeBase()) x y
fun dest_record x = TypeBasePure.dest_record (theTypeBase()) x
fun is_record x   = TypeBasePure.is_record (theTypeBase()) x;

(* ----------------------------------------------------------------------
    Initialise the case-split munger in the pretty-printer
   ---------------------------------------------------------------------- *)

val _ = term_pp.init_casesplit_munger strip_case

end
