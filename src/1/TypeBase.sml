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

val bool_info =
    TypeBasePure.mk_datatype_info
      {ax=ORIG boolTheory.boolAxiom,
       induction = ORIG boolTheory.bool_INDUCT,
       case_def = boolTheory.bool_case_thm,
       case_cong = boolTheory.COND_CONG,
       distinct = SOME (CONJUNCT1 boolTheory.BOOL_EQ_DISTINCT),
       nchotomy = boolTheory.BOOL_CASES_AX,
       fields = [], accessors = [], updates = [], one_one = NONE,
       recognizers=[], destructors = [],
       size = NONE, encode = NONE, lift = NONE}

val _ = write [bool_info];

(* and similarly for the itself type constructor *)
val [itself_info] = let
  open boolTheory
in
  TypeBasePure.gen_datatype_info {ax = itself_Axiom, ind = itself_induction,
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
    set_case_specials ((fn t => #functional (Pmatch.mk_functional lookup t)),
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

fun mk_pattern_fn css =
   let
      val pmthry = TypeBasePure.toPmatchThry (theTypeBase ())
   in
      Pmatch.mk_pattern_fn pmthry css
   end

(*---------------------------------------------------------------------------*)
(* Syntax operations on records                                              *)
(*---------------------------------------------------------------------------*)

fun mk_record x   = TypeBasePure.mk_record (theTypeBase()) x
fun dest_record x = TypeBasePure.dest_record (theTypeBase()) x
fun is_record x   = TypeBasePure.is_record (theTypeBase()) x;

fun dest_record_type x = TypeBasePure.dest_record_type (theTypeBase()) x;
fun is_record_type x = TypeBasePure.is_record_type (theTypeBase()) x;

(* ----------------------------------------------------------------------
    Initialise the case-split munger in the pretty-printer
   ---------------------------------------------------------------------- *)

(*
  This is broken because it can re-order rows in the case expression in a semantically significant way
local
  fun group_by f =
    let
      fun i x [] = [[x]]
        | i x (y::ys) =
          if f x (hd y)
          then ((x::y)::ys)
          else y::(i x ys)
      fun g acc [] = acc
        | g acc (x::xs) =
          g (i x acc) xs
    in
      g []
    end
  fun aconv_snd x y = aconv (snd x) (snd y)
  fun max x y = if x < y then y else x
  fun lengths [] n acc = (n,acc)
    | lengths (l::ls) n acc =
      let
        val m = length l
      in
        lengths ls (max n m) ((m,l)::acc)
      end
in
  fun pp_strip_case tm =
    let
      val (split_on, splits) = strip_case tm
      val reduced_splits =
        let
          val groups = group_by aconv_snd splits
          (* groups are in order, but each group is reversed *)
          val (maxl,lgs) = lengths groups 0 []
          (* lgs are now reversed *)
        in
          case total (pluck (equal maxl o fst)) lgs of
            SOME ((_,(p,v)::_),lgs) =>
              rev ((mk_var("_",type_of p),v)::flatten (map snd lgs))
          | _ => splits
        end
    in
      (split_on, reduced_splits)
    end
end
*)

(* Less ambitious version, which only fires if all (>1) but one row have
   the same right-hand-side and it doesn't depend on any pattern variables.*)
local
  val disjoint = HOLset.isEmpty o HOLset.intersection
  fun FV tm = FVL [tm] empty_varset
in
  fun pp_strip_case tm =
    let
      val (split_on, splits) = strip_case tm
      fun sole_exception (p,v) =
        let
          val (l1,l2) = partition (aconv v o snd) splits
          val v_rest = snd (hd l2)
          fun good (p,v) = aconv v_rest v andalso disjoint (FV p, FV v)
        in
          if length l1 = 1 andalso all good l2
          then (hd l1, v_rest)
          else raise Match
        end
      val reduced_splits =
        case splits of
          [] => splits
        | [_] => splits
        | [_,_] => splits
        | _ =>
          let
            val (u as (p,_),v_rest) = tryfind sole_exception splits
          in
            [u,(mk_var("_",type_of p),v_rest)]
          end
          handle HOL_ERR _ => splits
    in
      (split_on, reduced_splits)
    end
end

val _ = term_pp.init_casesplit_munger pp_strip_case

end
