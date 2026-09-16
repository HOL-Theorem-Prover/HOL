(*  Title:      HolRefute/Refute_ModelFinder_Nut.sml
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Underlying terms ("nuts") for the HOL4 Refute model finder.

This is a port of Isabelle Nitpick's nitpick_nut.ML.  HOL4 sets are
functions, and HOL4 binders use named variables rather than de Bruijn terms.
The [nut] datatype and the op1/op2/op3 enumerations are unchanged; [cst]
gains the word and char operations, and the representation pass gains their
cases and the carrier-budget checks, alongside the divergences marked in the
code.
*)

signature REFUTE_MODEL_FINDER_NUT = sig
  type hol_type = Type.hol_type
  type term = Term.term
  type context = Refute_ModelFinder_HOL.mf_context
  type scope = Refute_ModelFinder_Scope.scope
  type name_pool = Refute_ModelFinder_Peephole.name_pool
  type rep = Refute_ModelFinder_Rep.rep

  datatype cst =
    False | True | Iden | Num of int | Unknown | Unrep | Suc | Add |
    Subtract | Multiply | Divide | Gcd | Lcm | Fracs | NormFrac |
    NatToInt | IntToNat |
    (* Word operations with no arithmetic reading.  [Add], [Subtract] and
       [Multiply] serve the modular ring at a word type, and the rest of the
       direct tier reduces to those. *)
    NatToWord | WordToNat | WordAnd | WordOr | WordXor |
    WordShl | WordShr | WordAsr |
    (* The two morphisms of the [:char] carrier: the numbering that makes
       atom [j] denote [CHR j], and its inverse. *)
    NatToChar | CharToNat

  datatype op1 =
    Not | Finite | Converse | Closure | SingletonSet | IsUnknown |
    SafeThe | First | Second | Cast

  datatype op2 =
    All | Exist | Or | And | Less | DefEq | Eq | Triad | Composition |
    Apply | Lambda

  datatype op3 = Let | If

  datatype nut =
    Cst of cst * hol_type * rep
  | Op1 of op1 * hol_type * rep * nut
  | Op2 of op2 * hol_type * rep * nut * nut
  | Op3 of op3 * hol_type * rep * nut * nut * nut
  | Tuple of hol_type * rep * nut list
  | Construct of nut list * hol_type * rep * nut list
  | BoundName of int * hol_type * rep * string
  | FreeName of string * hol_type * rep
  | ConstName of string * hol_type * rep
  | BoundRel of Refute_Forl.n_ary_index * hol_type * rep * string
  | FreeRel of Refute_Forl.n_ary_index * hol_type * rep * string
  | RelReg of int * hol_type * rep
  | FormulaReg of int * hol_type * rep

  structure NameTable : TABLE
  exception NUT of string * nut list

  val string_for_nut : nut -> string
  val inline_nut : nut -> bool
  val type_of : nut -> hol_type
  val rep_of : nut -> rep
  val nickname_of : nut -> string
  val is_skolem_name : nut -> bool
  val is_eval_name : nut -> bool
  val is_Cst : cst -> nut -> bool
  val fold_nut : (nut -> 'a -> 'a) -> nut -> 'a -> 'a
  val map_nut : (nut -> nut) -> nut -> nut
  val untuple : (nut -> 'a) -> nut -> 'a list
  val add_free_and_const_names :
    nut -> nut list * nut list -> nut list * nut list
  val name_ord : nut * nut -> order
  val the_name : 'a NameTable.table -> nut -> 'a
  val the_rel : nut NameTable.table -> nut -> Refute_Forl.n_ary_index
  val nut_from_term : context -> op2 -> term -> nut
  val is_fully_representable_set : nut -> bool
  val choose_reps_for_free_vars :
    scope -> nut list -> rep NameTable.table ->
    nut list * rep NameTable.table
  val choose_reps_for_consts :
    scope -> bool -> nut list -> rep NameTable.table ->
    nut list * rep NameTable.table
  val choose_reps_for_all_sels :
    scope -> rep NameTable.table -> nut list * rep NameTable.table
  val choose_reps_in_nut :
    scope -> bool -> rep NameTable.table -> bool -> nut -> nut
  val rename_free_vars :
    nut list -> name_pool -> nut NameTable.table ->
    nut list * name_pool * nut NameTable.table
  val rename_vars_in_nut :
    name_pool -> nut NameTable.table -> nut -> nut
end

structure Refute_ModelFinder_Nut :> REFUTE_MODEL_FINDER_NUT = struct
  type hol_type = Type.hol_type
  type term = Term.term
  type context = Refute_ModelFinder_HOL.mf_context
  type scope = Refute_ModelFinder_Scope.scope
  type name_pool = Refute_ModelFinder_Peephole.name_pool
  type rep = Refute_ModelFinder_Rep.rep

  structure MFN = Refute_ModelFinder_Names
  structure MFH = Refute_ModelFinder_HOL
  structure MFS = Refute_ModelFinder_Scope
  structure MFR = Refute_ModelFinder_Rep
  structure MFP = Refute_ModelFinder_Peephole
  structure Util = Refute_ModelFinder_Util

  datatype cst =
    False | True | Iden | Num of int | Unknown | Unrep | Suc | Add |
    Subtract | Multiply | Divide | Gcd | Lcm | Fracs | NormFrac |
    NatToInt | IntToNat |
    (* Word operations with no arithmetic reading.  [Add], [Subtract] and
       [Multiply] serve the modular ring at a word type, and the rest of the
       direct tier reduces to those. *)
    NatToWord | WordToNat | WordAnd | WordOr | WordXor |
    WordShl | WordShr | WordAsr |
    (* The two morphisms of the [:char] carrier: the numbering that makes
       atom [j] denote [CHR j], and its inverse. *)
    NatToChar | CharToNat

  datatype op1 =
    Not | Finite | Converse | Closure | SingletonSet | IsUnknown |
    SafeThe | First | Second | Cast

  datatype op2 =
    All | Exist | Or | And | Less | DefEq | Eq | Triad | Composition |
    Apply | Lambda

  datatype op3 = Let | If

  datatype nut =
    Cst of cst * hol_type * rep
  | Op1 of op1 * hol_type * rep * nut
  | Op2 of op2 * hol_type * rep * nut * nut
  | Op3 of op3 * hol_type * rep * nut * nut * nut
  | Tuple of hol_type * rep * nut list
  | Construct of nut list * hol_type * rep * nut list
  | BoundName of int * hol_type * rep * string
  | FreeName of string * hol_type * rep
  | ConstName of string * hol_type * rep
  | BoundRel of Refute_Forl.n_ary_index * hol_type * rep * string
  | FreeRel of Refute_Forl.n_ary_index * hol_type * rep * string
  | RelReg of int * hol_type * rep
  | FormulaReg of int * hol_type * rep

  exception NUT of string * nut list

  fun string_for_cst False = "False"
    | string_for_cst True = "True"
    | string_for_cst Iden = "Iden"
    | string_for_cst (Num value) = "Num " ^ Int.toString value
    | string_for_cst Unknown = "Unknown"
    | string_for_cst Unrep = "Unrep"
    | string_for_cst Suc = "Suc"
    | string_for_cst Add = "Add"
    | string_for_cst Subtract = "Subtract"
    | string_for_cst Multiply = "Multiply"
    | string_for_cst Divide = "Divide"
    | string_for_cst Gcd = "Gcd"
    | string_for_cst Lcm = "Lcm"
    | string_for_cst Fracs = "Fracs"
    | string_for_cst NormFrac = "NormFrac"
    | string_for_cst NatToInt = "NatToInt"
    | string_for_cst IntToNat = "IntToNat"
    | string_for_cst NatToWord = "NatToWord"
    | string_for_cst WordToNat = "WordToNat"
    | string_for_cst WordAnd = "WordAnd"
    | string_for_cst WordOr = "WordOr"
    | string_for_cst WordXor = "WordXor"
    | string_for_cst WordShl = "WordShl"
    | string_for_cst WordShr = "WordShr"
    | string_for_cst WordAsr = "WordAsr"
    | string_for_cst NatToChar = "NatToChar"
    | string_for_cst CharToNat = "CharToNat"

  fun string_for_op1 Not = "Not"
    | string_for_op1 Finite = "Finite"
    | string_for_op1 Converse = "Converse"
    | string_for_op1 Closure = "Closure"
    | string_for_op1 SingletonSet = "SingletonSet"
    | string_for_op1 IsUnknown = "IsUnknown"
    | string_for_op1 SafeThe = "SafeThe"
    | string_for_op1 First = "First"
    | string_for_op1 Second = "Second"
    | string_for_op1 Cast = "Cast"

  fun string_for_op2 All = "All"
    | string_for_op2 Exist = "Exist"
    | string_for_op2 Or = "Or"
    | string_for_op2 And = "And"
    | string_for_op2 Less = "Less"
    | string_for_op2 DefEq = "DefEq"
    | string_for_op2 Eq = "Eq"
    | string_for_op2 Triad = "Triad"
    | string_for_op2 Composition = "Composition"
    | string_for_op2 Apply = "Apply"
    | string_for_op2 Lambda = "Lambda"

  fun string_for_op3 Let = "Let"
    | string_for_op3 If = "If"

  fun indent count = String.implode (List.tabulate (count, fn _ => #" "))

  fun basic_string_for_nut depth nut =
    let
      val prefix = if depth = 0 then "" else "\n" ^ indent (2 * depth)
      val sub = basic_string_for_nut (depth + 1)
      fun ty_string ty = Hol_pp.type_to_string ty
      fun rep_string representation = MFR.string_for_rep representation
      fun subs nuts = String.concat (map sub nuts)
    in
      prefix ^ "(" ^
      (case nut of
           Cst (constant, ty, representation) =>
             "Cst " ^ string_for_cst constant ^ " " ^ ty_string ty ^
             " " ^ rep_string representation
         | Op1 (operator, ty, representation, first) =>
             "Op1 " ^ string_for_op1 operator ^ " " ^ ty_string ty ^
             " " ^ rep_string representation ^ " " ^ sub first
         | Op2 (operator, ty, representation, first, second) =>
             "Op2 " ^ string_for_op2 operator ^ " " ^ ty_string ty ^
             " " ^ rep_string representation ^ " " ^ sub first ^
             " " ^ sub second
         | Op3 (operator, ty, representation, first, second, third) =>
             "Op3 " ^ string_for_op3 operator ^ " " ^ ty_string ty ^
             " " ^ rep_string representation ^ " " ^ sub first ^
             " " ^ sub second ^ " " ^ sub third
         | Tuple (ty, representation, nuts) =>
             "Tuple " ^ ty_string ty ^ " " ^ rep_string representation ^
             subs nuts
         | Construct (selectors, ty, representation, arguments) =>
             "Construct " ^ subs selectors ^ " " ^ ty_string ty ^ " " ^
             rep_string representation ^ " " ^ subs arguments
         | BoundName (index, ty, representation, nickname) =>
             "BoundName " ^ Int.toString index ^ " " ^ ty_string ty ^
             " " ^ rep_string representation ^ " " ^ nickname
         | FreeName (name, ty, representation) =>
             "FreeName " ^ name ^ " " ^ ty_string ty ^ " " ^
             rep_string representation
         | ConstName (name, ty, representation) =>
             "ConstName " ^ name ^ " " ^ ty_string ty ^ " " ^
             rep_string representation
         | BoundRel ((arity, index), ty, representation, nickname) =>
             "BoundRel " ^ Int.toString arity ^ "." ^
             Int.toString index ^ " " ^ ty_string ty ^ " " ^
             rep_string representation ^ " " ^ nickname
         | FreeRel ((arity, index), ty, representation, nickname) =>
             "FreeRel " ^ Int.toString arity ^ "." ^ Int.toString index ^
             " " ^ ty_string ty ^ " " ^ rep_string representation ^
             " " ^ nickname
         | RelReg (index, ty, representation) =>
             "RelReg " ^ Int.toString index ^ " " ^ ty_string ty ^ " " ^
             rep_string representation
         | FormulaReg (index, ty, representation) =>
             "FormulaReg " ^ Int.toString index ^ " " ^ ty_string ty ^
             " " ^ rep_string representation) ^ ")"
    end

  val string_for_nut = basic_string_for_nut 0

  fun inline_nut (Op1 _) = false
    | inline_nut (Op2 _) = false
    | inline_nut (Op3 _) = false
    | inline_nut (Tuple (_, _, nuts)) = List.all inline_nut nuts
    | inline_nut _ = true

  fun type_of (Cst (_, ty, _)) = ty
    | type_of (Op1 (_, ty, _, _)) = ty
    | type_of (Op2 (_, ty, _, _, _)) = ty
    | type_of (Op3 (_, ty, _, _, _, _)) = ty
    | type_of (Tuple (ty, _, _)) = ty
    | type_of (Construct (_, ty, _, _)) = ty
    | type_of (BoundName (_, ty, _, _)) = ty
    | type_of (FreeName (_, ty, _)) = ty
    | type_of (ConstName (_, ty, _)) = ty
    | type_of (BoundRel (_, ty, _, _)) = ty
    | type_of (FreeRel (_, ty, _, _)) = ty
    | type_of (RelReg (_, ty, _)) = ty
    | type_of (FormulaReg (_, ty, _)) = ty

  fun rep_of (Cst (_, _, representation)) = representation
    | rep_of (Op1 (_, _, representation, _)) = representation
    | rep_of (Op2 (_, _, representation, _, _)) = representation
    | rep_of (Op3 (_, _, representation, _, _, _)) = representation
    | rep_of (Tuple (_, representation, _)) = representation
    | rep_of (Construct (_, _, representation, _)) = representation
    | rep_of (BoundName (_, _, representation, _)) = representation
    | rep_of (FreeName (_, _, representation)) = representation
    | rep_of (ConstName (_, _, representation)) = representation
    | rep_of (BoundRel (_, _, representation, _)) = representation
    | rep_of (FreeRel (_, _, representation, _)) = representation
    | rep_of (RelReg (_, _, representation)) = representation
    | rep_of (FormulaReg (_, _, representation)) = representation

  fun nickname_of (BoundName (_, _, _, nickname)) = nickname
    | nickname_of (FreeName (name, _, _)) = name
    | nickname_of (ConstName (name, _, _)) = name
    | nickname_of (BoundRel (_, _, _, nickname)) = nickname
    | nickname_of (FreeRel (_, _, _, nickname)) = nickname
    | nickname_of nut = raise NUT
        ("Refute_ModelFinder_Nut.nickname_of", [nut])

  fun is_skolem_name nut = MFN.is_skolem_name (nickname_of nut)
    handle NUT _ => false

  fun is_eval_name nut =
    Option.isSome (MFN.eval_index (nickname_of nut))
    handle NUT _ => false

  fun is_Cst constant (Cst (other, _, _)) = constant = other
    | is_Cst _ _ = false

  fun fold_nut f nut accumulator =
    case nut of
        Op1 (_, _, _, first) => fold_nut f first accumulator
      | Op2 (_, _, _, first, second) =>
          fold_nut f second (fold_nut f first accumulator)
      | Op3 (_, _, _, first, second, third) =>
          fold_nut f third
            (fold_nut f second (fold_nut f first accumulator))
      | Tuple (_, _, nuts) =>
          List.foldl (fn (item, result) => fold_nut f item result)
            accumulator nuts
      | Construct (selectors, _, _, arguments) =>
          List.foldl (fn (item, result) => fold_nut f item result)
            (List.foldl (fn (item, result) => fold_nut f item result)
               accumulator arguments) selectors
      | _ => f nut accumulator

  fun map_nut f nut =
    case nut of
        Op1 (operator, ty, representation, first) =>
          Op1 (operator, ty, representation, map_nut f first)
      | Op2 (operator, ty, representation, first, second) =>
          Op2 (operator, ty, representation,
            map_nut f first, map_nut f second)
      | Op3 (operator, ty, representation, first, second, third) =>
          Op3 (operator, ty, representation, map_nut f first,
            map_nut f second, map_nut f third)
      | Tuple (ty, representation, nuts) =>
          Tuple (ty, representation, map (map_nut f) nuts)
      | Construct (selectors, ty, representation, arguments) =>
          Construct (map (map_nut f) selectors, ty, representation,
            map (map_nut f) arguments)
      | _ => f nut

  fun name_ord (BoundName (left, _, _, _),
                BoundName (right, _, _, _)) = Int.compare (left, right)
    | name_ord (BoundName _, _) = LESS
    | name_ord (_, BoundName _) = GREATER
    | name_ord (FreeName (left, left_ty, _),
                FreeName (right, right_ty, _)) =
        (case String.compare (left, right) of
             EQUAL => Type.compare (left_ty, right_ty)
           | order => order)
    | name_ord (FreeName _, _) = LESS
    | name_ord (_, FreeName _) = GREATER
    | name_ord (ConstName (left, left_ty, _),
                ConstName (right, right_ty, _)) =
        (case String.compare (left, right) of
             EQUAL => Type.compare (left_ty, right_ty)
           | order => order)
    | name_ord (left, right) = raise NUT
        ("Refute_ModelFinder_Nut.name_ord", [left, right])

  structure NameTable = Table(
    type key = nut
    val ord = name_ord
    val pp = HOLPP.add_string o string_for_nut)

  fun num_occurrences_in_nut needle stack =
    fold_nut (fn nut => fn count =>
      if nut = needle then count + 1 else count) stack 0

  fun is_subnut_of needle stack = num_occurrences_in_nut needle stack <> 0

  fun substitute_in_nut needle replacement =
    map_nut (fn nut => if nut = needle then replacement else nut)

  fun add_free_and_const_names nut (frees, constants) =
    fold_nut (fn item => fn (fs, cs) =>
      case item of
          FreeName _ => (Lib.insert item fs, cs)
        | ConstName _ => (fs, Lib.insert item cs)
        | _ => (fs, cs)) nut (frees, constants)

  fun modify_name_rep (BoundName (index, ty, _, nickname)) representation =
        BoundName (index, ty, representation, nickname)
    | modify_name_rep (FreeName (name, ty, _)) representation =
        FreeName (name, ty, representation)
    | modify_name_rep (ConstName (name, ty, _)) representation =
        ConstName (name, ty, representation)
    | modify_name_rep nut _ = raise NUT
        ("Refute_ModelFinder_Nut.modify_name_rep", [nut])

  fun the_name table name =
    case NameTable.lookup table name of
        SOME value => value
      | NONE => raise NUT ("Refute_ModelFinder_Nut.the_name", [name])

  fun the_rel table name =
    case the_name table name of
        FreeRel (index, _, _, _) => index
      | nut => raise NUT ("Refute_ModelFinder_Nut.the_rel", [nut])

  fun const_name constant =
    let val {Thy, Name, ...} = Term.dest_thy_const constant
    in Thy ^ "$" ^ Name end

  fun domain_type ty = #1 (Type.dom_rng ty)
  fun range_type ty = #2 (Type.dom_rng ty)
  fun body_type ty = #2 (boolSyntax.strip_fun ty)

  fun is_named key term =
    MFH.is_named_const key term orelse
    (case Lib.total Term.dest_var term of
         SOME (name, _) => MFN.is_reserved_name name andalso
           MFN.original_name name = #Thy key ^ "$" ^ #Name key
       | NONE => false)

  fun reserved_numeral term =
    case Lib.total Term.dest_var term of
        SOME (name, _) =>
          if String.isPrefix MFN.numeral_prefix name then
            Int.fromString (String.extract
              (name, size MFN.numeral_prefix, NONE))
          else NONE
      | NONE => NONE

  fun factor_types ty =
    if MFH.is_pair_type ty then
      let val (left, right) = pairSyntax.dest_prod ty
      in factor_types left @ factor_types right end
    else
      [ty]

  fun factorize (ty, term) =
    if MFH.is_pair_type ty then
      let
        val (left_ty, right_ty) = pairSyntax.dest_prod ty
        val (left, right) =
          if pairSyntax.is_pair term then pairSyntax.dest_pair term
          else (pairSyntax.mk_fst term, pairSyntax.mk_snd term)
      in
        factorize (left_ty, left) @ factorize (right_ty, right)
      end
    else
      [(ty, term)]

  fun selector_names_for constructor =
    let
      val data_ty = MFH.constructor_result_type constructor
      val constructor_id = MFH.constructor_name constructor
      val discriminator = MFN.mk_discriminator constructor_id
        (Type.-->(data_ty, Type.bool))
      val selector_tys = List.concat
        (map factor_types (MFH.constructor_arg_types constructor))
      fun selector (index, ty) = MFN.mk_selector index constructor_id
        (Type.-->(data_ty, ty))
    in
      discriminator :: map selector
        (ListPair.zip (List.tabulate (length selector_tys, fn x => x),
           selector_tys))
    end

  fun fresh_extensional_variables left right ty =
    let
      fun domains candidate result =
        case Lib.total Type.dom_rng candidate of
            SOME (domain, range) => domains range (domain :: result)
          | NONE => rev result
      fun add (arg_ty, (index, avoids, variables)) =
        let
          val candidate = Term.mk_var ("x" ^ Int.toString index, arg_ty)
          val variable = Term.variant avoids candidate
        in
          (index + 1, variable :: avoids, variable :: variables)
        end
      val (_, _, reversed) = List.foldl add
        (0, Term.all_vars left @ Term.all_vars right, []) (domains ty [])
    in
      rev reversed
    end

  (* The word and char carrier tables and their lookups: pure constants,
     kept at module level rather than inside [nut_from_term]'s per-node
     [aux], which would rebuild all 25 table entries and the four lookup
     closures at every subterm of every encoded term. *)

  (* Atom [j] of a word carrier denotes [n2w j], so a literal is a
     [Num] at the word type once reduced modulo the width. *)
  fun word_literal_value term =
    case Lib.total wordsSyntax.dest_mod_word_literal term of
        SOME (value, _) => Lib.total Arbnum.toInt value
      | NONE => NONE

  (* Shared by both carriers' tables: [applies] gates on the operation's
     type first, since a table miss is the common case and every entry's
     [is_named] re-destructs the head. *)
  fun guarded_key_lookup applies table head =
    if applies (Term.type_of head) then
      Option.map #2 (List.find (fn (key, _) => is_named key head) table)
    else NONE

  fun word_key_lookup table head =
    guarded_key_lookup (Option.isSome o MFH.word_op_dimension) table head

  fun char_key_lookup table head =
    guarded_key_lookup MFH.is_char_op_type table head

  (* [Add], [Subtract] and [Multiply] are the modular ring at a word
     type; the other direct operations have no arithmetic reading. *)
  val word_csts =
    [({Thy = "words", Name = "n2w"}, NatToWord),
     ({Thy = "words", Name = "w2n"}, WordToNat),
     ({Thy = "words", Name = "word_add"}, Add),
     ({Thy = "words", Name = "word_sub"}, Subtract),
     ({Thy = "words", Name = "word_mul"}, Multiply),
     ({Thy = "words", Name = "word_and"}, WordAnd),
     ({Thy = "words", Name = "word_or"}, WordOr),
     ({Thy = "words", Name = "word_xor"}, WordXor),
     ({Thy = "words", Name = "word_lsl"}, WordShl),
     ({Thy = "words", Name = "word_lsr"}, WordShr),
     ({Thy = "words", Name = "word_asr"}, WordAsr)]
  val word_cst_of = word_key_lookup word_csts

  (* Each order is the unsigned strict one, optionally swapped and
     negated; a signed order additionally adds the sign bit to both
     operands, which turns the signed order into the unsigned one. *)
  val word_orders =
    [({Thy = "words", Name = "word_lo"}, (false, false, false)),
     ({Thy = "words", Name = "word_hi"}, (false, true, false)),
     ({Thy = "words", Name = "word_ls"}, (false, true, true)),
     ({Thy = "words", Name = "word_hs"}, (false, false, true)),
     ({Thy = "words", Name = "word_lt"}, (true, false, false)),
     ({Thy = "words", Name = "word_gt"}, (true, true, false)),
     ({Thy = "words", Name = "word_le"}, (true, true, true)),
     ({Thy = "words", Name = "word_ge"}, (true, false, true))]
  val word_order_of = word_key_lookup word_orders

  (* Atom [j] of the char carrier denotes [CHR j], so a literal is a
     [Num] at [:char]. *)
  fun char_literal_value term =
    if MFH.is_char_literal term then
      Lib.total numSyntax.int_of_term (#2 (Term.dest_comb term))
    else NONE
  val char_csts =
    [({Thy = "string", Name = "CHR"}, NatToChar),
     ({Thy = "string", Name = "ORD"}, CharToNat)]
  val char_cst_of = char_key_lookup char_csts

  (* Character order is the order of the codes, which is the atom
     order, so the unsigned word orders read it unchanged. *)
  val char_orders =
    [({Thy = "string", Name = "char_lt"}, (false, false, false)),
     ({Thy = "string", Name = "char_gt"}, (false, true, false)),
     ({Thy = "string", Name = "char_le"}, (false, true, true)),
     ({Thy = "string", Name = "char_ge"}, (false, false, true))]
  val char_order_of = char_key_lookup char_orders

  (* Both carriers reach the same encoding, so one lookup serves the
     dispatch below and the two orders never drift apart. *)
  fun order_of head =
    case word_order_of head of
        NONE => char_order_of head
      | found => found

  fun cst_of head =
    case word_cst_of head of
        NONE => char_cst_of head
      | found => found

  (* Negation and complementation are both [value - x] for a
     width-dependent [value], so they are two more table rows.  The
     table's own guard is the word-type test the dispatch would
     otherwise spell out again. *)
  val word_subtract_bases =
    [({Thy = "words", Name = "word_2comp"}, fn _ => 0),
     ({Thy = "words", Name = "word_1comp"},
      fn width => Util.reasonable_power 2 width - 1)]
  val word_subtract_base_of = word_key_lookup word_subtract_bases

  (* [value - x] at a word type: complementation is [~1w - x] and
     negation is [0w - x], neither needing a primitive of its own. *)
  fun word_subtract_from word_ty value =
    Op2 (Apply, Type.-->(word_ty, word_ty), MFR.Any,
      Cst (Subtract,
        Type.-->(word_ty, Type.-->(word_ty, word_ty)), MFR.Any),
      Cst (Num value, word_ty, MFR.Any))

  fun word_add_sign_bit operand =
    let
      val word_ty = type_of operand
      val width = MFH.word_width word_ty
    in
      Op2 (Apply, word_ty, MFR.Any,
        Op2 (Apply, Type.-->(word_ty, word_ty), MFR.Any,
          Cst (Add,
            Type.-->(word_ty, Type.-->(word_ty, word_ty)), MFR.Any),
          Cst (Num (Util.reasonable_power 2 (width - 1)), word_ty,
            MFR.Any)),
        operand)
    end

  fun word_comparison (signed, swap, negate) left right =
    let
      val (first, second) =
        if swap then (right, left) else (left, right)
      val (first, second) =
        if signed then
          (word_add_sign_bit first, word_add_sign_bit second)
        else (first, second)
      val less = Op2 (Less, Type.bool, MFR.Any, first, second)
    in
      if negate then Op1 (Not, Type.bool, MFR.Any, less) else less
    end

  fun nut_from_term context equality term =
    let
      fun int_of_numeral integer =
        Arbint.toInt integer
        handle Overflow =>
          raise Util.TOO_LARGE
            ("Refute_ModelFinder_Nut.nut_from_term",
             "numeral does not fit in int")
      (* HOL4 binders expose named variables.  The environment records their
         de Bruijn levels, preserving Nitpick's BoundName convention. *)
      fun aux ambient environment candidate =
        let
          val sub = aux Eq environment
          val sub' = aux ambient environment
          fun bind variable body =
            let
              val (name, ty) = Term.dest_var variable
              val level = length environment
            in
              (BoundName (level, ty, MFR.Any, name),
               aux ambient ((variable, level, name) :: environment) body)
            end
          fun bound_name variable =
            case List.find (fn (other, _, _) =>
                   Term.aconv other variable) environment of
                SOME (_, level, name) =>
                  SOME (BoundName (level, Term.type_of variable,
                    MFR.Any, name))
              | NONE => NONE
          fun do_quantifier operator variable body =
            let val (bound, body_nut) = bind variable body
            in Op2 (operator, Type.bool, MFR.Any, bound, body_nut) end
          fun do_equals operator left right =
            let val operand_ty = Term.type_of left
            in
              if operator = Eq andalso MFH.is_fun_type operand_ty then
                let
                  val variables = fresh_extensional_variables
                    left right operand_ty
                  val equation = boolSyntax.mk_eq
                    (Term.list_mk_comb (left, variables),
                     Term.list_mk_comb (right, variables))
                in
                  aux ambient environment
                    (boolSyntax.list_mk_forall (variables, equation))
                end
              else
                Op2 (operator, Type.bool, MFR.Any, sub left, sub right)
            end
          fun do_apply head arguments =
            let
              val reversed = rev arguments
              val last = hd reversed
              val initial = rev (tl reversed)
              val function = Term.list_mk_comb (head, initial)
            in
              Op2 (Apply, Term.type_of candidate, MFR.Any,
                sub function, sub last)
            end
          fun do_construct constructor arguments =
            let
              val expected = length (MFH.constructor_arg_types constructor)
              val missing = expected - length arguments
            in
              if missing = 0 then
                let
                  val selectors = map (fn selector =>
                    ConstName (MFN.variable_name selector,
                      Term.type_of selector, MFR.Any))
                    (selector_names_for constructor)
                  val typed_arguments = ListPair.zip
                    (MFH.constructor_arg_types constructor, arguments)
                  val flattened = List.concat (map factorize typed_arguments)
                in
                  Construct (selectors,
                    MFH.constructor_result_type constructor, MFR.Any,
                    map (sub o #2) flattened)
                end
              else if missing > 0 then
                sub (MFH.eta_expand candidate missing)
              else
                do_apply constructor arguments
            end
          fun cst constant head =
            Cst (constant, Term.type_of head, MFR.Any)
          fun arithmetic_cst head =
            if MFH.iterator_marker_of_term context head =
                 SOME MFH.IteratorSuc then SOME Suc
            else if is_named {Thy = "num", Name = "SUC"} head then SOME Suc
            else if is_named {Thy = "arithmetic", Name = "+"} head orelse
                    is_named {Thy = "integer", Name = "int_add"} head then
              SOME Add
            else if is_named {Thy = "arithmetic", Name = "-"} head orelse
                    is_named {Thy = "integer", Name = "int_sub"} head then
              SOME Subtract
            else if is_named {Thy = "arithmetic", Name = "*"} head orelse
                    is_named {Thy = "integer", Name = "int_mul"} head then
              SOME Multiply
            else if is_named {Thy = "arithmetic", Name = "DIV"} head orelse
                    is_named {Thy = "integer", Name = "int_div"} head then
              SOME Divide
            else NONE
          fun is_numeral_skeleton head =
            is_named {Thy = "arithmetic", Name = "NUMERAL"} head orelse
            is_named {Thy = "arithmetic", Name = "BIT1"} head orelse
            is_named {Thy = "arithmetic", Name = "BIT2"} head
          fun expand_numeral_skeleton head arguments =
            case arguments of
                [] => MFH.eta_expand head 1
              | argument :: rest =>
                  let
                    val expanded =
                      if is_named {Thy = "arithmetic", Name = "NUMERAL"}
                           head then
                        argument
                      else
                        (* BIT1 n = 2n + 1 and BIT2 n = 2n + 2. *)
                        numSyntax.mk_plus
                          (numSyntax.mk_plus (argument, argument),
                           numSyntax.term_of_int
                             (if is_named {Thy = "arithmetic", Name = "BIT1"}
                                head then 1 else 2))
                  in
                    Term.list_mk_comb (expanded, rest)
                  end
          val (head, arguments) = HolKernel.strip_comb candidate
        in
          case MFH.iterator_marker_of_term context candidate of
              SOME MFH.IteratorZero =>
                Cst (Num 0, Term.type_of candidate, MFR.Any)
            | SOME MFH.IteratorSuc =>
                Cst (Suc, Term.type_of candidate, MFR.Any)
            | NONE =>
          (case reserved_numeral candidate of
              SOME integer =>
                Cst (Num integer, Term.type_of candidate, MFR.Any)
            | NONE =>
              (case MFH.numeral_value candidate of
                   SOME integer =>
                     Cst (Num (int_of_numeral integer),
                       Term.type_of candidate, MFR.Any)
                 | NONE =>
              case word_literal_value candidate of
                  SOME value =>
                    Cst (Num value, Term.type_of candidate, MFR.Any)
                | NONE =>
              case char_literal_value candidate of
                  SOME value =>
                    Cst (Num value, Term.type_of candidate, MFR.Any)
                | NONE =>
              if boolSyntax.is_forall candidate then
                let val (variable, body) = boolSyntax.dest_forall candidate
                in do_quantifier All variable body end
              else if boolSyntax.is_exists candidate then
                let val (variable, body) = boolSyntax.dest_exists candidate
                in do_quantifier Exist variable body end
              else if boolSyntax.is_neg candidate then
                (case sub (boolSyntax.dest_neg candidate) of
                     Op1 (Not, _, _, inner) => inner
                   | inner => Op1 (Not, Type.bool, MFR.Any, inner))
              else if Term.aconv candidate boolSyntax.F then
                Cst (False, Type.bool, MFR.Any)
              else if Term.aconv candidate boolSyntax.T then
                Cst (True, Type.bool, MFR.Any)
              else if boolSyntax.is_eq candidate then
                let val (left, right) = boolSyntax.dest_eq candidate
                in do_equals ambient left right end
              else if Term.is_const head andalso
                      is_named {Thy = "min", Name = "="} head andalso
                      length arguments = 1 then
                Op1 (SingletonSet, Term.type_of candidate, MFR.Any,
                  sub (hd arguments))
              else if Term.is_const head andalso
                      (is_named {Thy = "bool", Name = "!"} head orelse
                       is_named {Thy = "bool", Name = "?"} head) andalso
                      length arguments = 1 then
                sub' (Term.mk_comb
                  (head, MFH.eta_expand (hd arguments) 1))
              else if boolSyntax.is_imp_only candidate then
                let val (left, right) = boolSyntax.dest_imp candidate
                in
                  Op2 (Or, Type.bool, MFR.Any,
                    Op1 (Not, Type.bool, MFR.Any, sub left), sub' right)
                end
              else if boolSyntax.is_conj candidate then
                let val (left, right) = boolSyntax.dest_conj candidate
                in Op2 (And, Type.bool, MFR.Any, sub' left, sub' right) end
              else if boolSyntax.is_disj candidate then
                let val (left, right) = boolSyntax.dest_disj candidate
                in Op2 (Or, Type.bool, MFR.Any, sub left, sub right) end
              else if boolSyntax.is_cond candidate then
                let val (condition, left, right) =
                  boolSyntax.dest_cond candidate
                in
                  Op3 (If, Term.type_of candidate, MFR.Any,
                    sub condition, sub left, sub right)
                end
              else if boolSyntax.is_let candidate then
                let val (function, value) = boolSyntax.dest_let candidate
                in
                  case Lib.total Term.dest_abs function of
                      SOME (variable, body) =>
                        let
                          val value' = sub value
                          val (bound, body_nut) = bind variable body
                        in
                          Op3 (Let, Term.type_of candidate, MFR.Any,
                            bound, value', body_nut)
                        end
                    | NONE => sub
                        (Term.mk_comb (MFH.eta_expand function 1, value))
                end
              else if pairSyntax.is_pair candidate then
                let val (left, right) = pairSyntax.dest_pair candidate
                in Tuple (Term.type_of candidate, MFR.Any,
                     [sub left, sub right]) end
              else if pairSyntax.is_fst candidate then
                Op1 (First, Term.type_of candidate, MFR.Any,
                  sub (pairSyntax.dest_fst candidate))
              else if pairSyntax.is_snd candidate then
                Op1 (Second, Term.type_of candidate, MFR.Any,
                  sub (pairSyntax.dest_snd candidate))
              else if Term.is_const head andalso
                      is_named {Thy = "bool", Name = "IN"} head andalso
                      length arguments = 2 then
                do_apply (List.nth (arguments, 1)) [hd arguments]
              else if Term.is_const head andalso
                      is_named {Thy = "pred_set", Name = "FINITE"} head
                      andalso length arguments = 1 then
                let val set = hd arguments
                in
                  if MFH.is_finite_type context
                       (domain_type (Term.type_of set)) then
                    Cst (True, Type.bool, MFR.Any)
                  else if Term.is_const set andalso
                          is_named {Thy = "pred_set", Name = "UNIV"} set then
                    Cst (False, Type.bool, MFR.Any)
                  else
                    Op1 (Finite, Type.bool, MFR.Any, sub set)
                end
              else if Term.is_const head andalso
                      is_named {Thy = "relation", Name = "TC"} head andalso
                      length arguments = 1 then
                Op1 (Closure, Term.type_of candidate, MFR.Any,
                  sub (hd arguments))
              else if Term.is_const head andalso
                      is_named {Thy = "relation", Name = "inv"} head andalso
                      length arguments = 1 then
                Op1 (Converse, Term.type_of candidate, MFR.Any,
                  sub (hd arguments))
              else if Term.is_const head andalso
                      is_named {Thy = "relation", Name = "O"} head andalso
                      length arguments = 2 then
                (* HOL4's R1 O R2 applies R2 first.  Composition's internal
                   operands are ordered source-to-target, so reverse the
                   surface arguments (essential for heterogeneous relations). *)
                Op2 (Composition, Term.type_of candidate, MFR.Any,
                  sub (List.nth (arguments, 1)), sub (hd arguments))
              else if Term.is_const head andalso
                      is_named {Thy = "refute", Name = "is_unknown"} head
                      andalso length arguments = 1 then
                Op1 (IsUnknown, Type.bool, MFR.Any, sub (hd arguments))
              else if Term.is_const head andalso
                      is_named {Thy = "refute", Name = "safe_The"} head
                      andalso length arguments = 1 then
                Op1 (SafeThe, Term.type_of candidate, MFR.Any,
                  sub (hd arguments))
              else if (is_named {Thy = "prim_rec", Name = "<"} head orelse
                       is_named {Thy = "integer", Name = "int_lt"} head orelse
                       is_named {Thy = "arithmetic", Name = "<="} head orelse
                       is_named {Thy = "integer", Name = "int_le"} head)
                      andalso length arguments < 2 then
                sub (MFH.eta_expand candidate (2 - length arguments))
              else if (is_named {Thy = "prim_rec", Name = "<"} head orelse
                       is_named {Thy = "integer", Name = "int_lt"} head)
                      andalso length arguments = 2 then
                Op2 (Less, Type.bool, MFR.Any,
                  sub (hd arguments), sub (List.nth (arguments, 1)))
              else if (is_named {Thy = "arithmetic", Name = "<="} head orelse
                       is_named {Thy = "integer", Name = "int_le"} head)
                      andalso length arguments = 2 then
                (* As in Nitpick, whose own comment here is "FIXME: find
                   out if this case is necessary".  Both tools admit <=
                   only at linearly ordered carriers, where ~(y < x) is
                   x <= y. *)
                Op1 (Not, Type.bool, MFR.Any,
                  Op2 (Less, Type.bool, MFR.Any,
                    sub (List.nth (arguments, 1)), sub (hd arguments)))
              else if (is_named {Thy = "gcd", Name = "gcd"} head orelse
                       is_named {Thy = "refute", Name = "nat_gcd"} head)
                      andalso null arguments then
                Cst (Gcd, Term.type_of head, MFR.Any)
              else if (is_named {Thy = "gcd", Name = "lcm"} head orelse
                       is_named {Thy = "refute", Name = "nat_lcm"} head)
                      andalso null arguments then
                Cst (Lcm, Term.type_of head, MFR.Any)
              else if is_named {Thy = "refute", Name = "Frac"} head andalso
                      null arguments then
                Cst (Fracs, Term.type_of head, MFR.Any)
              else if is_named {Thy = "refute", Name = "norm_frac"} head
                      andalso null arguments then
                Cst (NormFrac, Term.type_of head, MFR.Any)
              else if is_named {Thy = "integer", Name = "int_neg"} head andalso
                      null arguments then
                let val number_ty = domain_type (Term.type_of head)
                in
                  Op2 (Apply, Type.-->(number_ty, number_ty), MFR.Any,
                    Cst (Subtract,
                      Type.-->(number_ty, Type.-->(number_ty, number_ty)),
                      MFR.Any),
                    Cst (Num 0, number_ty, MFR.Any))
                end
              else if is_named {Thy = "integer", Name = "int_of_num"} head
                      andalso null arguments then
                Cst (NatToInt, Term.type_of head, MFR.Any)
              else if is_named {Thy = "integer", Name = "Num"} head andalso
                      null arguments then
                Cst (IntToNat, Term.type_of head, MFR.Any)
              else if Option.isSome (order_of head) then
                let val order = valOf (order_of head) in
                  if length arguments < 2 then
                    sub (MFH.eta_expand candidate (2 - length arguments))
                  (* Both order tables hold only binary relations, so a
                     well-typed term cannot present a third argument and
                     the dropped [= 2] test could not have failed. *)
                  else
                    word_comparison order (sub (hd arguments))
                      (sub (List.nth (arguments, 1)))
                end
              else if null arguments andalso
                      Option.isSome (word_subtract_base_of head) then
                let
                  val word_ty = domain_type (Term.type_of head)
                in
                  word_subtract_from word_ty
                    (valOf (word_subtract_base_of head)
                       (MFH.word_width word_ty))
                end
              else if null arguments andalso Option.isSome (cst_of head) then
                cst (valOf (cst_of head)) head
              else if Term.is_const head andalso
                      is_named {Thy = "refute", Name = "unknown"} head andalso
                      null arguments then
                Cst (Unknown, Term.type_of head, MFR.Any)
              else if (Term.is_const head orelse
                       (Term.is_var head andalso MFN.is_reserved_name
                         (MFN.variable_name head))) andalso
                      null arguments andalso
                      Option.isSome (arithmetic_cst head) then
                cst (valOf (arithmetic_cst head)) head
              else if Term.is_const head andalso
                      is_numeral_skeleton head then
                (* A fully formed numeral was already recognized above, so
                   what reaches here is a skeleton constructor applied to a
                   non-literal, or standing alone as a function value.  The
                   binary skeleton stays built in so that preprocessing
                   cannot expand a literal into unary SUC chains; the
                   arithmetic it denotes is supplied here instead. *)
                sub (expand_numeral_skeleton head arguments)
              else if MFH.is_constr head then
                do_construct head arguments
              else if Term.is_const head then
                (case MFH.arity_of_built_in_const head of
                     SOME arity =>
                       let val missing = arity - length arguments
                       in
                         if missing = 0 then
                           raise Feedback.mk_HOL_ERR
                             "Refute_ModelFinder_Nut" "nut_from_term"
                             "unhandled fully applied built-in constant"
                         else if missing > 0 then
                           sub (MFH.eta_expand candidate missing)
                         else
                           do_apply head arguments
                       end
                   | NONE =>
                       if null arguments then
                         ConstName (const_name head, Term.type_of head,
                           MFR.Any)
                       else
                         do_apply head arguments)
              else if Term.is_var head andalso null arguments then
                (case bound_name head of
                     SOME name => name
                   | NONE =>
                       let val name = MFN.variable_name head
                       in
                         if String.isPrefix MFN.reserved_prefix name then
                           ConstName (name, Term.type_of head, MFR.Any)
                         else
                           FreeName (name, Term.type_of head, MFR.Any)
                       end)
              else if Term.is_abs candidate then
                let
                  val (variable, body) = Term.dest_abs candidate
                  val (bound, body_nut) = bind variable body
                in
                  Op2 (Lambda, Term.type_of candidate, MFR.Any,
                    bound, body_nut)
                end

              else if not (null arguments) then
                do_apply head arguments
              else
                raise Feedback.mk_HOL_ERR "Refute_ModelFinder_Nut"
                  "nut_from_term" "unsupported HOL term"))
        end
    in
      aux equality [] term
    end

  fun is_selector_like name =
    MFN.is_sel name andalso MFN.sel_no_from_name name >= 0

  fun is_fully_representable_set nut =
    not (MFR.is_opt_rep (rep_of nut)) andalso
    case nut of
        FreeName _ => true
      | Op1 (SingletonSet, _, _, _) => true
      | Op1 (Converse, _, _, inner) => is_fully_representable_set inner
      | Op2 (Lambda, _, _, _, Cst (False, _, _)) => true
      | Op2 (Apply, _, _, ConstName (name, _, _), _) =>
          is_selector_like name orelse
          MFN.original_name name = "list$LIST_TO_SET"
      | _ => false

  fun choose_rep_for_free_var scope variable (variables, table) =
    let
      val representation = MFR.best_non_opt_set_rep_for_type scope
        (type_of variable)
      val variable = modify_name_rep variable representation
    in
      (variable :: variables,
       NameTable.update (variable, representation) table)
    end

  fun is_set_rule_constant name =
    List.exists (fn special => MFN.original_name name = special)
      ["list$LIST_TO_SET", "list$ALL_DISTINCT", "prim_rec$<",
       "arithmetic$<=", "integer$int_lt", "integer$int_le"]

  fun choose_rep_for_const scope total_consts constant (constants, table) =
    let
      val name = nickname_of constant
      val ty = type_of constant
      val original = MFN.original_name name
      val representation =
        if total_consts orelse is_skolem_name constant orelse
           original = "refute$bisim" orelse
           original = "refute$bisim_iterator_max" then
          MFR.best_non_opt_set_rep_for_type scope ty
        else if is_set_rule_constant name then
          MFR.best_set_rep_for_type scope ty
        else
          MFR.best_opt_set_rep_for_type scope ty
      val constant = modify_name_rep constant representation
    in
      (constant :: constants,
       NameTable.update (constant, representation) table)
    end

  (* Upstream's pseudo_frees parameter is absent: nitpick.ML hardwires it
     to [], so both of its consumers, choose_rep_for_free_var and the
     model printer, always see the empty list. *)
  fun choose_reps_for_free_vars scope variables table =
    List.foldl (fn (variable, result) =>
      choose_rep_for_free_var scope variable result)
      ([], table) variables

  fun choose_reps_for_consts scope total_consts constants table =
    List.foldl (fn (constant, result) =>
      choose_rep_for_const scope total_consts constant result)
      ([], table) constants

  fun generated_names_for_constructor scope constructor =
    let
      val raw_arguments = MFH.constructor_arg_types constructor
      val flattened = List.concat (map factor_types raw_arguments)
      val selectors =
        if length raw_arguments = length flattened then
          MFH.binarized_and_boxed_nth_sel_for_constr
            (#hol_ctxt scope) (#binarize scope) constructor ~1 ::
          List.tabulate (length raw_arguments, fn index =>
            MFH.binarized_and_boxed_nth_sel_for_constr
              (#hol_ctxt scope) (#binarize scope) constructor index)
        else selector_names_for constructor
    in
      map (fn selector => ConstName (MFN.variable_name selector,
        Term.type_of selector, MFR.Any)) selectors
    end

  fun choose_rep_for_selector scope index selector (selectors, table) =
    let
      val ty = type_of selector
      val special = index = ~1 orelse
        MFH.is_bitword_type (domain_type ty) orelse
        (MFH.is_fun_type (range_type ty) andalso
         MFH.is_boolean_type (body_type (range_type ty)))
      val representation =
        if special then MFR.best_non_opt_set_rep_for_type scope ty
        else MFR.unopt_rep (MFR.best_opt_set_rep_for_type scope ty)
      val selector = modify_name_rep selector representation
    in
      (selector :: selectors,
       NameTable.update (selector, representation) table)
    end

  fun choose_reps_for_constructor scope constructor result =
    let val selectors = generated_names_for_constructor scope constructor
    in
      List.foldr (fn ((index, selector), current) =>
        choose_rep_for_selector scope (index - 1) selector current)
        result
        (ListPair.zip
          (List.tabulate (length selectors, fn index => index), selectors))
    end

  fun choose_reps_for_data_type scope
        (spec : MFS.data_type_spec) result =
    if not (#deep spec) then result
    else List.foldr (fn (constructor_spec, current) =>
      choose_reps_for_constructor scope (#const constructor_spec) current)
      result (#constrs spec)

  fun choose_reps_for_all_sels
        (scope as {data_types, ...} : scope) table =
    List.foldl (fn (spec, result) =>
      choose_reps_for_data_type scope spec result)
      ([], table) data_types

  val min_univ_card = 2

  fun choose_rep_for_bound_var scope variable table =
    let
      val representation = MFR.best_one_rep_for_type scope (type_of variable)
      val arity = MFR.arity_of_rep representation
    in
      if arity > Refute_Forl.max_arity min_univ_card then
        raise Util.TOO_LARGE
          ("Refute_ModelFinder_Nut.choose_rep_for_bound_var",
           "arity " ^ Int.toString arity ^ " of bound variable too large")
      else
        NameTable.update (variable, representation) table
    end

  fun is_constructive nut =
    is_Cst Unrep nut orelse
    (not (MFH.is_fun_type (type_of nut)) andalso
     not (MFR.is_opt_rep (rep_of nut))) orelse
    case nut of
        Cst (Num _, _, _) => true
      | Cst (constant, ty, _) =>
          body_type ty = MFH.num_type andalso
          (constant = Suc orelse constant = Add)
      | Op2 (Apply, _, _, first, second) =>
          List.all is_constructive [first, second]
      | Op3 (If, _, _, condition, left, right) =>
          not (MFR.is_opt_rep (rep_of condition)) andalso
          List.all is_constructive [left, right]
      | Tuple (_, _, nuts) => List.all is_constructive nuts
      | Construct (_, _, _, nuts) => List.all is_constructive nuts
      | _ => false

  (* Kodkod reads a word atom's value from its universe index, which is that
     atom's Kodkod integer only while the integer bounds stay sequential, and
     computes in a fixed integer width.  Binary integers replace the bounds
     with powers of two, and a width the integers cannot hold would wrap in
     Kodkod's arithmetic rather than the word's, so both refuse by name
     instead of encoding something else. *)
  (* [product] covers the operations whose unwrapped result is twice as wide
     as an operand: multiplication and the left shift.  The integer width is
     sized for the widest word of the scope, so the second refusal is a check
     on that sizing rather than a limit users meet. *)
  fun check_word_budget scope product ty =
    case MFH.word_op_dimension ty of
        NONE => ()
      | SOME width =>
          if #binarize scope then
            raise Util.NOT_SUPPORTED
              "word operations are not encoded with binary integers"
          else
            let
              val needed = (if product then 2 * width else width + 1) + 1
            in
              if needed >
                 MFP.bit_width_for (#bits scope) (MFS.max_word_width scope)
              then
                raise Util.NOT_SUPPORTED
                  ("word width " ^ Int.toString width ^ " needs " ^
                   Int.toString needed ^ " integer bits")
              else ()
            end

  (* The char carrier is read the same way as a word one, so it needs the same
     sequential [int_bounds].  Its 256 atoms always fit the integer width. *)
  fun check_char_budget scope ty =
    if MFH.is_char_op_type ty andalso #binarize scope then
      raise Util.NOT_SUPPORTED
        "char operations are not encoded with binary integers"
    else ()

  (* Both halves in one place: each is a no-op at the carrier it does not
     name, so an operation added to the dispatch below cannot check one
     carrier and silently skip the other. *)
  fun check_carrier_budget scope product ty =
    (check_word_budget scope product ty; check_char_budget scope ty)

  fun unknown_boolean ty representation =
    Cst (case representation of
             MFR.Formula Util.Pos => False
           | MFR.Formula Util.Neg => True
           | _ => Unknown,
         ty, representation)

  fun s_op1 operator ty representation first =
    ((if operator = Not then
        if is_Cst True first then Cst (False, ty, representation)
        else if is_Cst False first then Cst (True, ty, representation)
        else raise Util.SAME ()
      else raise Util.SAME ())
     handle Util.SAME () => Op1 (operator, ty, representation, first))

  fun s_op2 operator ty representation first second =
    ((case operator of
          All => if is_subnut_of first second then
                   Op2 (All, ty, representation, first, second)
                 else second
        | Exist => if is_subnut_of first second then
                     Op2 (Exist, ty, representation, first, second)
                   else second
        | Or =>
            if List.exists (is_Cst True) [first, second] then
              Cst (True, ty, MFR.unopt_rep representation)
            else if is_Cst False first then second
            else if is_Cst False second then first
            else raise Util.SAME ()
        | And =>
            if List.exists (is_Cst False) [first, second] then
              Cst (False, ty, MFR.unopt_rep representation)
            else if is_Cst True first then second
            else if is_Cst True second then first
            else raise Util.SAME ()
        | Eq =>
            (case (is_Cst Unrep first, is_Cst Unrep second) of
                 (true, true) => unknown_boolean ty representation
               | (false, false) => raise Util.SAME ()
               | _ =>
                   if List.all (MFR.is_opt_rep o rep_of) [first, second] then
                     raise Util.SAME ()
                   else Cst (False, ty, MFR.Formula Util.Neut))
        | Triad =>
            if is_Cst True first then first
            else if is_Cst False second then second
            else raise Util.SAME ()
        | Apply =>
            if is_Cst Unrep first then Cst (Unrep, ty, representation)
            else if is_Cst Unrep second then
              if MFH.is_boolean_type ty then
                if is_fully_representable_set first then
                  Cst (False, ty, MFR.Formula Util.Neut)
                else unknown_boolean ty representation
              else if is_constructive first then
                Cst (Unrep, ty, representation)
              else
                (case first of
                     Op2 (Apply, _, _,
                       ConstName (name, _, _), _) =>
                         if MFN.original_name name = "list$APPEND" then
                           Cst (Unrep, ty, representation)
                         else raise Util.SAME ()
                   | _ => raise Util.SAME ())
            else raise Util.SAME ()
        | _ => raise Util.SAME ())
     handle Util.SAME () =>
       Op2 (operator, ty, representation, first, second))

  fun s_op3 operator ty representation first second third =
    ((case operator of
          Let =>
            if inline_nut second orelse
               num_occurrences_in_nut first third < 2 then
              substitute_in_nut first second third
            else raise Util.SAME ()
        | _ => raise Util.SAME ())
     handle Util.SAME () =>
       Op3 (operator, ty, representation, first, second, third))

  fun s_tuple ty representation nuts =
    if List.exists (is_Cst Unrep) nuts then
      Cst (Unrep, ty, representation)
    else
      Tuple (ty, representation, nuts)

  fun untuple f (Tuple (_, _, nuts)) = List.concat (map (untuple f) nuts)
    | untuple f nut = [f nut]

  fun constructor_for_construct data_types selectors ty =
    let
      val original = MFN.original_name (nickname_of (hd selectors))
      fun matches (spec : MFS.constr_spec) =
        MFH.constructor_name (#const spec) = original andalso
        MFH.constructor_result_type (#const spec) = ty
      fun search [] = NONE
        | search ((data_type : MFS.data_type_spec) :: rest) =
            (case List.find matches (#constrs data_type) of
                 SOME spec => SOME (#const spec)
               | NONE => search rest)
    in
      case search data_types of
          SOME constructor => constructor
        | NONE => raise NUT
            ("Refute_ModelFinder_Nut.constructor_for_construct", selectors)
    end

  fun choose_reps_in_nut
        (scope as {card_assigns, data_types, ofs, ...} : scope)
        unsound table definition nut =
    let
      val bool_atom = MFR.Atom (2, MFS.offset_of_type ofs Type.bool)
      fun bool_rep polarity optional =
        if polarity = Util.Neut andalso optional then MFR.Opt bool_atom
        else MFR.Formula polarity
      fun unknown_boolean constant ty polarity =
        let val effective_polarity =
          if unsound then Util.flip_polarity polarity else polarity
        in
          case effective_polarity of
              Util.Pos => Cst (False, ty, MFR.Formula Util.Pos)
            | Util.Neg => Cst (True, ty, MFR.Formula Util.Neg)
            | Util.Neut => Cst (constant, ty, MFR.Opt bool_atom)
        end
      fun triad first second =
        s_op2 Triad (type_of first) (MFR.Opt bool_atom) first second
      fun triad_fn f = triad (f Util.Pos) (f Util.Neg)
      fun unrepify table definition polarity needle body =
        let val ty = type_of needle
        in
          aux table definition polarity
            (substitute_in_nut needle
              (Cst (if MFH.is_fun_type ty then Unknown else Unrep,
                    ty, MFR.Any)) body)
        end
      and aux table definition polarity candidate =
        let
          fun gsub definition polarity item =
            aux table definition polarity item
          fun sub item = gsub false Util.Neut item
        in
          case candidate of
              Cst (False, ty, _) =>
                Cst (False, ty, MFR.Formula Util.Neut)
            | Cst (True, ty, _) =>
                Cst (True, ty, MFR.Formula Util.Neut)
            | Cst (Num value, ty, _) =>
                if MFH.is_bitword_type ty then
                  let
                    val representation =
                      MFR.best_opt_set_rep_for_type scope ty
                  in
                    Cst (if MFP.is_twos_complement_representable
                               (#bits scope) value
                         then Num value else Unrep,
                      ty, representation)
                  end
                else
                  let
                    val (cardinality, offset) = MFS.spec_of_type scope ty
                    val representable =
                      if ty = MFH.int_type then
                        MFP.atom_for_int (cardinality, offset) value <> ~1
                      else value >= 0 andalso value < cardinality
                    val atom = MFR.Atom (cardinality, offset)
                  in
                    if representable then Cst (Num value, ty, atom)
                    else Cst (Unrep, ty, MFR.Opt atom)
                  end
            | Cst (Suc, ty, _) =>
                let val atom = MFR.Atom
                  (MFS.spec_of_type scope (domain_type ty))
                in Cst (Suc, ty, MFR.Func (atom, MFR.Opt atom)) end
            | Cst (Fracs, ty, _) =>
                Cst (Fracs, ty, MFR.best_non_opt_set_rep_for_type scope ty)
            | Cst (NormFrac, ty, _) =>
                let val atom = MFR.Atom
                  (MFS.spec_of_type scope (domain_type ty))
                in
                  Cst (NormFrac, ty,
                    MFR.Func (atom,
                      MFR.Func (atom, MFR.Opt (MFR.Struct [atom, atom]))))
                end
            | Cst (constant, ty, _) =>
                if constant = Unknown orelse constant = Unrep then
                  if MFH.is_boolean_type ty then
                    unknown_boolean constant ty polarity
                  else
                    Cst (constant, ty,
                      MFR.best_opt_set_rep_for_type scope ty)
                else if Lib.mem constant
                    [Add, Subtract, Multiply, Divide, Gcd, Lcm] then
                  let
                    val _ = check_carrier_budget scope
                      (constant = Multiply) ty
                    val number_ty = domain_type ty
                    val atom = MFR.Atom (MFS.spec_of_type scope number_ty)
                    (* The modular ring is total at a word type: every
                       operation wraps into the carrier. *)
                    val total = MFH.is_word_type number_ty orelse
                      (number_ty = MFH.num_type andalso
                       (constant = Subtract orelse constant = Divide orelse
                        constant = Gcd))
                    val range = if total then atom else MFR.Opt atom
                  in Cst (constant, ty,
                       MFR.Func (atom, MFR.Func (atom, range))) end
                else if Lib.mem constant
                    [NatToWord, WordToNat, NatToChar, CharToNat] then
                  let
                    val _ = check_carrier_budget scope false ty
                    val (domain_card, domain_offset) =
                      MFS.spec_of_type scope (domain_type ty)
                    val (range_card, range_offset) =
                      MFS.spec_of_type scope (range_type ty)
                    (* [n2w] wraps, so it is total whatever the carriers are.
                       [w2n] needs a numeric carrier holding every word value;
                       [CHR] is unspecified at or above 256 and [ORD] needs a
                       [num] carrier holding every code, so those three are
                       total exactly when the domain fits the range. *)
                    val total = constant = NatToWord orelse
                      domain_card <= range_card
                    val range = MFR.Atom (range_card, range_offset)
                  in
                    Cst (constant, ty,
                      MFR.Func (MFR.Atom (domain_card, domain_offset),
                        if total then range else MFR.Opt range))
                  end
                else if Lib.mem constant [WordAnd, WordOr, WordXor] then
                  let
                    val _ = check_carrier_budget scope false ty
                    val atom = MFR.Atom
                      (MFS.spec_of_type scope (domain_type ty))
                  in
                    Cst (constant, ty,
                      MFR.Func (atom, MFR.Func (atom, atom)))
                  end
                else if Lib.mem constant [WordShl, WordShr, WordAsr] then
                  let
                    val _ = check_carrier_budget scope (constant = WordShl) ty
                    val word_atom = MFR.Atom
                      (MFS.spec_of_type scope (domain_type ty))
                    val count_atom = MFR.Atom
                      (MFS.spec_of_type scope
                        (domain_type (range_type ty)))
                  in
                    Cst (constant, ty,
                      MFR.Func (word_atom, MFR.Func (count_atom, word_atom)))
                  end
                else if constant = NatToInt orelse constant = IntToNat then
                  let
                    val (domain_card, domain_offset) =
                      MFS.spec_of_type scope (domain_type ty)
                    val (range_card, range_offset) =
                      MFS.spec_of_type scope (range_type ty)
                    (* The largest nat atom is [domain_card - 1]; Nitpick
                       asks for [domain_card + 1] and so refuses two
                       total instances per scope. *)
                    val total =
                      not (MFH.is_bitword_type (domain_type ty)) andalso
                      (if constant = NatToInt then
                         MFP.max_int_for_card range_card >= domain_card - 1
                       else
                         MFP.max_int_for_card domain_card < range_card)
                    val range = MFR.Atom (range_card, range_offset)
                  in
                    Cst (constant, ty,
                      MFR.Func (MFR.Atom (domain_card, domain_offset),
                        if total then range else MFR.Opt range))
                  end
                else
                  Cst (constant, ty, MFR.best_set_rep_for_type scope ty)
            | Op1 (Not, ty, _, first) =>
                (case gsub definition (Util.flip_polarity polarity) first of
                     Op2 (Triad, _, _, positive, negative) =>
                       triad
                         (s_op1 Not ty (MFR.Formula Util.Pos) negative)
                         (s_op1 Not ty (MFR.Formula Util.Neg) positive)
                   | first' => s_op1 Not ty
                       (MFR.flip_rep_polarity (rep_of first')) first')
            | Op1 (IsUnknown, ty, _, first) =>
                let val first' = sub first
                in
                  if MFR.is_opt_rep (rep_of first') then
                    Op1 (IsUnknown, ty, MFR.Formula Util.Neut, first')
                  else Cst (False, ty, MFR.Formula Util.Neut)
                end
            | Op1 (operator, ty, _, first) =>
                let
                  val first' = sub first
                  val optional = MFR.is_opt_rep (rep_of first')
                  val representation =
                    if operator = Finite then
                      bool_rep polarity optional
                    else if optional then
                      MFR.best_opt_set_rep_for_type scope ty
                    else MFR.best_non_opt_set_rep_for_type scope ty
                in
                  (* [deviation from upstream] optional FINITE is the same
                     unknown Boolean as Cst Unknown, including the unsound
                     sibling's polarity flip. *)
                  if operator = Finite andalso optional andalso
                     polarity <> Util.Neut
                  then unknown_boolean Unknown ty polarity
                  else s_op1 operator ty representation first'
                end
            | Op2 (Less, ty, _, first, second) =>
                let
                  val _ = check_carrier_budget scope false (type_of first)
                  val first' = sub first
                  val second' = sub second
                  val optional = List.exists
                    (MFR.is_opt_rep o rep_of) [first', second']
                in
                  s_op2 Less ty (bool_rep polarity optional) first' second'
                end
            | Op2 (DefEq, ty, _, first, second) =>
                s_op2 DefEq ty (MFR.Formula Util.Neut)
                  (sub first) (sub second)
            | Op2 (Eq, ty, _, first, second) =>
                let
                  val first' = sub first
                  val second' = sub second
                  fun non_opt_case () =
                    s_op2 Eq ty (MFR.Formula polarity) first' second'
                  fun opt_opt_case () =
                    if polarity = Util.Neut then
                      triad_fn (fn p =>
                        s_op2 Eq ty (MFR.Formula p) first' second')
                    else non_opt_case ()
                  fun hybrid_case optional_side =
                    if is_constructive optional_side then
                      s_op2 Eq ty (MFR.Formula Util.Neut) first' second'
                    else opt_opt_case ()
                in
                  if unsound orelse polarity = Util.Neg orelse
                     MFS.is_concrete_type data_types true (type_of first) then
                    case (MFR.is_opt_rep (rep_of first'),
                          MFR.is_opt_rep (rep_of second')) of
                        (true, true) => opt_opt_case ()
                      | (true, false) => hybrid_case first'
                      | (false, true) => hybrid_case second'
                      | (false, false) => non_opt_case ()
                  else
                    let val positive =
                      Cst (False, ty, MFR.Formula Util.Pos)
                    in
                      if polarity = Util.Neut then
                        triad positive (gsub definition Util.Neg candidate)
                      else positive
                    end
                end
            | Op2 (Apply, ty, _, first, second) =>
                let
                  val first' = sub first
                  val second' = sub second
                  val function_ty = type_of first'
                  val function_rep = rep_of first'
                  val optional =
                    (case first' of
                         ConstName (name, _, _) =>
                           if MFN.original_name name =
                                "list$LIST_TO_SET" andalso
                              not (MFR.is_opt_rep (rep_of second')) then
                             false
                           else MFR.is_opt_rep function_rep orelse
                             MFR.is_opt_rep (rep_of second')
                       | _ => MFR.is_opt_rep function_rep orelse
                           MFR.is_opt_rep (rep_of second'))
                  val range_rep =
                    if MFH.is_boolean_type ty then
                      bool_rep polarity optional
                    else
                      let val base = MFR.lazy_range_rep ofs function_ty
                        (fn () => MFH.card_of_type card_assigns ty)
                        (MFR.unopt_rep function_rep)
                      in
                        if optional then MFR.opt_rep ofs ty base else base
                      end
                in s_op2 Apply ty range_rep first' second' end
            | Op2 (Lambda, ty, _, binder, body) =>
                (case MFR.best_set_rep_for_type scope ty of
                     representation as MFR.Func (domain_rep, _) =>
                       let
                         val table' = NameTable.update
                           (binder, domain_rep) table
                         val binder' = aux table' false Util.Neut binder
                         val body' = aux table' false Util.Neut body
                         val representation' =
                           if MFR.is_opt_rep (rep_of body') then
                             MFR.opt_rep ofs ty representation
                           else MFR.unopt_rep representation
                       in
                         s_op2 Lambda ty representation' binder' body'
                       end
                   | _ => raise NUT
                       ("Refute_ModelFinder_Nut.choose_reps_in_nut",
                        [candidate]))
            | Op2 (operator, ty, _, binder, body) =>
                if operator = All orelse operator = Exist then
                  let
                    val table' = List.foldl
                      (fn (variable, current) =>
                        choose_rep_for_bound_var scope variable current)
                      table (untuple (fn item => item) binder)
                    val binder' = aux table' definition polarity binder
                    val body' = aux table' definition polarity body
                  in
                    if polarity = Util.Neut andalso
                       MFR.is_opt_rep (rep_of body') then
                      triad_fn (fn p => gsub definition p candidate)
                    else
                      let
                        val quantified = s_op2 operator ty
                          (MFR.Formula polarity) binder' body'
                        val omit_guard = definition orelse
                          (unsound andalso
                           ((polarity = Util.Pos) = (operator = All))) orelse
                          MFS.is_complete_type data_types true
                            (type_of binder)
                      in
                        if omit_guard then quantified
                        else
                          let
                            val connective =
                              if operator = All then And else Or
                            val unrepified = unrepify table definition
                              polarity binder body
                          in
                            s_op2 connective ty
                              (MFR.min_rep (rep_of quantified)
                                (rep_of unrepified))
                              quantified unrepified
                          end
                      end
                  end
                else if operator = Or orelse operator = And then
                  let
                    val first' = gsub definition polarity binder
                    val second' = gsub definition polarity body
                  in
                    ((if polarity = Util.Neut then
                        case (MFR.is_opt_rep (rep_of first'),
                              MFR.is_opt_rep (rep_of second')) of
                            (true, true) => triad_fn
                              (fn p => gsub definition p candidate)
                          | (true, false) =>
                              s_op2 operator ty (MFR.Opt bool_atom)
                                (triad_fn (fn p =>
                                   gsub definition p binder)) second'
                          | (false, true) =>
                              s_op2 operator ty (MFR.Opt bool_atom) first'
                                (triad_fn (fn p =>
                                   gsub definition p body))
                          | (false, false) => raise Util.SAME ()
                      else raise Util.SAME ())
                     handle Util.SAME () =>
                       s_op2 operator ty (MFR.Formula polarity)
                         first' second')
                  end
                else
                  let
                    val first' = sub binder
                    val second' = sub body
                    val base = MFR.best_non_opt_set_rep_for_type scope ty
                    val optional = List.exists
                      (MFR.is_opt_rep o rep_of) [first', second']
                    val representation =
                      if optional then MFR.opt_rep ofs ty base else base
                  in s_op2 operator ty representation first' second' end
            | Op3 (Let, ty, _, binder, value, body) =>
                let
                  val value' = sub value
                  val value_rep = rep_of value'
                  val table' = NameTable.update (binder, value_rep) table
                  val binder' = modify_name_rep binder value_rep
                  val body' = aux table' false polarity body
                in s_op3 Let ty (rep_of body') binder' value' body' end
            | Op3 (If, ty, _, condition, left, right) =>
                let
                  val condition' = sub condition
                  val left' = gsub definition polarity left
                  val right' = gsub definition polarity right
                  val minimum = MFR.min_rep (rep_of left') (rep_of right')
                  val representation =
                    if MFR.is_opt_rep (rep_of condition') then
                      MFR.opt_rep ofs ty minimum
                    else minimum
                in s_op3 If ty representation condition' left' right' end
            | Tuple (ty, _, nuts) =>
                let
                  val reps = map
                    (MFR.best_one_rep_for_type scope o type_of) nuts
                  val nuts' = map sub nuts
                  val base = MFR.Struct reps
                  val representation =
                    if List.exists (MFR.is_opt_rep o rep_of) nuts' then
                      MFR.opt_rep ofs ty base
                    else base
                in s_tuple ty representation nuts' end
            | Construct (selectors, ty, _, arguments) =>
                let
                  val arguments' = map sub arguments
                  val representation = MFR.best_one_rep_for_type scope ty
                  val constructor = constructor_for_construct
                    data_types selectors ty
                  val spec = MFS.constr_spec data_types constructor
                  val optional = not (#total spec) orelse
                    List.exists (MFR.is_opt_rep o rep_of) arguments'
                in
                  Construct (map sub selectors, ty,
                    if optional then MFR.Opt representation
                    else representation, arguments')
                end
            | _ =>
                let
                  val representation = the_name table candidate
                  val named = modify_name_rep candidate representation
                in
                  if polarity = Util.Neut orelse
                     not (MFH.is_boolean_type (type_of named)) orelse
                     not (MFR.is_opt_rep representation) then
                    named
                  else
                    s_op1 Cast (type_of named) (MFR.Formula polarity) named
                end
        end
    in
      aux table definition Util.Pos nut
    end

  fun fresh_n_ary_index arity [] previous =
        (0, (arity, 1) :: previous)
    | fresh_n_ary_index arity ((other, index) :: rest) previous =
        if other = arity then
          (index, previous @ ((other, index + 1) :: rest))
        else
          fresh_n_ary_index arity rest ((other, index) :: previous)

  fun fresh_rel arity
        ({rels, vars, formula_reg, rel_reg} : name_pool) =
    let val (index, rels') = fresh_n_ary_index arity rels []
    in
      (index, {rels = rels', vars = vars, formula_reg = formula_reg,
               rel_reg = rel_reg})
    end

  fun fresh_var arity
        ({rels, vars, formula_reg, rel_reg} : name_pool) =
    let val (index, vars') = fresh_n_ary_index arity vars []
    in
      (index, {rels = rels, vars = vars', formula_reg = formula_reg,
               rel_reg = rel_reg})
    end

  fun fresh_formula_reg
        ({rels, vars, formula_reg, rel_reg} : name_pool) =
    (formula_reg,
     {rels = rels, vars = vars, formula_reg = formula_reg + 1,
      rel_reg = rel_reg})

  fun fresh_rel_reg
        ({rels, vars, formula_reg, rel_reg} : name_pool) =
    (rel_reg,
     {rels = rels, vars = vars, formula_reg = formula_reg,
      rel_reg = rel_reg + 1})

  fun rename_plain_var variable (variables, pool, table) =
    let
      val is_formula = rep_of variable = MFR.Formula Util.Neut
      val (index, pool') =
        if is_formula then fresh_formula_reg pool else fresh_rel_reg pool
      val renamed =
        if is_formula then
          FormulaReg (index, type_of variable, rep_of variable)
        else
          RelReg (index, type_of variable, rep_of variable)
    in
      (renamed :: variables, pool',
       NameTable.update (variable, renamed) table)
    end

  fun shape_tuple ty (representation as MFR.Struct [left_rep, right_rep])
        nuts =
        if MFH.is_pair_type ty then
          let
            val (left_ty, right_ty) = pairSyntax.dest_prod ty
            val left_arity = MFR.arity_of_rep left_rep
            val left = List.take (nuts, left_arity)
            val right = List.drop (nuts, left_arity)
          in
            Tuple (ty, representation,
              [shape_tuple left_ty left_rep left,
               shape_tuple right_ty right_rep right])
          end
        else raise NUT ("Refute_ModelFinder_Nut.shape_tuple", nuts)
    | shape_tuple ty (representation as MFR.Vect (count, element_rep))
        nuts =
        let
          val range_ty = range_type ty
          val chunk_size = length nuts div count
        in
          Tuple (ty, representation,
            map (shape_tuple range_ty element_rep)
              (Util.chunk_list chunk_size nuts))
        end
    | shape_tuple ty _ [nut] =
        if type_of nut = ty then nut
        else raise NUT ("Refute_ModelFinder_Nut.shape_tuple", [nut])
    | shape_tuple _ _ nuts =
        raise NUT ("Refute_ModelFinder_Nut.shape_tuple", nuts)

  fun rename_n_ary_var rename_free variable (variables, pool, table) =
    let
      val ty = type_of variable
      val representation = rep_of variable
      val arity = MFR.arity_of_rep representation
      val nickname = nickname_of variable
      fun construct index item_ty item_rep item_nickname =
        if rename_free then
          FreeRel (index, item_ty, item_rep, item_nickname)
        else
          BoundRel (index, item_ty, item_rep, item_nickname)
      fun fresh arity pool =
        if rename_free then fresh_rel arity pool else fresh_var arity pool
    in
      if not rename_free andalso arity > 1 then
        let
          val atom_schema = MFR.atom_schema_of_rep representation
          val type_schema = MFR.type_schema_of_rep ty representation
          fun allocate (indices, current_pool) =
            let val (index, next_pool) = fresh 1 current_pool
            in (index :: indices, next_pool) end
          val (reversed_indices, pool') =
            Lib.funpow arity allocate ([], pool)

          val indices = rev reversed_indices
          val renamed = ListPair.mapEq
            (fn (index, (atom, item_ty)) =>
              construct (1, index) item_ty (MFR.Atom atom)
                (nickname ^ " [" ^ Int.toString index ^ "]"))
            (indices, ListPair.zip (atom_schema, type_schema))
          val shaped = shape_tuple ty representation renamed
        in
          (renamed @ variables, pool',
           NameTable.update (variable, shaped) table)
        end
      else
        let
          val fixed =
            case variable of
                ConstName _ =>
                  if is_selector_like nickname andalso
                     MFH.is_bitword_type (domain_type ty) then
                    SOME (if domain_type ty = MFH.unsigned_bitword_type then
                            #2 MFP.unsigned_bit_word_sel_rel
                          else #2 MFP.signed_bit_word_sel_rel)
                  else NONE
              | _ => NONE
          val (index, pool') =
            case fixed of SOME index => (index, pool) | NONE => fresh arity pool
          val renamed = construct (arity, index) ty representation nickname
        in
          (renamed :: variables, pool',
           NameTable.update (variable, renamed) table)
        end
    end

  fun rename_free_vars variables pool table =
    let
      val (reversed, pool', table') = List.foldl
        (fn (variable, result) => rename_n_ary_var true variable result)
        ([], pool, table) variables
    in
      (rev reversed, pool', table')
    end

  fun rename_vars_in_nut pool table nut =
    case nut of
        Cst _ => nut
      | Op1 (operator, ty, representation, first) =>
          Op1 (operator, ty, representation,
            rename_vars_in_nut pool table first)
      | Op2 (operator, ty, representation, first, second) =>
          if operator = All orelse operator = Exist orelse
             operator = Lambda then
            let
              val (_, pool', table') = List.foldl
                (fn (variable, result) =>
                  rename_n_ary_var false variable result)
                ([], pool, table) (untuple (fn item => item) first)
            in
              Op2 (operator, ty, representation,
                rename_vars_in_nut pool' table' first,
                rename_vars_in_nut pool' table' second)
            end
          else
            Op2 (operator, ty, representation,
              rename_vars_in_nut pool table first,
              rename_vars_in_nut pool table second)
      | Op3 (Let, ty, representation, binder, value, body) =>
          if inline_nut value then
            let
              val value' = rename_vars_in_nut pool table value
              val table' = NameTable.update (binder, value') table
            in
              rename_vars_in_nut pool table' body
            end
          else
            let
              val (_, pool', table') = List.foldl
                (fn (variable, result) => rename_plain_var variable result)
                ([], pool, table) (untuple (fn item => item) binder)
            in
              Op3 (Let, ty, representation,
                rename_vars_in_nut pool' table' binder,
                rename_vars_in_nut pool table value,
                rename_vars_in_nut pool' table' body)
            end
      | Op3 (operator, ty, representation, first, second, third) =>
          Op3 (operator, ty, representation,
            rename_vars_in_nut pool table first,
            rename_vars_in_nut pool table second,
            rename_vars_in_nut pool table third)
      | Tuple (ty, representation, nuts) =>
          Tuple (ty, representation,
            map (rename_vars_in_nut pool table) nuts)
      | Construct (selectors, ty, representation, arguments) =>
          Construct (map (rename_vars_in_nut pool table) selectors,
            ty, representation,
            map (rename_vars_in_nut pool table) arguments)
      | _ => the_name table nut
end
