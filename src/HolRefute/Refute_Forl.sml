signature REFUTE_FORL = sig
  type n_ary_index = int * int
  type setting = string * string

  datatype tuple =
    Tuple of int list
  | TupleIndex of n_ary_index
  | TupleReg of n_ary_index

  datatype tuple_set =
    TupleUnion of tuple_set * tuple_set
  | TupleDifference of tuple_set * tuple_set
  | TupleIntersect of tuple_set * tuple_set
  | TupleProduct of tuple_set * tuple_set
  | TupleProject of tuple_set * int
  | TupleSet of tuple list
  | TupleRange of tuple * tuple
  | TupleArea of tuple * tuple
  | TupleAtomSeq of int * int
  | TupleSetReg of n_ary_index

  datatype tuple_assign =
    AssignTuple of n_ary_index * tuple
  | AssignTupleSet of n_ary_index * tuple_set

  type bound = (n_ary_index * string) list * tuple_set list
  type int_bound = int option * tuple_set list

  datatype formula =
    All of decl list * formula
  | Exist of decl list * formula
  | FormulaLet of expr_assign list * formula
  | FormulaIf of formula * formula * formula
  | Or of formula * formula
  | Iff of formula * formula
  | Implies of formula * formula
  | And of formula * formula
  | Not of formula
  | Acyclic of n_ary_index
  | Function of n_ary_index * rel_expr * rel_expr
  | Functional of n_ary_index * rel_expr * rel_expr
  | TotalOrdering of n_ary_index * rel_expr * rel_expr * rel_expr
  | Subset of rel_expr * rel_expr
  | RelEq of rel_expr * rel_expr
  | IntEq of int_expr * int_expr
  | LT of int_expr * int_expr
  | LE of int_expr * int_expr
  | No of rel_expr
  | Lone of rel_expr
  | One of rel_expr
  | Some of rel_expr
  | False
  | True
  | FormulaReg of int
  and rel_expr =
    RelLet of expr_assign list * rel_expr
  | RelIf of formula * rel_expr * rel_expr
  | Union of rel_expr * rel_expr
  | Difference of rel_expr * rel_expr
  | Override of rel_expr * rel_expr
  | Intersect of rel_expr * rel_expr
  | Product of rel_expr * rel_expr
  | IfNo of rel_expr * rel_expr
  | Project of rel_expr * int_expr list
  | Join of rel_expr * rel_expr
  | Closure of rel_expr
  | ReflexiveClosure of rel_expr
  | Transpose of rel_expr
  | Comprehension of decl list * formula
  | Bits of int_expr
  | Int of int_expr
  | Iden
  | Ints
  | None
  | Univ
  | Atom of int
  | AtomSeq of int * int
  | Rel of n_ary_index
  | Var of n_ary_index
  | RelReg of n_ary_index
  and int_expr =
    Sum of decl list * int_expr
  | IntLet of expr_assign list * int_expr
  | IntIf of formula * int_expr * int_expr
  | SHL of int_expr * int_expr
  | SHA of int_expr * int_expr
  | SHR of int_expr * int_expr
  | Add of int_expr * int_expr
  | Sub of int_expr * int_expr
  | Mult of int_expr * int_expr
  | Div of int_expr * int_expr
  | Mod of int_expr * int_expr
  | Cardinality of rel_expr
  | SetSum of rel_expr
  | BitOr of int_expr * int_expr
  | BitXor of int_expr * int_expr
  | BitAnd of int_expr * int_expr
  | BitNot of int_expr
  | Neg of int_expr
  | Absolute of int_expr
  | Signum of int_expr
  | Num of int
  | IntReg of int
  and decl =
    DeclNo of n_ary_index * rel_expr
  | DeclLone of n_ary_index * rel_expr
  | DeclOne of n_ary_index * rel_expr
  | DeclSome of n_ary_index * rel_expr
  | DeclSet of n_ary_index * rel_expr
  and expr_assign =
    AssignFormulaReg of int * formula
  | AssignRelReg of n_ary_index * rel_expr
  | AssignIntReg of int * int_expr

  type problem =
    {comment : string,
     settings : setting list,
     univ_card : int,
     tuple_assigns : tuple_assign list,
     bounds : bound list,
     int_bounds : int_bound list,
     expr_assigns : expr_assign list,
     formula : formula}

  type 'a fold_expr_funcs =
    {formula_func : formula -> 'a -> 'a,
     rel_expr_func : rel_expr -> 'a -> 'a,
     int_expr_func : int_expr -> 'a -> 'a}

  val fold_formula : 'a fold_expr_funcs -> formula -> 'a -> 'a
  val fold_rel_expr : 'a fold_expr_funcs -> rel_expr -> 'a -> 'a
  val fold_int_expr : 'a fold_expr_funcs -> int_expr -> 'a -> 'a
  val fold_decl : 'a fold_expr_funcs -> decl -> 'a -> 'a
  val fold_expr_assign : 'a fold_expr_funcs -> expr_assign -> 'a -> 'a

  type 'a fold_tuple_funcs =
    {tuple_func : tuple -> 'a -> 'a,
     tuple_set_func : tuple_set -> 'a -> 'a}

  val fold_tuple : 'a fold_tuple_funcs -> tuple -> 'a -> 'a
  val fold_tuple_set : 'a fold_tuple_funcs -> tuple_set -> 'a -> 'a
  val fold_tuple_assign : 'a fold_tuple_funcs -> tuple_assign -> 'a -> 'a
  val fold_bound :
    'a fold_expr_funcs -> 'a fold_tuple_funcs -> bound -> 'a -> 'a
  val fold_int_bound : 'a fold_tuple_funcs -> int_bound -> 'a -> 'a

  val max_arity : int -> int
  val arity_of_rel_expr : rel_expr -> int
  val is_problem_trivially_false : problem -> bool
  val problems_equivalent : problem * problem -> bool

  type raw_bound = n_ary_index * int list list

  datatype outcome =
    Normal of (int * raw_bound list) list * int list * string
  | TimedOut of int list
  | Error of string * int list

  exception SYNTAX of string * string

  val extract_instance : string -> raw_bound list
  val parse_output : string ->
    (int * raw_bound list) list * int list
  val first_error : string -> string

  val production_header : unit -> string
  val write_problem : TextIO.outstream -> string -> problem list -> unit

  (* Shared with Refute_ForlSat, which loads after this structure. *)
  val getenv : string -> string
  val readable_file : string -> bool
  val uname : string -> string
  val platform_name : unit -> string
  val jni_dir : unit -> string

  val is_configured : unit -> bool
  val solve_any_problem :
    bool -> bool -> Time.time -> int -> int -> problem list -> outcome
end

structure Refute_Forl :> REFUTE_FORL = struct
  type n_ary_index = int * int
  type setting = string * string

  datatype tuple =
    Tuple of int list
  | TupleIndex of n_ary_index
  | TupleReg of n_ary_index

  datatype tuple_set =
    TupleUnion of tuple_set * tuple_set
  | TupleDifference of tuple_set * tuple_set
  | TupleIntersect of tuple_set * tuple_set
  | TupleProduct of tuple_set * tuple_set
  | TupleProject of tuple_set * int
  | TupleSet of tuple list
  | TupleRange of tuple * tuple
  | TupleArea of tuple * tuple
  | TupleAtomSeq of int * int
  | TupleSetReg of n_ary_index

  datatype tuple_assign =
    AssignTuple of n_ary_index * tuple
  | AssignTupleSet of n_ary_index * tuple_set

  type bound = (n_ary_index * string) list * tuple_set list
  type int_bound = int option * tuple_set list

  datatype formula =
    All of decl list * formula
  | Exist of decl list * formula
  | FormulaLet of expr_assign list * formula
  | FormulaIf of formula * formula * formula
  | Or of formula * formula
  | Iff of formula * formula
  | Implies of formula * formula
  | And of formula * formula
  | Not of formula
  | Acyclic of n_ary_index
  | Function of n_ary_index * rel_expr * rel_expr
  | Functional of n_ary_index * rel_expr * rel_expr
  | TotalOrdering of n_ary_index * rel_expr * rel_expr * rel_expr
  | Subset of rel_expr * rel_expr
  | RelEq of rel_expr * rel_expr
  | IntEq of int_expr * int_expr
  | LT of int_expr * int_expr
  | LE of int_expr * int_expr
  | No of rel_expr
  | Lone of rel_expr
  | One of rel_expr
  | Some of rel_expr
  | False
  | True
  | FormulaReg of int
  and rel_expr =
    RelLet of expr_assign list * rel_expr
  | RelIf of formula * rel_expr * rel_expr
  | Union of rel_expr * rel_expr
  | Difference of rel_expr * rel_expr
  | Override of rel_expr * rel_expr
  | Intersect of rel_expr * rel_expr
  | Product of rel_expr * rel_expr
  | IfNo of rel_expr * rel_expr
  | Project of rel_expr * int_expr list
  | Join of rel_expr * rel_expr
  | Closure of rel_expr
  | ReflexiveClosure of rel_expr
  | Transpose of rel_expr
  | Comprehension of decl list * formula
  | Bits of int_expr
  | Int of int_expr
  | Iden
  | Ints
  | None
  | Univ
  | Atom of int
  | AtomSeq of int * int
  | Rel of n_ary_index
  | Var of n_ary_index
  | RelReg of n_ary_index
  and int_expr =
    Sum of decl list * int_expr
  | IntLet of expr_assign list * int_expr
  | IntIf of formula * int_expr * int_expr
  | SHL of int_expr * int_expr
  | SHA of int_expr * int_expr
  | SHR of int_expr * int_expr
  | Add of int_expr * int_expr
  | Sub of int_expr * int_expr
  | Mult of int_expr * int_expr
  | Div of int_expr * int_expr
  | Mod of int_expr * int_expr
  | Cardinality of rel_expr
  | SetSum of rel_expr
  | BitOr of int_expr * int_expr
  | BitXor of int_expr * int_expr
  | BitAnd of int_expr * int_expr
  | BitNot of int_expr
  | Neg of int_expr
  | Absolute of int_expr
  | Signum of int_expr
  | Num of int
  | IntReg of int
  and decl =
    DeclNo of n_ary_index * rel_expr
  | DeclLone of n_ary_index * rel_expr
  | DeclOne of n_ary_index * rel_expr
  | DeclSome of n_ary_index * rel_expr
  | DeclSet of n_ary_index * rel_expr
  and expr_assign =
    AssignFormulaReg of int * formula
  | AssignRelReg of n_ary_index * rel_expr
  | AssignIntReg of int * int_expr

  type problem =
    {comment : string,
     settings : setting list,
     univ_card : int,
     tuple_assigns : tuple_assign list,
     bounds : bound list,
     int_bounds : int_bound list,
     expr_assigns : expr_assign list,
     formula : formula}

  (* The five declaration constructors share a payload and differ only in
     the multiplicity keyword; splitting them once keeps the fan-outs
     below to a single clause each. *)
  fun decl_parts (DeclNo payload) = ("no", payload)
    | decl_parts (DeclLone payload) = ("lone", payload)
    | decl_parts (DeclOne payload) = ("one", payload)
    | decl_parts (DeclSome payload) = ("some", payload)
    | decl_parts (DeclSet payload) = ("set", payload)

  type 'a fold_expr_funcs =
    {formula_func : formula -> 'a -> 'a,
     rel_expr_func : rel_expr -> 'a -> 'a,
     int_expr_func : int_expr -> 'a -> 'a}

  fun fold_list fold_value values initial =
    List.foldl (fn (value, result) => fold_value value result)
      initial values

  fun fold_formula funcs formula initial =
    case formula of
        All (decls, body) =>
          fold_formula funcs body (fold_list (fold_decl funcs) decls initial)
      | Exist (decls, body) =>
          fold_formula funcs body (fold_list (fold_decl funcs) decls initial)
      | FormulaLet (assigns, body) =>
          fold_formula funcs body
            (fold_list (fold_expr_assign funcs) assigns initial)
      | FormulaIf (test, yes, no) =>
          fold_formula funcs no
            (fold_formula funcs yes (fold_formula funcs test initial))
      | Or (left, right) =>
          fold_formula funcs right (fold_formula funcs left initial)
      | Iff (left, right) =>
          fold_formula funcs right (fold_formula funcs left initial)
      | Implies (left, right) =>
          fold_formula funcs right (fold_formula funcs left initial)
      | And (left, right) =>
          fold_formula funcs right (fold_formula funcs left initial)
      | Not body => fold_formula funcs body initial
      | Acyclic index => fold_rel_expr funcs (Rel index) initial
      | Function (index, domain, range) =>
          fold_rel_expr funcs range
            (fold_rel_expr funcs domain
              (fold_rel_expr funcs (Rel index) initial))
      | Functional (index, domain, range) =>
          fold_rel_expr funcs range
            (fold_rel_expr funcs domain
              (fold_rel_expr funcs (Rel index) initial))
      | TotalOrdering (index, set, first, last) =>
          fold_rel_expr funcs last
            (fold_rel_expr funcs first
              (fold_rel_expr funcs set
                (fold_rel_expr funcs (Rel index) initial)))
      | Subset (left, right) =>
          fold_rel_expr funcs right (fold_rel_expr funcs left initial)
      | RelEq (left, right) =>
          fold_rel_expr funcs right (fold_rel_expr funcs left initial)
      | IntEq (left, right) =>
          fold_int_expr funcs right (fold_int_expr funcs left initial)
      | LT (left, right) =>
          fold_int_expr funcs right (fold_int_expr funcs left initial)
      | LE (left, right) =>
          fold_int_expr funcs right (fold_int_expr funcs left initial)
      | No relation => fold_rel_expr funcs relation initial
      | Lone relation => fold_rel_expr funcs relation initial
      | One relation => fold_rel_expr funcs relation initial
      | Some relation => fold_rel_expr funcs relation initial
      | False => #formula_func funcs formula initial
      | True => #formula_func funcs formula initial
      | FormulaReg _ => #formula_func funcs formula initial
  and fold_rel_expr funcs relation initial =
    case relation of
        RelLet (assigns, body) =>
          fold_rel_expr funcs body
            (fold_list (fold_expr_assign funcs) assigns initial)
      | RelIf (test, yes, no) =>
          fold_rel_expr funcs no
            (fold_rel_expr funcs yes (fold_formula funcs test initial))
      | Union (left, right) =>
          fold_rel_expr funcs right (fold_rel_expr funcs left initial)
      | Difference (left, right) =>
          fold_rel_expr funcs right (fold_rel_expr funcs left initial)
      | Override (left, right) =>
          fold_rel_expr funcs right (fold_rel_expr funcs left initial)
      | Intersect (left, right) =>
          fold_rel_expr funcs right (fold_rel_expr funcs left initial)
      | Product (left, right) =>
          fold_rel_expr funcs right (fold_rel_expr funcs left initial)
      | IfNo (left, right) =>
          fold_rel_expr funcs right (fold_rel_expr funcs left initial)
      | Project (body, columns) =>
          fold_list (fold_int_expr funcs) columns
            (fold_rel_expr funcs body initial)
      | Join (left, right) =>
          fold_rel_expr funcs right (fold_rel_expr funcs left initial)
      | Closure body => fold_rel_expr funcs body initial
      | ReflexiveClosure body => fold_rel_expr funcs body initial
      | Transpose body => fold_rel_expr funcs body initial
      | Comprehension (decls, body) =>
          fold_formula funcs body (fold_list (fold_decl funcs) decls initial)
      | Bits integer => fold_int_expr funcs integer initial
      | Int integer => fold_int_expr funcs integer initial
      | Iden => #rel_expr_func funcs relation initial
      | Ints => #rel_expr_func funcs relation initial
      | None => #rel_expr_func funcs relation initial
      | Univ => #rel_expr_func funcs relation initial
      | Atom _ => #rel_expr_func funcs relation initial
      | AtomSeq _ => #rel_expr_func funcs relation initial
      | Rel _ => #rel_expr_func funcs relation initial
      | Var _ => #rel_expr_func funcs relation initial
      | RelReg _ => #rel_expr_func funcs relation initial
  and fold_int_expr funcs integer initial =
    case integer of
        Sum (decls, body) =>
          fold_int_expr funcs body (fold_list (fold_decl funcs) decls initial)
      | IntLet (assigns, body) =>
          fold_int_expr funcs body
            (fold_list (fold_expr_assign funcs) assigns initial)
      | IntIf (test, yes, no) =>
          fold_int_expr funcs no
            (fold_int_expr funcs yes (fold_formula funcs test initial))
      | SHL (left, right) =>
          fold_int_expr funcs right (fold_int_expr funcs left initial)
      | SHA (left, right) =>
          fold_int_expr funcs right (fold_int_expr funcs left initial)
      | SHR (left, right) =>
          fold_int_expr funcs right (fold_int_expr funcs left initial)
      | Add (left, right) =>
          fold_int_expr funcs right (fold_int_expr funcs left initial)
      | Sub (left, right) =>
          fold_int_expr funcs right (fold_int_expr funcs left initial)
      | Mult (left, right) =>
          fold_int_expr funcs right (fold_int_expr funcs left initial)
      | Div (left, right) =>
          fold_int_expr funcs right (fold_int_expr funcs left initial)
      | Mod (left, right) =>
          fold_int_expr funcs right (fold_int_expr funcs left initial)
      | Cardinality relation => fold_rel_expr funcs relation initial
      | SetSum relation => fold_rel_expr funcs relation initial
      | BitOr (left, right) =>
          fold_int_expr funcs right (fold_int_expr funcs left initial)
      | BitXor (left, right) =>
          fold_int_expr funcs right (fold_int_expr funcs left initial)
      | BitAnd (left, right) =>
          fold_int_expr funcs right (fold_int_expr funcs left initial)
      | BitNot body => fold_int_expr funcs body initial
      | Neg body => fold_int_expr funcs body initial
      | Absolute body => fold_int_expr funcs body initial
      | Signum body => fold_int_expr funcs body initial
      | Num _ => #int_expr_func funcs integer initial
      | IntReg _ => #int_expr_func funcs integer initial
  and fold_decl funcs decl initial =
    let val (_, (index, relation)) = decl_parts decl
    in
      fold_rel_expr funcs relation (fold_rel_expr funcs (Var index) initial)
    end
  and fold_expr_assign funcs assign initial =
    case assign of
        AssignFormulaReg (index, formula) =>
          fold_formula funcs formula
            (fold_formula funcs (FormulaReg index) initial)
      | AssignRelReg (index, relation) =>
          fold_rel_expr funcs relation
            (fold_rel_expr funcs (RelReg index) initial)
      | AssignIntReg (index, integer) =>
          fold_int_expr funcs integer
            (fold_int_expr funcs (IntReg index) initial)

  type 'a fold_tuple_funcs =
    {tuple_func : tuple -> 'a -> 'a,
     tuple_set_func : tuple_set -> 'a -> 'a}

  fun fold_tuple funcs tuple initial = #tuple_func funcs tuple initial

  fun fold_tuple_set funcs tuple_set initial =
    case tuple_set of
        TupleUnion (left, right) =>
          fold_tuple_set funcs right (fold_tuple_set funcs left initial)
      | TupleDifference (left, right) =>
          fold_tuple_set funcs right (fold_tuple_set funcs left initial)
      | TupleIntersect (left, right) =>
          fold_tuple_set funcs right (fold_tuple_set funcs left initial)
      | TupleProduct (left, right) =>
          fold_tuple_set funcs right (fold_tuple_set funcs left initial)
      | TupleProject (set, _) => fold_tuple_set funcs set initial
      | TupleSet tuples => fold_list (fold_tuple funcs) tuples initial
      | TupleRange (first, last) =>
          fold_tuple funcs last (fold_tuple funcs first initial)
      | TupleArea (first, last) =>
          fold_tuple funcs last (fold_tuple funcs first initial)
      | TupleAtomSeq _ => #tuple_set_func funcs tuple_set initial
      | TupleSetReg _ => #tuple_set_func funcs tuple_set initial

  fun fold_tuple_assign funcs assign initial =
    case assign of
        AssignTuple (index, tuple) =>
          fold_tuple funcs tuple (fold_tuple funcs (TupleReg index) initial)
      | AssignTupleSet (index, tuple_set) =>
          fold_tuple_set funcs tuple_set
            (fold_tuple_set funcs (TupleSetReg index) initial)

  fun fold_bound expr_funcs tuple_funcs (relations, tuple_sets) initial =
    fold_list (fold_tuple_set tuple_funcs) tuple_sets
      (fold_list (fn (index, _) => fold_rel_expr expr_funcs (Rel index))
        relations initial)

  fun fold_int_bound funcs (_, tuple_sets) initial =
    fold_list (fold_tuple_set funcs) tuple_sets initial

  fun max_arity univ_card =
    Real.floor
      (Math.ln 2147483647.0 / Math.ln (Real.fromInt univ_card))

  fun arity_of_rel_expr (RelLet (_, relation)) =
        arity_of_rel_expr relation
    | arity_of_rel_expr (RelIf (_, relation, _)) =
        arity_of_rel_expr relation
    | arity_of_rel_expr (Union (relation, _)) =
        arity_of_rel_expr relation
    | arity_of_rel_expr (Difference (relation, _)) =
        arity_of_rel_expr relation
    | arity_of_rel_expr (Override (relation, _)) =
        arity_of_rel_expr relation
    | arity_of_rel_expr (Intersect (relation, _)) =
        arity_of_rel_expr relation
    | arity_of_rel_expr (Product (left, right)) =
        arity_of_rel_expr left + arity_of_rel_expr right
    | arity_of_rel_expr (IfNo (relation, _)) =
        arity_of_rel_expr relation
    | arity_of_rel_expr (Project (_, columns)) = length columns
    | arity_of_rel_expr (Join (left, right)) =
        arity_of_rel_expr left + arity_of_rel_expr right - 2
    | arity_of_rel_expr (Closure _) = 2
    | arity_of_rel_expr (ReflexiveClosure _) = 2
    | arity_of_rel_expr (Transpose _) = 2
    | arity_of_rel_expr (Comprehension (decls, _)) =
        List.foldl (fn (decl, arity) => arity_of_decl decl + arity)
          0 decls
    | arity_of_rel_expr (Rel (arity, _)) = arity
    | arity_of_rel_expr (Var (arity, _)) = arity
    | arity_of_rel_expr (RelReg (arity, _)) = arity
    | arity_of_rel_expr Iden = 2
    | arity_of_rel_expr _ = 1
  and arity_of_decl decl = #1 (#1 (#2 (decl_parts decl)))

  type raw_bound = n_ary_index * int list list

  datatype outcome =
    Normal of (int * raw_bound list) list * int list * string
  | TimedOut of int list
  | Error of string * int list

  exception SYNTAX of string * string

  fun find_index predicate values =
    Lib.index predicate values handle Feedback.HOL_ERR _ => ~1

  fun is_problem_trivially_false ({formula = False, ...} : problem) = true
    | is_problem_trivially_false _ = false

  fun first_two [] = []
    | first_two [value] = [value]
    | first_two (first :: second :: _) = [first, second]

  fun settings_equivalent ([], []) = true
    | settings_equivalent
        ((key1, value1) :: settings1, (key2, value2) :: settings2) =
        key1 = key2 andalso
        (value1 = value2 orelse key1 = "delay" orelse
         (key1 = "solver" andalso
          first_two (String.fields (fn character => character = #",") value1) =
          first_two
            (String.fields (fn character => character = #",") value2))) andalso
        settings_equivalent (settings1, settings2)
    | settings_equivalent _ = false

  fun problems_equivalent (first : problem, second : problem) =
    #univ_card first = #univ_card second andalso
    #formula first = #formula second andalso
    #bounds first = #bounds second andalso
    #expr_assigns first = #expr_assigns second andalso
    #tuple_assigns first = #tuple_assigns second andalso
    #int_bounds first = #int_bounds second andalso
    settings_equivalent (#settings first, #settings second)

  fun signed_string_of_int value =
    let val text = Int.toString value
    in
      if String.isPrefix "~" text then
        "-" ^ String.extract (text, 1, NONE)
      else
        text
    end

  fun base_name index =
    if index < 0 then
      IntInf.toString (~(IntInf.fromInt index) - 1) ^ "'"
    else
      Int.toString index

  fun n_ary_name (1, index) unary _ _ = unary ^ base_name index
    | n_ary_name (2, index) _ binary _ = binary ^ base_name index
    | n_ary_name (arity, index) _ _ many =
        many ^ Int.toString arity ^ "_" ^ base_name index

  fun atom_name index = "A" ^ base_name index
  fun atom_seq_name (count, 0) = "u" ^ base_name count
    | atom_seq_name (count, start) =
        "u" ^ base_name count ^ "@" ^ base_name start
  fun formula_reg_name index = "$f" ^ base_name index
  fun rel_reg_name index = "$e" ^ base_name index
  fun int_reg_name index = "$i" ^ base_name index

  fun tuple_name index = n_ary_name index "A" "P" "T"
  fun rel_name index = n_ary_name index "s" "r" "m"
  fun var_name index = n_ary_name index "S" "R" "M"
  fun tuple_reg_name index = n_ary_name index "$A" "$P" "$T"
  fun tuple_set_reg_name index = n_ary_name index "$a" "$p" "$t"

  fun inline_comment "" = ""
    | inline_comment comment =
        " /* " ^
        String.translate
          (fn #"\n" => " " | #"*" => "* " | character =>
             String.str character)
          comment ^
        " */"

  fun prefix_lines prefix text =
    prefix ^ String.translate
      (fn #"\n" => "\n" ^ prefix | character => String.str character)
      text

  fun block_comment "" = ""
    | block_comment comment = prefix_lines "// " comment ^ "\n"

  fun commented_rel_name (index, comment) =
    rel_name index ^ inline_comment comment

  fun string_for_tuple (Tuple indices) =
        "[" ^ String.concatWith ", " (List.map atom_name indices) ^ "]"
    | string_for_tuple (TupleIndex index) = tuple_name index
    | string_for_tuple (TupleReg index) = tuple_reg_name index

  val no_prec = 100
  val prec_tuple_union = 1
  val prec_tuple_intersect = 2
  val prec_tuple_product = 3
  val prec_tuple_project = 4

  fun precedence_ts (TupleUnion _) = prec_tuple_union
    | precedence_ts (TupleDifference _) = prec_tuple_union
    | precedence_ts (TupleIntersect _) = prec_tuple_intersect
    | precedence_ts (TupleProduct _) = prec_tuple_product
    | precedence_ts (TupleProject _) = prec_tuple_project
    | precedence_ts _ = no_prec

  fun string_for_tuple_set tuple_set =
    let
      fun sub current outer_prec =
        let
          val prec = precedence_ts current
          val need_parens = prec < outer_prec
          fun binary left separator right right_prec =
            sub left prec ^ separator ^ sub right right_prec
          val body =
            case current of
                TupleUnion (left, right) =>
                  binary left " + " right (prec + 1)
              | TupleDifference (left, right) =>
                  binary left " - " right (prec + 1)
              | TupleIntersect (left, right) =>
                  binary left " & " right prec
              | TupleProduct (left, right) =>
                  binary left "->" right prec
              | TupleProject (set, column) =>
                  sub set prec ^ "[" ^ Int.toString column ^ "]"
              | TupleSet tuples =>
                  "{" ^ String.concatWith ", "
                    (List.map string_for_tuple tuples) ^ "}"
              | TupleRange (first, last) =>
                  "{" ^ string_for_tuple first ^
                  (if first = last then ""
                   else " .. " ^ string_for_tuple last) ^ "}"
              | TupleArea (first, last) =>
                  "{" ^ string_for_tuple first ^ " # " ^
                  string_for_tuple last ^ "}"
              | TupleAtomSeq index => atom_seq_name index
              | TupleSetReg index => tuple_set_reg_name index
        in
          if need_parens then "(" ^ body ^ ")" else body
        end
    in
      sub tuple_set 0
    end

  fun string_for_tuple_assign (AssignTuple (index, tuple)) =
        tuple_reg_name index ^ " := " ^ string_for_tuple tuple ^ "\n"
    | string_for_tuple_assign (AssignTupleSet (index, tuple_set)) =
        tuple_set_reg_name index ^ " := " ^
        string_for_tuple_set tuple_set ^ "\n"

  fun string_for_bound (relations, tuple_sets) =
    "bounds " ^
    String.concatWith ", " (List.map commented_rel_name relations) ^ ": " ^
    (if length tuple_sets = 1 then "" else "[") ^
    String.concatWith ", " (List.map string_for_tuple_set tuple_sets) ^
    (if length tuple_sets = 1 then "" else "]") ^ "\n"

  fun int_string_for_bound (number, tuple_sets) =
    (case number of
         SOME value => signed_string_of_int value ^ ": "
       | NONE => "") ^
    "[" ^ String.concatWith ", "
      (List.map string_for_tuple_set tuple_sets) ^ "]"

  val prec_all = 1
  val prec_or = 2
  val prec_iff = 3
  val prec_implies = 4
  val prec_and = 5
  val prec_not = 6
  val prec_eq = 7
  val prec_some = 8
  val prec_shl = 9
  val prec_add = 10
  val prec_mult = 11
  val prec_override = 12
  val prec_intersect = 13
  val prec_product = 14
  val prec_if_no = 15
  val prec_project = 17
  val prec_join = 18
  val prec_bit_not = 19

  fun precedence_f (All _) = prec_all
    | precedence_f (Exist _) = prec_all
    | precedence_f (FormulaLet _) = prec_all
    | precedence_f (FormulaIf _) = prec_all
    | precedence_f (Or _) = prec_or
    | precedence_f (Iff _) = prec_iff
    | precedence_f (Implies _) = prec_implies
    | precedence_f (And _) = prec_and
    | precedence_f (Not _) = prec_not
    | precedence_f (Subset _) = prec_eq
    | precedence_f (RelEq _) = prec_eq
    | precedence_f (IntEq _) = prec_eq
    | precedence_f (LT _) = prec_eq
    | precedence_f (LE _) = prec_eq
    | precedence_f (No _) = prec_some
    | precedence_f (Lone _) = prec_some
    | precedence_f (One _) = prec_some
    | precedence_f (Some _) = prec_some
    | precedence_f _ = no_prec

  fun precedence_r (RelLet _) = prec_all
    | precedence_r (RelIf _) = prec_all
    | precedence_r (Union _) = prec_add
    | precedence_r (Difference _) = prec_add
    | precedence_r (Override _) = prec_override
    | precedence_r (Intersect _) = prec_intersect
    | precedence_r (Product _) = prec_product
    | precedence_r (IfNo _) = prec_if_no
    | precedence_r (Project _) = prec_project
    | precedence_r (Join _) = prec_join
    | precedence_r (Closure _) = prec_bit_not
    | precedence_r (ReflexiveClosure _) = prec_bit_not
    | precedence_r (Transpose _) = prec_bit_not
    | precedence_r _ = no_prec

  fun precedence_i (Sum _) = prec_all
    | precedence_i (IntLet _) = prec_all
    | precedence_i (IntIf _) = prec_all
    | precedence_i (SHL _) = prec_shl
    | precedence_i (SHA _) = prec_shl
    | precedence_i (SHR _) = prec_shl
    | precedence_i (Add _) = prec_add
    | precedence_i (Sub _) = prec_add
    | precedence_i (Mult _) = prec_mult
    | precedence_i (Div _) = prec_mult
    | precedence_i (Mod _) = prec_mult
    | precedence_i (BitOr _) = prec_intersect
    | precedence_i (BitXor _) = prec_intersect
    | precedence_i (BitAnd _) = prec_intersect
    | precedence_i (BitNot _) = prec_bit_not
    | precedence_i (Neg _) = prec_bit_not
    | precedence_i (Absolute _) = prec_bit_not
    | precedence_i (Signum _) = prec_bit_not
    | precedence_i _ = no_prec

  fun write_problem stream header problems =
    let
      fun out text = TextIO.output (stream, text)

      fun out_outmost_f (And (left, right)) =
            (out_outmost_f left; out "\n   && "; out_outmost_f right)
        | out_outmost_f formula = out_f formula prec_and
      and out_f formula outer_prec =
        let
          val prec = precedence_f formula
          val need_parens = prec < outer_prec
          val _ = if need_parens then out "(" else ()
          val _ =
            case formula of
                All (decls, body) =>
                  (out "all ["; out_decls decls; out "] | ";
                   out_f body prec)
              | Exist (decls, body) =>
                  (out "some ["; out_decls decls; out "] | ";
                   out_f body prec)
              | FormulaLet (assigns, body) =>
                  (out "let ["; out_assigns assigns; out "] | ";
                   out_f body prec)
              | FormulaIf (test, yes, no) =>
                  (out "if "; out_f test prec; out " then ";
                   out_f yes prec; out " else "; out_f no prec)
              | Or (left, right) =>
                  (out_f left prec; out " || "; out_f right prec)
              | Iff (left, right) =>
                  (out_f left prec; out " <=> "; out_f right prec)
              | Implies (left, right) =>
                  (out_f left (prec + 1); out " => "; out_f right prec)
              | And (left, right) =>
                  (out_f left prec; out " && "; out_f right prec)
              | Not body => (out "! "; out_f body prec)
              | Acyclic index => out ("ACYCLIC(" ^ rel_name index ^ ")")
              | Function (index, domain, range) =>
                  (out ("FUNCTION(" ^ rel_name index ^ ", ");
                   out_r domain 0; out " -> one "; out_r range 0; out ")")
              | Functional (index, domain, range) =>
                  (out ("FUNCTION(" ^ rel_name index ^ ", ");
                   out_r domain 0; out " -> lone "; out_r range 0; out ")")
              | TotalOrdering (index, set, first, last) =>
                  (out ("TOTAL_ORDERING(" ^ rel_name index ^ ", ");
                   out_r set 0; out ", "; out_r first 0; out ", ";
                   out_r last 0; out ")")
              | Subset (left, right) =>
                  (out_r left prec; out " in "; out_r right prec)
              | RelEq (left, right) =>
                  (out_r left prec; out " = "; out_r right prec)
              | IntEq (left, right) =>
                  (out_i left prec; out " = "; out_i right prec)
              | LT (left, right) =>
                  (out_i left prec; out " < "; out_i right prec)
              | LE (left, right) =>
                  (out_i left prec; out " <= "; out_i right prec)
              | No relation => (out "no "; out_r relation prec)
              | Lone relation => (out "lone "; out_r relation prec)
              | One relation => (out "one "; out_r relation prec)
              | Some relation => (out "some "; out_r relation prec)
              | False => out "false"
              | True => out "true"
              | FormulaReg index => out (formula_reg_name index)
        in
          if need_parens then out ")" else ()
        end
      and out_r relation outer_prec =
        let
          val prec = precedence_r relation
          val need_parens = prec < outer_prec
          val _ = if need_parens then out "(" else ()
          val _ =
            case relation of
                RelLet (assigns, body) =>
                  (out "let ["; out_assigns assigns; out "] | ";
                   out_r body prec)
              | RelIf (test, yes, no) =>
                  (out "if "; out_f test prec; out " then ";
                   out_r yes prec; out " else "; out_r no prec)
              | Union (left, right) =>
                  (out_r left prec; out " + "; out_r right (prec + 1))
              | Difference (left, right) =>
                  (out_r left prec; out " - "; out_r right (prec + 1))
              | Override (left, right) =>
                  (out_r left prec; out " ++ "; out_r right prec)
              | Intersect (left, right) =>
                  (out_r left prec; out " & "; out_r right prec)
              | Product (left, right) =>
                  (out_r left prec; out "->"; out_r right prec)
              | IfNo (left, right) =>
                  (out_r left prec; out "\\"; out_r right prec)
              | Project (body, columns) =>
                  (out_r body prec; out "["; out_columns columns; out "]")
              | Join (left, right) =>
                  (out_r left prec; out "."; out_r right (prec + 1))
              | Closure body => (out "^"; out_r body prec)
              | ReflexiveClosure body => (out "*"; out_r body prec)
              | Transpose body => (out "~"; out_r body prec)
              | Comprehension (decls, body) =>
                  (out "{["; out_decls decls; out "] | ";
                   out_f body 0; out "}")
              | Bits integer => (out "Bits["; out_i integer 0; out "]")
              | Int integer => (out "Int["; out_i integer 0; out "]")
              | Iden => out "iden"
              | Ints => out "ints"
              | None => out "none"
              | Univ => out "univ"
              | Atom index => out (atom_name index)
              | AtomSeq index => out (atom_seq_name index)
              | Rel index => out (rel_name index)
              | Var index => out (var_name index)
              | RelReg (_, index) => out (rel_reg_name index)
        in
          if need_parens then out ")" else ()
        end
      and out_i integer outer_prec =
        let
          val prec = precedence_i integer
          val need_parens = prec < outer_prec
          val _ = if need_parens then out "(" else ()
          val _ =
            case integer of
                Sum (decls, body) =>
                  (out "sum ["; out_decls decls; out "] | ";
                   out_i body prec)
              | IntLet (assigns, body) =>
                  (out "let ["; out_assigns assigns; out "] | ";
                   out_i body prec)
              | IntIf (test, yes, no) =>
                  (out "if "; out_f test prec; out " then ";
                   out_i yes prec; out " else "; out_i no prec)
              | SHL (left, right) =>
                  (out_i left prec; out " << "; out_i right (prec + 1))
              | SHA (left, right) =>
                  (out_i left prec; out " >> "; out_i right (prec + 1))
              | SHR (left, right) =>
                  (out_i left prec; out " >>> "; out_i right (prec + 1))
              | Add (left, right) =>
                  (out_i left prec; out " + "; out_i right (prec + 1))
              | Sub (left, right) =>
                  (out_i left prec; out " - "; out_i right (prec + 1))
              | Mult (left, right) =>
                  (out_i left prec; out " * "; out_i right (prec + 1))
              | Div (left, right) =>
                  (out_i left prec; out " / "; out_i right (prec + 1))
              | Mod (left, right) =>
                  (out_i left prec; out " % "; out_i right (prec + 1))
              | Cardinality relation =>
                  (out "#("; out_r relation 0; out ")")
              | SetSum relation => (out "sum("; out_r relation 0; out ")")
              | BitOr (left, right) =>
                  (out_i left prec; out " | "; out_i right prec)
              | BitXor (left, right) =>
                  (out_i left prec; out " ^ "; out_i right prec)
              | BitAnd (left, right) =>
                  (out_i left prec; out " & "; out_i right prec)
              | BitNot body => (out "~"; out_i body prec)
              | Neg body => (out "-"; out_i body prec)
              | Absolute body => (out "abs "; out_i body prec)
              | Signum body => (out "sgn "; out_i body prec)
              | Num value => out (signed_string_of_int value)
              | IntReg index => out (int_reg_name index)
        in
          if need_parens then out ")" else ()
        end
      and out_decls [] = ()
        | out_decls [decl] = out_decl decl
        | out_decls (decl :: decls) =
            (out_decl decl; out ", "; out_decls decls)
      and out_decl decl =
            let val (keyword, (index, relation)) = decl_parts decl
            in
              (out (var_name index); out (" : " ^ keyword ^ " ");
               out_r relation 0)
            end
      and out_assigns [] = ()
        | out_assigns [assign] = out_assign assign
        | out_assigns (assign :: assigns) =
            (out_assign assign; out ", "; out_assigns assigns)
      and out_assign (AssignFormulaReg (index, formula)) =
            (out (formula_reg_name index); out " := "; out_f formula 0)
        | out_assign (AssignRelReg ((_, index), relation)) =
            (out (rel_reg_name index); out " := "; out_r relation 0)
        | out_assign (AssignIntReg (index, integer)) =
            (out (int_reg_name index); out " := "; out_i integer 0)
      and out_columns [] = ()
        | out_columns [column] = out_i column 0
        | out_columns (column :: columns) =
            (out_i column 0; out ", "; out_columns columns)

      fun out_problem
          ({comment, settings, univ_card, tuple_assigns, bounds,
            int_bounds, expr_assigns, formula} : problem) =
        let
          val _ = out ("\n" ^ block_comment comment)
          val _ = List.app (fn (key, value) =>
            out (key ^ ": " ^ value ^ "\n")) settings
          val _ = out ("univ: " ^ atom_seq_name (univ_card, 0) ^ "\n")
          val _ = List.app (out o string_for_tuple_assign) tuple_assigns
          val _ = List.app (out o string_for_bound) bounds
          val _ =
            if null int_bounds then ()
            else
              out ("int_bounds: " ^ String.concatWith ", "
                (List.map int_string_for_bound int_bounds) ^ "\n")
          val _ = List.app (fn assign => (out_assign assign; out ";"))
            expr_assigns
          val _ = out "solve "
          val _ = out_outmost_f formula
        in
          out ";\n"
        end
    in
      out (block_comment header);
      List.app out_problem problems
    end

  fun is_ident_char character =
    Char.isAlpha character orelse Char.isDigit character orelse
    character = #"_" orelse character = #"'" orelse character = #"$"

  fun strip_blanks [] = []
    | strip_blanks (#" " :: characters) = strip_blanks characters
    | strip_blanks [character, #" "] = [character]
    | strip_blanks (first :: #" " :: second :: characters) =
        if is_ident_char first andalso is_ident_char second then
          first :: #" " :: strip_blanks (second :: characters)
        else
          strip_blanks (first :: second :: characters)
    | strip_blanks (character :: characters) =
        character :: strip_blanks characters

  exception ParseError

  fun expect [] characters = characters
    | expect (wanted :: wanteds) (character :: characters) =
        if wanted = character then expect wanteds characters
        else raise ParseError
    | expect _ _ = raise ParseError

  fun parse_nat characters =
    let
      fun take_digits (character :: rest, digits) =
            if Char.isDigit character then
              take_digits (rest, character :: digits)
            else
              (rev digits, character :: rest)
        | take_digits ([], digits) = (rev digits, [])
      val (digits, rest) = take_digits (characters, [])
    in
      case (digits, Int.fromString (String.implode digits)) of
          ([], _) => raise ParseError
        | (_, SOME value) => (value, rest)
        | _ => raise ParseError
    end

  fun parse_rel_name characters =
    let
      val ((arity, index), rest) =
        case characters of
            #"s" :: tail =>
              let val (index, rest) = parse_nat tail
              in ((1, index), rest) end
          | #"r" :: tail =>
              let val (index, rest) = parse_nat tail
              in ((2, index), rest) end
          | #"m" :: tail =>
              let
                val (arity, after_arity) = parse_nat tail
                val (index, rest) = parse_nat (expect [#"_"] after_arity)
              in
                ((arity, index), rest)
              end
          | _ => raise ParseError
    in
      case rest of
          #"'" :: tail => ((arity, ~index - 1), tail)
        | _ => ((arity, index), rest)
    end

  fun parse_atom (#"A" :: characters) = parse_nat characters
    | parse_atom _ = raise ParseError

  fun parse_list parse closing characters =
    if not (null characters) andalso hd characters = closing then
      ([], tl characters)
    else
      let
        val (first, rest) = parse characters
        fun more values (#"," :: tail) =
              let val (value, rest) = parse tail
              in more (value :: values) rest end
          | more values (character :: tail) =
              if character = closing then (rev values, tail)
              else raise ParseError
          | more _ [] = raise ParseError
      in
        more [first] rest
      end

  fun parse_tuple characters =
    parse_list parse_atom #"]" (expect [#"["] characters)

  fun parse_tuple_set characters =
    parse_list parse_tuple #"]" (expect [#"["] characters)

  fun parse_assignment characters =
    let
      val (relation, rest) = parse_rel_name characters
      val (tuples, rest) = parse_tuple_set (expect [#"="] rest)
    in
      ((relation, tuples), rest)
    end

  fun parse_instance characters =
    parse_list parse_assignment #"}"
      (expect (String.explode "relations:{") characters)

  fun extract_instance text =
    (case parse_instance (strip_blanks (String.explode text)) of
         (instance, []) => instance
       | _ => raise ParseError)
    handle ParseError =>
      raise SYNTAX
        ("Refute_Forl.extract_instance", "ill-formed Kodkodi output")

  val problem_marker = "*** PROBLEM "
  val outcome_marker = "---OUTCOME---\n"
  val instance_marker = "---INSTANCE---\n"

  fun read_section_body marker section =
    Substring.string
      (#1 (Substring.position "\n\n"
        (Substring.triml (String.size marker) section)))

  fun read_next_instance input =
    let val section = #2 (Substring.position instance_marker input)
    in
      if Substring.isEmpty section then
        raise SYNTAX
          ("Refute_Forl.read_next_instance",
           "expected \"INSTANCE\" marker")
      else
        extract_instance (read_section_body instance_marker section)
    end

  fun read_next_outcomes index (input, sat, unsat) =
    let
      val (prefix, section) = Substring.position outcome_marker input
      val next_problem = #2 (Substring.position problem_marker prefix)
    in
      if Substring.isEmpty section orelse
         not (Substring.isEmpty next_problem) then
        (input, sat, unsat)
      else
        let
          val outcome = read_section_body outcome_marker section
          val rest = Substring.triml (String.size outcome_marker) section
        in
          if String.isSuffix "UNSATISFIABLE" outcome then
            read_next_outcomes index (rest, sat, index :: unsat)
          else if String.isSuffix "SATISFIABLE" outcome then
            let
              (* An instance belongs to this problem only.  Do not let a
                 missing marker consume the next problem's model. *)
              val this_problem =
                #1 (Substring.position problem_marker section)
            in
              read_next_outcomes index
                (rest, (index, read_next_instance this_problem) :: sat, unsat)
            end
          else
            raise SYNTAX
              ("Refute_Forl.read_next_outcomes",
               "unknown outcome \"" ^ outcome ^ "\"")
        end
    end

  fun read_next_problems (input, sat, unsat) =
    let val section = #2 (Substring.position problem_marker input)
    in
      if Substring.isEmpty section then
        (sat, unsat)
      else
        let
          val after_marker =
            Substring.triml (String.size problem_marker) section
          val number = Substring.string
            (Substring.takel (fn character => character <> #" ")
              after_marker)
        in
          case Int.fromString number of
              SOME one_based =>
                read_next_problems
                  (read_next_outcomes (one_based - 1)
                    (after_marker, sat, unsat))
            | NONE =>
                raise SYNTAX
                  ("Refute_Forl.read_next_problems",
                   "expected number after \"PROBLEM\"")
        end
    end

  fun parse_output text =
    let val (sat, unsat) =
      read_next_problems (Substring.full text, [], [])
    in
      (rev sat, rev unsat)
    end

  fun trim_line text =
    if String.isSuffix "\r\n" text then
      String.substring (text, 0, String.size text - 2)
    else if String.isSuffix "\r" text orelse String.isSuffix "\n" text then
      String.substring (text, 0, String.size text - 1)
    else
      text

  fun split_lines "" = []
    | split_lines text =
        String.fields (fn character => character = #"\n") text

  fun trim_split_lines text =
    List.map trim_line (split_lines (trim_line text))

  fun remove_suffix suffix text =
    if String.isSuffix suffix text then
      String.substring (text, 0, String.size text - String.size suffix)
    else
      text

  fun remove_prefix prefix text =
    if String.isPrefix prefix text then
      String.extract (text, String.size prefix, NONE)
    else
      text

  fun first_error error_text =
    let
      fun clean line =
        remove_prefix "Error: "
          (remove_prefix "Solve error: " (remove_suffix "." line))
      val lines = List.map clean (trim_split_lines error_text)
    in
      case List.find (fn line => line <> "" andalso line <> "EXIT") lines of
          SOME line => line
        | NONE => ""
    end

  fun production_header () =
    "generated by HOL4 Refute\n" ^
    Date.fmt "%Y-%m-%d %H:%M:%S"
      (Date.fromTimeLocal (Time.now ()))

  fun getenv name = Option.getOpt (OS.Process.getEnv name, "")

  fun regular_file path =
    path <> "" andalso
    Posix.FileSys.ST.isReg (Posix.FileSys.stat path)
      handle Interrupt => raise Interrupt | _ => false

  fun readable_file path =
    regular_file path andalso
    OS.FileSys.access (path, [OS.FileSys.A_READ])
      handle Interrupt => raise Interrupt | _ => false

  fun executable_file path =
    regular_file path andalso
    OS.FileSys.access (path, [OS.FileSys.A_EXEC])
      handle Interrupt => raise Interrupt | _ => false

  fun absolute_path path =
    OS.FileSys.fullPath path handle Interrupt => raise Interrupt | _ => path

  fun path_entries () =
    String.fields (fn character => character = #":") (getenv "PATH")

  fun find_on_path executable =
    Option.map absolute_path
      (List.find executable_file
        (List.map (fn directory =>
           OS.Path.concat
             (if directory = "" then "." else directory, executable))
         (path_entries ())))

  fun java_executable () =
    let
      val explicit = getenv "HOL4_JAVA_EXECUTABLE"
      val java_home = getenv "JAVA_HOME"
      val home_java =
        if java_home = "" then ""
        else OS.Path.concat (OS.Path.concat (java_home, "bin"), "java")
    in
      if executable_file explicit then SOME (absolute_path explicit)
      else if executable_file home_java then SOME (absolute_path home_java)
      else find_on_path "java"
    end

  fun component_jars component =
    List.map (fn name =>
      OS.Path.concat (OS.Path.concat (component, "jar"), name))
      ["antlr-runtime-3.1.1.jar", "kodkod-1.5.jar",
       "kodkodi-1.5.7.jar", "sat4j-2.3.jar"]

  fun component_is_complete component =
    component <> "" andalso
    List.all readable_file (component_jars (absolute_path component))

  fun launcher_is_configured () =
    if not Systeml.isUnix then false
    else
      let val override = getenv "HOL4_KODKODI_EXEC"
      in
        (* This is deliberately only a presence check.  The override is a
           shell command, not necessarily a single pathname, and must be
           passed to the shell verbatim below.  Do not probe it here: loading
           this module must never start a JVM or launcher. *)
        if override <> "" then true
        else
          component_is_complete (getenv "HOL4_KODKODI") andalso
          Option.isSome (java_executable ())
      end

  val configured =
    Synchronized.var "Refute_Forl.configured" (NONE : bool option)

  fun is_configured () =
    Synchronized.change_result configured (fn cached =>
      case cached of
          SOME answer => (answer, cached)
        | NONE =>
            let val answer = launcher_is_configured ()
            in (answer, SOME answer) end)

  fun uname field =
    case List.find (fn (name, _) => name = field) (Posix.ProcEnv.uname ()) of
        SOME (_, value) => value
      | NONE => ""

  fun platform_name () =
    let
      val machine = uname "machine"
      val system = uname "sysname"
      val architecture =
        if machine = "aarch64" orelse machine = "arm64" then "arm64"
        else if machine = "amd64" then "x86_64"
        else machine
      val operating_system =
        if system = "Linux" then "linux"
        else if system = "Darwin" then "darwin"
        else String.map Char.toLower system
    in
      architecture ^ "-" ^ operating_system
    end

  fun jni_dir () =
    let val component = absolute_path (getenv "HOL4_KODKODI")
    in
      OS.Path.concat (OS.Path.concat (component, "jni"), platform_name ())
    end

  fun shell_quote text =
    "'" ^ String.translate
      (fn #"'" => "'\\''" | character => String.str character) text ^ "'"

  fun launcher_command () =
    let val override = getenv "HOL4_KODKODI_EXEC"
    in
      if override <> "" then override
      else
        let
          val component = absolute_path (getenv "HOL4_KODKODI")
          val java = valOf (java_executable ())
          val classpath = String.concatWith ":" (component_jars component)
          val jni = jni_dir ()
        in
          String.concatWith " "
            [shell_quote java, "-cp", shell_quote classpath,
             shell_quote ("-Djava.library.path=" ^ jni),
             "isabelle.kodkodi.Kodkodi"]
        end
    end

  val temp_counter = Portable.make_counter {init = 0, inc = 1}

  fun pid_string () =
    SysWord.toString (Posix.Process.pidToWord (Posix.ProcEnv.getpid ()))

  fun temp_root () =
    let val candidate = getenv "TMPDIR"
    in
      OS.FileSys.fullPath
        (if candidate <> "" andalso
            (OS.FileSys.isDir candidate handle OS.SysErr _ => false)
         then candidate
         else "/tmp")
    end

  val private_directory_mode = Posix.FileSys.S.flags
    [Posix.FileSys.S.irusr, Posix.FileSys.S.iwusr,
     Posix.FileSys.S.ixusr]

  fun path_exists path =
    ((ignore (Posix.FileSys.lstat path); true) handle OS.SysErr _ => false)

  fun make_private_temp_directory () =
    let
      val root = temp_root ()
      fun create 0 = raise Fail "unable to create a private Kodkodi directory"
        | create attempts =
            let
              val name = "kodkodi" ^ pid_string () ^ "_" ^
                Int.toString (temp_counter ())
              val path = OS.Path.concat (root, name)
            in
              (Posix.FileSys.mkdir (path, private_directory_mode); path)
              handle error as OS.SysErr _ =>
                if path_exists path then create (attempts - 1)
                else raise error
            end
    in
      create 100
    end

  fun path_for directory stem suffix =
    OS.Path.concat (directory, stem ^ "." ^ suffix)

  fun write_problems path problems =
    let
      val stream = TextIO.openOut path
      fun close () =
        TextIO.closeOut stream handle Interrupt => raise Interrupt | _ => ()
      fun work () = write_problem stream (production_header ()) problems
    in
      Portable.finally close work ()
    end

  fun read_all path =
    let
      val stream = TextIO.openIn path
      fun close () =
        TextIO.closeIn stream handle Interrupt => raise Interrupt | _ => ()
    in
      Portable.finally close (fn () => TextIO.inputAll stream) ()
    end

  fun remove path = OS.FileSys.remove path handle OS.SysErr _ => ()

  fun exit_code status =
    case Posix.Process.fromStatus status of
        Posix.Process.W_EXITED => 0
      | Posix.Process.W_EXITSTATUS word => Word8.toInt word
      | Posix.Process.W_SIGNALED signal =>
          128 + SysWord.toInt (Posix.Signal.toWord signal)
      | Posix.Process.W_STOPPED signal =>
          128 + SysWord.toInt (Posix.Signal.toWord signal)

  fun run_child command =
    Thread_Attributes.uninterruptible (fn restore_interrupts => fn () =>
      let
        (* Put the launcher and all of its descendants in a fresh session.
           The supervising shell forwards cancellation to that process group
           before it exits, so a wrapper cannot orphan its JVM or SAT child. *)
        val supervised =
          "trap 'kill -TERM -$child 2>/dev/null; wait \"$child\"; " ^
          "exit 130' TERM INT; setsid /bin/sh -c " ^ shell_quote command ^
          " & child=$!; wait \"$child\""
        val process = Unix.execute ("/bin/sh", ["-c", supervised])
        val reaped = ref false
        fun reap () =
          let val status = Unix.reap process
          in reaped := true; status end
        fun terminate () =
          if !reaped then ()
          else
            ((Unix.kill (process, Posix.Signal.term) handle _ => ());
             (ignore (reap ()) handle _ => ()))
        fun wait () = exit_code (reap ())
      in
        restore_interrupts wait ()
          handle error => (terminate (); Exn.reraise error)
      end) ()

  val fudge_milliseconds = 250

  fun uncached_solve_any_problem overlord deadline max_threads
      max_solutions problems =
    let
      val true_index = find_index (fn problem => #formula problem = True)
        problems
      val all_indices = Portable.upto 0 (length problems - 1)
      val indexed = ListPair.zip (all_indices, problems)
      val (indexed_problems, trivially_unsat) =
        if true_index >= 0 then
          (* A trivially true problem is satisfiable outright, so solving it
             alone answers the batch.  Only the trivially false problems may
             be reported unsat alongside it; the rest are merely left
             unsolved, and claiming they are unsat would let the driver
             retire scopes that were never given to the solver. *)
          ([(true_index, List.nth (problems, true_index))],
           List.map #1 (List.filter
             (fn (index, problem) =>
                index <> true_index andalso
                is_problem_trivially_false problem)
             indexed))
        else
          let
            val (kept, dropped) =
              List.partition
                (fn (_, problem) => not (is_problem_trivially_false problem))
                indexed
          in
            (kept, List.map #1 dropped)
          end
      fun reindex index =
        if index >= 0 andalso index < length indexed_problems then
          #1 (List.nth (indexed_problems, index))
        else
          raise SYNTAX
            ("Refute_Forl.uncached_solve_any_problem",
             "problem index out of range")
      val milliseconds =
        Time.toMilliseconds (deadline - Time.now ()) - fudge_milliseconds
      val solve_all = max_solutions > 1
    in
      if null indexed_problems then
        Normal ([], trivially_unsat, "")
      else if milliseconds <= 0 then
        TimedOut trivially_unsat
      else if not (is_configured ()) then
        Error ("Kodkodi is not configured", trivially_unsat)
      else
        let
          val directory =
            if overlord then OS.FileSys.getDir ()
            else make_private_temp_directory ()
          val stem = "kodkodi"
          val input_path = path_for directory stem "kki"
          val output_path = path_for directory stem "out"
          val error_path = path_for directory stem "err"
          val paths = [input_path, output_path, error_path]
          fun remove_files () =
            if overlord then ()
            else
              (List.app remove paths;
               OS.FileSys.rmDir directory handle OS.SysErr _ => ())
          fun work () =
            let
              val _ = write_problems input_path (List.map #2 indexed_problems)
              val arguments =
                ["-max-msecs", IntInf.toString milliseconds] @
                (if solve_all then ["-solve-all"] else []) @
                ["-max-solutions", Int.toString max_solutions] @
                (if max_threads > 0 then
                   ["-max-threads", Int.toString max_threads]
                 else [])
              (* Keep the caller's working directory for a shell-command
                 override such as [./kodkodi].  The private paths below are
                 already absolute, so changing directory is unnecessary. *)
              val command =
                "exec " ^ launcher_command () ^ " " ^
                String.concatWith " " arguments ^ " < " ^
                shell_quote input_path ^ " > " ^ shell_quote output_path ^
                " 2> " ^ shell_quote error_path
              val code = run_child command
              val output = read_all output_path
              val errors = read_all error_path
              val (solutions0, nontrivial_unsat0) = parse_output output
              val solutions = List.map (fn (index, instance) =>
                (reindex index, instance)) solutions0
              val nontrivial_unsat = List.map reindex nontrivial_unsat0
              val unsat = trivially_unsat @ nontrivial_unsat
              val message = first_error errors
              val _ =
                if errors <> "" andalso
                   (Feedback.current_trace "Refute"
                      handle Feedback.HOL_ERR _ => 0) >= 2
                then Feedback.HOL_WARNING "Refute_Forl"
                  "solve_any_problem" errors
                else ()
            in
              if not (null solutions) orelse code = 0 then
                Normal (solutions, unsat, message)
              else if code = 2 then TimedOut unsat
              else if code = 130 then Exn.interrupt ()
              else Error
                (if message = "" then "Unknown error" else message,
                 unsat)
            end
        in
          Portable.finally remove_files work ()
        end
    end

  val cached_outcome =
    Synchronized.var "Refute_Forl.cached_outcome"
      (NONE : ((int * problem list) * outcome) option)

  (* ListPair.allEq is already false on unequal lengths. *)
  fun problem_lists_equivalent (first, second) =
    ListPair.allEq problems_equivalent (first, second)

  fun solve_any_problem debug overlord deadline max_threads max_solutions
      problems =
    let
      fun solve () =
        uncached_solve_any_problem overlord deadline max_threads
          max_solutions problems
      fun keys_equivalent ((solutions1, problems1),
                           (solutions2, problems2)) =
        solutions1 = solutions2 andalso
        problem_lists_equivalent (problems1, problems2)
      fun fresh () =
        let val outcome = solve ()
        in
          (case outcome of
               Normal (_, _, "") =>
                 Synchronized.change cached_outcome
                   (fn _ => SOME ((max_solutions, problems), outcome))
             | _ => ());
          outcome
        end
    in
      if debug orelse overlord then solve ()
      else
        case Synchronized.value cached_outcome of
            SOME (key, outcome) =>
              if keys_equivalent (key, (max_solutions, problems)) then outcome
              else fresh ()
          | NONE => fresh ()
    end
end
