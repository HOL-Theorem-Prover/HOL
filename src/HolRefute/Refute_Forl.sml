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

  val production_header : unit -> string
  val write_problem : TextIO.outstream -> string -> problem list -> unit
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
    case decl of
        DeclNo (index, relation) =>
          fold_rel_expr funcs relation
            (fold_rel_expr funcs (Var index) initial)
      | DeclLone (index, relation) =>
          fold_rel_expr funcs relation
            (fold_rel_expr funcs (Var index) initial)
      | DeclOne (index, relation) =>
          fold_rel_expr funcs relation
            (fold_rel_expr funcs (Var index) initial)
      | DeclSome (index, relation) =>
          fold_rel_expr funcs relation
            (fold_rel_expr funcs (Var index) initial)
      | DeclSet (index, relation) =>
          fold_rel_expr funcs relation
            (fold_rel_expr funcs (Var index) initial)
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
  and arity_of_decl (DeclNo ((arity, _), _)) = arity
    | arity_of_decl (DeclLone ((arity, _), _)) = arity
    | arity_of_decl (DeclOne ((arity, _), _)) = arity
    | arity_of_decl (DeclSome ((arity, _), _)) = arity
    | arity_of_decl (DeclSet ((arity, _), _)) = arity

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
      and out_decl (DeclNo (index, relation)) =
            (out (var_name index); out " : no "; out_r relation 0)
        | out_decl (DeclLone (index, relation)) =
            (out (var_name index); out " : lone "; out_r relation 0)
        | out_decl (DeclOne (index, relation)) =
            (out (var_name index); out " : one "; out_r relation 0)
        | out_decl (DeclSome (index, relation)) =
            (out (var_name index); out " : some "; out_r relation 0)
        | out_decl (DeclSet (index, relation)) =
            (out (var_name index); out " : set "; out_r relation 0)
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

  fun production_header () =
    "generated by HOL4 Refute\n" ^
    Date.fmt "%Y-%m-%d %H:%M:%S"
      (Date.fromTimeLocal (Time.now ()))
end
