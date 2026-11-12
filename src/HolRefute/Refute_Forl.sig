signature Refute_Forl = sig
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

  type 'a fold_tuple_funcs =
    {tuple_func : tuple -> 'a -> 'a,
     tuple_set_func : tuple_set -> 'a -> 'a}

  val fold_bound :
    'a fold_expr_funcs -> 'a fold_tuple_funcs -> bound -> 'a -> 'a

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

  (* The third component reports a transcript that stops mid-section, i.e.
     one the solver was killed before it finished writing.  The solutions
     and unsat indices returned beside it are the ones it did write. *)
  val first_error : string -> string

  (* Shared with Refute_ForlSat, which loads after this structure. *)
  val getenv : string -> string
  val readable_file : string -> bool
  val uname : string -> string
  val jni_dir : unit -> string
  (* An absolute scratch path with the given suffix, under the temporary
     root and cleaned up by the solve that uses it. *)
  val scratch_file_path : string -> string

  val is_configured : unit -> bool
  val solve_any_problem :
    bool -> bool -> Time.time -> int -> int -> problem list -> outcome
end
