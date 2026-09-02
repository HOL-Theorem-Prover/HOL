signature REFUTE_MODEL_FINDER_UTIL = sig
  datatype polarity = Pos | Neg | Neut

  exception ARG of string * string
  exception BAD of string * string
  exception TOO_SMALL of string * string
  exception TOO_LARGE of string * string
  exception NOT_SUPPORTED of string
  exception SAME of unit

  val curry3 : ('a * 'b * 'c -> 'd) -> 'a -> 'b -> 'c -> 'd
  val pair_from_fun : (bool -> 'a) -> 'a * 'a
  val fun_from_pair : 'a * 'a -> bool -> 'a

  val int_from_bool : bool -> int
  val nat_minus : int -> int -> int
  val reasonable_power : int -> int -> int
  val exact_log : int -> int -> int
  val exact_root : int -> int -> int

  val offset_list : int list -> int list
  val index_seq : int -> int -> int list
  val filter_indices : int list -> 'a list -> 'a list
  val filter_out_indices : int list -> 'a list -> 'a list
  val fold1 : ('a -> 'a -> 'a) -> 'a list -> 'a
  val replicate_list : int -> 'a list -> 'a list
  val all_distinct_unordered_pairs_of :
    ''a list -> (''a * ''a) list
  val nth_combination : (int * int) list -> int -> int list
  val all_combinations : (int * int) list -> int list list
  val all_permutations : 'a list -> 'a list list
  val chunk_list : int -> 'a list -> 'a list list
  val chunk_list_unevenly : int list -> 'a list -> 'a list list

  val double_lookup :
    ('a * 'a -> bool) -> ('a option * 'b) list -> 'a -> 'b option
  val triple_lookup :
    (''a * ''a -> bool) -> (''a option * 'b) list -> ''a -> 'b option

  val is_substring_of : string -> string -> bool
  val plural_s : int -> string
  val plural_s_for_list : 'a list -> string
  val serial_commas : string -> string list -> string list
  val signed_string_of_int : int -> string

  val apply_within_budget : Time.time -> ('a -> 'b) -> 'a -> 'b

  val flip_polarity : polarity -> polarity

  val same_type : Type.hol_type -> Type.hol_type -> bool
  val member_type : Type.hol_type -> Type.hol_type list -> bool
  val add_type :
    Type.hol_type -> Type.hol_type list -> Type.hol_type list
  val aconv_member : Term.term -> Term.term list -> bool
  val distinct_terms : Term.term list -> Term.term list
end

structure Refute_ModelFinder_Util :> REFUTE_MODEL_FINDER_UTIL = struct
  datatype polarity = Pos | Neg | Neut

  exception ARG of string * string
  exception BAD of string * string
  exception TOO_SMALL of string * string
  exception TOO_LARGE of string * string
  exception NOT_SUPPORTED of string
  exception SAME of unit

  fun signed_string_of_int value =
    let val string = Int.toString value
    in
      if String.isPrefix "~" string then
        "-" ^ String.extract (string, 1, NONE)
      else
        string
    end

  fun curry3 f x y z = f (x, y, z)

  fun pair_from_fun f = (f false, f true)

  fun fun_from_pair (false_value, true_value) value =
    if value then true_value else false_value

  fun int_from_bool value = if value then 1 else 0

  fun nat_minus i j = if i > j then i - j else 0

  local
    val function_name = "Refute_ModelFinder_Util.reasonable_power"
    val max_exponent = 16384

    fun power _ 0 = 1
      | power base 1 = base
      | power 0 _ = 0
      | power 1 _ = 1
      | power base exponent =
          if exponent < 0 then
            raise ARG
              (function_name,
               "negative exponent (" ^ signed_string_of_int exponent ^ ")")
          else if exponent > max_exponent then
            raise TOO_LARGE
              (function_name,
               "too large exponent (" ^ signed_string_of_int base ^ " ^ " ^
               signed_string_of_int exponent ^ ")")
          else
            let
              val half = power base (exponent div 2)
            in
              half * half * power base (exponent mod 2)
            end
  in
    fun reasonable_power base exponent =
      power base exponent
      handle Overflow =>
        raise TOO_LARGE
          (function_name,
           "result does not fit in int (" ^
           signed_string_of_int base ^ " ^ " ^
           signed_string_of_int exponent ^ ")")
  end

  local
    fun arguments first second =
      String.concatWith ", "
        (List.map signed_string_of_int [first, second])
  in
    fun exact_log base value =
      let
        val result = Real.round
          (Math.ln (Real.fromInt value) / Math.ln (Real.fromInt base))
      in
        if reasonable_power base result = value then result
        else
          raise ARG
            ("Refute_ModelFinder_Util.exact_log", arguments base value)
      end

    fun exact_root degree value =
      let
        val result = Real.round
          (Math.pow (Real.fromInt value, 1.0 / Real.fromInt degree))
      in
        if reasonable_power result degree = value then result
        else
          raise ARG
            ("Refute_ModelFinder_Util.exact_root",
             arguments degree value)
      end
  end

  fun offset_list values =
    let
      fun accumulate [] _ offsets = rev offsets
        | accumulate (value :: rest) offset offsets =
            accumulate rest (offset + value) (offset :: offsets)
    in
      accumulate values 0 []
    end

  fun index_seq start count =
    if count <= 0 then []
    else if start < 0 then List.tabulate (count, fn index => start - index)
    else List.tabulate (count, fn index => start + index)

  fun filter_indices indices values =
    let
      fun filter _ [] _ = []
        | filter index (wanted :: rest) (value :: values) =
            if index = wanted then
              value :: filter (index + 1) rest values
            else
              filter (index + 1) (wanted :: rest) values
        | filter _ _ _ =
            raise ARG
              ("Refute_ModelFinder_Util.filter_indices",
               "indices unordered or out of range")
    in
      filter 0 indices values
    end

  fun filter_out_indices indices values =
    let
      fun filter _ [] values = values
        | filter index (wanted :: rest) (value :: values) =
            if index = wanted then
              filter (index + 1) rest values
            else
              value :: filter (index + 1) (wanted :: rest) values
        | filter _ _ _ =
            raise ARG
              ("Refute_ModelFinder_Util.filter_out_indices",
               "indices unordered or out of range")
    in
      filter 0 indices values
    end

  fun fold1 _ [] = raise List.Empty
    | fold1 f (value :: values) =
        List.foldl (fn (next, result) => f result next) value values

  fun replicate_list count values =
    if count < 0 then
      raise ARG
        ("Refute_ModelFinder_Util.replicate_list", "negative count")
    else
      let
        fun replicate 0 result = result
          | replicate remaining result =
              replicate (remaining - 1) (List.revAppend (values, result))
      in
        rev (replicate count [])
      end

  fun all_distinct_unordered_pairs_of [] = []
    | all_distinct_unordered_pairs_of (value :: values) =
        List.map (fn other => (value, other)) values @
        all_distinct_unordered_pairs_of values

  fun nth_combination cards index =
    let
      fun combination [] remaining = ([], remaining)
        | combination ((card, offset) :: rest) remaining =
            let
              val (indices, quotient) = combination rest remaining
            in
              ((quotient mod card) + offset :: indices,
               quotient div card)
            end
    in
      #1 (combination cards index)
    end

  local
    fun cartesian_product [] _ = []
      | cartesian_product (value :: values) products =
          List.map (fn product => value :: product) products @
          cartesian_product values products

    fun product [] = [[]]
      | product (values :: value_lists) =
          cartesian_product values (product value_lists)
  in
    fun all_combinations cards =
      product (List.map (fn (card, offset) => index_seq offset card) cards)
  end

  local
    fun remove_nth index values =
      let
        fun remove _ [] = raise Subscript
          | remove 0 (_ :: rest) = rest
          | remove remaining (value :: rest) =
              value :: remove (remaining - 1) rest
      in
        if index < 0 then raise Subscript else remove index values
      end
  in
    fun all_permutations [] = [[]]
      | all_permutations values =
          List.concat (List.map (fn index =>
            List.map (fn permutation =>
              List.nth (values, index) :: permutation)
              (all_permutations (remove_nth index values)))
            (index_seq 0 (length values)))
  end

  local
    fun chop count values =
      let
        fun split 0 front rest = (rev front, rest)
          | split _ front [] = (rev front, [])
          | split remaining front (value :: rest) =
              split (remaining - 1) (value :: front) rest
      in
        if count < 0 then
          raise ARG ("Refute_ModelFinder_Util.chop", "negative chunk size")
        else
          split count [] values
      end
  in
    fun chunk_list size values =
      if size <= 0 then
        raise ARG
          ("Refute_ModelFinder_Util.chunk_list", "nonpositive chunk size")
      else
        let
          fun chunks [] = []
            | chunks values =
                let val (chunk, rest) = chop size values
                in chunk :: chunks rest end
        in
          chunks values
        end

    fun chunk_list_unevenly _ [] = []
      | chunk_list_unevenly [] values = List.map (fn value => [value]) values
      | chunk_list_unevenly (size :: sizes) values =
          let val (chunk, rest) = chop size values
          in chunk :: chunk_list_unevenly sizes rest end
  end

  fun double_lookup equal pairs key =
    case AList.lookup
      (fn (SOME left, SOME right) => equal (left, right) | _ => false)
      pairs (SOME key) of
        SOME value => SOME value
      | NONE =>
          Option.map #2
            (List.find (fn (NONE, _) => true | _ => false) pairs)

  fun triple_lookup _ [(NONE, value)] _ = SOME value
    | triple_lookup equal pairs key =
        case AList.lookup (op =) pairs (SOME key) of
          SOME value => SOME value
        | NONE => double_lookup equal pairs key

  fun is_substring_of needle stack =
    not (Substring.isEmpty
      (#2 (Substring.position needle (Substring.full stack))))

  fun plural_s count = if count = 1 then "" else "s"

  fun plural_s_for_list values = plural_s (length values)

  fun serial_commas _ [] = ["??"]
    | serial_commas _ [value] = [value]
    | serial_commas conjunction [left, right] =
        [left, conjunction, right]
    | serial_commas conjunction [first, second, third] =
        [first ^ ",", second ^ ",", conjunction, third]
    | serial_commas conjunction (value :: values) =
        (value ^ ",") :: serial_commas conjunction values

  (* Timeout.apply raises only when the Event_Timer thread interrupts the
     body before it returns, so an already-spent budget is a race rather
     than a decision: the body may well finish first and be accepted.  On
     this tree that is observable.  The monotonicity calculus run under
     "tac_timeout = 0.0" completed, and fused the scope grid it was meant
     to leave alone, in 1 of 12 measured runs.  A budget of zero means the
     work does not get to start, so decide that here instead of asking a
     timer to win a race it has no reason to win.  The exception is the
     one the deadline itself would have raised, so callers need no second
     abandonment path. *)
  fun apply_within_budget budget work argument =
    if Time.<= (budget, Time.zeroTime) then raise Timeout.TIMEOUT budget
    else Timeout.apply budget work argument

  fun flip_polarity Pos = Neg
    | flip_polarity Neg = Pos
    | flip_polarity Neut = Neut

  (* Re-exported from Refute_Util so the model-finder modules can reach the
     shared type/term helpers through their usual Util alias. *)
  val same_type = Refute_Util.same_type
  val member_type = Refute_Util.member_type
  val add_type = Refute_Util.add_type
  val aconv_member = Refute_Util.aconv_member
  val distinct_terms = Refute_Util.distinct_terms

  (* Prefix ownership belongs to Refute_ModelFinder_Names. *)
  (* Upstream Pretty/PIDE, parsing, type, tactic, hash, and spy helpers drop. *)
end
