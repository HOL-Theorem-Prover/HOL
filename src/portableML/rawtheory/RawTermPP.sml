(* Lightweight pretty-printer for terms from RawTheory .dat files *)

structure RawTermPP :> RawTermPP = struct

(* Import RawTheory types *)
open RawTheory_dtype

(* Type alias for sharing tables *)
type sharing_tables = {
  stringt : string Vector.vector,
  idt : (int * int) list,
  typet : raw_type list,
  termt : raw_term list
}

(* ========================================================================
   Simplified term and type structures
   ======================================================================== *)

datatype hol_type = TyVar of string
                   | TyOp of {name : string, args : hol_type list}

datatype term = Var of {name : string, ty : hol_type}
              | Const of {name : string, thy : string, ty : hol_type}
              | Comb of term * term
              | Abs of term * term
              | Bv of int  (* bound variable index - only valid inside Abs *)

fun is_abs (Abs _) = true | is_abs _ = false

(* ========================================================================
   Decoder for write_raw format
   ======================================================================== *)

(* Parse the write_raw encoding. The format uses:
   - | for lambda
   - %n for reference to index n (identifier)
   - $n for bound variable reference n
   - U/B for unary/binary application with index
   - u/b for unary/binary with bound variable
   - @ or @n for n-ary application (default 1)
*)

local
  val numeric = Char.contains "0123456789"

  fun take_numb ss0 =
    let val (ns, ss1) = Substring.splitl numeric ss0
    in case Int.fromString (Substring.string ns)
        of SOME i => (i, ss1)
         | NONE => raise Fail "take_numb"
    end

  (* Simple lexer for write_raw format *)
  datatype token = Lamb
                  | Ident of int
                  | BVar of int
                  | I1 of int      (* unary indexed *)
                  | BV1 of int     (* unary bound var *)
                  | I2 of int      (* binary indexed *)
                  | BV2 of int     (* binary bound var *)
                  | App of int     (* n-ary application *)

  fun lexer ss1 =
    case Substring.getc ss1 of
      NONE => NONE
    | SOME (#"|", ss2) => SOME (Lamb, ss2)
    | SOME (#"%", ss2) =>
        let val (n, ss3) = take_numb ss2
        in SOME (Ident n, ss3)
        end
    | SOME (#"$", ss2) =>
        let val (n, ss3) = take_numb ss2
        in SOME (BVar n, ss3)
        end
    | SOME (#"U", ss2) =>
        let val (n, ss3) = take_numb ss2
        in SOME (I1 n, ss3)
        end
    | SOME (#"u", ss2) =>
        let val (n, ss3) = take_numb ss2
        in SOME (BV1 n, ss3)
        end
    | SOME (#"B", ss2) =>
        let val (n, ss3) = take_numb ss2
        in SOME (I2 n, ss3)
        end
    | SOME (#"b", ss2) =>
        let val (n, ss3) = take_numb ss2
        in SOME (BV2 n, ss3)
        end
    | SOME (#"@", ss2) =>
        let
          val (n_opt, (_, ss3)) = (Int.fromString (Substring.string (Substring.takel numeric ss2)),
                                   Substring.splitl numeric ss2)
        in
          case n_opt of
            SOME n => SOME (App n, ss3)
          | NONE => SOME (App 1, ss2)
        end
    | SOME (c, _) => raise Fail ("Bad character in raw encoding: " ^ str c)

in

fun decode_term (tables : sharing_tables) (encoded_str : string) =
  let
    val {termt, stringt, idt, ...} = tables

    fun get_indexed idx =
      if idx < List.length termt then
        (* Reference to sharing table - decode it recursively *)
        (case List.nth (termt, idx) of
           TMV (name_str, _) =>
             Var {name = name_str, ty = TyVar "?"}
          | TMC (idt_idx, _) =>
              if idt_idx < List.length idt then
                let val (thy_idx, name_idx) = List.nth (idt, idt_idx)
                    val name = Vector.sub (stringt, name_idx)
                            handle _ => "<invalid>"
                    val thy = Vector.sub (stringt, thy_idx)
                            handle _ => "<invalid>"
                in
                  Const {name = name, thy = thy, ty = TyVar "?"}
                end
              else
                Const {name = "<invalid>", thy = "<invalid>", ty = TyVar "?"}
         | TMAp (func_idx, arg_idx) =>
             Comb (get_indexed func_idx, get_indexed arg_idx)
         | TMAbs (body_idx, _) =>
             Abs (Bv 0, get_indexed body_idx))
      else
        raise Fail ("Index out of range: " ^ Int.toString idx)

    fun parse (stk, ss) =
      case (stk, lexer ss) of
        (_, SOME (Ident n, rst)) =>
          parse (get_indexed n :: stk, rst)
      | (_, SOME (App n, rst)) =>
          doapps n stk rst
      | (t :: stk, SOME (I1 n, rst)) =>
          let val result = Comb (get_indexed n, t)
          in
             parse (result :: stk, rst)
          end
      | (t :: stk, SOME (BV1 n, rst)) =>
          let val result = Comb (Bv n, t)
          in
             parse (result :: stk, rst)
          end
      | (t2 :: t1 :: stk, SOME (I2 n, rst)) =>
          let val result = Comb (Comb (get_indexed n, t1), t2)
          in
             parse (result :: stk, rst)
          end
      | (t2 :: t1 :: stk, SOME (BV2 n, rst)) =>
          let val result = Comb (Comb (Bv n, t1), t2)
          in
             parse (result :: stk, rst)
          end
      | (body :: bv :: stk, SOME (Lamb, rst)) =>
          let val result = Abs (bv, body)
          in
             parse (result :: stk, rst)
          end
      | (_, SOME (BVar n, rst)) =>
          let val bv = Bv n
          in
             parse (bv :: stk, rst)
          end
      | ([tm], NONE) => tm
      | ([], NONE) => raise Fail "decode_term: empty stack at EOF"
      | (_, NONE) => raise Fail "decode_term: multiple terms at EOF"
      | (_, SOME (Lamb, _)) => raise Fail "decode_term: lambda with small stack"
      | (_, tok) => raise Fail ("decode_term: unexpected token with stack: " ^
                                Int.toString (List.length stk))

    and doapps n stk rst =
      if n = 0 then
        parse (stk, rst)
      else
        case stk of
          (f :: args) =>
            let
              fun apply_n (0, acc, stk') = (acc, stk')
                | apply_n (n, acc, x :: stk') =
                    apply_n (n - 1, Comb (acc, x), stk')
                | apply_n (_, _, []) =
                    raise Fail ("doapps: not enough arguments for " ^ Int.toString n)

              val (result, new_stk) = apply_n (n, f, List.drop (stk, 1))
            in
              parse (result :: new_stk, rst)
            end
        | _ => raise Fail ("doapps: empty stack")

  in
    parse ([], Substring.full encoded_str)
  end

end (* local *)

(* ========================================================================
   Helper functions for term manipulation
   ======================================================================== *)

(* Replace Bv indices in a term body with the given binding variable.
   This emulates Term.dest_abs behavior: walks the term and replaces
   (Bv j) with the binding variable when (i=j), incrementing i for nested Abs. *)
fun dest_abs (Abs(binding_var, body)) : term*term =
    let
      fun subst_at_depth d (Var v) = Var v
        | subst_at_depth d (Const c) = Const c
        | subst_at_depth d (Bv j) = if d = j then binding_var else Bv j
        | subst_at_depth d (Comb (f, arg)) = Comb (subst_at_depth d f, subst_at_depth d arg)
        | subst_at_depth d (Abs (bv, body)) = Abs (bv, subst_at_depth (d + 1) body)
    in
      (binding_var, subst_at_depth 0 body)
    end
    | dest_abs _ = raise Fail "dest_abs: shouldn't happen"

fun strip_abs t = let
  fun recurse A t =
      case t of
          Abs _ => let val (bv,body) = dest_abs t
                   in
                     recurse (bv::A) body
                   end
        | _ => (List.rev A, t)
in
  recurse [] t
end

(* ========================================================================
   Pretty-printing
   ======================================================================== *)

fun pp_type (TyVar name) = name
  | pp_type (TyOp {name, args = []}) = name
  | pp_type (TyOp {name, args}) =
      "(" ^ name ^ " " ^ (String.concatWith " " (map pp_type args)) ^ ")"

fun strip_comb t =
    let fun recurse acc t =
            case t of
                Comb(f,x) => recurse (x::acc) f
              | _ => (t, acc)
    in
      recurse [] t
    end

(* Check if a term matches a specific named constant *)
fun is_const_named (thy, name) (Const {name = n, thy = t, ...}) =
     n = name andalso t = thy
  | is_const_named _ _ = false

fun const_name (Const{name,thy,...}) = (thy,name)
  | const_name _ = ("", "")

fun strip_quant thynm tm =
    let fun recurse A tm =
            case tm of
                Comb(c, bd as Abs _) =>
                if is_const_named thynm c then
                  let val (bv,bod) = dest_abs bd
                  in
                    recurse (bv::A) bod
                  end
                else (List.rev A, tm)
              | _ => (List.rev A, tm)
    in
      recurse [] tm
    end

fun strip_binopr thynm tm =
    let
      fun recurse A tm =
          case tm of
              Comb(Comb(c, t1), t2) => if is_const_named thynm c then
                                         recurse (t1::A) t2
                                       else List.rev (tm::A)
            | _ => List.rev (tm::A)
    in
      recurse [] tm
    end

(* Try to decode a numeral from BIT1/BIT2/ZERO structure *)
fun decode_numeral tm =
    let
      fun bits_to_num (Const {name = "ZERO", thy = "arithmetic", ...}) =
          SOME Arbnum.zero
        | bits_to_num (Comb (Const {name = "BIT1", thy = "arithmetic", ...}, bits)) =
          (case bits_to_num bits of
               NONE => NONE
             | SOME an => SOME (Arbnum.+ (Arbnum.* (an, Arbnum.two), Arbnum.one)))
        | bits_to_num (Comb (Const {name = "BIT2", thy = "arithmetic", ...}, bits)) =
          (case bits_to_num bits of
               NONE => NONE
             | SOME an => SOME (Arbnum.+ (Arbnum.* (an, Arbnum.two), Arbnum.two)))
        | bits_to_num _ = NONE
    in
      case tm of
          Const {name = "0", thy = "num", ...} => SOME (Arbnum.zero)
        | Comb (Const {name = "NUMERAL", thy = "arithmetic", ...}, bits) =>
          bits_to_num bits
        | _ => NONE
    end


(* Pretty-print with special handling for common patterns *)
fun pp_term tm =
  let
    fun atom_name (Var {name, ...}) = name
      | atom_name (Const {name, thy, ...}) =
          if thy = "bool" orelse thy = "min" then name else thy ^ "." ^ name
      | atom_name _ = "??"

    fun pp_internal tm =
      case decode_numeral tm of
          SOME n => Arbnum.toString n
        | NONE =>
          (case strip_comb tm of
               (vca, []) =>
               (case strip_abs vca of
                    ([], vc) => atom_name vc
                  | (bvs, body) => "(lambda (" ^
                                   String.concatWith " " (map atom_name bvs) ^
                                   ") " ^ pp_internal body ^ ")")
             | (f, [x]) =>
               if is_abs x then
                 if is_const_named ("bool", "!") f orelse is_const_named ("bool", "?") f then
                   let
                     val thyn as (_, cn) = const_name f
                     val (bvs, body) = strip_quant thyn tm
                   in
                     "(" ^ (if cn = "!" then "forall" else "exists") ^
                     " (" ^ String.concatWith " " (map atom_name bvs) ^ ") " ^
                     pp_internal body ^ ")"
                   end
                 else
                   pr_comb2 f x
               else pr_comb2 f x
             | (f, [x1, x2]) =>
               if is_const_named ("bool", "/\\") f orelse is_const_named ("bool", "\\/") f then
                 let
                   val thyn as (_, cn) = const_name f
                   val args = strip_binopr thyn tm
                 in
                   "(" ^ (if cn = "/\\" then "and " else "or ") ^
                   String.concatWith " " (map pp_internal args) ^ ")"
                 end
               else "(" ^ String.concatWith " " (map pp_internal (f::[x1,x2])) ^ ")"
             | (f, xs) => "(" ^ String.concatWith " " (map pp_internal (f::xs)) ^ ")")
    and pr_comb2 f x = "(" ^ pp_internal f ^ " " ^ pp_internal x ^ ")"
  in
    pp_internal tm
  end

end
