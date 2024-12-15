structure ringSyntax :> ringSyntax =
struct

open HolKernel boolLib bossLib intSyntax ringLibTheory;

(* ------------------------------------------------------------------------- *)
(* Establish the required grammar(s) for executing this file                 *)
(* ------------------------------------------------------------------------- *)

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars ringLib_grammars
end

open Parse;

val ERR = mk_HOL_ERR "ringSyntax";
fun failwith s = raise ERR "?" s

val ring_add_tm    = “ring_add :'a Ring -> 'a -> 'a -> 'a”;
val ring_sub_tm    = “ring_sub :'a Ring -> 'a -> 'a -> 'a”;
val ring_mul_tm    = “ring_mul :'a Ring -> 'a -> 'a -> 'a”;
val ring_pow_tm    = “ring_pow :'a Ring -> 'a -> num -> 'a”;
val ring_neg_tm    = “ring_neg :'a Ring -> 'a -> 'a”;
val ring_of_num_tm = “ring_of_num :'a Ring -> num -> 'a”;
val ring_of_int_tm = “ring_of_int :'a Ring -> int -> 'a”;

val ring_carrier_tm =
   “ring_carrier :'a Ring -> 'a -> bool”;

val ring_monomorphism_tm =
   “ring_monomorphism :'a Ring # 'b Ring -> ('a -> 'b) -> bool”;

val dest_ring_add    = dest_triop ring_add_tm    (Fail "not a ring_add");
val dest_ring_sub    = dest_triop ring_sub_tm    (Fail "not a ring_sub");
val dest_ring_mul    = dest_triop ring_mul_tm    (Fail "not a ring_mul");
val dest_ring_pow    = dest_triop ring_pow_tm    (Fail "not a ring_pow");
val dest_ring_neg    = dest_binop ring_neg_tm    (Fail "not a ring_neg");
val dest_ring_of_num = dest_binop ring_of_num_tm (Fail "not a ring_of_num");
val dest_ring_of_int = dest_binop ring_of_int_tm (Fail "not a ring_of_num");

fun is_ring_0 tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_const op' andalso let
        val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op'
      in
        Thy = "ringLib" andalso Name = "ring_0"
      end
    end;

fun is_ring_1 tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_const op' andalso let
        val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op'
      in
        Thy = "ringLib" andalso Name = "ring_1"
      end
    end;

fun is_ring_of_num tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_comb op' andalso let
        val (op'',_) = dest_comb op'
      in
        is_const op'' andalso let
          val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op''
        in
          Thy = "ringLib" andalso Name = "ring_of_num"
        end
      end
    end;

fun is_ring_of_int tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_comb op' andalso let
        val (op'',_) = dest_comb op'
      in
        is_const op'' andalso let
          val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op''
        in
          Thy = "ringLib" andalso Name = "ring_of_int"
        end
      end
    end;

fun is_ring_neg tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_comb op' andalso let
        val (op'',_) = dest_comb op'
      in
        is_const op'' andalso let
          val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op''
        in
          Thy = "ringLib" andalso Name = "ring_neg"
        end
      end
    end;

fun is_ring_pow tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_comb op' andalso let
        val (op'',_) = dest_comb op'
      in
        is_comb op'' andalso let
          val (op''',_) = dest_comb op''
        in
          is_const op''' andalso let
            val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op'''
          in
            Thy = "ringLib" andalso Name = "ring_pow"
          end
        end
      end
    end;

fun is_ring_add tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_comb op' andalso let
        val (op'',_) = dest_comb op'
      in
        is_comb op'' andalso let
          val (op''',_) = dest_comb op''
        in
          is_const op''' andalso let
            val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op'''
          in
            Thy = "ringLib" andalso Name = "ring_add"
          end
        end
      end
    end;

fun is_ring_sub tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_comb op' andalso let
        val (op'',_) = dest_comb op'
      in
        is_comb op'' andalso let
          val (op''',_) = dest_comb op''
        in
          is_const op''' andalso let
            val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op'''
          in
            Thy = "ringLib" andalso Name = "ring_sub"
          end
        end
      end
    end;

fun is_ring_mul tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_comb op' andalso let
        val (op'',_) = dest_comb op'
      in
        is_comb op'' andalso let
          val (op''',_) = dest_comb op''
        in
          is_const op''' andalso let
            val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op'''
          in
            Thy = "ringLib" andalso Name = "ring_mul"
          end
        end
      end
    end;

fun is_ringconst tm =
    is_ring_of_int tm andalso is_int_literal (snd (dest_ring_of_int tm));

end (* struct *)
