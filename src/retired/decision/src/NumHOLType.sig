signature NumHOLType =
sig
   type num = NumType.num

   val num_ty : Type.hol_type
   val term_of_num : num -> Term.term
   val num_of_term : Term.term -> num
   val plus : string
   val minus : string
   val mult : string
   val less : string
   val leq : string
   val great : string
   val geq : string
   val suc : string
   val pre : string
end;

