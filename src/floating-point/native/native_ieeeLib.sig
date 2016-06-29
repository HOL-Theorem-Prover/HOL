signature native_ieeeLib =
sig
   val floatToReal : Term.term -> real
   val wordToReal  : Term.term -> real
   val realToFloat : real -> Term.term
   val realToWord  : real -> Term.term
   val native_ty   : Type.hol_type
end
