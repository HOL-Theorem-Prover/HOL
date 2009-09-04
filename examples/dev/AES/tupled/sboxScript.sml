open HolKernel Parse boolLib bossLib pairTools word8Theory;

infix THEN

val _ = new_theory "sbox";


(*---------------------------------------------------------------------------
            Sbox and its inverse.

  val Sbox : word8 list =
  [0wx63, 0wx7c, 0wx77, 0wx7b, 0wxf2, 0wx6b, 0wx6f, 0wxc5,
          0wx30, 0wx01, 0wx67, 0wx2b, 0wxfe, 0wxd7, 0wxab, 0wx76,
   0wxca, 0wx82, 0wxc9, 0wx7d, 0wxfa, 0wx59, 0wx47, 0wxf0,
          0wxad, 0wxd4, 0wxa2, 0wxaf, 0wx9c, 0wxa4, 0wx72, 0wxc0,
   0wxb7, 0wxfd, 0wx93, 0wx26, 0wx36, 0wx3f, 0wxf7, 0wxcc,
          0wx34, 0wxa5, 0wxe5, 0wxf1, 0wx71, 0wxd8, 0wx31, 0wx15,
   0wx04, 0wxc7, 0wx23, 0wxc3, 0wx18, 0wx96, 0wx05, 0wx9a,
          0wx07, 0wx12, 0wx80, 0wxe2, 0wxeb, 0wx27, 0wxb2, 0wx75,
   0wx09, 0wx83, 0wx2c, 0wx1a, 0wx1b, 0wx6e, 0wx5a, 0wxa0,
          0wx52, 0wx3b, 0wxd6, 0wxb3, 0wx29, 0wxe3, 0wx2f, 0wx84,
   0wx53, 0wxd1, 0wx00, 0wxed, 0wx20, 0wxfc, 0wxb1, 0wx5b,
          0wx6a, 0wxcb, 0wxbe, 0wx39, 0wx4a, 0wx4c, 0wx58, 0wxcf,
   0wxd0, 0wxef, 0wxaa, 0wxfb, 0wx43, 0wx4d, 0wx33, 0wx85,
          0wx45, 0wxf9, 0wx02, 0wx7f, 0wx50, 0wx3c, 0wx9f, 0wxa8,
   0wx51, 0wxa3, 0wx40, 0wx8f, 0wx92, 0wx9d, 0wx38, 0wxf5,
          0wxbc, 0wxb6, 0wxda, 0wx21, 0wx10, 0wxff, 0wxf3, 0wxd2,
   0wxcd, 0wx0c, 0wx13, 0wxec, 0wx5f, 0wx97, 0wx44, 0wx17,
          0wxc4, 0wxa7, 0wx7e, 0wx3d, 0wx64, 0wx5d, 0wx19, 0wx73,
   0wx60, 0wx81, 0wx4f, 0wxdc, 0wx22, 0wx2a, 0wx90, 0wx88,
          0wx46, 0wxee, 0wxb8, 0wx14, 0wxde, 0wx5e, 0wx0b, 0wxdb,
   0wxe0, 0wx32, 0wx3a, 0wx0a, 0wx49, 0wx06, 0wx24, 0wx5c,
          0wxc2, 0wxd3, 0wxac, 0wx62, 0wx91, 0wx95, 0wxe4, 0wx79,
   0wxe7, 0wxc8, 0wx37, 0wx6d, 0wx8d, 0wxd5, 0wx4e, 0wxa9,
          0wx6c, 0wx56, 0wxf4, 0wxea, 0wx65, 0wx7a, 0wxae, 0wx08,
   0wxba, 0wx78, 0wx25, 0wx2e, 0wx1c, 0wxa6, 0wxb4, 0wxc6,
          0wxe8, 0wxdd, 0wx74, 0wx1f, 0wx4b, 0wxbd, 0wx8b, 0wx8a,
   0wx70, 0wx3e, 0wxb5, 0wx66, 0wx48, 0wx03, 0wxf6, 0wx0e,
          0wx61, 0wx35, 0wx57, 0wxb9, 0wx86, 0wxc1, 0wx1d, 0wx9e,
   0wxe1, 0wxf8, 0wx98, 0wx11, 0wx69, 0wxd9, 0wx83, 0wx94,
          0wx9b, 0wx1e, 0wx87, 0wxe9, 0wxce, 0wx55, 0wx28, 0wxdf,
   0wx8c, 0wxa1, 0wx89, 0wx0d, 0wxbf, 0wxe6, 0wx42, 0wx68,
          0wx41, 0wx99, 0wx2d, 0wx0f, 0wxb0, 0wx54, 0wxbb, 0wx16]

  val InvSbox : word8 list =
  [0wx52, 0wx09, 0wx6a, 0wxd5, 0wx30, 0wx36, 0wxa5,
          0wx38, 0wxbf, 0wx40, 0wxa3, 0wx9e, 0wx81, 0wxf3, 0wxd7, 0wxfb,
   0wx7c, 0wxe3, 0wx39, 0wx82, 0wx9b, 0wx2f, 0wxff,
          0wx87, 0wx34, 0wx8e, 0wx43, 0wx44, 0wxc4, 0wxde, 0wxe9, 0wxcb,
   0wx54, 0wx7b, 0wx94, 0wx32, 0wxa6, 0wxc2, 0wx23,
          0wx3d, 0wxee, 0wx4c, 0wx95, 0wx0b, 0wx42, 0wxfa, 0wxc3, 0wx4e,
   0wx08, 0wx2e, 0wxa1, 0wx66, 0wx28, 0wxd9, 0wx24,
          0wxb2, 0wx76, 0wx5b, 0wxa2, 0wx49, 0wx6d, 0wx8b, 0wxd1, 0wx25,
   0wx72, 0wxf8, 0wxf6, 0wx64, 0wx86, 0wx68, 0wx98,
          0wx16, 0wxd4, 0wxa4, 0wx5c, 0wxcc, 0wx5d, 0wx65, 0wxb6, 0wx92,
   0wx6c, 0wx70, 0wx48, 0wx50, 0wxfd, 0wxed, 0wxb9,
          0wxda, 0wx5e, 0wx15, 0wx46, 0wx57, 0wxa7, 0wx8d, 0wx9d, 0wx84,
   0wx90, 0wxd8, 0wxab, 0wx00, 0wx8c, 0wxbc, 0wxd3,
          0wx0a, 0wxf7, 0wxe4, 0wx58, 0wx05, 0wxb8, 0wxb3, 0wx45, 0wx06,
   0wxd0, 0wx2c, 0wx1e, 0wx8f, 0wxca, 0wx3f, 0wx0f,
          0wx02, 0wxc1, 0wxaf, 0wxbd, 0wx03, 0wx01, 0wx13, 0wx8a, 0wx6b,
   0wx3a, 0wx91, 0wx11, 0wx41, 0wx4f, 0wx67, 0wxdc,
          0wxea, 0wx97, 0wxf2, 0wxcf, 0wxce, 0wxf0, 0wxb4, 0wxe6, 0wx73,
   0wx96, 0wxac, 0wx74, 0wx22, 0wxe7, 0wxad, 0wx35,
          0wx85, 0wxe2, 0wxf9, 0wx37, 0wxe8, 0wx1c, 0wx75, 0wxdf, 0wx6e,
   0wx47, 0wxf1, 0wx1a, 0wx71, 0wx1d, 0wx29, 0wxc5,
          0wx89, 0wx6f, 0wxb7, 0wx62, 0wx0e, 0wxaa, 0wx18, 0wxbe, 0wx1b,
   0wxfc, 0wx56, 0wx3e, 0wx4b, 0wxc6, 0wxd2, 0wx79,
          0wx20, 0wx9a, 0wxdb, 0wxc0, 0wxfe, 0wx78, 0wxcd, 0wx5a, 0wxf4,
   0wx1f, 0wxdd, 0wxa8, 0wx33, 0wx88, 0wx07, 0wxc7,
          0wx31, 0wxb1, 0wx12, 0wx10, 0wx59, 0wx27, 0wx80, 0wxec, 0wx5f,
   0wx60, 0wx51, 0wx7f, 0wxa9, 0wx19, 0wxb5, 0wx4a,
          0wx0d, 0wx2d, 0wxe5, 0wx7a, 0wx9f, 0wx93, 0wxc9, 0wx9c, 0wxef,
   0wxa0, 0wxe0, 0wx3b, 0wx4d, 0wxae, 0wx2a, 0wxf5,
          0wxb0, 0wxc8, 0wxeb, 0wxbb, 0wx3c, 0wx83, 0wx53, 0wx99, 0wx61,
   0wx17, 0wx2b, 0wx04, 0wx7e, 0wxba, 0wx77, 0wxd6,
          0wx26, 0wxe1, 0wx69, 0wx14, 0wx63, 0wx55, 0wx21, 0wx0c, 0wx7d];

 ---------------------------------------------------------------------------*)



(*---------------------------------------------------------------------------
    Support for constructing HOL Sboxen from ML.
    A byte is represented as bool^8 in HOL.
 ---------------------------------------------------------------------------*)
(*
load "Word8";
datatype bit = T | F;

fun int_of T = 1 | int_of F = 0
fun bit_of 1 = T | bit_of 0 = F

fun char_to_int #"1" = 1 | char_to_int #"0" = 0;
val char_to_bit = bit_of o char_to_int;
fun to_8tuple [a,b,c,d,e,f,g,h] = (a,b,c,d,e,f,g,h);

local fun pad 0 = ""
        | pad 1 = "0"
        | pad 2 = "00"
        | pad 3 = "000"
        | pad 4 = "0000"
        | pad 5 = "00000"
        | pad 6 = "000000"
        | pad 7 = "0000000"
in
fun padword s = pad (8 - String.size s)^s
end

val word8_to_8tuple =
    to_8tuple
  o map char_to_bit
  o String.explode
  o padword
  o Word8.fmt stringCvt.BIN;

val int_to_8tuple = word8_to_8tuple o Word8.fromInt;

fun upto b t acc = if b>t then rev acc else upto (b+1) t (b::acc);
val ilist = upto 0 255 [];
val wlist = map Word8.fromInt ilist;
val blist = map word8_to_8tuple wlist;
*)

(*---------------------------------------------------------------------------
     This is just a one dimensional array indexed by words up to 256.
 ---------------------------------------------------------------------------*)

val Sbox_def =
 Count.apply Define
    `(Sbox (F,F,F,F,F,F,F,F) = (F,T,T,F,F,F,T,T)) /\
     (Sbox (F,F,F,F,F,F,F,T) = (F,T,T,T,T,T,F,F)) /\
     (Sbox (F,F,F,F,F,F,T,F) = (F,T,T,T,F,T,T,T)) /\
     (Sbox (F,F,F,F,F,F,T,T) = (F,T,T,T,T,F,T,T)) /\
     (Sbox (F,F,F,F,F,T,F,F) = (T,T,T,T,F,F,T,F)) /\
     (Sbox (F,F,F,F,F,T,F,T) = (F,T,T,F,T,F,T,T)) /\
     (Sbox (F,F,F,F,F,T,T,F) = (F,T,T,F,T,T,T,T)) /\
     (Sbox (F,F,F,F,F,T,T,T) = (T,T,F,F,F,T,F,T)) /\
     (Sbox (F,F,F,F,T,F,F,F) = (F,F,T,T,F,F,F,F)) /\
     (Sbox (F,F,F,F,T,F,F,T) = (F,F,F,F,F,F,F,T)) /\
     (Sbox (F,F,F,F,T,F,T,F) = (F,T,T,F,F,T,T,T)) /\
     (Sbox (F,F,F,F,T,F,T,T) = (F,F,T,F,T,F,T,T)) /\
     (Sbox (F,F,F,F,T,T,F,F) = (T,T,T,T,T,T,T,F)) /\
     (Sbox (F,F,F,F,T,T,F,T) = (T,T,F,T,F,T,T,T)) /\
     (Sbox (F,F,F,F,T,T,T,F) = (T,F,T,F,T,F,T,T)) /\
     (Sbox (F,F,F,F,T,T,T,T) = (F,T,T,T,F,T,T,F)) /\
     (Sbox (F,F,F,T,F,F,F,F) = (T,T,F,F,T,F,T,F)) /\
     (Sbox (F,F,F,T,F,F,F,T) = (T,F,F,F,F,F,T,F)) /\
     (Sbox (F,F,F,T,F,F,T,F) = (T,T,F,F,T,F,F,T)) /\
     (Sbox (F,F,F,T,F,F,T,T) = (F,T,T,T,T,T,F,T)) /\
     (Sbox (F,F,F,T,F,T,F,F) = (T,T,T,T,T,F,T,F)) /\
     (Sbox (F,F,F,T,F,T,F,T) = (F,T,F,T,T,F,F,T)) /\
     (Sbox (F,F,F,T,F,T,T,F) = (F,T,F,F,F,T,T,T)) /\
     (Sbox (F,F,F,T,F,T,T,T) = (T,T,T,T,F,F,F,F)) /\
     (Sbox (F,F,F,T,T,F,F,F) = (T,F,T,F,T,T,F,T)) /\
     (Sbox (F,F,F,T,T,F,F,T) = (T,T,F,T,F,T,F,F)) /\
     (Sbox (F,F,F,T,T,F,T,F) = (T,F,T,F,F,F,T,F)) /\
     (Sbox (F,F,F,T,T,F,T,T) = (T,F,T,F,T,T,T,T)) /\
     (Sbox (F,F,F,T,T,T,F,F) = (T,F,F,T,T,T,F,F)) /\
     (Sbox (F,F,F,T,T,T,F,T) = (T,F,T,F,F,T,F,F)) /\
     (Sbox (F,F,F,T,T,T,T,F) = (F,T,T,T,F,F,T,F)) /\
     (Sbox (F,F,F,T,T,T,T,T) = (T,T,F,F,F,F,F,F)) /\
     (Sbox (F,F,T,F,F,F,F,F) = (T,F,T,T,F,T,T,T)) /\
     (Sbox (F,F,T,F,F,F,F,T) = (T,T,T,T,T,T,F,T)) /\
     (Sbox (F,F,T,F,F,F,T,F) = (T,F,F,T,F,F,T,T)) /\
     (Sbox (F,F,T,F,F,F,T,T) = (F,F,T,F,F,T,T,F)) /\
     (Sbox (F,F,T,F,F,T,F,F) = (F,F,T,T,F,T,T,F)) /\
     (Sbox (F,F,T,F,F,T,F,T) = (F,F,T,T,T,T,T,T)) /\
     (Sbox (F,F,T,F,F,T,T,F) = (T,T,T,T,F,T,T,T)) /\
     (Sbox (F,F,T,F,F,T,T,T) = (T,T,F,F,T,T,F,F)) /\
     (Sbox (F,F,T,F,T,F,F,F) = (F,F,T,T,F,T,F,F)) /\
     (Sbox (F,F,T,F,T,F,F,T) = (T,F,T,F,F,T,F,T)) /\
     (Sbox (F,F,T,F,T,F,T,F) = (T,T,T,F,F,T,F,T)) /\
     (Sbox (F,F,T,F,T,F,T,T) = (T,T,T,T,F,F,F,T)) /\
     (Sbox (F,F,T,F,T,T,F,F) = (F,T,T,T,F,F,F,T)) /\
     (Sbox (F,F,T,F,T,T,F,T) = (T,T,F,T,T,F,F,F)) /\
     (Sbox (F,F,T,F,T,T,T,F) = (F,F,T,T,F,F,F,T)) /\
     (Sbox (F,F,T,F,T,T,T,T) = (F,F,F,T,F,T,F,T)) /\
     (Sbox (F,F,T,T,F,F,F,F) = (F,F,F,F,F,T,F,F)) /\
     (Sbox (F,F,T,T,F,F,F,T) = (T,T,F,F,F,T,T,T)) /\
     (Sbox (F,F,T,T,F,F,T,F) = (F,F,T,F,F,F,T,T)) /\
     (Sbox (F,F,T,T,F,F,T,T) = (T,T,F,F,F,F,T,T)) /\
     (Sbox (F,F,T,T,F,T,F,F) = (F,F,F,T,T,F,F,F)) /\
     (Sbox (F,F,T,T,F,T,F,T) = (T,F,F,T,F,T,T,F)) /\
     (Sbox (F,F,T,T,F,T,T,F) = (F,F,F,F,F,T,F,T)) /\
     (Sbox (F,F,T,T,F,T,T,T) = (T,F,F,T,T,F,T,F)) /\
     (Sbox (F,F,T,T,T,F,F,F) = (F,F,F,F,F,T,T,T)) /\
     (Sbox (F,F,T,T,T,F,F,T) = (F,F,F,T,F,F,T,F)) /\
     (Sbox (F,F,T,T,T,F,T,F) = (T,F,F,F,F,F,F,F)) /\
     (Sbox (F,F,T,T,T,F,T,T) = (T,T,T,F,F,F,T,F)) /\
     (Sbox (F,F,T,T,T,T,F,F) = (T,T,T,F,T,F,T,T)) /\
     (Sbox (F,F,T,T,T,T,F,T) = (F,F,T,F,F,T,T,T)) /\
     (Sbox (F,F,T,T,T,T,T,F) = (T,F,T,T,F,F,T,F)) /\
     (Sbox (F,F,T,T,T,T,T,T) = (F,T,T,T,F,T,F,T)) /\
     (Sbox (F,T,F,F,F,F,F,F) = (F,F,F,F,T,F,F,T)) /\
     (Sbox (F,T,F,F,F,F,F,T) = (T,F,F,F,F,F,T,T)) /\
     (Sbox (F,T,F,F,F,F,T,F) = (F,F,T,F,T,T,F,F)) /\
     (Sbox (F,T,F,F,F,F,T,T) = (F,F,F,T,T,F,T,F)) /\
     (Sbox (F,T,F,F,F,T,F,F) = (F,F,F,T,T,F,T,T)) /\
     (Sbox (F,T,F,F,F,T,F,T) = (F,T,T,F,T,T,T,F)) /\
     (Sbox (F,T,F,F,F,T,T,F) = (F,T,F,T,T,F,T,F)) /\
     (Sbox (F,T,F,F,F,T,T,T) = (T,F,T,F,F,F,F,F)) /\
     (Sbox (F,T,F,F,T,F,F,F) = (F,T,F,T,F,F,T,F)) /\
     (Sbox (F,T,F,F,T,F,F,T) = (F,F,T,T,T,F,T,T)) /\
     (Sbox (F,T,F,F,T,F,T,F) = (T,T,F,T,F,T,T,F)) /\
     (Sbox (F,T,F,F,T,F,T,T) = (T,F,T,T,F,F,T,T)) /\
     (Sbox (F,T,F,F,T,T,F,F) = (F,F,T,F,T,F,F,T)) /\
     (Sbox (F,T,F,F,T,T,F,T) = (T,T,T,F,F,F,T,T)) /\
     (Sbox (F,T,F,F,T,T,T,F) = (F,F,T,F,T,T,T,T)) /\
     (Sbox (F,T,F,F,T,T,T,T) = (T,F,F,F,F,T,F,F)) /\
     (Sbox (F,T,F,T,F,F,F,F) = (F,T,F,T,F,F,T,T)) /\
     (Sbox (F,T,F,T,F,F,F,T) = (T,T,F,T,F,F,F,T)) /\
     (Sbox (F,T,F,T,F,F,T,F) = (F,F,F,F,F,F,F,F)) /\
     (Sbox (F,T,F,T,F,F,T,T) = (T,T,T,F,T,T,F,T)) /\
     (Sbox (F,T,F,T,F,T,F,F) = (F,F,T,F,F,F,F,F)) /\
     (Sbox (F,T,F,T,F,T,F,T) = (T,T,T,T,T,T,F,F)) /\
     (Sbox (F,T,F,T,F,T,T,F) = (T,F,T,T,F,F,F,T)) /\
     (Sbox (F,T,F,T,F,T,T,T) = (F,T,F,T,T,F,T,T)) /\
     (Sbox (F,T,F,T,T,F,F,F) = (F,T,T,F,T,F,T,F)) /\
     (Sbox (F,T,F,T,T,F,F,T) = (T,T,F,F,T,F,T,T)) /\
     (Sbox (F,T,F,T,T,F,T,F) = (T,F,T,T,T,T,T,F)) /\
     (Sbox (F,T,F,T,T,F,T,T) = (F,F,T,T,T,F,F,T)) /\
     (Sbox (F,T,F,T,T,T,F,F) = (F,T,F,F,T,F,T,F)) /\
     (Sbox (F,T,F,T,T,T,F,T) = (F,T,F,F,T,T,F,F)) /\
     (Sbox (F,T,F,T,T,T,T,F) = (F,T,F,T,T,F,F,F)) /\
     (Sbox (F,T,F,T,T,T,T,T) = (T,T,F,F,T,T,T,T)) /\
     (Sbox (F,T,T,F,F,F,F,F) = (T,T,F,T,F,F,F,F)) /\
     (Sbox (F,T,T,F,F,F,F,T) = (T,T,T,F,T,T,T,T)) /\
     (Sbox (F,T,T,F,F,F,T,F) = (T,F,T,F,T,F,T,F)) /\
     (Sbox (F,T,T,F,F,F,T,T) = (T,T,T,T,T,F,T,T)) /\
     (Sbox (F,T,T,F,F,T,F,F) = (F,T,F,F,F,F,T,T)) /\
     (Sbox (F,T,T,F,F,T,F,T) = (F,T,F,F,T,T,F,T)) /\
     (Sbox (F,T,T,F,F,T,T,F) = (F,F,T,T,F,F,T,T)) /\
     (Sbox (F,T,T,F,F,T,T,T) = (T,F,F,F,F,T,F,T)) /\
     (Sbox (F,T,T,F,T,F,F,F) = (F,T,F,F,F,T,F,T)) /\
     (Sbox (F,T,T,F,T,F,F,T) = (T,T,T,T,T,F,F,T)) /\
     (Sbox (F,T,T,F,T,F,T,F) = (F,F,F,F,F,F,T,F)) /\
     (Sbox (F,T,T,F,T,F,T,T) = (F,T,T,T,T,T,T,T)) /\
     (Sbox (F,T,T,F,T,T,F,F) = (F,T,F,T,F,F,F,F)) /\
     (Sbox (F,T,T,F,T,T,F,T) = (F,F,T,T,T,T,F,F)) /\
     (Sbox (F,T,T,F,T,T,T,F) = (T,F,F,T,T,T,T,T)) /\
     (Sbox (F,T,T,F,T,T,T,T) = (T,F,T,F,T,F,F,F)) /\
     (Sbox (F,T,T,T,F,F,F,F) = (F,T,F,T,F,F,F,T)) /\
     (Sbox (F,T,T,T,F,F,F,T) = (T,F,T,F,F,F,T,T)) /\
     (Sbox (F,T,T,T,F,F,T,F) = (F,T,F,F,F,F,F,F)) /\
     (Sbox (F,T,T,T,F,F,T,T) = (T,F,F,F,T,T,T,T)) /\
     (Sbox (F,T,T,T,F,T,F,F) = (T,F,F,T,F,F,T,F)) /\
     (Sbox (F,T,T,T,F,T,F,T) = (T,F,F,T,T,T,F,T)) /\
     (Sbox (F,T,T,T,F,T,T,F) = (F,F,T,T,T,F,F,F)) /\
     (Sbox (F,T,T,T,F,T,T,T) = (T,T,T,T,F,T,F,T)) /\
     (Sbox (F,T,T,T,T,F,F,F) = (T,F,T,T,T,T,F,F)) /\
     (Sbox (F,T,T,T,T,F,F,T) = (T,F,T,T,F,T,T,F)) /\
     (Sbox (F,T,T,T,T,F,T,F) = (T,T,F,T,T,F,T,F)) /\
     (Sbox (F,T,T,T,T,F,T,T) = (F,F,T,F,F,F,F,T)) /\
     (Sbox (F,T,T,T,T,T,F,F) = (F,F,F,T,F,F,F,F)) /\
     (Sbox (F,T,T,T,T,T,F,T) = (T,T,T,T,T,T,T,T)) /\
     (Sbox (F,T,T,T,T,T,T,F) = (T,T,T,T,F,F,T,T)) /\
     (Sbox (F,T,T,T,T,T,T,T) = (T,T,F,T,F,F,T,F)) /\
     (Sbox (T,F,F,F,F,F,F,F) = (T,T,F,F,T,T,F,T)) /\
     (Sbox (T,F,F,F,F,F,F,T) = (F,F,F,F,T,T,F,F)) /\
     (Sbox (T,F,F,F,F,F,T,F) = (F,F,F,T,F,F,T,T)) /\
     (Sbox (T,F,F,F,F,F,T,T) = (T,T,T,F,T,T,F,F)) /\
     (Sbox (T,F,F,F,F,T,F,F) = (F,T,F,T,T,T,T,T)) /\
     (Sbox (T,F,F,F,F,T,F,T) = (T,F,F,T,F,T,T,T)) /\
     (Sbox (T,F,F,F,F,T,T,F) = (F,T,F,F,F,T,F,F)) /\
     (Sbox (T,F,F,F,F,T,T,T) = (F,F,F,T,F,T,T,T)) /\
     (Sbox (T,F,F,F,T,F,F,F) = (T,T,F,F,F,T,F,F)) /\
     (Sbox (T,F,F,F,T,F,F,T) = (T,F,T,F,F,T,T,T)) /\
     (Sbox (T,F,F,F,T,F,T,F) = (F,T,T,T,T,T,T,F)) /\
     (Sbox (T,F,F,F,T,F,T,T) = (F,F,T,T,T,T,F,T)) /\
     (Sbox (T,F,F,F,T,T,F,F) = (F,T,T,F,F,T,F,F)) /\
     (Sbox (T,F,F,F,T,T,F,T) = (F,T,F,T,T,T,F,T)) /\
     (Sbox (T,F,F,F,T,T,T,F) = (F,F,F,T,T,F,F,T)) /\
     (Sbox (T,F,F,F,T,T,T,T) = (F,T,T,T,F,F,T,T)) /\
     (Sbox (T,F,F,T,F,F,F,F) = (F,T,T,F,F,F,F,F)) /\
     (Sbox (T,F,F,T,F,F,F,T) = (T,F,F,F,F,F,F,T)) /\
     (Sbox (T,F,F,T,F,F,T,F) = (F,T,F,F,T,T,T,T)) /\
     (Sbox (T,F,F,T,F,F,T,T) = (T,T,F,T,T,T,F,F)) /\
     (Sbox (T,F,F,T,F,T,F,F) = (F,F,T,F,F,F,T,F)) /\
     (Sbox (T,F,F,T,F,T,F,T) = (F,F,T,F,T,F,T,F)) /\
     (Sbox (T,F,F,T,F,T,T,F) = (T,F,F,T,F,F,F,F)) /\
     (Sbox (T,F,F,T,F,T,T,T) = (T,F,F,F,T,F,F,F)) /\
     (Sbox (T,F,F,T,T,F,F,F) = (F,T,F,F,F,T,T,F)) /\
     (Sbox (T,F,F,T,T,F,F,T) = (T,T,T,F,T,T,T,F)) /\
     (Sbox (T,F,F,T,T,F,T,F) = (T,F,T,T,T,F,F,F)) /\
     (Sbox (T,F,F,T,T,F,T,T) = (F,F,F,T,F,T,F,F)) /\
     (Sbox (T,F,F,T,T,T,F,F) = (T,T,F,T,T,T,T,F)) /\
     (Sbox (T,F,F,T,T,T,F,T) = (F,T,F,T,T,T,T,F)) /\
     (Sbox (T,F,F,T,T,T,T,F) = (F,F,F,F,T,F,T,T)) /\
     (Sbox (T,F,F,T,T,T,T,T) = (T,T,F,T,T,F,T,T)) /\
     (Sbox (T,F,T,F,F,F,F,F) = (T,T,T,F,F,F,F,F)) /\
     (Sbox (T,F,T,F,F,F,F,T) = (F,F,T,T,F,F,T,F)) /\
     (Sbox (T,F,T,F,F,F,T,F) = (F,F,T,T,T,F,T,F)) /\
     (Sbox (T,F,T,F,F,F,T,T) = (F,F,F,F,T,F,T,F)) /\
     (Sbox (T,F,T,F,F,T,F,F) = (F,T,F,F,T,F,F,T)) /\
     (Sbox (T,F,T,F,F,T,F,T) = (F,F,F,F,F,T,T,F)) /\
     (Sbox (T,F,T,F,F,T,T,F) = (F,F,T,F,F,T,F,F)) /\
     (Sbox (T,F,T,F,F,T,T,T) = (F,T,F,T,T,T,F,F)) /\
     (Sbox (T,F,T,F,T,F,F,F) = (T,T,F,F,F,F,T,F)) /\
     (Sbox (T,F,T,F,T,F,F,T) = (T,T,F,T,F,F,T,T)) /\
     (Sbox (T,F,T,F,T,F,T,F) = (T,F,T,F,T,T,F,F)) /\
     (Sbox (T,F,T,F,T,F,T,T) = (F,T,T,F,F,F,T,F)) /\
     (Sbox (T,F,T,F,T,T,F,F) = (T,F,F,T,F,F,F,T)) /\
     (Sbox (T,F,T,F,T,T,F,T) = (T,F,F,T,F,T,F,T)) /\
     (Sbox (T,F,T,F,T,T,T,F) = (T,T,T,F,F,T,F,F)) /\
     (Sbox (T,F,T,F,T,T,T,T) = (F,T,T,T,T,F,F,T)) /\
     (Sbox (T,F,T,T,F,F,F,F) = (T,T,T,F,F,T,T,T)) /\
     (Sbox (T,F,T,T,F,F,F,T) = (T,T,F,F,T,F,F,F)) /\
     (Sbox (T,F,T,T,F,F,T,F) = (F,F,T,T,F,T,T,T)) /\
     (Sbox (T,F,T,T,F,F,T,T) = (F,T,T,F,T,T,F,T)) /\
     (Sbox (T,F,T,T,F,T,F,F) = (T,F,F,F,T,T,F,T)) /\
     (Sbox (T,F,T,T,F,T,F,T) = (T,T,F,T,F,T,F,T)) /\
     (Sbox (T,F,T,T,F,T,T,F) = (F,T,F,F,T,T,T,F)) /\
     (Sbox (T,F,T,T,F,T,T,T) = (T,F,T,F,T,F,F,T)) /\
     (Sbox (T,F,T,T,T,F,F,F) = (F,T,T,F,T,T,F,F)) /\
     (Sbox (T,F,T,T,T,F,F,T) = (F,T,F,T,F,T,T,F)) /\
     (Sbox (T,F,T,T,T,F,T,F) = (T,T,T,T,F,T,F,F)) /\
     (Sbox (T,F,T,T,T,F,T,T) = (T,T,T,F,T,F,T,F)) /\
     (Sbox (T,F,T,T,T,T,F,F) = (F,T,T,F,F,T,F,T)) /\
     (Sbox (T,F,T,T,T,T,F,T) = (F,T,T,T,T,F,T,F)) /\
     (Sbox (T,F,T,T,T,T,T,F) = (T,F,T,F,T,T,T,F)) /\
     (Sbox (T,F,T,T,T,T,T,T) = (F,F,F,F,T,F,F,F)) /\
     (Sbox (T,T,F,F,F,F,F,F) = (T,F,T,T,T,F,T,F)) /\
     (Sbox (T,T,F,F,F,F,F,T) = (F,T,T,T,T,F,F,F)) /\
     (Sbox (T,T,F,F,F,F,T,F) = (F,F,T,F,F,T,F,T)) /\
     (Sbox (T,T,F,F,F,F,T,T) = (F,F,T,F,T,T,T,F)) /\
     (Sbox (T,T,F,F,F,T,F,F) = (F,F,F,T,T,T,F,F)) /\
     (Sbox (T,T,F,F,F,T,F,T) = (T,F,T,F,F,T,T,F)) /\
     (Sbox (T,T,F,F,F,T,T,F) = (T,F,T,T,F,T,F,F)) /\
     (Sbox (T,T,F,F,F,T,T,T) = (T,T,F,F,F,T,T,F)) /\
     (Sbox (T,T,F,F,T,F,F,F) = (T,T,T,F,T,F,F,F)) /\
     (Sbox (T,T,F,F,T,F,F,T) = (T,T,F,T,T,T,F,T)) /\
     (Sbox (T,T,F,F,T,F,T,F) = (F,T,T,T,F,T,F,F)) /\
     (Sbox (T,T,F,F,T,F,T,T) = (F,F,F,T,T,T,T,T)) /\
     (Sbox (T,T,F,F,T,T,F,F) = (F,T,F,F,T,F,T,T)) /\
     (Sbox (T,T,F,F,T,T,F,T) = (T,F,T,T,T,T,F,T)) /\
     (Sbox (T,T,F,F,T,T,T,F) = (T,F,F,F,T,F,T,T)) /\
     (Sbox (T,T,F,F,T,T,T,T) = (T,F,F,F,T,F,T,F)) /\
     (Sbox (T,T,F,T,F,F,F,F) = (F,T,T,T,F,F,F,F)) /\
     (Sbox (T,T,F,T,F,F,F,T) = (F,F,T,T,T,T,T,F)) /\
     (Sbox (T,T,F,T,F,F,T,F) = (T,F,T,T,F,T,F,T)) /\
     (Sbox (T,T,F,T,F,F,T,T) = (F,T,T,F,F,T,T,F)) /\
     (Sbox (T,T,F,T,F,T,F,F) = (F,T,F,F,T,F,F,F)) /\
     (Sbox (T,T,F,T,F,T,F,T) = (F,F,F,F,F,F,T,T)) /\
     (Sbox (T,T,F,T,F,T,T,F) = (T,T,T,T,F,T,T,F)) /\
     (Sbox (T,T,F,T,F,T,T,T) = (F,F,F,F,T,T,T,F)) /\
     (Sbox (T,T,F,T,T,F,F,F) = (F,T,T,F,F,F,F,T)) /\
     (Sbox (T,T,F,T,T,F,F,T) = (F,F,T,T,F,T,F,T)) /\
     (Sbox (T,T,F,T,T,F,T,F) = (F,T,F,T,F,T,T,T)) /\
     (Sbox (T,T,F,T,T,F,T,T) = (T,F,T,T,T,F,F,T)) /\
     (Sbox (T,T,F,T,T,T,F,F) = (T,F,F,F,F,T,T,F)) /\
     (Sbox (T,T,F,T,T,T,F,T) = (T,T,F,F,F,F,F,T)) /\
     (Sbox (T,T,F,T,T,T,T,F) = (F,F,F,T,T,T,F,T)) /\
     (Sbox (T,T,F,T,T,T,T,T) = (T,F,F,T,T,T,T,F)) /\
     (Sbox (T,T,T,F,F,F,F,F) = (T,T,T,F,F,F,F,T)) /\
     (Sbox (T,T,T,F,F,F,F,T) = (T,T,T,T,T,F,F,F)) /\
     (Sbox (T,T,T,F,F,F,T,F) = (T,F,F,T,T,F,F,F)) /\
     (Sbox (T,T,T,F,F,F,T,T) = (F,F,F,T,F,F,F,T)) /\
     (Sbox (T,T,T,F,F,T,F,F) = (F,T,T,F,T,F,F,T)) /\
     (Sbox (T,T,T,F,F,T,F,T) = (T,T,F,T,T,F,F,T)) /\
     (Sbox (T,T,T,F,F,T,T,F) = (T,F,F,F,T,T,T,F)) /\
     (Sbox (T,T,T,F,F,T,T,T) = (T,F,F,T,F,T,F,F)) /\
     (Sbox (T,T,T,F,T,F,F,F) = (T,F,F,T,T,F,T,T)) /\
     (Sbox (T,T,T,F,T,F,F,T) = (F,F,F,T,T,T,T,F)) /\
     (Sbox (T,T,T,F,T,F,T,F) = (T,F,F,F,F,T,T,T)) /\
     (Sbox (T,T,T,F,T,F,T,T) = (T,T,T,F,T,F,F,T)) /\
     (Sbox (T,T,T,F,T,T,F,F) = (T,T,F,F,T,T,T,F)) /\
     (Sbox (T,T,T,F,T,T,F,T) = (F,T,F,T,F,T,F,T)) /\
     (Sbox (T,T,T,F,T,T,T,F) = (F,F,T,F,T,F,F,F)) /\
     (Sbox (T,T,T,F,T,T,T,T) = (T,T,F,T,T,T,T,T)) /\
     (Sbox (T,T,T,T,F,F,F,F) = (T,F,F,F,T,T,F,F)) /\
     (Sbox (T,T,T,T,F,F,F,T) = (T,F,T,F,F,F,F,T)) /\
     (Sbox (T,T,T,T,F,F,T,F) = (T,F,F,F,T,F,F,T)) /\
     (Sbox (T,T,T,T,F,F,T,T) = (F,F,F,F,T,T,F,T)) /\
     (Sbox (T,T,T,T,F,T,F,F) = (T,F,T,T,T,T,T,T)) /\
     (Sbox (T,T,T,T,F,T,F,T) = (T,T,T,F,F,T,T,F)) /\
     (Sbox (T,T,T,T,F,T,T,F) = (F,T,F,F,F,F,T,F)) /\
     (Sbox (T,T,T,T,F,T,T,T) = (F,T,T,F,T,F,F,F)) /\
     (Sbox (T,T,T,T,T,F,F,F) = (F,T,F,F,F,F,F,T)) /\
     (Sbox (T,T,T,T,T,F,F,T) = (T,F,F,T,T,F,F,T)) /\
     (Sbox (T,T,T,T,T,F,T,F) = (F,F,T,F,T,T,F,T)) /\
     (Sbox (T,T,T,T,T,F,T,T) = (F,F,F,F,T,T,T,T)) /\
     (Sbox (T,T,T,T,T,T,F,F) = (T,F,T,T,F,F,F,F)) /\
     (Sbox (T,T,T,T,T,T,F,T) = (F,T,F,T,F,T,F,F)) /\
     (Sbox (T,T,T,T,T,T,T,F) = (T,F,T,T,T,F,T,T)) /\
     (Sbox (T,T,T,T,T,T,T,T) = (F,F,F,T,F,T,T,F))`;


val InvSbox_def =
 Count.apply Define
    `(InvSbox(F,F,F,F,F,F,F,F) = (F,T,F,T,F,F,T,F)) /\
     (InvSbox(F,F,F,F,F,F,F,T) = (F,F,F,F,T,F,F,T)) /\
     (InvSbox(F,F,F,F,F,F,T,F) = (F,T,T,F,T,F,T,F)) /\
     (InvSbox(F,F,F,F,F,F,T,T) = (T,T,F,T,F,T,F,T)) /\
     (InvSbox(F,F,F,F,F,T,F,F) = (F,F,T,T,F,F,F,F)) /\
     (InvSbox(F,F,F,F,F,T,F,T) = (F,F,T,T,F,T,T,F)) /\
     (InvSbox(F,F,F,F,F,T,T,F) = (T,F,T,F,F,T,F,T)) /\
     (InvSbox(F,F,F,F,F,T,T,T) = (F,F,T,T,T,F,F,F)) /\
     (InvSbox(F,F,F,F,T,F,F,F) = (T,F,T,T,T,T,T,T)) /\
     (InvSbox(F,F,F,F,T,F,F,T) = (F,T,F,F,F,F,F,F)) /\
     (InvSbox(F,F,F,F,T,F,T,F) = (T,F,T,F,F,F,T,T)) /\
     (InvSbox(F,F,F,F,T,F,T,T) = (T,F,F,T,T,T,T,F)) /\
     (InvSbox(F,F,F,F,T,T,F,F) = (T,F,F,F,F,F,F,T)) /\
     (InvSbox(F,F,F,F,T,T,F,T) = (T,T,T,T,F,F,T,T)) /\
     (InvSbox(F,F,F,F,T,T,T,F) = (T,T,F,T,F,T,T,T)) /\
     (InvSbox(F,F,F,F,T,T,T,T) = (T,T,T,T,T,F,T,T)) /\
     (InvSbox(F,F,F,T,F,F,F,F) = (F,T,T,T,T,T,F,F)) /\
     (InvSbox(F,F,F,T,F,F,F,T) = (T,T,T,F,F,F,T,T)) /\
     (InvSbox(F,F,F,T,F,F,T,F) = (F,F,T,T,T,F,F,T)) /\
     (InvSbox(F,F,F,T,F,F,T,T) = (T,F,F,F,F,F,T,F)) /\
     (InvSbox(F,F,F,T,F,T,F,F) = (T,F,F,T,T,F,T,T)) /\
     (InvSbox(F,F,F,T,F,T,F,T) = (F,F,T,F,T,T,T,T)) /\
     (InvSbox(F,F,F,T,F,T,T,F) = (T,T,T,T,T,T,T,T)) /\
     (InvSbox(F,F,F,T,F,T,T,T) = (T,F,F,F,F,T,T,T)) /\
     (InvSbox(F,F,F,T,T,F,F,F) = (F,F,T,T,F,T,F,F)) /\
     (InvSbox(F,F,F,T,T,F,F,T) = (T,F,F,F,T,T,T,F)) /\
     (InvSbox(F,F,F,T,T,F,T,F) = (F,T,F,F,F,F,T,T)) /\
     (InvSbox(F,F,F,T,T,F,T,T) = (F,T,F,F,F,T,F,F)) /\
     (InvSbox(F,F,F,T,T,T,F,F) = (T,T,F,F,F,T,F,F)) /\
     (InvSbox(F,F,F,T,T,T,F,T) = (T,T,F,T,T,T,T,F)) /\
     (InvSbox(F,F,F,T,T,T,T,F) = (T,T,T,F,T,F,F,T)) /\
     (InvSbox(F,F,F,T,T,T,T,T) = (T,T,F,F,T,F,T,T)) /\
     (InvSbox(F,F,T,F,F,F,F,F) = (F,T,F,T,F,T,F,F)) /\
     (InvSbox(F,F,T,F,F,F,F,T) = (F,T,T,T,T,F,T,T)) /\
     (InvSbox(F,F,T,F,F,F,T,F) = (T,F,F,T,F,T,F,F)) /\
     (InvSbox(F,F,T,F,F,F,T,T) = (F,F,T,T,F,F,T,F)) /\
     (InvSbox(F,F,T,F,F,T,F,F) = (T,F,T,F,F,T,T,F)) /\
     (InvSbox(F,F,T,F,F,T,F,T) = (T,T,F,F,F,F,T,F)) /\
     (InvSbox(F,F,T,F,F,T,T,F) = (F,F,T,F,F,F,T,T)) /\
     (InvSbox(F,F,T,F,F,T,T,T) = (F,F,T,T,T,T,F,T)) /\
     (InvSbox(F,F,T,F,T,F,F,F) = (T,T,T,F,T,T,T,F)) /\
     (InvSbox(F,F,T,F,T,F,F,T) = (F,T,F,F,T,T,F,F)) /\
     (InvSbox(F,F,T,F,T,F,T,F) = (T,F,F,T,F,T,F,T)) /\
     (InvSbox(F,F,T,F,T,F,T,T) = (F,F,F,F,T,F,T,T)) /\
     (InvSbox(F,F,T,F,T,T,F,F) = (F,T,F,F,F,F,T,F)) /\
     (InvSbox(F,F,T,F,T,T,F,T) = (T,T,T,T,T,F,T,F)) /\
     (InvSbox(F,F,T,F,T,T,T,F) = (T,T,F,F,F,F,T,T)) /\
     (InvSbox(F,F,T,F,T,T,T,T) = (F,T,F,F,T,T,T,F)) /\
     (InvSbox(F,F,T,T,F,F,F,F) = (F,F,F,F,T,F,F,F)) /\
     (InvSbox(F,F,T,T,F,F,F,T) = (F,F,T,F,T,T,T,F)) /\
     (InvSbox(F,F,T,T,F,F,T,F) = (T,F,T,F,F,F,F,T)) /\
     (InvSbox(F,F,T,T,F,F,T,T) = (F,T,T,F,F,T,T,F)) /\
     (InvSbox(F,F,T,T,F,T,F,F) = (F,F,T,F,T,F,F,F)) /\
     (InvSbox(F,F,T,T,F,T,F,T) = (T,T,F,T,T,F,F,T)) /\
     (InvSbox(F,F,T,T,F,T,T,F) = (F,F,T,F,F,T,F,F)) /\
     (InvSbox(F,F,T,T,F,T,T,T) = (T,F,T,T,F,F,T,F)) /\
     (InvSbox(F,F,T,T,T,F,F,F) = (F,T,T,T,F,T,T,F)) /\
     (InvSbox(F,F,T,T,T,F,F,T) = (F,T,F,T,T,F,T,T)) /\
     (InvSbox(F,F,T,T,T,F,T,F) = (T,F,T,F,F,F,T,F)) /\
     (InvSbox(F,F,T,T,T,F,T,T) = (F,T,F,F,T,F,F,T)) /\
     (InvSbox(F,F,T,T,T,T,F,F) = (F,T,T,F,T,T,F,T)) /\
     (InvSbox(F,F,T,T,T,T,F,T) = (T,F,F,F,T,F,T,T)) /\
     (InvSbox(F,F,T,T,T,T,T,F) = (T,T,F,T,F,F,F,T)) /\
     (InvSbox(F,F,T,T,T,T,T,T) = (F,F,T,F,F,T,F,T)) /\
     (InvSbox(F,T,F,F,F,F,F,F) = (F,T,T,T,F,F,T,F)) /\
     (InvSbox(F,T,F,F,F,F,F,T) = (T,T,T,T,T,F,F,F)) /\
     (InvSbox(F,T,F,F,F,F,T,F) = (T,T,T,T,F,T,T,F)) /\
     (InvSbox(F,T,F,F,F,F,T,T) = (F,T,T,F,F,T,F,F)) /\
     (InvSbox(F,T,F,F,F,T,F,F) = (T,F,F,F,F,T,T,F)) /\
     (InvSbox(F,T,F,F,F,T,F,T) = (F,T,T,F,T,F,F,F)) /\
     (InvSbox(F,T,F,F,F,T,T,F) = (T,F,F,T,T,F,F,F)) /\
     (InvSbox(F,T,F,F,F,T,T,T) = (F,F,F,T,F,T,T,F)) /\
     (InvSbox(F,T,F,F,T,F,F,F) = (T,T,F,T,F,T,F,F)) /\
     (InvSbox(F,T,F,F,T,F,F,T) = (T,F,T,F,F,T,F,F)) /\
     (InvSbox(F,T,F,F,T,F,T,F) = (F,T,F,T,T,T,F,F)) /\
     (InvSbox(F,T,F,F,T,F,T,T) = (T,T,F,F,T,T,F,F)) /\
     (InvSbox(F,T,F,F,T,T,F,F) = (F,T,F,T,T,T,F,T)) /\
     (InvSbox(F,T,F,F,T,T,F,T) = (F,T,T,F,F,T,F,T)) /\
     (InvSbox(F,T,F,F,T,T,T,F) = (T,F,T,T,F,T,T,F)) /\
     (InvSbox(F,T,F,F,T,T,T,T) = (T,F,F,T,F,F,T,F)) /\
     (InvSbox(F,T,F,T,F,F,F,F) = (F,T,T,F,T,T,F,F)) /\
     (InvSbox(F,T,F,T,F,F,F,T) = (F,T,T,T,F,F,F,F)) /\
     (InvSbox(F,T,F,T,F,F,T,F) = (F,T,F,F,T,F,F,F)) /\
     (InvSbox(F,T,F,T,F,F,T,T) = (F,T,F,T,F,F,F,F)) /\
     (InvSbox(F,T,F,T,F,T,F,F) = (T,T,T,T,T,T,F,T)) /\
     (InvSbox(F,T,F,T,F,T,F,T) = (T,T,T,F,T,T,F,T)) /\
     (InvSbox(F,T,F,T,F,T,T,F) = (T,F,T,T,T,F,F,T)) /\
     (InvSbox(F,T,F,T,F,T,T,T) = (T,T,F,T,T,F,T,F)) /\
     (InvSbox(F,T,F,T,T,F,F,F) = (F,T,F,T,T,T,T,F)) /\
     (InvSbox(F,T,F,T,T,F,F,T) = (F,F,F,T,F,T,F,T)) /\
     (InvSbox(F,T,F,T,T,F,T,F) = (F,T,F,F,F,T,T,F)) /\
     (InvSbox(F,T,F,T,T,F,T,T) = (F,T,F,T,F,T,T,T)) /\
     (InvSbox(F,T,F,T,T,T,F,F) = (T,F,T,F,F,T,T,T)) /\
     (InvSbox(F,T,F,T,T,T,F,T) = (T,F,F,F,T,T,F,T)) /\
     (InvSbox(F,T,F,T,T,T,T,F) = (T,F,F,T,T,T,F,T)) /\
     (InvSbox(F,T,F,T,T,T,T,T) = (T,F,F,F,F,T,F,F)) /\
     (InvSbox(F,T,T,F,F,F,F,F) = (T,F,F,T,F,F,F,F)) /\
     (InvSbox(F,T,T,F,F,F,F,T) = (T,T,F,T,T,F,F,F)) /\
     (InvSbox(F,T,T,F,F,F,T,F) = (T,F,T,F,T,F,T,T)) /\
     (InvSbox(F,T,T,F,F,F,T,T) = (F,F,F,F,F,F,F,F)) /\
     (InvSbox(F,T,T,F,F,T,F,F) = (T,F,F,F,T,T,F,F)) /\
     (InvSbox(F,T,T,F,F,T,F,T) = (T,F,T,T,T,T,F,F)) /\
     (InvSbox(F,T,T,F,F,T,T,F) = (T,T,F,T,F,F,T,T)) /\
     (InvSbox(F,T,T,F,F,T,T,T) = (F,F,F,F,T,F,T,F)) /\
     (InvSbox(F,T,T,F,T,F,F,F) = (T,T,T,T,F,T,T,T)) /\
     (InvSbox(F,T,T,F,T,F,F,T) = (T,T,T,F,F,T,F,F)) /\
     (InvSbox(F,T,T,F,T,F,T,F) = (F,T,F,T,T,F,F,F)) /\
     (InvSbox(F,T,T,F,T,F,T,T) = (F,F,F,F,F,T,F,T)) /\
     (InvSbox(F,T,T,F,T,T,F,F) = (T,F,T,T,T,F,F,F)) /\
     (InvSbox(F,T,T,F,T,T,F,T) = (T,F,T,T,F,F,T,T)) /\
     (InvSbox(F,T,T,F,T,T,T,F) = (F,T,F,F,F,T,F,T)) /\
     (InvSbox(F,T,T,F,T,T,T,T) = (F,F,F,F,F,T,T,F)) /\
     (InvSbox(F,T,T,T,F,F,F,F) = (T,T,F,T,F,F,F,F)) /\
     (InvSbox(F,T,T,T,F,F,F,T) = (F,F,T,F,T,T,F,F)) /\
     (InvSbox(F,T,T,T,F,F,T,F) = (F,F,F,T,T,T,T,F)) /\
     (InvSbox(F,T,T,T,F,F,T,T) = (T,F,F,F,T,T,T,T)) /\
     (InvSbox(F,T,T,T,F,T,F,F) = (T,T,F,F,T,F,T,F)) /\
     (InvSbox(F,T,T,T,F,T,F,T) = (F,F,T,T,T,T,T,T)) /\
     (InvSbox(F,T,T,T,F,T,T,F) = (F,F,F,F,T,T,T,T)) /\
     (InvSbox(F,T,T,T,F,T,T,T) = (F,F,F,F,F,F,T,F)) /\
     (InvSbox(F,T,T,T,T,F,F,F) = (T,T,F,F,F,F,F,T)) /\
     (InvSbox(F,T,T,T,T,F,F,T) = (T,F,T,F,T,T,T,T)) /\
     (InvSbox(F,T,T,T,T,F,T,F) = (T,F,T,T,T,T,F,T)) /\
     (InvSbox(F,T,T,T,T,F,T,T) = (F,F,F,F,F,F,T,T)) /\
     (InvSbox(F,T,T,T,T,T,F,F) = (F,F,F,F,F,F,F,T)) /\
     (InvSbox(F,T,T,T,T,T,F,T) = (F,F,F,T,F,F,T,T)) /\
     (InvSbox(F,T,T,T,T,T,T,F) = (T,F,F,F,T,F,T,F)) /\
     (InvSbox(F,T,T,T,T,T,T,T) = (F,T,T,F,T,F,T,T)) /\
     (InvSbox(T,F,F,F,F,F,F,F) = (F,F,T,T,T,F,T,F)) /\
     (InvSbox(T,F,F,F,F,F,F,T) = (T,F,F,T,F,F,F,T)) /\
     (InvSbox(T,F,F,F,F,F,T,F) = (F,F,F,T,F,F,F,T)) /\
     (InvSbox(T,F,F,F,F,F,T,T) = (F,T,F,F,F,F,F,T)) /\
     (InvSbox(T,F,F,F,F,T,F,F) = (F,T,F,F,T,T,T,T)) /\
     (InvSbox(T,F,F,F,F,T,F,T) = (F,T,T,F,F,T,T,T)) /\
     (InvSbox(T,F,F,F,F,T,T,F) = (T,T,F,T,T,T,F,F)) /\
     (InvSbox(T,F,F,F,F,T,T,T) = (T,T,T,F,T,F,T,F)) /\
     (InvSbox(T,F,F,F,T,F,F,F) = (T,F,F,T,F,T,T,T)) /\
     (InvSbox(T,F,F,F,T,F,F,T) = (T,T,T,T,F,F,T,F)) /\
     (InvSbox(T,F,F,F,T,F,T,F) = (T,T,F,F,T,T,T,T)) /\
     (InvSbox(T,F,F,F,T,F,T,T) = (T,T,F,F,T,T,T,F)) /\
     (InvSbox(T,F,F,F,T,T,F,F) = (T,T,T,T,F,F,F,F)) /\
     (InvSbox(T,F,F,F,T,T,F,T) = (T,F,T,T,F,T,F,F)) /\
     (InvSbox(T,F,F,F,T,T,T,F) = (T,T,T,F,F,T,T,F)) /\
     (InvSbox(T,F,F,F,T,T,T,T) = (F,T,T,T,F,F,T,T)) /\
     (InvSbox(T,F,F,T,F,F,F,F) = (T,F,F,T,F,T,T,F)) /\
     (InvSbox(T,F,F,T,F,F,F,T) = (T,F,T,F,T,T,F,F)) /\
     (InvSbox(T,F,F,T,F,F,T,F) = (F,T,T,T,F,T,F,F)) /\
     (InvSbox(T,F,F,T,F,F,T,T) = (F,F,T,F,F,F,T,F)) /\
     (InvSbox(T,F,F,T,F,T,F,F) = (T,T,T,F,F,T,T,T)) /\
     (InvSbox(T,F,F,T,F,T,F,T) = (T,F,T,F,T,T,F,T)) /\
     (InvSbox(T,F,F,T,F,T,T,F) = (F,F,T,T,F,T,F,T)) /\
     (InvSbox(T,F,F,T,F,T,T,T) = (T,F,F,F,F,T,F,T)) /\
     (InvSbox(T,F,F,T,T,F,F,F) = (T,T,T,F,F,F,T,F)) /\
     (InvSbox(T,F,F,T,T,F,F,T) = (T,T,T,T,T,F,F,T)) /\
     (InvSbox(T,F,F,T,T,F,T,F) = (F,F,T,T,F,T,T,T)) /\
     (InvSbox(T,F,F,T,T,F,T,T) = (T,T,T,F,T,F,F,F)) /\
     (InvSbox(T,F,F,T,T,T,F,F) = (F,F,F,T,T,T,F,F)) /\
     (InvSbox(T,F,F,T,T,T,F,T) = (F,T,T,T,F,T,F,T)) /\
     (InvSbox(T,F,F,T,T,T,T,F) = (T,T,F,T,T,T,T,T)) /\
     (InvSbox(T,F,F,T,T,T,T,T) = (F,T,T,F,T,T,T,F)) /\
     (InvSbox(T,F,T,F,F,F,F,F) = (F,T,F,F,F,T,T,T)) /\
     (InvSbox(T,F,T,F,F,F,F,T) = (T,T,T,T,F,F,F,T)) /\
     (InvSbox(T,F,T,F,F,F,T,F) = (F,F,F,T,T,F,T,F)) /\
     (InvSbox(T,F,T,F,F,F,T,T) = (F,T,T,T,F,F,F,T)) /\
     (InvSbox(T,F,T,F,F,T,F,F) = (F,F,F,T,T,T,F,T)) /\
     (InvSbox(T,F,T,F,F,T,F,T) = (F,F,T,F,T,F,F,T)) /\
     (InvSbox(T,F,T,F,F,T,T,F) = (T,T,F,F,F,T,F,T)) /\
     (InvSbox(T,F,T,F,F,T,T,T) = (T,F,F,F,T,F,F,T)) /\
     (InvSbox(T,F,T,F,T,F,F,F) = (F,T,T,F,T,T,T,T)) /\
     (InvSbox(T,F,T,F,T,F,F,T) = (T,F,T,T,F,T,T,T)) /\
     (InvSbox(T,F,T,F,T,F,T,F) = (F,T,T,F,F,F,T,F)) /\
     (InvSbox(T,F,T,F,T,F,T,T) = (F,F,F,F,T,T,T,F)) /\
     (InvSbox(T,F,T,F,T,T,F,F) = (T,F,T,F,T,F,T,F)) /\
     (InvSbox(T,F,T,F,T,T,F,T) = (F,F,F,T,T,F,F,F)) /\
     (InvSbox(T,F,T,F,T,T,T,F) = (T,F,T,T,T,T,T,F)) /\
     (InvSbox(T,F,T,F,T,T,T,T) = (F,F,F,T,T,F,T,T)) /\
     (InvSbox(T,F,T,T,F,F,F,F) = (T,T,T,T,T,T,F,F)) /\
     (InvSbox(T,F,T,T,F,F,F,T) = (F,T,F,T,F,T,T,F)) /\
     (InvSbox(T,F,T,T,F,F,T,F) = (F,F,T,T,T,T,T,F)) /\
     (InvSbox(T,F,T,T,F,F,T,T) = (F,T,F,F,T,F,T,T)) /\
     (InvSbox(T,F,T,T,F,T,F,F) = (T,T,F,F,F,T,T,F)) /\
     (InvSbox(T,F,T,T,F,T,F,T) = (T,T,F,T,F,F,T,F)) /\
     (InvSbox(T,F,T,T,F,T,T,F) = (F,T,T,T,T,F,F,T)) /\
     (InvSbox(T,F,T,T,F,T,T,T) = (F,F,T,F,F,F,F,F)) /\
     (InvSbox(T,F,T,T,T,F,F,F) = (T,F,F,T,T,F,T,F)) /\
     (InvSbox(T,F,T,T,T,F,F,T) = (T,T,F,T,T,F,T,T)) /\
     (InvSbox(T,F,T,T,T,F,T,F) = (T,T,F,F,F,F,F,F)) /\
     (InvSbox(T,F,T,T,T,F,T,T) = (T,T,T,T,T,T,T,F)) /\
     (InvSbox(T,F,T,T,T,T,F,F) = (F,T,T,T,T,F,F,F)) /\
     (InvSbox(T,F,T,T,T,T,F,T) = (T,T,F,F,T,T,F,T)) /\
     (InvSbox(T,F,T,T,T,T,T,F) = (F,T,F,T,T,F,T,F)) /\
     (InvSbox(T,F,T,T,T,T,T,T) = (T,T,T,T,F,T,F,F)) /\
     (InvSbox(T,T,F,F,F,F,F,F) = (F,F,F,T,T,T,T,T)) /\
     (InvSbox(T,T,F,F,F,F,F,T) = (T,T,F,T,T,T,F,T)) /\
     (InvSbox(T,T,F,F,F,F,T,F) = (T,F,T,F,T,F,F,F)) /\
     (InvSbox(T,T,F,F,F,F,T,T) = (F,F,T,T,F,F,T,T)) /\
     (InvSbox(T,T,F,F,F,T,F,F) = (T,F,F,F,T,F,F,F)) /\
     (InvSbox(T,T,F,F,F,T,F,T) = (F,F,F,F,F,T,T,T)) /\
     (InvSbox(T,T,F,F,F,T,T,F) = (T,T,F,F,F,T,T,T)) /\
     (InvSbox(T,T,F,F,F,T,T,T) = (F,F,T,T,F,F,F,T)) /\
     (InvSbox(T,T,F,F,T,F,F,F) = (T,F,T,T,F,F,F,T)) /\
     (InvSbox(T,T,F,F,T,F,F,T) = (F,F,F,T,F,F,T,F)) /\
     (InvSbox(T,T,F,F,T,F,T,F) = (F,F,F,T,F,F,F,F)) /\
     (InvSbox(T,T,F,F,T,F,T,T) = (F,T,F,T,T,F,F,T)) /\
     (InvSbox(T,T,F,F,T,T,F,F) = (F,F,T,F,F,T,T,T)) /\
     (InvSbox(T,T,F,F,T,T,F,T) = (T,F,F,F,F,F,F,F)) /\
     (InvSbox(T,T,F,F,T,T,T,F) = (T,T,T,F,T,T,F,F)) /\
     (InvSbox(T,T,F,F,T,T,T,T) = (F,T,F,T,T,T,T,T)) /\
     (InvSbox(T,T,F,T,F,F,F,F) = (F,T,T,F,F,F,F,F)) /\
     (InvSbox(T,T,F,T,F,F,F,T) = (F,T,F,T,F,F,F,T)) /\
     (InvSbox(T,T,F,T,F,F,T,F) = (F,T,T,T,T,T,T,T)) /\
     (InvSbox(T,T,F,T,F,F,T,T) = (T,F,T,F,T,F,F,T)) /\
     (InvSbox(T,T,F,T,F,T,F,F) = (F,F,F,T,T,F,F,T)) /\
     (InvSbox(T,T,F,T,F,T,F,T) = (T,F,T,T,F,T,F,T)) /\
     (InvSbox(T,T,F,T,F,T,T,F) = (F,T,F,F,T,F,T,F)) /\
     (InvSbox(T,T,F,T,F,T,T,T) = (F,F,F,F,T,T,F,T)) /\
     (InvSbox(T,T,F,T,T,F,F,F) = (F,F,T,F,T,T,F,T)) /\
     (InvSbox(T,T,F,T,T,F,F,T) = (T,T,T,F,F,T,F,T)) /\
     (InvSbox(T,T,F,T,T,F,T,F) = (F,T,T,T,T,F,T,F)) /\
     (InvSbox(T,T,F,T,T,F,T,T) = (T,F,F,T,T,T,T,T)) /\
     (InvSbox(T,T,F,T,T,T,F,F) = (T,F,F,T,F,F,T,T)) /\
     (InvSbox(T,T,F,T,T,T,F,T) = (T,T,F,F,T,F,F,T)) /\
     (InvSbox(T,T,F,T,T,T,T,F) = (T,F,F,T,T,T,F,F)) /\
     (InvSbox(T,T,F,T,T,T,T,T) = (T,T,T,F,T,T,T,T)) /\
     (InvSbox(T,T,T,F,F,F,F,F) = (T,F,T,F,F,F,F,F)) /\
     (InvSbox(T,T,T,F,F,F,F,T) = (T,T,T,F,F,F,F,F)) /\
     (InvSbox(T,T,T,F,F,F,T,F) = (F,F,T,T,T,F,T,T)) /\
     (InvSbox(T,T,T,F,F,F,T,T) = (F,T,F,F,T,T,F,T)) /\
     (InvSbox(T,T,T,F,F,T,F,F) = (T,F,T,F,T,T,T,F)) /\
     (InvSbox(T,T,T,F,F,T,F,T) = (F,F,T,F,T,F,T,F)) /\
     (InvSbox(T,T,T,F,F,T,T,F) = (T,T,T,T,F,T,F,T)) /\
     (InvSbox(T,T,T,F,F,T,T,T) = (T,F,T,T,F,F,F,F)) /\
     (InvSbox(T,T,T,F,T,F,F,F) = (T,T,F,F,T,F,F,F)) /\
     (InvSbox(T,T,T,F,T,F,F,T) = (T,T,T,F,T,F,T,T)) /\
     (InvSbox(T,T,T,F,T,F,T,F) = (T,F,T,T,T,F,T,T)) /\
     (InvSbox(T,T,T,F,T,F,T,T) = (F,F,T,T,T,T,F,F)) /\
     (InvSbox(T,T,T,F,T,T,F,F) = (T,F,F,F,F,F,T,T)) /\
     (InvSbox(T,T,T,F,T,T,F,T) = (F,T,F,T,F,F,T,T)) /\
     (InvSbox(T,T,T,F,T,T,T,F) = (T,F,F,T,T,F,F,T)) /\
     (InvSbox(T,T,T,F,T,T,T,T) = (F,T,T,F,F,F,F,T)) /\
     (InvSbox(T,T,T,T,F,F,F,F) = (F,F,F,T,F,T,T,T)) /\
     (InvSbox(T,T,T,T,F,F,F,T) = (F,F,T,F,T,F,T,T)) /\
     (InvSbox(T,T,T,T,F,F,T,F) = (F,F,F,F,F,T,F,F)) /\
     (InvSbox(T,T,T,T,F,F,T,T) = (F,T,T,T,T,T,T,F)) /\
     (InvSbox(T,T,T,T,F,T,F,F) = (T,F,T,T,T,F,T,F)) /\
     (InvSbox(T,T,T,T,F,T,F,T) = (F,T,T,T,F,T,T,T)) /\
     (InvSbox(T,T,T,T,F,T,T,F) = (T,T,F,T,F,T,T,F)) /\
     (InvSbox(T,T,T,T,F,T,T,T) = (F,F,T,F,F,T,T,F)) /\
     (InvSbox(T,T,T,T,T,F,F,F) = (T,T,T,F,F,F,F,T)) /\
     (InvSbox(T,T,T,T,T,F,F,T) = (F,T,T,F,T,F,F,T)) /\
     (InvSbox(T,T,T,T,T,F,T,F) = (F,F,F,T,F,T,F,F)) /\
     (InvSbox(T,T,T,T,T,F,T,T) = (F,T,T,F,F,F,T,T)) /\
     (InvSbox(T,T,T,T,T,T,F,F) = (F,T,F,T,F,T,F,T)) /\
     (InvSbox(T,T,T,T,T,T,F,T) = (F,F,T,F,F,F,F,T)) /\
     (InvSbox(T,T,T,T,T,T,T,F) = (F,F,F,F,T,T,F,F)) /\
     (InvSbox(T,T,T,T,T,T,T,T) = (F,T,T,T,T,T,F,T))`;



val Sbox_Inversion = Q.store_thm
("Sbox_Inversion",
 `!w:word8. InvSbox (Sbox w) = w`,
 SIMP_TAC std_ss [FORALL_BYTE_BITS,Sbox_def, InvSbox_def]);

val _ = export_theory();
