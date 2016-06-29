structure regexpSyntax :> regexpSyntax = 
struct

open Feedback Lib HolKernel boolLib 
     Regexp_Type regexpTheory regexp_compilerTheory;

val ERR = mk_HOL_ERR "regexpSyntax";

val regexp_ty = mk_thy_type{Thy="regexp",Tyop="regexp",Args=[]};

(*---------------------------------------------------------------------------*)
(* regexp constructors                                                       *)
(*---------------------------------------------------------------------------*)

fun mkc s = prim_mk_const {Thy = "regexp", Name = s};

val chset_tm = mkc "Chset"
val cat_tm   = mkc "Cat"
val star_tm  = mkc "Star"
val or_tm    = mkc "Or"
val neg_tm   = mkc "Neg"
val and_tm   = mkc "And"
val regexp_matcher_tm = 
  prim_mk_const{Thy="regexp_compiler", Name = "regexp_matcher"};


val mk_chset    = mk_monop chset_tm;
val mk_cat      = mk_binop cat_tm
val mk_star     = mk_monop star_tm
val mk_neg      = mk_monop neg_tm
fun mk_or tlist = mk_comb(or_tm,listSyntax.mk_list(tlist,regexp_ty));
val mk_and      = mk_binop and_tm
val mk_regexp_matcher = mk_binop regexp_matcher_tm

val dest_chset = dest_monop chset_tm (ERR "dest_chset" "expected a Chset");
val dest_cat   = dest_binop cat_tm   (ERR "dest_cat" "expected a Cat");
val dest_star   = dest_monop star_tm  (ERR "dest_star" "expected a Star");
val dest_neg   = dest_monop neg_tm   (ERR "dest_neg" "expected a Neg");
val dest_and   = dest_binop and_tm   (ERR "dest_and" "expected an And");
val dest_regexp_matcher = dest_binop regexp_matcher_tm
        (ERR "dest_regexp_matcher" "expected an instance of regexp_matcher");

fun dest_or tm = 
 let val (tlist,ty) = listSyntax.dest_list
                        (dest_monop or_tm (ERR "dest_or" "expected an Or") tm)
 in if ty = regexp_ty
    then tlist
    else raise ERR "dest_or" "expected Or of list of regexps"
 end;

(*
val vector_tm = prim_mk_const{Thy="ml_translator",Name="Vector"};
*)

val vector_tm = prim_mk_const{Thy="charset",Name="Vector"} 

val mk_vector = mk_monop vector_tm;
val dest_vector = dest_monop vector_tm (ERR "dest_vector" "expected a Vector");
val is_vector = Lib.can dest_vector;

fun list_mk_vector (tlist,ty) = mk_vector(listSyntax.mk_list(tlist,ty))

fun strip_vector tm = 
  listSyntax.dest_list(dest_vector tm)
  handle HOL_ERR _ => raise ERR "strip_vector" "";

fun list_mk_chset blist = mk_chset (list_mk_vector(blist,Type.bool));
fun chset_to_list tm = fst(strip_vector(dest_chset tm));

val is_chset = Lib.can dest_chset
val is_cat     = Lib.can dest_cat
val is_star    = Lib.can dest_star
val is_neg     = Lib.can dest_neg
val is_or      = Lib.can dest_or
val is_and     = Lib.can dest_and
val is_regexp_matcher = Lib.can dest_regexp_matcher;


(*---------------------------------------------------------------------------*)
(* Maps between ML bitvectors and HOL terms                                  *)
(* The following commented out functions implement the maps for n-bit words  *)
(*
val bitvector_to_word = 
 let val num_of = Vector.foldr(fn (b,n) => if b then  2 * n + 1 else 2 * n) 0 
 in
   fn bv => wordsSyntax.mk_wordii(num_of bv,Regexp_Type.alphabet_size)
 end;

fun word_to_bitvector tm = 
 let val n = wordsSyntax.dest_word_literal tm
     val A = Array.tabulate(Regexp_Type.alphabet_size, K false)
     open Arbnum Array
     val _ = foldli (fn (i,e,n) => 
              let val (d,m) = divmod(n,two) in (update(A,i,m=one); d) end) n A
 in vector A
 end
*)

fun bitvector_to_bitlist bv =  
 let open boolSyntax
 in Vector.foldr(fn (b,list) => 
        listSyntax.mk_cons(if b then T else F,list)) 
       (listSyntax.mk_nil Type.bool) bv
 end;

fun bitlist_to_bitvector tm = 
 let val (tmlist,ty) = listSyntax.dest_list tm
     val blist = List.map (equal boolSyntax.T) tmlist
 in Vector.fromList blist
 end

(*---------------------------------------------------------------------------*)
(* Build a regexp term from an ML regexp expression                          *)
(*---------------------------------------------------------------------------*)

fun mk_regexp r = 
 case r 
  of Chset bv    => mk_chset(mk_vector(bitvector_to_bitlist bv))
   | Cat (r1,r2) => mk_cat(mk_regexp r1,mk_regexp r2)
   | Star r      => mk_star (mk_regexp r)
   | Or rlist    => mk_or (List.map mk_regexp rlist)
   | Neg r       => mk_neg (mk_regexp r);

fun dest_regexp tm = 
 (case total (dest_vector o dest_chset) tm
  of SOME w => Chset (bitlist_to_bitvector w)
   | NONE =>
 case total dest_cat tm
  of SOME (t1,t2) => Cat(dest_regexp t1,dest_regexp t2)
   | NONE =>
 case total dest_star tm
  of SOME t => Star (dest_regexp t)
   | NONE =>
 case total dest_or tm
  of SOME tlist => Or (List.map dest_regexp tlist)
   | NONE => 
 case total dest_neg tm
  of SOME t => Neg (dest_regexp t)
   | NONE => raise ERR "dest_regexp" "not a ground regexp term")
 handle e => raise wrap_exn "regexpSyntax" "dest_regexp" e;

(*---------------------------------------------------------------------------*)
(* Derived syntax                                                            *)
(*---------------------------------------------------------------------------*)

fun mkc s = prim_mk_const {Thy = "charset", Name = s};

val charset_empty_tm = mkc "charset_empty";
val charset_full_tm = mkc "charset_full";
val empty_tm = mk_chset charset_empty_tm;
val sigma_tm = mk_chset charset_full_tm;

val epsilon_tm = mk_star empty_tm;
val sigmastar_tm = mk_star sigma_tm;

end
