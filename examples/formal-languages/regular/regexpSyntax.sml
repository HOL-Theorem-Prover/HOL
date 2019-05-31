structure regexpSyntax :> regexpSyntax =
struct

open Feedback Lib HolKernel boolLib
     Regexp_Type regexpTheory regexp_compilerTheory;

val ERR = mk_HOL_ERR "regexpSyntax";

val charset_ty = ``:charset``;

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
val regexp_lang_tm = mkc "regexp_lang"
val regexp_matcher_tm =
  prim_mk_const{Thy="regexp_compiler", Name = "regexp_matcher"};


val mk_chset    = mk_monop chset_tm;
val mk_cat      = mk_binop cat_tm
val mk_star     = mk_monop star_tm
val mk_neg      = mk_monop neg_tm
fun mk_or tlist = mk_comb(or_tm,listSyntax.mk_list(tlist,regexp_ty));
val mk_and      = mk_binop and_tm
val mk_regexp_lang = mk_monop regexp_lang_tm
val mk_regexp_matcher = mk_binop regexp_matcher_tm

val dest_chset = dest_monop chset_tm (ERR "dest_chset" "expected a Chset");
val dest_cat   = dest_binop cat_tm   (ERR "dest_cat" "expected a Cat");
val dest_star  = dest_monop star_tm  (ERR "dest_star" "expected a Star");
val dest_neg   = dest_monop neg_tm   (ERR "dest_neg" "expected a Neg");
val dest_and   = dest_binop and_tm   (ERR "dest_and" "expected an And");
val dest_regexp_lang = 
    dest_monop regexp_lang_tm   
        (ERR "dest_regexp_lang" "expected regexp_lang application");
val dest_regexp_matcher = 
    dest_binop regexp_matcher_tm
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
val vector_tm = prim_mk_const{Thy="charset",Name="Vector"}
*)

val vector_tm = prim_mk_const{Thy="regexp_compiler",Name="Vector"}

val mk_vector = mk_monop vector_tm;
val dest_vector = dest_monop vector_tm (ERR "dest_vector" "expected a Vector");
val is_vector = Lib.can dest_vector;

fun list_mk_vector (tlist,ty) = mk_vector(listSyntax.mk_list(tlist,ty))

fun strip_vector tm =
  listSyntax.dest_list(dest_vector tm)
  handle HOL_ERR _ => raise ERR "strip_vector" "";

val is_chset = Lib.can dest_chset
val is_cat   = Lib.can dest_cat
val is_star  = Lib.can dest_star
val is_neg   = Lib.can dest_neg
val is_or    = Lib.can dest_or
val is_and   = Lib.can dest_and
val is_regexp_lang = Lib.can dest_regexp_lang
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

The following functions implement the maps for bool vectors

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

The following functions implement the maps for bool vectors

fun bitvector_to_bitlist bv =
 let open boolSyntax
     fun bit ch = (ch = #"1")
     fun bin i = IntInf.fmt StringCvt.BIN i
     val ml_bitlist = map bit (explode (bin bv))
 in
    List.foldr(fn (b,list) =>
        listSyntax.mk_cons(if b then T else F,list))
       (listSyntax.mk_nil Type.bool) ml_bitlist
 end;

fun bitlist_to_bitvector tm =
 let val (tmlist,ty) = listSyntax.dest_list tm
     fun binchar tm =
       if tm = T then #"1" else
       if tm = F then #"0"
       else raise ERR "bitlist_to_bitvector" "expected boolean literal"
     val blist = List.map binchar tmlist
     fun list_reader (h::t) = SOME(h,t)
       | list_reader [] = NONE
 in
   case IntInf.scan StringCvt.BIN list_reader blist
    of SOME (i,[]) => i
     | otherwise => raise ERR "bitlist_to_bitvector" "unexpected input"
 end
*)

val charset_tm = prim_mk_const{Thy="charset",Name="Charset"}

(*---------------------------------------------------------------------------*)
(* Lift and drop charsets between ML and HOL                                 *)
(*---------------------------------------------------------------------------*)
(*
val (chop4,join4) =
 let open IntInf
     val exp2_64 = pow(2,64)
     val exp2_128 = pow(2,128)
     val exp2_192 = pow(2,192)
     val exp2_256 = pow(2,256)
     fun chop4 i =
      let val (a,b) = divMod(i,exp2_64)
          val (c,d) = divMod(a,exp2_64)
          val (e,f) = divMod(c,exp2_64)
          val (g,h) = divMod(e,exp2_64)
      in (h,f,d,b)
      end
     fun join4 (h,f,d,b) = b + d*exp2_64 + f*exp2_128 + h*exp2_192
 in
  (chop4,join4)
 end;

 let val num = IntInf.toInt
 in fn cset =>
    let open wordsSyntax
        val (h,f,d,b) = chop4 cset
        val htm = mk_wordii(num h,64)
        val ftm = mk_wordii(num f,64)
        val dtm = mk_wordii(num d,64)
        val btm = mk_wordii(num b,64)
    in list_mk_comb(charset_tm,[htm,ftm,dtm,btm])
    end
 end;

fun term_to_charset tm = (* ``:charset`` -> IntInf.int *)
 case strip_comb tm
  of (const,[htm,ftm,dtm,btm]) =>
      if same_const const charset_tm
        then let open wordsSyntax
                 val inf = IntInf.fromInt
                 val h = inf (uint_of_word htm)
                 val f = inf (uint_of_word ftm)
                 val d = inf (uint_of_word dtm)
                 val b = inf (uint_of_word btm)
             in join4(h,f,d,b)
             end
        else raise ERR "term_to_charset" "expected Charset _ _ _ _"
   | other => raise ERR "term_to_charset" "expected Charset _ _ _ _"
*)

val charset_to_term = (* w64*w64*w64*w64 -> ``:charset`` *)
 let val num = Arbnum.fromLargeInt o Word64.toLargeInt
 in fn (v1,v2,v3,v4) =>
    let open wordsSyntax
        val v1tm = mk_wordi(num v1,64)
        val v2tm = mk_wordi(num v2,64)
        val v3tm = mk_wordi(num v3,64)
        val v4tm = mk_wordi(num v4,64)
    in list_mk_comb(charset_tm,[v1tm,v2tm,v3tm,v4tm])
    end
 end;

fun term_to_charset tm = (* ``:charset`` -> w64*w64*w64*w64 *)
 case strip_comb tm
  of (const,[v1tm,v2tm,v3tm,v4tm]) =>
      if same_const const charset_tm
        then let open wordsSyntax
                 val inf = Word64.fromLargeInt o Arbnum.toLargeInt
                 val v1 = inf (dest_word_literal v1tm)
                 val v2 = inf (dest_word_literal v2tm)
                 val v3 = inf (dest_word_literal v3tm)
                 val v4 = inf (dest_word_literal v4tm)
             in (v1,v2,v3,v4)
             end
        else raise ERR "term_to_charset" "expected Charset _ _ _ _"
   | other => raise ERR "term_to_charset" "expected Charset _ _ _ _"

(*---------------------------------------------------------------------------*)
(* Build a regexp term from an ML regexp expression                          *)
(*---------------------------------------------------------------------------*)

fun regexp_to_term r =
 case r
  of Chset bv    => mk_chset(charset_to_term bv)
   | Cat (r1,r2) => mk_cat(regexp_to_term r1,regexp_to_term r2)
   | Star r      => mk_star (regexp_to_term r)
   | Or rlist    => mk_or (List.map regexp_to_term rlist)
   | Neg r       => mk_neg (regexp_to_term r);

fun term_to_regexp tm =
 (case total dest_chset tm
  of SOME w => Chset (term_to_charset w)
   | NONE =>
 case total dest_cat tm
  of SOME (t1,t2) => Cat(term_to_regexp t1,term_to_regexp t2)
   | NONE =>
 case total dest_star tm
  of SOME t => Star (term_to_regexp t)
   | NONE =>
 case total dest_or tm
  of SOME tlist => Or (List.map term_to_regexp tlist)
   | NONE =>
 case total dest_neg tm
  of SOME t => Neg (term_to_regexp t)
   | NONE => raise ERR "term_to_regexp" "not a ground regexp term")
 handle e => raise wrap_exn "regexpSyntax" "term_to_regexp" e;

(*---------------------------------------------------------------------------*)
(* Derived syntax                                                            *)
(*---------------------------------------------------------------------------*)

fun mkc s = prim_mk_const {Thy = "charset", Name = s};

val charset_empty_tm = mkc "charset_empty";
val charset_full_tm = mkc "charset_full";
val empty_tm = mk_chset charset_empty_tm;
val dot_tm = mk_chset charset_full_tm;

val epsilon_tm = mk_star empty_tm;
val dot_star_tm = mk_star dot_tm;

end
