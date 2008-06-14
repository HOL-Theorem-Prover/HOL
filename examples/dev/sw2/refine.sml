structure refine :> refine = 
struct

(* app load ["wordsLib", "Normal"]; 
*)

open HolKernel Parse boolLib bossLib 
  wordsSyntax numSyntax pairSyntax NormalTheory;

(*---------------------------------------------------------------------------*)

val C_tm = prim_mk_const{Name="C",Thy="Normal"};
fun mk_C tm = 
  mk_comb (inst [alpha |-> type_of tm, beta |-> type_of tm] C_tm, tm);

val dest_C = dest_monop C_tm (ERR "dest_C" "");

(*---------------------------------------------------------------------------*)
(* To eventually go to wordsSyntax.                                          *)
(*---------------------------------------------------------------------------*)

val is_word_literal = is_n2w;

fun strip_word_or tm = 
 let fun f tm = 
      case total dest_word_or tm
       of SOME (l,r) => f(l) @ f(r)
        | NONE => [tm]
 in Lib.front_last(f tm)
 end;

val list_mk_word_or = end_itlist (curry mk_word_or);

fun pflat [] = []
  | pflat ((x,y)::t) = x::y::pflat t;

(*---------------------------------------------------------------------------*)
(* Translating constants into compound expressions.                          *)
(*---------------------------------------------------------------------------*)

fun type_to_name t = 
 String.extract(Hol_pp.type_to_string t, 1, NONE);

fun numeric_type_to_num t =
 Lib.with_flag(type_pp.pp_num_types,true)
  Arbnum.fromString (type_to_name t);

fun pad s i =
 let fun loop n acc = if n <= 0 then acc else loop(n-1) (#"0"::acc)
 in String.implode (loop i (String.explode s))
 end;

fun bit_pattern w = 
 let open wordsSyntax
     val (ntm,ty) = dest_n2w w
     val n = numSyntax.dest_numeral ntm
     val ty_width = Arbnum.toInt(numeric_type_to_num ty)
     val str = Arbnum.toBinString n
 in 
   pad str (ty_width - String.size str)
 end;

fun word_of_string(s,width) = 
    mk_n2w(mk_numeral(Arbnum.fromBinString s),width);

val index32 = fcpLib.index_type (Arbnum.fromInt 32);
fun word32_of_string s = word_of_string(s,index32);

fun word_of_int (i,width) =
  mk_n2w(numSyntax.term_of_int i,
         fcpLib.index_type(Arbnum.fromInt width));

fun chunk s = 
 let open String numSyntax
     val s1 = substring(s,0,8)
     val s2 = substring(s,8,8)
     val s3 = substring(s,16,8)
     val s4 = substring(s,24,8)
 in 
   (word32_of_string s1,word32_of_string s2,
    word32_of_string s3,word32_of_string s4)
 end;

val zero32 = ``0w:word32``;
val n8 = term_of_int 8;
val n16 = term_of_int 16;
val n24 = term_of_int 24;
val n256 = Arbnum.fromInt 256;

fun bytes_to_let (b1,b2,b3,b4) = 
 let val plist = List.mapPartial 
                   (fn p as (b,s) => if b = zero32 then NONE else SOME p)
                    [(b1,n24), (b2,n16), (b3,n8)]
     val plist' = enumerate 0 plist
     val plist'' = map (fn (i,p as (b,_)) => 
                          (mk_var("v"^Int.toString i,type_of b),p)) plist'
     val vlist = list_mk_word_or (map fst plist'' @ [b4])
     fun foo (v,(c,s)) = ((v,c),(v,mk_word_lsl(v,s)))
     val vb4 = mk_var("v"^Int.toString(length plist''), type_of b4)
     val plist3 = pflat(map foo plist'') @ [(vb4,vlist)]
 in list_mk_anylet (map single plist3,vb4)
 end;

fun IMMEDIATE_CONST_CONV c =
 let val n = numSyntax.dest_numeral(fst(dest_n2w c))
 in if Arbnum.<(n,n256) then failwith "CONST_CONV" else 
    let val bstr = bit_pattern c
        val res = bytes_to_let (chunk bstr)
    in EQT_ELIM (wordsLib.WORDS_CONV (mk_eq(c,res)))
    end
 end;

(*---------------------------------------------------------------------------*)
(* Want to remove returned constants, in favour of returned registers.       *)
(* So "if P then c else d" where c or d are constants, needs to become       *)
(*                                                                           *)
(*   if P then (let x = c in x) else (let x = d in x)                        *)
(*---------------------------------------------------------------------------*)

fun MK_COND tm th1 th2 = 
 let val core = rator(rator tm)
     val thm1 = MK_COMB (REFL core, th1)
     val thm2 = MK_COMB (thm1,th2)
 in thm2
 end;

fun letify c = 
 let val v = genvar (type_of c)
     val tm = mk_let (mk_abs(v,v),c)
 in SYM(BETA_RULE (REWR_CONV LET_THM tm))
 end;

fun COND_CONST_ELIM_CONV tm = 
 let val (t,a1,a2) = dest_cond tm
 in case (is_const a1 orelse is_word_literal a1,
          is_const a2 orelse is_word_literal a2)
     of (true,true) => MK_COND tm (letify a1) (letify a2)
      | (true,false) => MK_COND tm (letify a1) (REFL a2)
      | (false,true) => MK_COND tm (REFL a1) (letify a2)
      | (false,false) => failwith ""
 end
  handle HOL_ERR _ => raise ERR "COND_CONST_ELIM_CONV" "";

(*---------------------------------------------------------------------------*)
(* Expand constants, and eliminate returned constants (return values must    *)
(* be in registers).                                                         *)
(*---------------------------------------------------------------------------*)

val refine0 = CONV_RULE (DEPTH_CONV IMMEDIATE_CONST_CONV);
val refine0a = CONV_RULE (DEPTH_CONV COND_CONST_ELIM_CONV);
val refine0b = Ho_Rewrite.PURE_REWRITE_RULE [NormalTheory.FLATTEN_LET];

val refine_const = refine0b o refine0a o refine0;

(*---------------------------------------------------------------------------*)
(* Some refinements after compilation                                        *)
(*---------------------------------------------------------------------------*)

val LIFT_COND_ABOVE_LET = Q.prove
(`!f v1 v2 v3. 
  (let x = (if v1 then v2 else v3) in f x) = 
    if v1 then (let x = v2 in f x) else (let x = v3 in f x)`,
 RW_TAC std_ss [LET_DEF]);

val LIFT_COND_ABOVE_LET1 = Q.prove
(`(let x = val in (if v1 then v2 x else v3 x)) = 
  if v1 then (let x = val in v2 x) else (let x = val in v3 x)`,
 RW_TAC std_ss [LET_DEF]);

val LIFT_COND_ABOVE_TRIVLET = Q.prove
(`(let x = (if v1 then v2 else v3) in x) = 
  if v1 then v2 else v3`,
 SIMP_TAC std_ss [LET_DEF]);

val ID_LET = Q.prove
(`LET (\x.x) y = y`,
 SIMP_TAC std_ss [LET_DEF]);

fun lift_cond def =
  let
    fun mk_flat_let (x, e1, e2) = 
        if is_pair x andalso is_pair e1 then
           let val (x1,x2) = dest_pair x
               val (e1',e1'') = dest_pair e1
           in  mk_flat_let(x1, e1', mk_flat_let(x2, e1'', e2))
           end
        else if basic.is_atomic e1 andalso basic.is_atomic x then
           subst [x |-> e1] e2
        else
           mk_plet(x, e1, e2)

    fun trav t =
      if is_let t then
        let val (v,M,N) = dest_plet t
            val N' = trav N
        in if is_cond M then
             let val (J, M1, M2) = dest_cond M
                 val M1' = mk_flat_let (v, trav M1, N')
                 val M2' = mk_flat_let (v, trav M2, N')
             in mk_cond (J, M1', M2') end
           else
             mk_flat_let(v, trav M, trav N)
        end
       else if is_comb t then
            let val (M1,M2) = dest_comb t
                val M1' = trav M1
                val M2' = trav M2
            in mk_comb(M1',M2')
            end
       else if is_pabs t then
           let val (v,M) = dest_pabs t
           in mk_pabs(v,trav M)
           end
       else t

      val (fname, fbody) = dest_eq (concl (SPEC_ALL def))
      val fbody' = trav fbody
      val th1 = prove (mk_eq(fbody, fbody'), 
		       SIMP_TAC bool_ss [LET_THM])
                handle _ => prove (mk_eq(fbody, fbody'), 
		                   RW_TAC std_ss [LET_THM])
                handle _ => def 
      val th2 = CONV_RULE (RHS_CONV (REWRITE_CONV [Once th1])) (SPEC_ALL def)
  in
     th2
  end

(*---------------------------------------------------------------------------*)
(*   Convert a definiton to its equivalent refined format                    *)
(*---------------------------------------------------------------------------*)

(*
val LIFT_COND_ABOVE_C = Q.prove (
  `!f v1 v2 v3. C (let x = (if v1 then v2 else v3) in f x) = 
     if v1 then C v2 (\x. C (f x)) else C v3 (\y. C (f y))`,
  SIMP_TAC std_ss [C_def, LET_THM, FUN_EQ_THM] THEN
  Cases_on `v1` THEN
  RW_TAC std_ss []
 );

fun lift_cond exp =
 let val t = dest_C exp               (* eliminate the C *)
 in
  if is_let t then                    (*  exp = LET (\v. N) M  *)
    let val (v,M,N) = dest_plet t
        val (th0, th1) = (lift_cond (mk_C M), lift_cond (mk_C N))
    in  if is_cond M then
          let val (J, M1, M2) = dest_cond M
              val M1' = mk_plet (v, lift_cond M1, N')
              val M2' = mk_plet (v, lift_cond M2, N')

	      val th3 = 
                     let val f = mk_pabs(v,N)
                         val th = INST_TYPE [alpha |-> type_of N, 
                                            beta  |-> type_of N, 
                                            gamma |-> type_of v]
                                 (LIFT_COND_ABOVE_C)
                         val t2 = rhs (concl (SPECL [f, J, M1, M2] th))
                         val th2 = prove (mk_eq(exp,t2), 
					  RW_TAC std_ss [LET_THM, C_def])
                     in
			 PairRules.PBETA_RULE (SIMP_RULE std_ss [pairTheory.LAMBDA_PROD] th2)
                     end
    in
       th5
    end

   else
    REFL exp
 end;
*)

(*---------------------------------------------------------------------------*)

end
