(* =====================================================================*)
(* FILE		: charScript.sml				        *)
(* DESCRIPTION  : Creates a theory of 8-bit ascii character codes	*)
(*									*)
(* AUTHOR	: (c) T. Melham 1988					*)
(* DATE		: 87.07.27						*)
(* REVISED	: 90.10.27						*)
(* TRANSLATED   : Konrad Slind, University of Calgary                   *)
(* =====================================================================*)

open HolKernel boolLib numLib numSyntax QLib BasicProvers;

infix THEN ; infixr -->;

(* ---------------------------------------------------------------------*)
(* Create the new theory						*)
(* ---------------------------------------------------------------------*)

val _ = new_theory "char";

(* ---------------------------------------------------------------------*)
(* Characters are isomorphic to the natural numbers <= 255.             *)
(* ---------------------------------------------------------------------*)

val is_char = 
 let val n = mk_var("n",num)
     val topnum = mk_numeral (Arbnum.fromInt 256)
 in 
     mk_abs(n,mk_less(n,topnum))
 end;

val CHAR_EXISTS = Q.prove (`?n. ^is_char n`, Q.EXISTS_TAC `0` THEN REDUCE_TAC);

val CHAR_TYPE = new_type_definition("char", CHAR_EXISTS);

val CHAR_TYPE_FACTS = 
  define_new_type_bijections 
      {ABS="CHAR", REP="ORD",name="char_BIJ", tyax=CHAR_TYPE};

val CHAR_ORD  = save_thm("CHAR_ORD", CONJUNCT1 CHAR_TYPE_FACTS);
val ORD_CHAR_IMP  = save_thm("ORD_CHAR",BETA_RULE (CONJUNCT2 CHAR_TYPE_FACTS));

val ORD_11    = save_thm("ORD_11",prove_rep_fn_one_one CHAR_TYPE_FACTS)
val ORD_ONTO  = save_thm("ORD_ONTO", 
                         BETA_RULE (prove_rep_fn_onto CHAR_TYPE_FACTS));
val CHAR_11   = save_thm("CHAR_ONE_ONE",
                         BETA_RULE (prove_abs_fn_one_one CHAR_TYPE_FACTS));
val CHAR_ONTO = save_thm("CHAR_ONTO",
                         BETA_RULE (prove_abs_fn_onto CHAR_TYPE_FACTS));

val ORD_BOUND = Q.store_thm
("ORD_BOUND",
 `!c. ORD c < 256`,
 PROVE_TAC [ORD_ONTO]);

val CHAR_ONTO = Q.store_thm
("CHAR_ONTO",
 `!c. ?m. c = CHAR m`,
 GEN_TAC
  THEN Q.EXISTS_TAC `ORD c`
  THEN PROVE_TAC [ORD_BOUND,CHAR_ORD,REDUCE_CONV(Term `256-1`),
              ARITH_CONV (Term `x < y ==> ~(y-1<x)`)]);

val CHAR_EQ_THM = Q.store_thm
("CHAR_EQ_THM",
 `!c1 c2. (c1 = c2) = (ORD c1 = ORD c2)`,
 REPEAT GEN_TAC 
   THEN EQ_TAC 
   THEN RW_TAC bool_ss [ORD_11]);

val char_ty = mk_type("char",[]);
val mk_char_tm = mk_const("CHAR",num --> char_ty);
fun mk_char tm = mk_comb(mk_char_tm, tm);

val bound = mk_numeral(Arbnum.fromInt 256);
fun cond m = EQT_ELIM(REDUCE_CONV (mk_less(m,bound)));
fun lemma m = EQ_MP (SPEC m ORD_CHAR_IMP) (cond m);


(*---------------------------------------------------------------------------
      Show that, for 0<=n<=255, 

           ORD (CHAR n) = n. 

      For computeLib, this must unfortunately expand into 256 
      unconditional rewrite rules ... is there a better way?

 ---------------------------------------------------------------------------*)

val _ = 
  let fun upto b t = if b <= t then b::upto (b+1) t else [];
      val nums = upto 0 255
      val int2term = mk_numeral o Arbnum.fromInt 
      val num_tms = map int2term nums
  in
    save_thm ("ORD_CHAR", LIST_CONJ (map lemma num_tms))
  end;


(* Code to be emitted *)
(* let open charTheory 
   in computeLib.add_funs [ORD_CHAR,CHAR_ORD,CHAR_EQ_THM] 
   end;
*)

val _ = export_theory();
