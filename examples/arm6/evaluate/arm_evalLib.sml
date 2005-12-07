(* ========================================================================= *)
(* FILE          : arm_evalLib.sml                                           *)
(* DESCRIPTION   : Code for evaluating the I/O free ARM specification        *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005                                                      *)
(* ========================================================================= *)

structure arm_evalLib :> arm_evalLib =
struct

(* interactive use:
  app load ["Unix", "computeLib", "onestepTheory", "modelsLib",
            "disassemblerLib", "arm_evalTheory"];
*)

open HolKernel boolLib bossLib;
open Parse Q computeLib wordsSyntax rich_listTheory;
open armTheory arm_evalTheory;

(* ------------------------------------------------------------------------- *)

val UNDEF_INST  = Arbnum.fromHexString "E6000010";
val BINUTILS    = "/local/scratch/acjf3/gas/bin/arm-coff-";
val AS_BIN      = BINUTILS ^ "as";
val OBJCOPY_BIN = BINUTILS ^ "objcopy";

(* ------------------------------------------------------------------------- *)
(* Some conversions *)

val SUC2NUM = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

fun add_rws f rws =
let val cmp_set = f()
    val _ = add_thms rws cmp_set
in cmp_set end;

fun arm_eval_compset () = let open simTheory in
  add_rws modelsLib.arm_compset 
    [ADDR30_def,SET_BYTE_def,BSUBST_EVAL,dimindex_30,finite_30,memop_case_def,
     MEM_WRITE_BYTE_def,MEM_WRITE_WORD_def,MEM_WRITE_def,TRANSFERS_def,
     SIMP_RULE (bool_ss++pred_setSimps.PRED_SET_ss) [] NEXT_ARMe_def]
end;

val ARMe_CONV = CBV_CONV (arm_eval_compset());
val ARMe_RULE = CONV_RULE ARMe_CONV;

val SORT_SUBST_CONV = let open simTheory
  val compset = add_rws reduceLib.num_compset
        [register_EQ_register,register2num_thm,psrs_EQ_psrs,psrs2num_thm,
         SYM Sa_def,Sab_EQ,Sa_RULE4,Sb_RULE4,Sa_RULE_PSR,Sb_RULE_PSR,
         combinTheory.o_THM]
in
  computeLib.CBV_CONV compset THENC PURE_REWRITE_CONV [Sa_def,Sb_def]
end;

val SORT_BSUBST_CONV = let open simTheory
  val compset = add_rws wordsLib.words_compset
        [dimindex_30,finite_30,LENGTH,SUC2NUM JOIN,SUC2NUM BUTFIRSTN,
         APPEND,SUBST_BSUBST,BSa_RULE,BSb_RULE,GSYM BSa_def,combinTheory.o_THM]
in
  computeLib.CBV_CONV compset THENC PURE_REWRITE_CONV [BSa_def,BSb_def]
end;

val FOLD_SUBST_CONV = let open simTheory
  val compset = add_rws wordsLib.words_compset
      [SET_IFMODE_def,SET_NZCV_def,FOLDL,SUBST_EVAL,mode_num_def,mode_case_def,
       register_EQ_register,register2num_thm,psrs_EQ_psrs,psrs2num_thm]
in
  computeLib.CBV_CONV compset THENC SORT_SUBST_CONV
end;

val SUBST_EQ_CONV = SIMP_CONV (srw_ss()) [SUBST_EQ2,simTheory.SUBST_EVAL];

val rhsc = rhs o concl;

fun printn s = print (s ^ "\n");

(* ------------------------------------------------------------------------- *)
(* Syntax *)

fun mk_word30 n = mk_n2w(numSyntax.mk_numeral n,``:i30``);
fun mk_word32 n = mk_n2w(numSyntax.mk_numeral n,``:i32``);

fun eval_word t = (numSyntax.dest_numeral o rhsc o FOLD_SUBST_CONV o mk_w2n) t;

val subst_tm  = prim_mk_const{Name = ":-",  Thy = "arm"};
val bsubst_tm = prim_mk_const{Name = "::-", Thy = "sim"};

fun mk_subst (a,b,m) =
   list_mk_comb(inst[alpha |-> type_of a,beta |-> type_of b] subst_tm,[a,b,m])
   handle HOL_ERR _ => raise ERR "mk_subst" "";

fun mk_bsubst (a,b,m) =
   list_mk_comb(inst[alpha |-> dim_of a,beta |-> listSyntax.eltype b]
     bsubst_tm,[a,b,m])
   handle HOL_ERR _ => raise ERR "mk_subst" "";

val dest_subst  = dest_triop subst_tm  (ERR "dest_word_slice" "");
val dest_bsubst = dest_triop bsubst_tm (ERR "dest_word_slice" "");

fun dest_arm_eval t =
  let val (h,l) = strip_comb t
      val (h2, l2) = strip_comb (hd l)
  in
    if term_eq h ``ARM_EVAL`` andalso term_eq h2 ``ARM`` then
      case (tl l,l2) of
        ([m, u], [r, s]) => {mem = m, reg = r, psrs = s, undef = u}
      | _ => raise ERR "dest_arm_eval" ""
    else raise ERR "dest_arm_eval" ""
  end
  handle HOL_ERR _ => raise ERR "dest_arm_eval" "";

(* ------------------------------------------------------------------------- *)
(* Funtions for memory loading and saving *)

local
  fun bytes2num (b0,b1,b2,b3) =
    let open Arbnum
        val byte2num = fromInt o Char.ord o Byte.byteToChar
    in
      (byte2num b0) * (fromInt 16777216) + (byte2num b1) * (fromInt 65536) +
      (byte2num b2) * (fromInt 256) + byte2num b3
    end

  fun read_word (v,i) =
    let val l = Word8Vector.length v
        fun f i = if i < l then Word8Vector.sub(v,i) else 0wx0
    in
      mk_word32 (bytes2num (f i, f (i + 1), f (i + 2), f (i + 3)))
      (* could change order to do little-endian *)
    end
in
  fun load_mem fname skip top_addr m =
    let open BinIO
        val istr = openIn fname
        val data = inputAll istr
        val _ = closeIn istr
        val lines = (Word8Vector.length data - skip) div 4
        val l = List.tabulate(lines, fn i => read_word (data,4 * i + skip))
        val lterm = listSyntax.mk_list(l,``:word32``)
    in
      rhsc (SORT_BSUBST_CONV (mk_bsubst(mk_word30 top_addr,lterm,m)))
    end
end;

fun mem_read m a = (eval_word o rhsc o ARMe_CONV) (mk_comb(m,mk_word30 a));

fun save_mem fname start finish le m = let open BinIO Arbnum
    fun bits  h l n = (n mod pow(two,plus1 h)) div (pow(two,l))
    val ostr = openOut fname
    val num2byte = Word8.fromInt o Arbnum.toInt;
    fun num2bytes w =
          map (fn (i,j) => num2byte (bits (fromInt i) (fromInt j) w))
              ((if le then rev else I) [(31,24),(23,16),(15,8),(7,0)])
    fun save_word i = map (fn b => output1(ostr,b)) (num2bytes (mem_read m i))
    fun recurse i =
          if Arbnum.<=(i,finish) then recurse (save_word i; Arbnum.plus1 i)
          else closeOut ostr
in
  recurse start
end;

(* ------------------------------------------------------------------------- *)

(* -----------
 A suitable ARM code binary can be generated using GNU's binutils:

   arm-coff-as -EB assembler.s
   arm-coff-objcopy -S -j .text a.out code

 Then a skip of 60 is needed to pass over the header of the COFF binary
   ----------- *)

fun assemble m a s =
  let val as_ex  = Unix.execute(AS_BIN,["-EB","-aln"])
      val (inp,out) = Unix.streamsOf as_ex
      val _ = TextIO.output(out,String.concat (map (fn t => t ^ "\n") s))
      val _ = TextIO.closeOut out
      val err = TextIO.inputAll inp
      val _ = TextIO.closeIn inp
      val args = ["-S","-j",".text","a.out","a.out"]
      val objcopy_ex = Unix.execute(OBJCOPY_BIN, args)
      val _ = Unix.reap objcopy_ex
  in
    load_mem "a.out" 60 a m handle _ => (printn err; m)
  end;

fun assemble1 m a s =
   let val x = if s = "" then UNDEF_INST else Arbnum.fromHexString s in
      mk_subst(mk_word30 a,mk_word32 x,m)
   end handle _ => assemble m a [s];

fun disassemble1 m a = disassemblerLib.opcode_string (mem_read m a)

local
  fun recurse n m a l =
    if n = 0 then l
    else recurse (n - 1) m (Arbnum.plus1 a) (disassemble1 m a :: l)
in
  fun disassemble n m a = rev (recurse n m a [])
end;

fun list_mem n m a =
  let val l = disassemble n m a in
    (print o String.concat o (map (fn t => t ^ "\n"))) l
  end;

(* ------------------------------------------------------------------------- *)
(* Set the general purpose and program status registers *)

val foldl_tm = ``FOLDL (\m (r,v). if v = m r then m else (r :- v) m) x y``;

fun set_registers reg rvs  =
 (rhsc o FOLD_SUBST_CONV o
  subst [``x:reg`` |-> reg, ``y:(register # word32) list`` |-> rvs] o
  inst [alpha |-> ``:register``, beta |-> ``:word32``]) foldl_tm;

fun set_status_registers psr rvs  = (rhsc o 
  (FOLD_SUBST_CONV
     THENC PURE_ONCE_REWRITE_CONV [SPEC `n2w n` simTheory.PSR_CONS]
     THENC ARMe_CONV) o
  subst [``x:psr`` |-> psr, ``y:(psrs # word32) list`` |-> rvs] o
  inst [alpha |-> ``:psrs``, beta |-> ``:word32``]) foldl_tm;

(* ------------------------------------------------------------------------- *)
(* Running the model *)

fun init m r s =
   (PURE_ONCE_REWRITE_CONV [CONJUNCT1 STATE_ARMe_def] o
    subst [``mem:mem`` |-> m, ``reg:reg`` |-> r, ``psr:psr`` |-> s])
   ``STATE_ARMe 0 (ARM_EVAL (ARM reg psr) mem F)``;

fun next t =
  let val t1 = rhsc t
      val t2 = ((ARMe_CONV THENC ONCE_DEPTH_CONV SORT_BSUBST_CONV
                   THENC ONCE_DEPTH_CONV SORT_SUBST_CONV
                   THENC SUBST_EQ_CONV) o
                 subst [``s:state_arme`` |-> t1]) ``NEXT_ARMe s``
      val STATE_ARMe_NEXT = MATCH_MP onestepTheory.IMAP_NEXT STATE_ARMe_THM;
  in
     numLib.REDUCE_RULE (MATCH_MP STATE_ARMe_NEXT (CONJ t t2))
  end;

fun done t = term_eq T (#undef (dest_arm_eval (rhsc t)));

fun state n [] = []
  | state n (l as (t::ts)) =
      if n = 0 then l
      else let val nl = (time next t) :: l in
        if done t then nl else state (n - 1) nl
      end;

fun eval n m r s = state n [init m r s];
fun evaluate n m r s = hd (eval n m r s);

(* ------------------------------------------------------------------------- *)

end
