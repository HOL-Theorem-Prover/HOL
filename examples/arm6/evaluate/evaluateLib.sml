(* ========================================================================= *)
(* FILE          : evaluateLib.sml                                           *)
(* DESCRIPTION   : Code for executing the ARM specifications                 *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2003 - 2005                                               *)
(* ========================================================================= *)

structure evaluateLib :> evaluateLib =
struct

(* interactive use:
  app load ["Unix", "listLib", "computeLib", "io_onestepTheory",
            "modelsLib", "disassemblerLib", "patriciaLib"];
*)

open HolKernel boolLib bossLib;
open Parse Q;

(* ------------------------------------------------------------------------- *)

val EXC_HANDLER = "handler";
val UNDEF_INST  = Arbnum.fromHexString "E6000010";
val BINUTILS    = "/local/scratch/acjf3/gas/bin/arm-coff-";
val AS_BIN      = BINUTILS ^ "as";
val OBJCOPY_BIN = BINUTILS ^ "objcopy";

(* ------------------------------------------------------------------------- *)

val is_true = term_eq boolSyntax.T;
val is_false = not o is_true;

val num2word = Word.fromInt o Arbnum.toInt;
val word2num = Arbnum.fromInt o Word.toInt;

val block_width = 8;
val block_size = Word.toInt (Word.<<(0w1,Word.fromInt block_width));

type memory =  num array patriciaLib.ptree ref;

val mem = (ref patriciaLib.empty) : memory;

fun mem_blocks ()    = patriciaLib.keys (!mem);
fun mem_rm_block n   = mem := patriciaLib.remove n (!mem);
fun mem_nth_block n  = List.nth(mem_blocks(), n);
fun mem_read_block n = patriciaLib.member n (!mem);

local
  open Arbnum
in
  val n3 = fromInt 3
  val n4 = fromInt 4
  val n7 = fromInt 7
  val n8 = fromInt 8
  val n31 = fromInt 31
  val n32 = fromInt 32
  val n256 = Arbnum.fromInt 256
  val n65536 = Arbnum.fromInt 65536
  val n16777216 = Arbnum.fromInt 16777216
  val block_size_num = fromInt block_size
  val block_size_bytes = block_size_num * n4

  val plus4 = fn x => x + n4

  fun bits h l n =
    (n mod pow(two,plus1 h)) div (pow(two,l))
  fun slice h l n =
    (n mod pow(two,plus1 h)) - (n mod pow(two,l))

  fun ror32 n x =
    if x = zero then n else
      let val y = x mod n32 in
         (bits n31 y n) + (bits (less1 y) zero n) * pow(two, n32 - y)
      end

  fun set_byte align w x =
    let val b = bits n7 zero w in
      if align = zero then
        (slice n31 n8 x) + b
      else let val a = align * n8 in
        (slice n31 (a + n8) x) + b * pow(two,a) + (bits (less1 a) zero x)
      end
  end
end;

fun nzeros_string n = funpow n (fn x => x ^ "0") "";

fun toHexString8 n = let val x = Arbnum.toHexString n in
  nzeros_string (8 - size x) ^ x
end;

fun block_start n = Arbnum.*(block_size_num,Arbnum.*(word2num n,n4));

fun block_range n =
      let val x = block_start n
          val y = Arbnum.-(Arbnum.+(x,block_size_bytes),Arbnum.one)
      in
        (toHexString8 x) ^ " - " ^ (toHexString8 y)
      end

fun line_string l n =
  (toHexString8 l) ^ ":  " ^ (toHexString8 n) ^ "    " ^
  (disassemblerLib.opcode_string n);

fun printn s = print (s ^ "\n");

fun print_block (b:{data : num array, key : word},i,x) =
  let val n = block_start (#key b)
      val _ = ((Vector.foldl
                  (fn (a,l) => (printn (line_string l a); plus4 l)) n) o
                Array.extract) (#data b,i,x)
  in () end;

fun mem_print_block w =
  case mem_read_block w of
    SOME b => print_block (b,0,NONE)
  | _ => (printn "Empty memory block.");

fun mem_read byto n =
  let val (q,align) = Arbnum.divmod(n,n4)
      val (bl,i) = Arbnum.divmod(q,block_size_num)
  in
    case (mem_read_block (num2word bl), byto) of
      (NONE,_)          => UNDEF_INST
    | (SOME b,NONE)     => Array.sub(#data b,Arbnum.toInt i)
    | (SOME b,SOME byt) =>
         let val a = Arbnum.*(align,n8)
             val w = Array.sub(#data b,Arbnum.toInt i)
         in
           if byt then
             bits (Arbnum.+(a,n7)) a w
           else
             ror32 w a
         end
  end;

val mem_read_word = mem_read NONE;

fun mem_write byt n w =
  let val (q,align) = Arbnum.divmod(n,n4)
      val (bl,i) = Arbnum.divmod(q,block_size_num)
      val i = Arbnum.toInt i
  in
    case mem_read_block (num2word bl) of
      NONE => mem := (patriciaLib.add
        {key = num2word bl,
         data = let val d = Array.array(block_size,UNDEF_INST)
                    val w' = if byt then set_byte align w Arbnum.zero else w
                    val _ = Array.update(d,i,w')
                in
                  d
                end} (!mem))
    | SOME b => let val w' = if byt then
                               set_byte align w (Array.sub(#data b,i))
                             else w
                in
                  Array.update(#data b,i,w')
                end
  end;

(* ------------------------------------------------------------------------- *)

val ARM_CONV = modelsLib.ARM_CONV;
val ARM6_CONV = modelsLib.ARM6_CONV;

local
  val thms = [armTheory.SET_IFMODE_def,armTheory.SET_NZCV_def,
              armTheory.mode_num_def,armTheory.mode_case_def];
  val compset = wordsLib.words_compset ()
  val _ = computeLib.add_thms thms compset
in
  val WEVAL_CONV = computeLib.CBV_CONV compset;
end;

local open io_onestepTheory in
  val STATE_INP_ss =
     rewrites [state_inp_accessors, state_inp_updates_eq_literal,
       state_inp_accfupds, state_inp_fupdfupds, state_inp_literal_11,
       state_inp_fupdfupds_comp, state_inp_fupdcanon,
       state_inp_fupdcanon_comp]
end;

(* ------------------------------------------------------------------------- *)

val SUC_BETA_RULE = CONV_RULE (RATOR_CONV
  (DEPTH_CONV reduceLib.SUC_CONV THENC DEPTH_CONV PairRules.PBETA_CONV));

val SUBST_RULE = CONV_RULE (RAND_CONV
  (PURE_REWRITE_CONV [simTheory.Sa_def,simTheory.Sb_def]));

val rhsc = rhs o concl;
val lhsc = lhs o concl;
val fdest_comb = fst o dest_comb;
val sdest_comb = snd o dest_comb;

fun mk_word n = mk_comb(``n2w:num->word32``,numSyntax.mk_numeral n);

fun eval_word t = (numSyntax.dest_numeral o rhsc o WEVAL_CONV)
  (mk_comb (``w2n:word32->num``,t));

fun eval_pc t = (eval_word o rhsc o ARM_CONV) (mk_comb (t,``r15``));

local
  val hss = hd o snd o strip_comb
  val sss = (fn x => List.nth(x,1)) o snd o strip_comb
  fun f n t = snd (List.nth(TypeBase.dest_record t,n))
in
  val get_ireg = sss
  val get_reg = hss o hss
  val get_psr = sss o hss
  val get_state = f 0 o rhsc
  val get_out = f 1 o rhsc
  val get_input = f 1 o sdest_comb o lhsc
end;

local
  val gpc = eval_pc o get_reg
  val mk_read = mk_word o mem_read_word
in
  fun fetch_ireg t = let val pc = gpc t in
        (pc = n4,mk_read pc)
    end
  fun fetch_ireg_pipeb t = let val pc = gpc t in
        (mk_read pc, mk_read (Arbnum.+(pc,n4)))
    end
end;

local
  val split_enum = (snd o strip_comb o sdest_comb o concl)
  val register = split_enum armTheory.datatype_register;
  val psrs = split_enum armTheory.datatype_psrs;
  val reg_subst = mk_thy_const {Name = ":-", Thy ="arm",
   Ty = ``:register -> word32 -> (register -> word32) -> register -> word32``};
  val psr_subst = mk_thy_const {Name = ":-", Thy ="arm",
   Ty = ``:psrs -> word32 -> (psrs -> word32) -> psrs -> word32``};


  fun recurse _ [] _ = NONE
    | recurse x (h::t) n =
         if term_eq h x then SOME n
         else recurse x t (n + 1)

  fun register2word x = case (recurse x register 0) of
                          NONE  => NONE
                        | SOME n => SOME (Word.fromInt n)

  fun psrs2num x = recurse x psrs 0

  fun recurse2 ptree x =
       let val (l,r) = strip_comb x in  (* r = [i,d,m]; (i :- d) m *)
         if term_eq l reg_subst then
           recurse2
             (case register2word (List.nth(r,0)) of
                NONE => ptree
              | SOME d => patriciaLib.add {data = List.nth(r,1), key = d} ptree)
             (List.nth(r,2))
         else
           (x,ptree)
       end

  fun recurse3 a x =
    let val (l,r) = strip_comb x in  (* r = [i,d,m]; (i :- d) m *)
      if term_eq l psr_subst then
        recurse3
          (let val i = psrs2num (List.nth(r,0))
               val _ = if isSome i andalso
                          not (isSome (Array.sub(a,valOf i))) then
                         Array.update(a,valOf i,SOME (List.nth(r,1)))
                       else ()
           in a end) (List.nth(r,2))
      else Array.tabulate(length psrs,
              (fn i => let val d = Array.sub(a,i) in
                if isSome d then valOf d
                else (rhsc o ARM_CONV o mk_comb) (x,List.nth(psrs,i)) end))
    end

  fun read_registers x = recurse2 patriciaLib.empty x
  fun read_psrs x = recurse3 (Array.array(length psrs,NONE: term option)) x

  fun read_input t =
    let fun recurse t a =
          if is_cond t then
            let val (c,t1,t2) = dest_cond t in
              recurse t2 (pairLib.strip_pair t1::a)
            end
          else a
    in
      recurse (snd (dest_abs t)) []
    end;

  fun regVal (x,ptree) n =
    let val y = patriciaLib.member (Word.fromInt n) ptree in
      if isSome y then
        #data (valOf y)
      else
        (rhsc o ARM_CONV o mk_comb) (x,List.nth(register,n))
  end

  fun read_state t =
    let val (l,r) = strip_comb t
        val ireg = List.nth(r, 1)
        val exc  = List.nth(r, 2)
        val (l,r) = strip_comb (List.nth(r, 0))
        val reg = List.nth(r, 0)
        val psr = List.nth(r, 1)
    in
      {registers = read_registers reg, psrs = read_psrs psr,
       ireg = ireg, exc = exc}
    end
in
  fun read_trace t =
     let val f1 = rev o (map (fn t => ((read_state o get_state) t, get_out t)))
         val f2 = (read_input o get_input o hd)
     in
       zip (f1 t) ((f2 t) @
         [[``ARB:interrupts option``,``ARB:bool``,
           ``ARB:word32``,``ARB:word32 list``]])
     end;

  fun reg_string n = term_to_string (List.nth(register,Word.toInt n))
end;

fun is_word_literal t =
  is_comb t andalso
    (let val (l,r) = dest_comb t in
      (term_eq l ``n2w:num->word32``) andalso numSyntax.is_numeral r end);

(* ------------------------------------------------------------------------- *)

datatype mem_op = MemRead of num | MemWrite of bool * num * num |
                  CPMemRead of bool * num | CPMemWrite of bool * num |
                  CPWrite of num;

fun dec_memop t =
  let val (l,r) = strip_comb t
      val r0 = hd r
  in
    if term_eq l ``MemRead`` then
      MemRead (eval_word r0)
    else if term_eq l ``CPWrite`` then
      MemRead (eval_word r0)
    else let val r1 = List.nth(r,1) in
      if term_eq l ``CPMemRead`` then
        CPMemRead (is_true r0, eval_word r1)
      else if term_eq l ``CPMemWrite`` then
        CPMemWrite (is_true r0, eval_word r1)
      else
        MemWrite (is_true r0, eval_word r1, eval_word (List.nth(r,2)))
    end
  end;

fun dec_memop_list t =
  let fun recursion acc t =
         if term_eq t ``[]:memop list`` then acc else
           let val (t1,t2) = dest_comb t in
              recursion ((dec_memop (sdest_comb t1))::acc) t2
           end
  in
    rev (recursion [] t)
  end;

fun transfer mop =
  case mop of
    MemRead n => [mk_word (mem_read_word n)]
  | MemWrite (b,a,d) => (mem_write b a d;[])
  | _ => [];

fun do_transfers mops =
  foldr (fn (mop,l) => l @ transfer mop) [] (dec_memop_list mops);

val term_list2list_term = foldl listLib.mk_cons ``[]:word32 list``;

(* ------------------------------------------------------------------------- *)

fun transfer6 pending t =
  case pairLib.spine_pair t of
    [dout,nmreq,nopc,nrw,nbw,areg] =>
      let val mreq = is_false nmreq
          val rw   = is_false nrw
          val bw   = is_false nbw
          val _ = case pending of
                    NONE => ()
                  | SOME (bw,areg) => mem_write bw areg (eval_word dout)
      in
        if mreq then
          if rw then
             (NONE, (mk_word o mem_read_word o eval_word) areg)
          else
             (SOME (bw,eval_word areg), ``ARB:word32``)
        else
          (NONE, ``ARB:word32``)
      end
   | _ => raise HOL_ERR {origin_structure = "executeLib",
                         origin_function = "transfer6", 
                         message = "Cannot decode ARM6 output." };

(* ------------------------------------------------------------------------- *)

local
  val byte2num = Arbnum.fromInt o Char.ord o Byte.byteToChar
  fun bytes2num (b0,b1,b2,b3) =
        Arbnum.+(Arbnum.*(byte2num b0,n16777216),
        Arbnum.+(Arbnum.*(byte2num b1,n65536),
        Arbnum.+(Arbnum.*(byte2num b2,n256),byte2num b3)))
        
  fun read_word (v,i) =
        let val l = Word8Vector.length v
            fun f i = if i < l then Word8Vector.sub(v,i) else 0wx0
        in
          bytes2num (f i, f (i + 1), f (i + 2), f (i + 3))
          (* could change order to do little-endian *)
        end
in
  fun load_data fname skip top_addr =
    let open BinIO
        val istr = openIn fname
        val data = inputAll istr
        val _ = closeIn istr
    in
      for_se 0 ((Word8Vector.length data - skip) div 4 - 1)
        (fn i => let val a = 4 * i
                     val n = read_word (data,a + skip)
                 in mem_write false (Arbnum.+(top_addr,Arbnum.fromInt a)) n end)
    end
end;

fun save_data fname start finish le =
  let open BinIO Arbnum
      val ostr = openOut fname
      val num2word8 = Word8.fromInt o Arbnum.toInt;
      val offset = bits one zero start
      fun swap_end i = slice n31 two i + (n3 - bits one zero i)
      fun addr i = if le then i else swap_end (i - offset) + offset
      fun save_word i = output1(ostr,num2word8 (mem_read (SOME true) (addr i)))
      fun recurse i =
            if Arbnum.<=(i,finish) then recurse (save_word i; Arbnum.plus1 i)
            else closeOut ostr
  in
    recurse start
  end;

(* -----------
 A suitable ARM code binary can be generated using GNU's binutils:

   arm-coff-as -EB assembler.s
   arm-coff-objcopy -S -j .text a.out code

 Then a skip of 60 is needed to pass over the header of the COFF binary
   ----------- *)

fun assemble a s =
  let val as_ex  = Unix.execute(AS_BIN,["-EB","-aln"])
      val (inp,out) = Unix.streamsOf as_ex
      val _ = TextIO.output(out,String.concat (map (fn t => t ^ "\n") s))
      val _ = TextIO.closeOut out
      val err = TextIO.inputAll inp
      val _ = TextIO.closeIn inp
      val objcopy_ex = Unix.execute(OBJCOPY_BIN,
                         ["-S","-j",".text","a.out","a.out"])
      val _ = Unix.reap objcopy_ex
  in
    (load_data "a.out" 60 a) handle _ => print err
  end;
  
fun assemble1 a s =
   let val x = if s = "" then UNDEF_INST else Arbnum.fromHexString s in
      mem_write false a x
   end handle _ => assemble a [s];

(* load and save rudimentary exception handler *)

val _ = assemble Arbnum.zero
  ["movs pc, #32",
   "label: b label",
   "movs pc, r14",
   "subs pc, r14, #4",
   "subs pc, r14, #8",
   "movs pc, r14",
   "subs pc, r14, #4",
   "subs pc, r14, #4"];

val _ = save_data EXC_HANDLER Arbnum.zero n31 false;

(* ------------------------------------------------------------------------- *)

val INITIAL_PSR = (rhsc o SUBST_RULE o modelsLib.ARM_CONV)
  ``CPSR_WRITE (SPSR_WRITE ARB svc
       (SET_NZCV (F,F,F,F) (SET_IFMODE F F usr 0w)))
       (SET_NZCV (F,F,F,F) (SET_IFMODE F F svc 0w))``;

val ARM_SPEC_NEXT =
  MATCH_MP io_onestepTheory.IMAP_NEXT armTheory.STATE_ARM_THM;

val ARM6_SPEC_NEXT =
  MATCH_MP io_onestepTheory.IMAP_NEXT coreTheory.STATE_ARM6_THM;

(* ------------------------------------------------------------------------- *)

fun init_state6 t =
  let val (ireg,pipeb) = fetch_ireg_pipeb t
      val s = SIMP_CONV (std_ss++STATE_INP_ss++boolSimps.LET_ss)
                [coreTheory.STATE_ARM6_def,coreTheory.ARM6_SPEC_def]
               (subst [``x:state_arm6`` |->
                subst [``ireg:word32`` |-> ireg, ``pipea:word32`` |-> pipeb,
                       ``pipeb:word32`` |-> pipeb] t]
                 ``ARM6_SPEC 0 <| state := x; inp := \c. ARB |>``)
      val ns = SUBST_RULE (CONV_RULE (RAND_CONV ARM6_CONV) s)
      val l = (snd o strip_comb)
                 (List.nth ((snd o strip_comb o get_state) ns,1))
      val newinst = (is_true (List.nth(l,5))) andalso
                    (is_true (List.nth(l,7)))
      val done = not (is_word_literal (List.nth(l,4)))
  in
    {newinst = newinst, done = done, state = ns}
  end;

fun next_state6 pending p =
  let val (pending2,out) = (transfer6 pending o get_out) p
      val inp = subst [``data:word32`` |-> out] ``(T,F,T,T,data:word32,T,T)``
      val ns = ARM6_CONV (subst [``x:state_arm6`` |-> get_state p,
                ``i:bool # bool # bool # bool # word32 # bool # bool`` |-> inp]
                ``NEXT_ARM6 x i``)
      val out2 = ARM6_CONV (mk_comb(``OUT_ARM6``,rhsc ns))
      val l = (snd o strip_comb) (List.nth ((snd o strip_comb o rhsc) ns,1))
      val newinst = (is_true (List.nth(l,5))) andalso
                    (is_true (List.nth(l,7)))
      val done = not (is_word_literal (List.nth(l,4)))
  in
     {newinst = newinst, done = done,
      pending = pending2,
      state = (SUBST_RULE o SUC_BETA_RULE)
                 (MATCH_MP ARM6_SPEC_NEXT (CONJ  p (CONJ ns out2)))}
  end;

fun state6 t x =
  let fun recurse t pending l =
        if t = 0 then l
        else let val s = time next_state6 pending (hd l) in
          if #done s then (#state s::l)
          else
            recurse (if #newinst s then t - 1 else t) (#pending s) (#state s::l)
        end
      val s0 = init_state6 x
   in
     if #done s0 then [#state s0]
     else recurse t NONE [#state s0]
   end;

(* ------------------------------------------------------------------------- *)

fun init_state t =
  let val (done,ireg) = fetch_ireg t
      val s = SIMP_CONV (std_ss++STATE_INP_ss++boolSimps.LET_ss)
              [armTheory.STATE_ARM_def,armTheory.ARM_SPEC_def]
             (subst [``x:state_arm_ex`` |-> subst [``ireg:word32`` |-> ireg] t]
              ``ARM_SPEC 0 <| state := x; inp := \c. ARB |>``)
      val ns = SUBST_RULE (CONV_RULE (RAND_CONV ARM_CONV) s)
      val done = done orelse (not o is_word_literal o get_ireg o get_state) ns
  in
     {done = done, state = ns}
  end;

fun next_state p =
  let val out = (term_list2list_term o do_transfers o get_out) p
      val copro =
               (disassemblerLib.is_coproc o eval_word o get_ireg o get_state) p
      val inp = subst [``irpt : interrupts option`` |->
                       (if copro then ``SOME Undef``
                        else ``NONE : interrupts option``),
                       ``data : word32 list`` |-> out]
               ``(irpt : interrupts option,F,IREG : word32,data : word32 list)``
      val ns = ARM_CONV (subst [``x:state_arm_ex`` |-> get_state p,
                ``i:interrupts option # bool # word32 # word32 list `` |-> inp]
                ``NEXT_ARM x i``)
      val (done,ireg) = fetch_ireg (rhsc ns)
      val ns2 = Thm.INST [``IREG:word32`` |-> ireg] ns
      val out2 = ARM_CONV (mk_comb(``OUT_ARM``,rhsc ns2))
      val done = done orelse (not o is_word_literal o get_ireg o rhsc) ns2
  in
     {done = done,
      state = (SUBST_RULE o SUC_BETA_RULE)
                (MATCH_MP ARM_SPEC_NEXT (CONJ  p (CONJ ns2 out2)))}
  end;

fun state t x =
  let fun recurse t l =
        if t = 0 then l
        else let val s = time next_state (hd l) in
          if #done s then (#state s::l)
          else
            recurse (t - 1) (#state s::l)
        end
      val s0 = init_state x
   in
     if #done s0 then [#state s0]
     else recurse t [#state s0]
   end;

(* ------------------------------------------------------------------------- *)

(*
val _ = npp_word_arm_ex();
val _ = npp_word_arm();
val _ = npp_word_pipe();
val _ = npp_word_psr();
*)

(*
val r0 =
   (subst [``reg:register -> word32`` |-> ``(r15 :- (0w:word32)) ARB``,
           ``onfq:bool`` |-> ``T``,
           ``ooonfq:bool`` |-> ``T``,
           ``oniq:bool`` |-> ``T``,
           ``oooniq:bool`` |-> ``T``,
           ``pipebabt:bool`` |-> ``F``,
           ``aregn2:word3`` |-> ``2w:word3``,
           ``mrq2:bool`` |-> ``T``,
           ``psr:psrs -> word32`` |-> INITIAL_PSR]
    ``ARM6 (DP reg psr areg din alua alub dout)
        (CTRL pipea pipeaval pipeb pipebval ireg iregval ointstart
           onewinst endinst obaselatch opipebll nxtic nxtis nopc1 oorst
           resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2
           dataabt2 aregn2 mrq2 nbw nrw sctrlreg psrfb oareg mask orp
           oorp mul mul2 borrow2 mshift)``);

val r = state6 1 r0;

val s0 =
   (subst [``reg:register -> word32`` |-> ``(r15 :- (0w:word32)) ARB``,
           ``psrs:psrs -> word32`` |-> INITIAL_PSR]
     ``ARM_EX (ARM reg psrs) ireg software``);

val s1 = next_state (#state (init_state s0));
val s = state 2 s0;

val k = mem_blocks();
val _ = mem_print_block 0wx0;
val SOME db = mem_read_block 0wx2;
val _ = print_block(db,0,SOME 10);
val _ = Array.copy {si = 0, len = NONE, dst = #data db, di = 0,
                    src = Array.array(block_size,Arbnum.zero)};
val _ = Array.copy {si = 0, len = NONE, dst = #data mb, di = 0,
                    src = Array.array(block_size,Arbnum.zero)};
*)

end
