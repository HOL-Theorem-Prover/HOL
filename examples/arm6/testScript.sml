(* app load ["metisLib","listLib","compLib","io_onestepTheory",
             "armLib","coreLib","disassemblerLib","patriciaLib"]; *)
open HolKernel boolLib bossLib Parse Q;

(* -------------------------------------------------------- *)

val _ = new_theory "test";

val _ = numLib.prefer_num();

val EXC_HANDLER = "exc_handler";

(* -------------------------------------------------------- *)

fun add_rws f rws =
  let val cmp_set = f()
      val _ = compLib.add_thms rws cmp_set
  in
    cmp_set
end;

(* -------------------------------------------------------- *)

val SET_IREG_def = Define`
  SET_IREG (ARM_EX s ireg exc) ireg2 = ARM_EX s ireg2 exc `;

val SET_IREG = prove(
  `!x s irpt data. (NEXT_ARM s (irpt,ARB,data) = x) ==>
                   (NEXT_ARM s (irpt,ireg,data) = SET_IREG x ireg)`,
  Cases THEN RW_TAC std_ss [armTheory.NEXT_ARM_def,SET_IREG_def]
);

val ARM_SPEC_NEXT = MATCH_MP io_onestepTheory.IMAP_NEXT armTheory.STATE_ARM_THM;
val ARM6_SPEC_NEXT = MATCH_MP io_onestepTheory.IMAP_NEXT coreTheory.STATE_ARM6_THM;

(* -------------------------------------------------------- *)

val num2word = Word.fromInt o Arbnum.toInt;
val word2num = Arbnum.fromInt o Word.toInt;

val block_width = 8;
val block_size = Word.toInt (Word.<<(0w1,Word.fromInt block_width));

val memory = ref (patriciaLib.empty : num array patriciaLib.ptree);

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

  fun swap_ends n =
    let val x0 = bits n7 zero n
        val x1 = bits (fromInt 15) n8 n
        val x2 = bits (fromInt 23) (fromInt 16) n
        val x3 = bits n31 (fromInt 24) n
    in
       x0 * n16777216 + x1 * n65536 + x2 * n256 + x3
    end
end;

fun nzeros_string n = funpow n (fn x => x ^ "0") "";
fun toHexString8 n = let val x = Arbnum.toHexString n in nzeros_string (8 - size x) ^ x end;
fun block_start n = Arbnum.*(block_size_num,Arbnum.*(word2num n,n4));

fun block_range n =
      let val x = block_start n
          val y = Arbnum.-(Arbnum.+(x,block_size_bytes),Arbnum.one)
      in
        (toHexString8 x) ^ " - " ^ (toHexString8 y)
      end

fun line_string l n = (toHexString8 l) ^ ":  " ^ (toHexString8 n) ^ "    " ^ (disassemblerLib.opcode_string n);

fun printn s = print (s ^ "\n");

fun print_block (b:{data : num array, key : word},i,x) =
  let val n = block_start (#key b)
      val _ =
    ((Vector.foldl (fn (a,l) => (printn (line_string l a); plus4 l)) n) o Array.extract) (#data b,i,x)
  in () end;

fun mem_read byto n =
  let val (q,align) = Arbnum.divmod(n,n4)
      val (bl,i) = Arbnum.divmod(q,block_size_num)
  in
    case patriciaLib.member (num2word bl) (!memory) of
      NONE => Arbnum.zero
    | SOME b =>
        let val w = Array.sub(#data b,Arbnum.toInt i) in
        case byto of
          NONE => w
        | SOME (le,byt) =>
            let val w = if le then w else swap_ends w
                val a = Arbnum.*(align,n8) in
              if byt then
                bits (Arbnum.+(a,n7)) a w
              else
                ror32 w a
            end
        end
  end;

val mem_read_word = mem_read NONE;

fun mem_write byt n w =
  let val (q,align) = Arbnum.divmod(n,n4)
      val (bl,i) = Arbnum.divmod(q,block_size_num)
      val i = Arbnum.toInt i
  in
    case patriciaLib.member (num2word bl) (!memory) of
      NONE => memory := (patriciaLib.add
        {key = num2word bl,
         data = let val d = Array.array(block_size,Arbnum.zero)
                    val _ = Array.update(d,i,if byt then set_byte align w Arbnum.zero else w) in
                 d
               end} (!memory))
    | SOME b => Array.update(#data b,i,if byt then set_byte align w (Array.sub(#data b,i)) else w)
  end;

(* -------------------------------------------------------- *)

(*
val ZM_def = Define`ZM = \x. 0w`;

fun barmsim_rws () = add_rws arm_rws [ZM_def];

val SIMARM_CONV = CBV_CONV (barmsim_rws());
*)

val SIMARM_CONV = armLib.ARM_CONV;
val SIMARM6_CONV = coreLib.ARM6_CONV;

fun weval_rws () = add_rws word32Lib.word_compset
  [armTheory.SET_IFMODE_def,armTheory.SET_NZCV_def,
   armTheory.mode_num_def,armTheory.mode_case_def];

val WEVAL_CONV = computeLib.CBV_CONV (weval_rws());

local open io_onestepTheory in
  val STATE_INP_ss =
     rewrites [state_inp_accessors, state_inp_updates_eq_literal,
       state_inp_accfupds, state_inp_fupdfupds, state_inp_literal_11,
       state_inp_fupdfupds_comp, state_inp_fupdcanon,
       state_inp_fupdcanon_comp]
end;

(* -------------------------------------------------------- *)

val SUC_BETA_RULE =
  CONV_RULE (RATOR_CONV (DEPTH_CONV reduceLib.SUC_CONV THENC DEPTH_CONV PairRules.PBETA_CONV));

val SUBST_RULE = CONV_RULE (RAND_CONV (PURE_REWRITE_CONV [simTheory.Sa_def,simTheory.Sb_def]));

val rhsc = rhs o concl;
val lhsc = lhs o concl;
val fdest_comb = fst o dest_comb;
val sdest_comb = snd o dest_comb;

fun mk_word32 n = mk_comb(``n2w``,numSyntax.mk_numeral n);

fun eval_word t = (numSyntax.dest_numeral o rhsc o WEVAL_CONV) (mk_comb (``w2n``,t));
fun eval_pc t = (eval_word o rhsc o SIMARM_CONV) (mk_comb (t,``r15``));

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
  val mk_read = mk_word32 o mem_read_word
in
  val fetch_ireg = mk_read o gpc
  fun fetch_ireg_pipeb t = let val pc = gpc t in
        (mk_read pc, mk_read (Arbnum.+(pc,n4)))
    end
end;

datatype arm_component = Register of int | PSR of int | Ireg | Exc;

local
  val register = (snd o strip_comb o sdest_comb o concl) armTheory.datatype_register;
  val psrs = (snd o strip_comb o sdest_comb o concl) armTheory.datatype_psrs;

  fun recurse _ [] _ = NONE
    | recurse x (h::t) n =
         if term_eq h x then SOME n
         else recurse x t (n + 1)

  fun register2word x = case (recurse x register 0) of NONE => NONE | SOME n => SOME (Word.fromInt n)
  fun psrs2num x = recurse x psrs 0

  fun recurse2 ptree x =
        let val (l,r) = strip_comb x in  (* r = [m,i,d]; m {.i <- d.} *)
          if term_eq l ``SUBST:(register->word32)->register->word32->register->word32`` then
            recurse2
              (let val d = register2word (List.nth(r,1)) in
                 if isSome d then patriciaLib.add {data = List.nth(r,2), key = valOf d} ptree
                             else ptree
               end) (List.nth(r,0))
          else
            (x,ptree)
        end

  fun recurse3 a x =
    let val (l,r) = strip_comb x in  (* r = [m,i,d]; m {.i <- d.} *)
      if term_eq l ``SUBST:(psrs->word32)->psrs->word32->psrs->word32`` then
        recurse3
          (let val i = psrs2num (List.nth(r,1))
               val _ = if isSome i andalso not (isSome (Array.sub(a,valOf i))) then
                         Array.update(a,valOf i,SOME (List.nth(r,2)))
                       else ()
           in a end) (List.nth(r,0))
      else Array.tabulate(length psrs,
              (fn i => let val d = Array.sub(a,i) in
                if isSome d then valOf d
                else (rhsc o SIMARM_CONV o mk_comb) (x,List.nth(psrs,i)) end))
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
        (rhsc o SIMARM_CONV o mk_comb) (x,List.nth(register,n))
  end

  fun read_state t =
    let val (l,r) = strip_comb t
        val ireg = List.nth(r, 1)
        val exc  = List.nth(r, 2)
        val (l,r) = strip_comb (List.nth(r, 0))
        val reg = List.nth(r, 0)
        val psr = List.nth(r, 1)
    in
      {registers = read_registers reg, psrs = read_psrs psr, ireg = ireg, exc = exc}
    end

in
(*  fun state_val (x: {exc : term, ireg : term, psrs : term array, registers : term * term patriciaLib.ptree}) c =
    case c of
      Ireg => #ireg x
    | Exc => #exc x
    | PSR n => Array.sub(#psrs x,n)
    | Register n => regVal (#registers x) n *)
  fun read_trace t =
     let val f1 = rev o (map (fn t => ((read_state o get_state) t, get_out t)))
         val f2 = (read_input o get_input o hd)
     in
       zip (f1 t) ((f2 t) @ [[``ARB:interrupts option``,``ARB:word32``,``ARB:word32 list``]])
     end;

  fun word2reg_string n = term_to_string (List.nth(register,Word.toInt n))
end;

fun is_word_literal t =
  if is_comb t then
    let val (l,r) = dest_comb t in
      (term_eq l ``n2w``) andalso numSyntax.is_numeral r
    end
  else false;

(* -------------------------------------------------------- *)

datatype mem_op = MemRead of num | MemWrite of bool * num * num;

fun dec_memop t =
  let val (t1,t2) = dest_comb t
  in
    if term_eq t1 ``MemRead`` then
      MemRead (eval_word t2)
    else
      let val (t3,t4) = dest_comb t1
          val (t5,t6) = dest_comb t3
      in
        MemWrite (term_eq t6 boolSyntax.T,eval_word t4,eval_word t2)
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
    MemRead n => [mk_word32 (mem_read_word n)]
  | MemWrite (b,a,d) => (mem_write b a d;[]);

fun do_transfers mops = foldr (fn (mop,l) => l @ transfer mop) [] (dec_memop_list mops);

val term_list2list_term = foldl listLib.mk_cons ``[]:word32 list``;

(* -------------------------------------------------------- *)

val pending = ref (NONE:(bool * num) option);

fun transfer6 t =
  let val [dout,nmreq,nopc,nrw,nbw,areg] = pairLib.spine_pair t
      val [mreq,rw,bw] = map (term_eq boolSyntax.F) [nmreq,nrw,nbw]
      val _ = if isSome (!pending) then
                let val (bw,areg) = valOf (!pending) in
                  mem_write bw areg (eval_word dout)
                end
              else ()
  in
    if mreq then
      if rw then
         (pending := NONE; (mk_word32 o mem_read_word o eval_word) areg)
      else
         (pending := SOME (bw,eval_word areg); ``ARB:word32``)
    else
      (pending := NONE; ``ARB:word32``)
  end;

(* -------------------------------------------------------- *)

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
        end
in
  fun load_data fname skip top_addr =
    let open BinIO
        val istr = openIn fname
        val data = inputAll istr
        val _ = closeIn istr
    in
      for_se 0 ((Word8Vector.length data - skip) div 4)
        (fn i => let val a = 4 * i
                     val n = read_word (data,a + skip)
                 in mem_write false (Arbnum.+(top_addr,Arbnum.fromInt a)) n end)
    end
end

fun save_data fname start finish le =
  let open BinIO
      val ostr = openOut fname
      val num2word8 = Word8.fromInt o Arbnum.toInt;
      fun save_word i = output1(ostr,num2word8 (mem_read (SOME (le,true)) i))
      fun recurse i =
            if Arbnum.<=(i,finish) then recurse (save_word i; Arbnum.plus1 i)
            else closeOut ostr
  in
    recurse start
  end

(* -----------
 A suitable ARM code binary can be generated using GNU's binutils:

   arm-coff-as -EB assembler.s
   arm-coff-objcopy -S -j .text a.out code

 Then a skip of 60 is needed to pass over the header of the COFF binary
   ----------- *)

val exc_handler = Word8Vector.fromList
  [0wxE3,0wxB0,0wxF0,0wx20,
   0wxE1,0wxB0,0wxF0,0wx0E,
   0wxE1,0wxB0,0wxF0,0wx0E,
   0wxE2,0wx5E,0wxF0,0wx04,
   0wxE2,0wx5E,0wxF0,0wx08,
   0wxE1,0wxB0,0wxF0,0wx0E,
   0wxE2,0wx5E,0wxF0,0wx04,
   0wxE2,0wx5E,0wxF0,0wx04];

(* save exception handler *)
val _ = let open BinIO
            val ostr = openOut EXC_HANDLER
        in output(ostr,exc_handler); closeOut ostr end;

(** Load Exception Handler *************)
val _ = load_data EXC_HANDLER 0 Arbnum.zero;
(***************************************)

(* -------------------------------------------------------- *)

val _ = word32Lib.pp_word_unsigned_hex();
(*
val _ = npp_word_arm_ex();
val _ = npp_word_arm();
val _ = npp_word_pipe();
val _ = npp_word_psr();
*)

val RESET_PSR_def = Define`
  RESET_PSR = CPSR_WRITE (SPSR_WRITE ARB svc (SET_NZCV (F,F,F,F) (SET_IFMODE F F irq 0w)))
                         (SET_NZCV (F,F,F,F) (SET_IFMODE F F svc 0w))`;

val RESET_PSR = (SUBST_RULE o armLib.ARM_RULE) RESET_PSR_def;

(* -------------------------------------------------------- *)

fun init_state6 t =
  let val _ = pending := NONE
      val (ireg,pipeb) = fetch_ireg_pipeb t
      val s = SIMP_CONV (std_ss++STATE_INP_ss++boolSimps.LET_ss)
                [coreTheory.STATE_ARM6_def,coreTheory.ARM6_SPEC_def]
               (subst [``x:state_arm6`` |->
                subst [``ireg:word32`` |-> ireg, ``pipea:word32`` |-> pipeb, ``pipeb:word32`` |-> pipeb] t]
                 ``ARM6_SPEC 0 <| state := x; inp := \c. ARB |>``)
      val ns = SUBST_RULE (CONV_RULE (RAND_CONV SIMARM6_CONV) s)
      val l = (snd o strip_comb) (List.nth ((snd o strip_comb o get_state) ns,1))
      val newinst = (term_eq (List.nth(l,5)) boolSyntax.T) andalso
                    (term_eq (List.nth(l,7)) boolSyntax.T)
      val done = not (is_word_literal (List.nth(l,4)))
  in
    {newinst = newinst, done = done, state = ns}
  end;

(*
val r0 =
   (subst [``reg:register -> word32`` |-> ``ARB {. r15 <- 0x0w .}``,
           ``onfq:bool`` |-> ``T``,
           ``ooonfq:bool`` |-> ``T``,
           ``oniq:bool`` |-> ``T``,
           ``oooniq:bool`` |-> ``T``,
           ``pipebabt:bool`` |-> ``F``,
           ``aregn2:num`` |-> ``2``,
           ``mrq2:bool`` |-> ``T``,
           ``psr:psrs -> word32`` |-> rhsc RESET_PSR]
    ``ARM6 (DP reg psr areg din alua alub dout)
        (CTRL pipea pipeaval pipeb pipebval ireg iregval ointstart
           onewinst endinst obaselatch opipebll nxtic nxtis nopc1 oorst
           resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2
           dataabt2 aregn2 mrq2 nbw nrw sctrlreg psrfb oareg mask orp
           oorp mul mul2 borrow2 mshift)``);
*)

(* --- *)

fun next_state6 p =
  let val out = (transfer6 o get_out) p
      val inp = subst [``data:word32`` |-> out] ``(T,F,T,T,data:word32)``
      val ns = SIMARM6_CONV (subst [``x:state_arm6`` |-> get_state p,
                 ``i:bool # bool # bool # bool # word32`` |-> inp] ``NEXT_ARM6 x i``)
      val out2 = SIMARM6_CONV (mk_comb(``OUT_ARM6``,rhsc ns))
      val l = (snd o strip_comb) (List.nth ((snd o strip_comb o rhsc) ns,1))
      val newinst = (term_eq (List.nth(l,5)) boolSyntax.T) andalso
                    (term_eq (List.nth(l,7)) boolSyntax.T)
      val done = not (is_word_literal (List.nth(l,4)))
  in
     {newinst = newinst, done = done,
      state = (SUBST_RULE o SUC_BETA_RULE) (MATCH_MP ARM6_SPEC_NEXT (CONJ  p (CONJ ns out2)))}
  end;

fun state6 t x =
  let fun recurse t l =
        if t = 0 then l
        else let val s = time next_state6 (hd l) in
          if #done s then (#state s::l)
          else
            recurse (if #newinst s then t - 1 else t) (#state s::l)
        end
      val s0 = init_state6 x
   in
     if #done s0 then [#state s0]
     else recurse t [#state s0]
   end;

(*
val r = state6 5 r0;
*)

(* -------------------------------------------------------- *)

fun init_state t =
  let val ireg = fetch_ireg t
      val s = SIMP_CONV (std_ss++STATE_INP_ss++boolSimps.LET_ss)
                [armTheory.STATE_ARM_def,armTheory.ARM_SPEC_def]
               (subst [``x:state_arm_ex`` |-> subst [``ireg:word32`` |-> ireg] t]
                 ``ARM_SPEC 0 <| state := x; inp := \c. ARB |>``)
      val ns = SUBST_RULE (CONV_RULE (RAND_CONV SIMARM_CONV) s)
      val done = (not o is_word_literal o get_ireg o get_state) ns
  in
     {done = done, state = ns}
  end;

(*
val s0 =
   (subst [``reg:register -> word32`` |-> ``ARB {. r15 <- 0x0w .}``,
           ``psrs:psrs -> word32`` |-> rhsc RESET_PSR]
     ``ARM_EX (ARM reg psrs) ireg software``);
*)

(* --- *)

fun next_state p =
  let val out = (term_list2list_term o do_transfers o get_out) p
      val inp = subst [``data:word32 list`` |-> out]
                  ``(NONE:interrupts option,ARB:word32,data:word32 list)``
      val ns = SIMARM_CONV (subst [``x:state_arm_ex`` |-> get_state p,
                 ``i:interrupts option # word32 # word32 list `` |-> inp] ``NEXT_ARM x i``)
      val ireg = fetch_ireg (rhsc ns)
      val ns2 = (CONV_RULE (RHS_CONV (PURE_REWRITE_CONV [SET_IREG_def])))
                  (MATCH_MP (Thm.INST [``ireg:word32`` |-> ireg] SET_IREG) ns)
      val out2 = SIMARM_CONV (mk_comb(``OUT_ARM``,rhsc ns2))
      val done = (not o is_word_literal o get_ireg o rhsc) ns2
  in
     {done = done,
      state = (SUBST_RULE o SUC_BETA_RULE) (MATCH_MP ARM_SPEC_NEXT (CONJ  p (CONJ ns2 out2)))}
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

(* val s1 = next_state (#state (init_state s0)); *)
(* val s = state 2 s0; *)

(* -------------------------------------------------------- *)

(* val k = patriciaLib.keys (!memory); *)
(* val SOME mb = patriciaLib.member 0wx0 (!memory); *)
(* val SOME db = patriciaLib.member 0wx2 (!memory); *)
(* val _ = print_block(db,0,NONE); *)
(* val _ = print_block(db,0,SOME 10); *)
(* val _ = print_block(mb,0,SOME 14); *)
(* val _ = Array.copy {si = 0, len = NONE, dst = #data db, di = 0, src = Array.array(block_size,Arbnum.zero)}; *)
(* val _ = Array.copy {si = 0, len = NONE, dst = #data mb, di = 0, src = Array.array(block_size,Arbnum.zero)}; *)

(* -------------------------------------------------------- *)

val concat = String.concat;
val _ = use "root_mosml.sml";
val _ = SmlTk.init();

local
  open SmlTk
  datatype mode = usr | fiq | irq | svc | abt | und
  datatype exc = reset | undefined | software | pabort | dabort | interrupt | fast
  type psr = {c : bool, f : bool, i : bool, mode : mode, n : bool, v : bool, z : bool}

  val modeId = newWidgetId()
  val regId = Array.tabulate(16,fn _ => newWidgetId())
  val reg_nameId = Array.tabulate(7,fn _ => newWidgetId())
  val psr_nameId = newWidgetId()
  val psrId = newWidgetId()
  val excId = newWidgetId()
  val intId = newWidgetId()
  val maxcId = newWidgetId()

  val ex_regs = Array.array(22,"")
  val mode = ref usr
  val exc = ref software
  val psr = Array.array(6,{n = false, z = false, c = false, v = false, i = false, f = false, mode = usr})

  val trace_winId = newWinId()

  val load_winId = newWinId()
  val load_fnameId = newWidgetId()
  val load_offsetId = newWidgetId()
  val load_startId = newWidgetId()

  val save_winId = newWinId()
  val save_fnameId = newWidgetId()
  val save_startId = newWidgetId()
  val save_finishId = newWidgetId()

  val mem_winId = newWinId()
  val mem_blockId = newWidgetId()
  val mem_dumpId = newWidgetId()

  val st_opcId = newWidgetId()
  val st_excId = newWidgetId()
  val st_regId = newWidgetId()
  val st_psrId = newWidgetId()
  val in_intId = newWidgetId()
  val in_opcId = newWidgetId()
  val in_dinId = newWidgetId()
  val doutId = newWidgetId()
  val timeId = newWidgetId()

  val the_thm_trace = ref ([]:thm list)
  val the_trace = ref ([]:(({exc : term, ireg : term, psrs : term array,
     registers : term * term patriciaLib.ptree} * term) * term list) list)

  fun reset_all() =
        let val _ = Array.modify (fn _ => "") ex_regs
            val _ = Array.modify (fn _ => {n = false, z = false, c = false, v = false,
                                           i = false, f = false, mode = usr}) psr
            val _ = mode := usr
            val _ = exc  := software
        in
          ()
        end

  (* --- *)

  fun simple_text id = TextWid {
        widId = id, scrolltype = NoneScb, annotext = mtAT,
        packings = [Side Right], configs = [Width 40, Height 1], bindings = []}

  fun simple_list (x,y) scrl id = Listbox {
        widId = id, scrolltype = if scrl then RightScb else NoneScb, packings = [], bindings = [],
        configs = [Font (Typewriter []),Width x, Height y]}

  fun simple_frame p w = Frame {
        widId = newWidgetId(), bindings = [], configs = [], packings = p, widgets = w}
        
  fun simple_label t = Label {
        widId = newWidgetId(), bindings = [], configs = [Text t], packings = [Side Left]}

  fun simple_top_label t = Label {
        widId = newWidgetId(), bindings = [], configs = [Text t], packings = [Side Top]}

  fun simple_tt_label id t = Label {
        widId = id, bindings = [], packings = [Side Left],
        configs = [Text t,Font (Typewriter []),Foreground Black]}

  fun simple_entry id = Entry {
        widId = id, bindings = [], configs = [], packings = [Side Right]}

  fun simple_button p t c = Button {
        widId = newWidgetId(), configs = [Text t, Command c],
        packings = p, bindings = []}

  fun bind_list (Listbox {bindings, configs, packings, scrolltype, widId}) d = 
        Listbox {bindings = d, configs = configs, packings = packings, scrolltype = scrolltype, widId = widId}
    | bind_list x _ = x

  fun bind_entry (Entry {bindings, configs, packings, widId}) d = 
        Entry {bindings = d, configs = configs, packings = packings, widId = widId}
    | bind_entry x _ = x

  fun copenWindow wid win = if occursWin wid then () else openWindow win

  (* --- *)

  fun show_blocks() =
        (clearText mem_blockId;
         app (fn b => insertTextEnd mem_blockId (block_range b)) (patriciaLib.keys (!memory));
         clearText mem_dumpId)

  fun load_load() =
        let val fname = readTextAll load_fnameId
            val offset = case Int.fromString (readTextAll load_offsetId) of SOME n => n | _ => 0
            val start = Arbnum.fromHexString (readTextAll load_startId) handle _ => Arbnum.zero
        in
           (load_data (if fname = "" then EXC_HANDLER else fname) offset start;
            closeWindow load_winId; show_blocks())
        end
  (* add handle for failing to open file *)
 
  local fun bind x = bind_entry x ([BindEv(KeyPress "Return", fn _ => load_load())]) in
    val load_fname = simple_frame [Side Top] (Pack [simple_label ("file name [default \"" ^ EXC_HANDLER ^ "\"]:"),
                      bind (simple_entry load_fnameId)])
    val load_offset = simple_frame [Side Top] (Pack [simple_label "offset (bytes) [default 0]:",
                      bind (simple_entry load_offsetId)])
    val load_start = simple_frame [Side Top] (Pack [simple_label "start address [default 0]:",
                      bind (simple_entry load_startId)])
  end

  val load_buttons = simple_frame [Side Bottom]
                      (Pack [simple_button [Side Left]  "cancel" (fn _ => closeWindow load_winId),
                             simple_button [Side Right] "load" load_load])

  val load_win = mkWindow {
    winId    = load_winId,
    config   = [WinTitle "load block"],
    widgets  = Pack [load_fname,load_offset,load_start,load_buttons],
    bindings = [],
    init     = noAction}

  (* --- *)

  fun save_save() =
        let val fname = readTextAll save_fnameId
            val start = Arbnum.fromHexString (readTextAll save_startId) handle _ => Arbnum.zero
            val finish = Arbnum.fromHexString (readTextAll save_finishId) handle _ => Arbnum.zero
        in
           (save_data fname start finish ((readVarValue "LE") = "1"); closeWindow save_winId)
        end
  (* add handle for failing to open file *)

  local fun bind x = bind_entry x ([BindEv(KeyPress "Return", fn _ => save_save())]) in
    val save_fname =
      simple_frame [Side Top] (Pack [simple_label "file name:", bind (simple_entry save_fnameId)])
    val save_start =
      simple_frame [Side Top] (Pack [simple_label "first address:", bind (simple_entry save_startId)])
    val save_finish =
      simple_frame [Side Top] (Pack [simple_label "last address:", bind (simple_entry save_finishId)])
  end

  fun save_le b _ = setVarValue "LE" (if b then "1" else "0")

  val save_ends = simple_frame [Side Top] (Pack [
        Radiobutton {widId = newWidgetId(), bindings = [], packings = [Side Top],
                     configs = [Text "little endian",Variable "LE", Value "1",
                                Command(save_le true)]},
        Radiobutton {widId = newWidgetId(), bindings = [], packings = [Side Top],
                     configs = [Text "big endian",Variable "LE", Value "0",
                                Command(save_le false)]}])

  val save_buttons = simple_frame [Side Bottom]
                      (Pack [simple_button [Side Left]  "cancel" (fn _ => closeWindow save_winId),
                             simple_button [Side Right] "save" save_save])

  val save_win = mkWindow {
    winId    = save_winId,
    config   = [WinTitle "save block"],
    widgets  = Pack [save_fname,save_start,save_finish,save_ends,save_buttons],
    bindings = [],
    init     = save_le false}

  (* --- *)

  local
    fun projMark (Mark(x,_)) = x
      | projMark (MarkToEnd x) = x
      | projMark MarkEnd = 0
    fun delete_block n = memory := patriciaLib.remove n (!memory)
    fun nth_key n = List.nth(patriciaLib.keys (!memory),n)
    fun nth_block n = valOf (patriciaLib.member (nth_key n) (!memory))
  in
    fun view_block() =
        (clearText mem_dumpId;
         if readSelWindow() = SOME (mem_winId,mem_blockId) then
            let val a = nth_block (projMark (readCursor mem_blockId))
                val n = block_start (#key a)
                val d = #data a
            in
              (Array.foldl (fn (a,l) => (insertTextEnd mem_dumpId ((line_string l a)); plus4 l)) n d;())
            end
          else ())

    fun wipe_block() =
         ((if readSelWindow() = SOME (mem_winId,mem_blockId) then
             let val n = projMark (readCursor mem_blockId) in
               delete_block (nth_key n)
             end
           else ()); show_blocks())
  end

  val delete_button = simple_button [Side Top] "wipe block" wipe_block
  val load_button = simple_button [Side Top] "load" (fn _ => copenWindow load_winId load_win)
  val save_button = simple_button [Side Top] "save" (fn _ => copenWindow save_winId save_win)

  val mem_blocks = simple_frame [Side Left] (
         Pack [simple_frame [Side Top] (Pack [simple_top_label "blocks",
                 bind_list (simple_list (19,10) true mem_blockId)
                           [BindEv(Double(ButtonPress (SOME 1)), fn _ => view_block())]]),
               delete_button,load_button,save_button])

  val mem_content = simple_frame [Side Right]
                     (Pack [simple_top_label "content", simple_list (50,24) true mem_dumpId])

  val mem_win = mkWindow {
    winId    = mem_winId,
    config   = [WinTitle "memory"],
    widgets  = Pack [mem_blocks,mem_content],
    bindings = [],
    init     = show_blocks}

  (* --- *)

  val st_reg = simple_frame [Side Top,Fill X] (Pack [simple_label "registers:", simple_list (50,8) true st_regId])
  val st_psr = simple_frame [Side Top,Fill X] (Pack [simple_label "status:",    simple_list (50,6) false st_psrId])

  val st_opcode    = simple_frame [Side Top,Fill X] (Pack [simple_label "opcode:",    simple_text st_opcId])
  val st_exception = simple_frame [Side Top,Fill X] (Pack [simple_label "exception:", simple_text st_excId])
  val in_opcode    = simple_frame [Side Top,Fill X] (Pack [simple_label "fetch:",     simple_text in_opcId])
  val in_interrupt = simple_frame [Side Top,Fill X] (Pack [simple_label "interrupt:", simple_text in_intId])
  val in_din       = simple_frame [Side Top,Fill X] (Pack [simple_label "data-in:",   simple_text in_dinId])
  val dout         = simple_frame [Side Top,Fill X] (Pack [simple_label "data-out:",  simple_text doutId])

  fun show_registers (l,r) =
        let val ks = patriciaLib.keys r
            val lks = length ks
        in
          (clearText st_regId;
           app (fn i => insertTextEnd st_regId
                  ((word2reg_string i) ^ ": " ^ (term_to_string (#data (valOf (patriciaLib.member i r)))))) ks;
           if lks < 31 then
             insertTextEnd st_regId ((if (lks = 0) then "all: " else "rest: ") ^
                                     (term_to_string (if is_abs l then (snd o dest_abs) l else l)))
           else ())
        end

  fun show_psrs psrs =
        (clearText st_psrId;
         let fun f n = (disassemblerLib.psr_string o eval_word) (Array.sub(psrs,n)) in
           app (insertTextEnd st_psrId)
             ["    CPSR: " ^ (f 0),
              "SPSR_fiq: " ^ (f 1),
              "SPSR_irq: " ^ (f 2),
              "SPSR_svc: " ^ (f 3),
              "SPSR_abt: " ^ (f 4),
              "SPSR_und: " ^ (f 5)]
         end)

  fun show_time n =
     let val ((s,out),i) = List.nth(!the_trace,n)
         val irpt = List.nth(i,0)
         val ftch = List.nth(i,1)
         val din  = List.nth(i,2)
         fun write_text wid s = (setTextWidReadOnly wid false; clearText wid;
                                 insertTextEnd wid s; setTextWidReadOnly wid true)
         fun write_opcode x = disassemblerLib.opcode_string (eval_word x) handle HOL_ERR _ => term_to_string x
     in
       (write_text st_opcId (write_opcode (#ireg s));
        write_text st_excId (term_to_string (#exc s));
        write_text in_intId (term_to_string irpt);
        write_text in_opcId (write_opcode ftch);
        write_text in_dinId (term_to_string din);
        write_text doutId (term_to_string out);
        show_registers (#registers s);
        show_psrs (#psrs s))
     end

  val trace_scale = ScaleWid {widId = timeId, packings = [], bindings  = [],
        configs = [Orient Horizontal,SLabel "cycle", From 0.0, To 0.0,
                   Resolution 1.0,ShowValue true,SCommand (show_time o Real.trunc)]}

  fun trace_to n = addConf timeId [To (Real.fromInt n)]

  val trace_win = mkWindow {
    winId    = trace_winId,
    config   = [WinTitle "trace"],
    widgets  = Pack [st_opcode,st_exception,st_reg,st_psr,in_opcode,in_interrupt,in_din,dout,trace_scale],
    bindings = [],
    init     = (fn () => (app (fn x => setTextWidReadOnly x true)
                            [st_opcId,st_excId,in_opcId,in_intId,in_dinId,doutId]))}

  (* --- *)

  (* Constructs and SUBST term *)
  fun mk_subst m a b =
        let val ta = type_of a and tb = type_of b in
          subst [``a : ^(ty_antiq ta)`` |-> a,
                 ``b : ^(ty_antiq tb)`` |-> b,
                 ``m : ^(ty_antiq ((ta --> tb)))`` |-> m]
          ``SUBST m (a:^(ty_antiq ta)) (b:^(ty_antiq tb))``
        end

  (* Constructs the exception term *)
  fun mk_exc e = case e of
      reset     => ``reset``
    | undefined => ``undefined``
    | software  => ``software``
    | pabort    => ``pabort``
    | dabort    => ``dabort``
    | interrupt => ``interrupt``
    | fast      => ``fast``

  (* mk_psrs takes and array of PSR values and constructs a PSR term. *)
  local
    fun is_nzcv_clear (a:psr) = not (#n a orelse #z a orelse #c a orelse #v a)
    fun is_ifmode_clear (a:psr) = not (#i a orelse #f a) andalso #mode a = usr
    val clear_psr = ``SET_IFMODE F F usr 0w``

    fun mk_bool b = if b then boolSyntax.T else boolSyntax.F

    fun mk_mode m = case m of
        usr => ``usr``
      | fiq => ``fiq``
      | irq => ``irq``
      | svc => ``svc``
      | abt => ``abt``
      | und => ``und``

    fun num2psr m = case m of
        5 => ``CPSR``
      | 4 => ``SPSR_fiq``
      | 3 => ``SPSR_irq``
      | 2 => ``SPSR_svc``
      | 1 => ``SPSR_abt``
      | _ => ``SPSR_und``

    fun mk_set_ifmode i f m n =
          foldl (fn (a,t) => mk_comb(t,a)) ``SET_IFMODE`` [mk_bool i,mk_bool f,mk_mode m,n]

    fun mk_set_nzcv n z c v t =
          subst [``n:bool`` |-> mk_bool n,``z:bool`` |-> mk_bool z, ``t:word32`` |-> t,
                 ``c:bool`` |-> mk_bool c,``v:bool`` |-> mk_bool v] ``SET_NZCV (n,z,c,v) t``

    fun mk_psr a =
          let val t = mk_set_ifmode (#i a) (#f a) (#mode a) ``0w``
          in
            if is_nzcv_clear a then t else mk_set_nzcv (#n a) (#z a) (#c a) (#v a) t
          end

    fun add_psr (n,a,t) =
          if is_nzcv_clear a andalso is_ifmode_clear a then
            t
          else
            mk_subst t (num2psr n) (mk_psr a)
  in
    fun mk_psrs a = Array.foldli add_psr ``\(x:psrs). ^(clear_psr)`` (a,0,NONE)
  end

  fun b2string b = if b then "1" else "0"

  fun mode2num m =
    case m of
      usr => 5
    | fiq => 4
    | irq => 3
    | svc => 2
    | abt => 1
    | und => 0

  fun mode_name m =
    case m of
      usr => "usr"
    | fiq => "fiq"
    | irq => "irq"
    | svc => "svc"
    | abt => "abt"
    | und => "und"

  fun exc_name e =
    case e of
      reset     => "reset"
    | undefined => "undefined instruction"
    | software  => "no excpetion or SWI"
    | pabort    => "pre-fetch abort"
    | dabort    => "data abort"
    | interrupt => "normal interrupt"
    | fast      => "fast interrupt"

  fun ex_reg_index m i =
    case m of
      usr => i
    | fiq => i + 7
    | irq => i + 14
    | svc => i + 16
    | abt => i + 18
    | und => i + 20

  local
    fun num2reg n = case n of
       0 => ``r0``
     | 1 => ``r1``
     | 2 => ``r2``
     | 3 => ``r3``
     | 4 => ``r4``
     | 5 => ``r5``
     | 6 => ``r6``
     | 7 => ``r7``
     | 8 => ``r15``
     | 9 => ``r8``
     | 10 => ``r9``
     | 11 => ``r10``
     | 12 => ``r11``
     | 13 => ``r12``
     | 14 => ``r13``
     | 15 => ``r14``
     | 16 => ``r8_fiq``
     | 17 => ``r9_fiq``
     | 18 => ``r10_fiq``
     | 19 => ``r11_fiq``
     | 20 => ``r12_fiq``
     | 21 => ``r13_fiq``
     | 22 => ``r14_fiq``
     | 23 => ``r13_irq``
     | 24 => ``r14_irq``
     | 25 => ``r13_svc``
     | 26 => ``r14_svc``
     | 27 => ``r13_abt``
     | 28 => ``r14_abt``
     | 29 => ``r13_und``
     | 30 => ``r14_und``
     | _ => ``ARB:register``

    fun add_reg (i,s,t) =
          if s = "" then t
          else
            mk_subst t (num2reg i) (((mk_word32 o Arbnum.fromString) s) handle e => ``ARB:word32``)
    (* inst [alpha |-> ``:word32``] (Term ([QUOTE s]))) *)

    fun read_regid (i,regid,t) = (i,readTextAll regid,t)
    fun read_ex_reg (i,s,t) = (i + 9,s,t)
  in
    fun mk_reg r = add_reg (8,readTextAll (Array.sub(r,15)),
           Array.foldli (add_reg o read_ex_reg)
             (Array.foldli (add_reg o read_regid) ``(\x. 0w):register->word32`` (r,0,SOME 8)) (ex_regs,0,SOME 21))
  end

  fun mk_init_state() =
        (subst [``reg:register -> word32`` |-> mk_reg regId,
           ``psrs:psrs -> word32`` |-> mk_psrs psr,
           ``exc:exception`` |-> mk_exc (!exc)]
           ``ARM_EX (ARM reg psrs) ireg exc``)

  fun write_top_regs() =
        let fun upd_fiq_reg i =
              let val t = readTextAll (Array.sub(regId,i))
                  val i2 = ex_reg_index (if ((!mode) = fiq) then fiq else usr) (i - 8)
              in
                Array.update(ex_regs,i2,t)
              end
            fun upd_reg i =
              let val t = readTextAll (Array.sub(regId,i))
                  val i2 = ex_reg_index (!mode) (if ((!mode) = usr) orelse ((!mode) = fiq) then i - 8 else i - 13)
              in
                Array.update(ex_regs,i2,t)
              end
        in
          (for_se 8 12 upd_fiq_reg;
           for_se 13 14 upd_reg)
        end

  (* set_mode is called when the user chooses to enter/display a different
     ARM operating mode - it changes the banked registers and PSR value. *)
  local
    (* used in debugging:
    fun print_ex_reg() =
        Array.appi (fn (i,t) => printn ((Int.toString i) ^ ": " ^ t)) (ex_regs,0,NONE); *)

    fun read_top_regs() =
        let fun read_fiq_reg i =
              Array.sub(ex_regs,ex_reg_index (if ((!mode) = fiq) then fiq else usr) (i - 8))
            fun read_reg i =
              Array.sub(ex_regs,ex_reg_index (!mode)
                (if ((!mode) = usr) orelse ((!mode) = fiq) then i - 8 else i - 13))
            fun read_reg_ex f i = let val regid = Array.sub(regId,i) in
                (clearText regid; insertTextEnd regid (f i))
              end
        in
          (for_se 8 12 (read_reg_ex read_fiq_reg);
           for_se 13 14 (read_reg_ex read_reg))
        end

  in
    fun set_mode m _ = (
        let val c1 = if m = fiq then Red else Black
            val c2 = if m = usr then Black else Red in
          for_se 0 4 (fn i => addConf (Array.sub(reg_nameId,i)) [Foreground c1]);
          for_se 5 6 (fn i => addConf (Array.sub(reg_nameId,i)) [Foreground c2])
        end;
        write_top_regs();
        mode := m;
        read_top_regs(); (* print_ex_reg(); *)
        addConf modeId [Text (mode_name m)];
        addConf psr_nameId [Text (if m = usr then "cpsr:" else "spsr:")];
        let val x = Array.sub(psr,mode2num m) in
          (setVarValue "N" (b2string (#n x));
           setVarValue "Z" (b2string (#z x));
           setVarValue "C" (b2string (#c x));
           setVarValue "V" (b2string (#v x));
           setVarValue "I" (b2string (#i x));
           setVarValue "F" (b2string (#f x));
           addConf psrId [Text (mode_name (#mode x))])
        end
        )
  end

  (* called when the NZCVIF flags are updated *)
  fun set_psr _ =
        let val x = Array.sub(psr,mode2num (!mode)) in
          Array.update(psr,mode2num (!mode),
            let val n = (readVarValue "N") = "1";
                val z = (readVarValue "Z") = "1"
                val c = (readVarValue "C") = "1"
                val v = (readVarValue "V") = "1"
                val i = (readVarValue "I") = "1"
                val f = (readVarValue "F") = "1"
            in
              {n = n, z = z, c = c, v = v, i = i, f = f, mode = #mode x}
            end)
        end

  (* called when the MODE of the PSR is updated *)
  fun set_psr_mode m _ =
        let val x = Array.sub(psr,mode2num (!mode))
            val _ = Array.update(psr,mode2num (!mode),
                      {n = #n x, z = #z x, c = #c x, v = #v x, i = #i x, f = #f x, mode = m})
        in addConf psrId [Text (mode_name m)] end

  val psr_label = Label {
        widId = psr_nameId, packings = [Row 1, Column 1], bindings = [], configs = [Text "cpsr:"]}

  fun register_string n =
    case n of
      13 => " sp"
    | 14 => " lr"
    | 15 => " pc"
    | _  => (if n < 10 then " r" else "r") ^ int_to_string n;

  fun reg_label wid n = simple_tt_label wid (register_string n);
  fun reg_entry n = simple_entry (Array.sub(regId,n))

  fun mode_popup wid act = Menubutton {
        widId = wid, configs = [Font (Typewriter []), Relief Raised, Tearoff false, Text (mode_name (!mode))],
        packings = [Side Right, Row 1, Column 8], bindings = [],
        mitems = map (fn m => MCommand [Font (Typewriter []), Text (mode_name m),Command (act m)])
                  [usr, fiq, irq, svc, abt, und]}

  (* called when the exception is updated *)
  fun set_exc e _ = (exc := e; addConf excId [Text (exc_name e)])

  val exc_popup = simple_frame [Row 4,PadY 2]
        (Pack [simple_label "exception:",
          Menubutton {
            widId = excId, packings = [Side Right], bindings = [],
            configs = [Width 21, Font (Typewriter []), Relief Raised,
                       Tearoff false, Text (exc_name (!exc))],
            mitems = map (fn e => MCommand [Font (Typewriter []), Text (exc_name e),Command (set_exc e)])
                      [reset, undefined, software, pabort, dabort, interrupt, fast]}])

  fun TF_picker l act c =
        Checkbutton {
            widId = newWidgetId(), packings = [Row 1,Column c], bindings = [],
            configs = [Text l,Font (Typewriter []), Command act, Variable l]};

  val psr_picker = simple_frame [Row 3]
        (Grid ([psr_label] @
               (map (fn (s,n) => TF_picker s set_psr (n + 2))
                     [("N",0), ("Z",1), ("C",2), ("V",3), ("I",4), ("F",5)]) @ [mode_popup psrId set_psr_mode]))

  (* Registers r0-r7 are the same for all modes *)
  val bot_registers = simple_frame [Side Left]
         (Pack (List.tabulate(8,fn i => simple_frame [Side Top] (Pack [reg_label (newWidgetId()) i,reg_entry i]))))

  (* Registers r8-r14 are mode dependent; r15 (i = 7) is the same for all modes.  *)
  val top_registers = simple_frame [Side Right]
         (Pack (List.tabulate(7,fn i => simple_frame [Side Top]
                             (Pack [reg_label (Array.sub(reg_nameId,i)) (i + 8), reg_entry (i + 8)])) @
                [simple_frame [Side Top] (Pack [reg_label (newWidgetId()) 15,reg_entry 15])]))

  val reg_frame = simple_frame [Row 2] (Pack [bot_registers,top_registers])
  val mode_frame = simple_frame [Row 1, PadY 2] (Pack [simple_label "mode:",mode_popup modeId set_mode])

 (* val int_frame = simple_frame [Row 5, PadY 2]
        (Pack [simple_label "interrupt at time t:", simple_entry intId]) *)

  fun execute _ = (write_top_regs();
                   let val n =
                         case Int.fromString (readTextAll maxcId) of
                           NONE => valOf Int.maxInt
                         | SOME x => x
                       val i = mk_init_state()
                    (* val _ = (print_term i; print "\n"; printn (Int.toString n)) *)
                       val _ = the_thm_trace := state n i
                   in
                     the_trace := read_trace (!the_thm_trace)
                   end;
                   show_blocks();
                   copenWindow trace_winId trace_win;
                   trace_to (length (!the_trace) - 1))

  val maxc_frame = simple_frame [Row 6, PadY 2]
        (Pack [simple_label "no. of cycles:",
               bind_entry (simple_entry maxcId) [BindEv(KeyPress "Return", execute)]])

  val go_button = simple_button [Row 7, PadY 5] "execute" execute;

  val win = mkWindow {
    winId    = newWinId(),
    config   = [WinTitle "HOL simulator for the ARM ISA"],
    widgets  = Grid [reg_frame,psr_picker,mode_frame,exc_popup,maxc_frame,go_button],
    bindings = [],
    init     = reset_all}
in
  fun go() = (init();startTcl [win,mem_win]; the_thm_trace)
end

(* -------------------------------------------------------- *)

val _ = export_theory();
