(* app load ["metisLib","listLib","compLib","io_onestepTheory",
             "armLib","coreLib","disassemblerLib","patriciaLib"]; *)
open HolKernel boolLib bossLib Parse Q;

(* -------------------------------------------------------- *)

val _ = new_theory "test";

val _ = numLib.prefer_num();

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

val prog_block = Array.array(block_size,Arbnum.zero);

val memory = ref (patriciaLib.add {data = prog_block, key = 0w0} patriciaLib.empty);

local
  open Arbnum
in
  val n4 = fromInt 4
  val n7 = fromInt 7
  val n8 = fromInt 8
  val n31 = fromInt 31
  val n32 = fromInt 32
  val block_size_num = fromInt block_size

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
fun toHexString8 n = let val x = Arbnum.toHexString n in nzeros_string (8 - size x) ^ x end;

fun print_word n =
  print (toHexString8 n ^ "; " ^ (disassemblerLib.opcode_string n) ^ "\n");

fun print_line l n = (print (toHexString8 l ^ ": ");print_word n);

fun print_block (b:{data : num array, key : word},i,x) =
  let val n = Arbnum.*(block_size_num,Arbnum.*(word2num (#key b),n4))
      val _ =
    ((Vector.foldl (fn (a,l) => (print_line l a; plus4 l)) n) o Array.extract) (#data b,i,x)
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
        | SOME byt =>
            let val a = Arbnum.*(align,n8) in
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

fun eval_word t = (numSyntax.dest_numeral o rhsc o word32Lib.WORD_CONV) (mk_comb (``w2n``,t));
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

fun read_input t =
  let fun recurse t a =
        if is_cond t then
          let val (c,t1,t2) = dest_cond t in
            recurse t2 (t1::a)
          end
        else a
  in
    recurse (snd (dest_abs t)) []
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

  val read_registers = recurse2 patriciaLib.empty
  val read_psrs = recurse3 (Array.array(length psrs,NONE: term option))

  fun regVal (x,ptree) n =
    let val y = patriciaLib.member (Word.fromInt n) ptree in
      if isSome y then
        #data (valOf y)
      else
        (rhsc o SIMARM_CONV o mk_comb) (x,List.nth(register,n))
  end
in
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

  fun state_val (x: {exc : term, ireg : term, psrs : term array, registers : term * term patriciaLib.ptree}) c =
    case c of
      Ireg => #ireg x
    | Exc => #exc x
    | PSR n => Array.sub(#psrs x,n)
    | Register n => regVal (#registers x) n
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

val _ = Array.copy {si = 0, len = NONE, dst = prog_block, di = 0,
 src = Array.fromList
   (map Arbnum.fromHexString [ 
"E3B0F020",
"E1B0F00E",
"E1B0F00E",
"E25EF004",
"E25EF008",
"E1B0F00E",
"E25EF004",
"E25EF004",
"E3B0020F"
])};

(* -------------------------------------------------------- *)

val _ = word32Lib.pp_word_unsigned_hex();
(*
val _ = npp_word_arm_ex();
val _ = npp_word_arm();
val _ = npp_word_pipe();
val _ = npp_word_psr();
*)

val RESET_PSR_def = Define`
  RESET_PSR = CPSR_WRITE (SPSR_WRITE ARB svc (SET_NZCV (F,F,F,F) (SET_IFMODE F F usr 0w)))
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

val s0 =
   (subst [``reg:register -> word32`` |-> ``ARB {. r15 <- 0x0w .}``,
           ``psrs:psrs -> word32`` |-> rhsc RESET_PSR]
     ``ARM_EX (ARM reg psrs) ireg software``);

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

val s1 = next_state (#state (init_state s0));
val s = state 2 s0;
val i = (read_input o get_input o hd) s;

val states = map (read_state o get_state) s;

(* -------------------------------------------------------- *)

val k = patriciaLib.keys (!memory);
val SOME mb = patriciaLib.member 0wx0 (!memory);
(* val SOME db = patriciaLib.member 0wx2 (!memory); *)
(* val _ = print_block(db,0,NONE); *)
(* val _ = print_block(db,0,SOME 10); *)
val _ = print_block(mb,0,SOME 14);
(* val _ = Array.copy {si = 0, len = NONE, dst = #data db, di = 0, src = Array.array(block_size,Arbnum.zero)}; *)
(* val _ = Array.copy {si = 0, len = NONE, dst = #data mb, di = 0, src = Array.array(block_size,Arbnum.zero)}; *)

(* -------------------------------------------------------- *)

val concat = String.concat;
val _ = use "root_mosml.sml";
val _ = SmlTk.init();

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

  fun mk_subst m a b =
        let val ta = type_of a and tb = type_of b in
          subst [``a : ^(ty_antiq ta)`` |-> a,
                 ``b : ^(ty_antiq tb)`` |-> b,
                 ``m : ^(ty_antiq ((ta --> tb)))`` |-> m]
          ``SUBST m (a:^(ty_antiq ta)) (b:^(ty_antiq tb))``
        end

  fun mk_exc e = case e of
      reset     => ``reset``
    | undefined => ``reset``
    | software  => ``software``
    | pabort    => ``pabort``
    | dabort    => ``dabort``
    | interrupt => ``interrupt``
    | fast      => ``fast``

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

  fun print_ex_reg() =
        Array.appi (fn (i,t) => print ((Int.toString i) ^ ": " ^ t ^ "\n")) (ex_regs,0,NONE);

  fun swp_reg b regid m1 m2 i =
        let val i1 = if b orelse (m1 = usr) orelse (m1 = fiq) then i else i - 5
            val j1 = ex_reg_index (if b andalso not (m1 = fiq) then usr else m1) i1
            val i2 = if b orelse (m2 = usr) orelse (m2 = fiq) then i else i - 5
            val j2 = ex_reg_index (if b andalso not (m2 = fiq) then usr else m2) i2
            val t1 = readTextAll regid
            val t2 = Array.sub(ex_regs,j2)
            val _ = Array.update(ex_regs,j1,t1)
        in
           (clearText regid; insertTextEnd regid t2)
        end

  fun set_mode m _ = (
        let val c1 = if m = fiq then Red else Black
            val c2 = if m = usr then Black else Red in
          for_se 0 4 (fn i => addConf (Array.sub(reg_nameId,i)) [Foreground c1]);
          for_se 5 6 (fn i => addConf (Array.sub(reg_nameId,i)) [Foreground c2])
        end;
        for_se 0 4 (fn i => swp_reg true (Array.sub(regId,i + 8)) (!mode) m i);
        for_se 5 6 (fn i => swp_reg false (Array.sub(regId,i + 8)) (!mode) m i);
   (*     print_ex_reg(); *)
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
        end;
        mode := m
        )

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

  fun set_exc e _ = (exc := e; addConf excId [Text (exc_name e)])

  fun set_psr_mode m _ =
        let val x = Array.sub(psr,mode2num (!mode))
            val _ = Array.update(psr,mode2num (!mode),
                      {n = #n x, z = #z x, c = #c x, v = #v x, i = #i x, f = #f x, mode = m})
        in addConf psrId [Text (mode_name m)] end

  val psr_label = Label {
        widId = psr_nameId, packings = [Row 1, Column 1], bindings = [], configs = [Text "cpsr:"]}

  fun reg_label wid n = Label {
        widId = wid, packings = [Side Left], bindings = [],
        configs = [Text ("r" ^ Int.toString n ^ (if n < 10 then " " else "")),
                   Font (Typewriter []),Foreground Black]}

  fun reg n = Entry {
        widId = Array.sub(regId,n), packings = [Side Right],
        configs = [], bindings = []}

  val mode_label = Label {
        widId = newWidgetId(), packings = [Side Left],
        configs = [Text "mode:"], bindings = []}

  fun mode_popup wid act = Menubutton {
        widId = wid, configs = [Font (Typewriter []), Relief Raised, Tearoff false, Text (mode_name (!mode))],
        packings = [Side Right, Row 1, Column 8], bindings = [],
        mitems = map (fn m => MCommand [Font (Typewriter []), Text (mode_name m),Command (act m)])
                  [usr, fiq, irq, svc, abt, und]}

  val exc_popup = Frame {
        widId = newWidgetId(), configs = [], bindings = [], packings = [Row 4,PadY 2],
        widgets = Pack [
          Label {
            widId = newWidgetId(), packings = [Side Left], bindings = [],
            configs = [Text "exception:"]},
          Menubutton {
            widId = excId, packings = [Side Right], bindings = [],
            configs = [Width 21, Font (Typewriter []), Relief Raised,
                       Tearoff false, Text (exc_name (!exc))],
            mitems = map (fn e => MCommand [Font (Typewriter []), Text (exc_name e),Command (set_exc e)])
                      [reset, undefined, software, pabort, dabort, interrupt, fast]}]}

  fun TF_picker l act c = 
        Checkbutton {
            widId = newWidgetId(), packings = [Row 1,Column c], bindings = [],
            configs = [Text l,Font (Typewriter []), Command act, Variable l]};

  val psr_picker = Frame {
        widId = newWidgetId(), packings = [Row 3], configs = [], bindings = [],
        widgets = Grid ([psr_label] @
                        (map (fn (s,n) => TF_picker s set_psr (n + 2))
                          [("N",0), ("Z",1), ("C",2), ("V",3), ("I",4), ("F",5)]) @
                        [mode_popup psrId set_psr_mode])}

  val bot_registers = Frame {
         widId = newWidgetId(),
         widgets = Pack (List.tabulate(8,fn i => Frame {
                           widId = newWidgetId(), packings = [Side Top], configs = [], bindings = [],
                           widgets = Pack [reg_label (newWidgetId()) i,reg i]})),
         packings = [Side Left], configs = [],  bindings = []}

  val top_registers = Frame {
         widId = newWidgetId(), 
         widgets = Pack (List.tabulate(8,fn i => Frame {
                           widId = newWidgetId(),
                           packings = [Side Top], configs = [], bindings = [],
                           widgets = Pack
                            [reg_label (if i = 7 then newWidgetId() else Array.sub(reg_nameId,i)) (i + 8),
                             reg (i + 8)]})),
         packings = [Side Right], configs = [],  bindings = []}

  val reg_frame = Frame {
        widId = newWidgetId(), widgets = Pack [bot_registers,top_registers],
        packings = [Row 2], configs = [],  bindings = []}

  val mode_frame = Frame {
        widId = newWidgetId(), widgets = Pack [mode_label,mode_popup modeId set_mode],
        packings = [Row 1, PadY 2], configs = [],  bindings = []}

  val int_frame = Frame {
        widId = newWidgetId(), packings = [Row 5, PadY 2], configs = [],  bindings = [],
        widgets = Pack [Label {
                          widId = newWidgetId(), packings = [Side Left],
                          configs = [Text "interrupt at time t:"], bindings = []},
                        Entry {
                          widId = intId, packings = [Side Right],
                          configs = [], bindings = []}]}

  val maxc_frame = Frame {
        widId = newWidgetId(), packings = [Row 6, PadY 2], configs = [Relief Groove],  bindings = [],
        widgets = Pack [Label {
                          widId = newWidgetId(), packings = [Side Left],
                          configs = [Text "max cycles:"], bindings = []},
                        Entry {
                          widId = maxcId, packings = [Side Right],
                          configs = [], bindings = []}]}

  val go_button = Button {
        widId = newWidgetId(), configs = [Text "execute"], packings = [Row 7, PadY 5], bindings = []}

  val win = mkWindow {
    winId    = newWinId(),
    config   = [WinTitle "HOL simulator for the ARM ISA"],
    widgets  = Grid [reg_frame,psr_picker,mode_frame,exc_popup,int_frame,maxc_frame,go_button],
    bindings = [],
    init     = noAction}

  fun reset_all() =
        let val _ = Array.modify (fn _ => "") ex_regs
            val _ = Array.modify (fn _ => {n = false, z = false, c = false, v = false,
                                           i = false, f = false, mode = usr}) psr
            val _ = mode := usr
            val _ = exc  := software
        in
          init()
        end

  val go = (reset_all(); startTcl [win]; mode)

(* -------------------------------------------------------- *)

val _ = export_theory();
