structure disassemblerLib :> disassemblerLib =
struct

(* app load ["armTheory","coreTheory"]; *)

open HolKernel boolLib;

(* ------------------------------------------------------------------------- *)

datatype shiftmode = Immediate of num |
                     Immediate_shift of {Imm : int, Rm : int, Sh : string} |
                     Register_shift of {Rm : int, Rs : int, Sh : string};

datatype iclass = swp | mrs | msr | Data_proc of shiftmode | mla_mul |
                  ldr_str | ldm_stm | br | swi_ex | cdp | undef |
                  mcr_mrc | ldc_stc;

(* ------------------------------------------------------------------------- *)

val toUpperString = I;
(* val toUpperString = String.map Char.toUpper; *)
val max_width = 8;
fun nspaces_string n = funpow n (fn x => x ^ " ") "";
fun mnemonic s = (toUpperString s) ^ (nspaces_string (max_width - size s))

(* ------------------------------------------------------------------------- *)

fun num2list l n =
  if l = 0 then
    []
   else if n = Arbnum.zero then
     List.tabulate(l,fn x => 0)
   else
     (if Arbnum.mod2 n = Arbnum.one then [1] else [0]) @
     (num2list (l - 1) (Arbnum.div2 n));

val numeral2num = (numSyntax.dest_numeral o snd o dest_comb);

local 
  fun llist2num [] n = n
   |  llist2num (x::xs) n = llist2num xs ((if x = 1 then Arbnum.plus1 else I)
                              (Arbnum.times2 n))
in
  fun list2num l = llist2num (rev l) Arbnum.zero
end;

(* ------------------------------------------------------------------------- *)

fun bitsl h l n = List.take(List.drop(n,l),h + 1 - l);
fun bits h l n = (Arbnum.toInt o list2num) (bitsl h l n);
fun bit b n = (bits b b n = 1);

fun Rn l = bits 19 16 l;
fun Rd l = bits 15 12 l;
fun Rs l = bits 11 8 l;
fun Rm l = bits 3 0 l;

(* ------------------------------------------------------------------------- *)

fun decode_shift z l = toUpperString(
  case l of
    [0,0] => "lsl"
  | [0,1] => "lsr"
  | [1,0] => "asr"
  | [1,1] => if z then "rrx" else "ror"
  | _ => raise HOL_ERR { origin_structure = "disassemlerLib",
                         origin_function = "decode_shift",
                         message = "Cannot decode shift." });

val msb32 = Arbnum.pow(Arbnum.two,Arbnum.fromInt 31);
fun smsb b = if b then msb32 else Arbnum.zero;

local
  fun mror32 x n =
    if n = 0 then
      x
    else
      (mror32 (Arbnum.+(Arbnum.div2 x, smsb (Arbnum.mod2 x = Arbnum.one))))
        (n - 1);
in
  fun ror32 x n = mror32 x (n mod 32)
end;

fun decode_immediate l =
  let val rot = bits 11 8 l
      val imm = list2num (bitsl 7 0 l);
  in
    ror32 imm (2 * rot)
  end;

fun decode_immediate_shift l =
  let val imm = bits 11 7 l in
    {Rm = Rm l, Imm = imm, Sh = decode_shift (imm = 0) (bitsl 6 5 l)}
  end;

fun decode_register_shift l =
    {Rm = Rm l, Rs = Rs l, Sh = decode_shift false (bitsl 6 5 l)};

(* ------------------------------------------------------------------------- *)

fun decode_inst l =
  let fun op2 x = rev (List.drop(x,16)) in
  case l of
    [0,0,1,1,0,_,1,0,_,_,_,_,1,1,1,1,_,_,_,_,_,_,_,_,_,_,_,_] => msr 
  | [0,0,0,1,0,_,1,0,_,_,_,_,1,1,1,1,0,0,0,0,0,0,0,0,_,_,_,_] => msr
  | [0,0,0,1,0,_,0,0,1,1,1,1,_,_,_,_,_,0,0,0,0,0,0,0,0,0,0,0] => mrs
  | [0,0,0,0,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,1,0,0,1,_,_,_,_] => mla_mul
  | [0,0,0,1,0,_,0,0,_,_,_,_,_,_,_,_,0,0,0,0,1,0,0,1,_,_,_,_] => swp
  | [0,1,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => ldr_str
  | [0,1,1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,0,_,_,_,_] => ldr_str
  | [1,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => ldm_stm
  | [1,0,1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => br
  | [1,1,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => ldc_stc
  | [1,1,1,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,0,_,_,_,_] => cdp
  | [1,1,1,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,1,_,_,_,_] => mcr_mrc
  | [1,1,1,1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => swi_ex
  | [0,0,1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] =>
       Data_proc (Immediate (decode_immediate (op2 l)))
  | [0,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,0,_,_,_,_] =>
       Data_proc (Immediate_shift (decode_immediate_shift (op2 l)))
  | [0,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,0,_,_,1,_,_,_,_] =>
       Data_proc (Register_shift (decode_register_shift (op2 l)))
  | _ => undef
  end;

fun decode_condition l =
  case l of
    [0,0,0,0] => "eq"
  | [0,0,0,1] => "ne"
  | [0,0,1,0] => "cs"
  | [0,0,1,1] => "cc"
  | [0,1,0,0] => "mi"
  | [0,1,0,1] => "pl"
  | [0,1,1,0] => "vs"
  | [0,1,1,1] => "vc"
  | [1,0,0,0] => "hi"
  | [1,0,0,1] => "ls"
  | [1,0,1,0] => "ge"
  | [1,0,1,1] => "lt"
  | [1,1,0,0] => "gt"
  | [1,1,0,1] => "le"
  | [1,1,1,0] => "" (* al *)
  | _ => "nv";

fun decode_opcode l =
  case l of
    [0,0,0,0] => "and"
  | [0,0,0,1] => "eor"
  | [0,0,1,0] => "sub"
  | [0,0,1,1] => "rsb"
  | [0,1,0,0] => "add"
  | [0,1,0,1] => "adc"
  | [0,1,1,0] => "sbc"
  | [0,1,1,1] => "rsc"
  | [1,0,0,0] => "tst"
  | [1,0,0,1] => "teq"
  | [1,0,1,0] => "cmp"
  | [1,0,1,1] => "cmn"
  | [1,1,0,0] => "orr"
  | [1,1,0,1] => "mov"
  | [1,1,1,0] => "bic"
  | _ => "mvn";

fun decode_address_mode p u =
  case (p,u) of
    (false,false) => "da"
  | (false,true)  => "ia"
  | (true,false)  => "db"
  | (true,true)   => "ib";

fun register_string n =
  case n of
    13 => "sp"
  | 14 => "lr"
  | 15 => "pc"
  | _  => "r" ^ int_to_string n;

fun cp_reg_string n = "C" ^ int_to_string n;
fun cp_string n = "p" ^ int_to_string n;

local
  fun finish i ys = if ys = [] then [(i,i)] else ((fst (hd ys), i)::(tl ys));
  fun blocks [] i ys = ys
    | blocks [x] i ys = if x then finish i ys else ys
    | blocks (x::y::xs) i ys =
    case (x,y) of
      (true,true) => blocks (y::xs) (i + 1) ys
    | (false,true) => blocks (y::xs) (i + 1) ((i + 1,~1)::ys)
    | (true,false) => blocks (y::xs) (i + 1) (finish i ys)
    | (false,false) => blocks (y::xs) (i + 1) ys;
  fun make_blocks l = let val bl = map (fn x => x = 1) l in
      rev (blocks bl 0 (if hd bl then [(0,~1)] else [])) end;
  fun blocks_to_string [] s = s ^ "}"
    | blocks_to_string ((i,j)::xs) s =
        let val comma = (if xs = [] then "" else ", ") in
          blocks_to_string xs (s ^ register_string i ^
            (if i = j then
              ""
             else if i + 1 = j then
              ", " ^ register_string j
             else
              "-" ^ register_string j) ^ comma)
        end;
in
  fun decode_register_list l =
         blocks_to_string (make_blocks (List.take(l,16))) "{"
end;

(* ------------------------------------------------------------------------- *)

fun decode_mode l =
  case l of
    [1,0,0,0,0] => "usr"
  | [1,0,0,0,1] => "fiq"
  | [1,0,0,1,0] => "irq"
  | [1,0,0,1,1] => "svc"
  | [1,0,1,1,1] => "abt"
  | [1,1,0,1,1] => "und"
  | [1,1,1,1,1] => "sys"
  | _ => "safe";

fun decode_psr l =
  {N = bit 31 l, Z = bit 30 l, C = bit 29 l, V = bit 28 l,
   I = bit 7 l, F = bit 6 l, mode = decode_mode (rev (bitsl 4 0 l))};

(* ------------------------------------------------------------------------- *)

fun decode_branch l =
   let val sgn = bit 23 l
       val mag = bits 22 0 l
   in
     {L = bit 24 l, sign = sgn,
      offset = if sgn then abs (~8388608 + mag) else mag}
   end;

fun decode_data_proc l =
  let val opl = rev (bitsl 24 21 l)
      val binop = bit 0 opl andalso not (bit 1 opl)
  in
    {opcode = decode_opcode opl, S = bit 20 l, binop = binop,
     Rn = Rn l, Rd = Rd l}
  end;

fun decode_mrs l = {R = bit 22 l, Rd = Rd l};

fun decode_msr l = {I = bit 25 l, R = bit 22 l, Rm = Rm l};

fun decode_mla_mul l =
  {A = bit 21 l, S = bit 20 l, Rd = Rn l, Rn = Rd l, Rs = Rs l, Rm = Rm l};

fun decode_ldr_str l =
  {I = bit 25 l, P = bit 24 l, U = bit 23 l, B = bit 22 l, W = bit 21 l,
   L = bit 20 l, Rn = Rn l, Rd = Rd l, offset = bitsl 11 0 l};

fun decode_ldm_stm l =
  {P = bit 24 l, U = bit 23 l, S = bit 22 l, W = bit 21 l, L = bit 20 l,
   Rn = Rn l, list = decode_register_list l};

fun decode_swp l = {B = bit 22 l, Rn = Rn l, Rd = Rd l, Rm = Rm l};

fun decode_cdp l =
  {Cop1 = bits 23 20 l, CRn = Rn l, CRd = Rd l, CP = Rs l,
   Cop2 = bits 7 5 l, CRm = Rm l};

fun decode_ldc_stc l =
  {P = bit 24 l, U = bit 23 l, W = bit 21 l, L = bit 20 l, CRd = Rd l,
   Rn = Rn l, CP = Rs l, offset = bits 7 0 l};

fun decode_mcr_mrc l =
  {Cop1 = bits 23 21 l, L = bit 20 l, Rd = Rd l,
   CRn = Rn l, CP = Rs l, CRm = Rm l, Cop2 = bits 7 5 l};

(* ------------------------------------------------------------------------- *)

fun psr_string n =
  let val dl = decode_psr (num2list 32 n) in
    (if #N dl then "N" else "n") ^ (if #Z dl then " Z" else " z") ^
    (if #C dl then " C" else " c") ^ (if #V dl then " V" else " v") ^
    (if #I dl then " I" else " i") ^ (if #F dl then " F" else " f") ^
    " " ^ #mode dl
  end;

(* ------------------------------------------------------------------------- *)

fun shift_immediate_string (y:{Imm : int, Rm : int, Sh : string}) =
  register_string (#Rm y) ^
  (let val imm = #Imm y in
     if imm = 0 then
        toUpperString (if #Sh y = "rrx" then ", rrx" else "")
     else
       ", " ^ (#Sh y) ^ " #" ^ int_to_string imm
   end);

fun branch_string l conds =
  let val dl = decode_branch l
      val h = mnemonic ("b" ^ (if #L dl then "l" else "") ^ conds)
  in
    h ^ (if #sign dl then "#-" else "#") ^ (int_to_string (#offset dl))
  end;

fun data_proc_string l conds x =
  let val dl = decode_data_proc l
      val h = mnemonic ((#opcode dl) ^ conds ^
                (if #S dl andalso not (#binop dl) then "s" else ""))
  in
    h ^ (if #binop dl then "" else register_string (#Rd dl) ^ ", ") ^
      (if #opcode dl = "mov" orelse #opcode dl = "mvn" then ""
       else register_string (#Rn dl) ^ ", ") ^
      (case x of
         Immediate y => "#" ^ Arbnum.toString y
       | Immediate_shift y => shift_immediate_string y
       | Register_shift y => register_string (#Rm y) ^ ", " ^ (#Sh y) ^
                               " " ^ register_string (#Rs y))
  end;

fun mrs_string l conds =
  let val dl = decode_mrs l
      val h = mnemonic ("mrs" ^ conds)
  in
    h ^ register_string (#Rd dl) ^ ", " ^ (if #R dl then "SPSR" else "CPSR")
  end;

fun msr_string l conds =
  let val dl = decode_msr l
      val h = mnemonic ("msr" ^ conds)
  in
    h ^ (if #R dl then "SPSR" else "CPSR") ^
      (if #I dl then "_f, #" ^ Arbnum.toString (decode_immediate l)
       else ", " ^ register_string (#Rm dl))
  end;

fun mla_mul_string l conds =
  let val dl = decode_mla_mul l
      val h = mnemonic ((if #A dl then "MLA" else "MUL") ^ conds ^
                (if #S dl then "S" else ""))
  in
    h ^ register_string (#Rd dl) ^ ", " ^ register_string (#Rm dl) ^ ", " ^
     register_string (#Rs dl) ^
       (if #A dl then ", " ^ register_string (#Rn dl) else "")
  end;

fun ldr_str_string l conds =
  let val dl = decode_ldr_str l
      val offset =
       (if #I dl then
          (if not (#U dl) then "-" else "") ^
             shift_immediate_string (decode_immediate_shift (#offset dl))
        else let val n = list2num (#offset dl) in
          if n = Arbnum.zero then "" else
            (if not (#U dl) then ", #-" else ", #") ^ Arbnum.toString n end)
      val h = mnemonic ((if #L dl then "ldr" else "str") ^ conds ^
                (if #B dl then "b" else ""))
  in
    h ^ register_string (#Rd dl) ^ ", [" ^ register_string (#Rn dl) ^
      (if #P dl then
          offset ^ "]" ^ (if #W dl then "!" else "")
       else "]" ^ offset)
  end;

fun ldm_stm_string l conds =
  let val dl = decode_ldm_stm l
      val h = mnemonic ((if #L dl then "ldm" else "stm") ^ conds ^
                decode_address_mode (#P dl) (#U dl))
  in
    h ^ register_string (#Rn dl) ^ (if #W dl then "!, " else ", ") ^
     #list dl ^ (if #S dl then "^" else "")
  end;

fun swp_string l conds =
  let val dl = decode_swp l
      val h = mnemonic ("swp" ^ conds ^ (if #B dl then "B" else ""))
  in
    h ^ register_string (#Rd dl) ^ ", " ^ register_string (#Rm dl) ^ ", [" ^
      register_string (#Rn dl) ^ "]"
  end;

fun swi_ex_string conds = mnemonic ("swi" ^ conds);

fun cdp_string l conds = let
  val dl = decode_cdp l
  val h = mnemonic ("cdp" ^ conds)
  val op2 = #Cop2 dl
in
    h ^ cp_string (#CP dl) ^ ", " ^ int_to_string (#Cop1 dl) ^ ", " ^
     cp_reg_string (#CRd dl) ^ ", " ^ cp_reg_string (#CRn dl) ^ ", " ^
     cp_reg_string (#CRm dl) ^
     (if op2 = 0 then "" else ", " ^ int_to_string (#Cop2 dl))
end;

fun ldc_stc_string l conds = let
  val dl = decode_ldc_stc l
  val h = mnemonic ((if #L dl then "ldc" else "stc") ^ conds)
  val n = #offset dl
  val offset = if n = 0 then "" else
                (if not (#U dl) then ", #-" else ", #")  ^ int_to_string n
in
    h ^ cp_string (#CP dl) ^ ", " ^ cp_reg_string (#CRd dl) ^
      ", [" ^ register_string (#Rn dl) ^
      (if #P dl then
          offset ^ "]" ^ (if #W dl then "!" else "")
       else "]" ^ offset)
end;

fun mcr_mrc_string l conds = let
  val dl = decode_mcr_mrc l
  val h = mnemonic ((if #L dl then "mrc" else "mcr") ^ conds)
  val op2 = #Cop2 dl
in
    h ^ cp_string (#CP dl) ^ ", " ^ int_to_string (#Cop1 dl) ^ ", " ^
     register_string (#Rd dl) ^ ", " ^ cp_reg_string (#CRn dl) ^ ", " ^
     cp_reg_string (#CRm dl) ^
     (if op2 = 0 then "" else ", " ^ int_to_string (#Cop2 dl))
end;

(* ------------------------------------------------------------------------- *)

fun opcode_string n =
  let val xl = num2list 32 n
      val l = List.take(xl,28)
      val iclass = decode_inst (rev l)
      val conds = decode_condition (rev (List.drop(xl,28)))
  in
    if iclass = undef then "undefined"
    else case iclass of
           br          => branch_string l conds
         | mrs         => mrs_string l conds
         | msr         => msr_string l conds
         | Data_proc x => data_proc_string l conds x
         | mla_mul     => mla_mul_string l conds
         | ldr_str     => ldr_str_string l conds
         | ldm_stm     => ldm_stm_string l conds
         | swp         => swp_string l conds
         | cdp         => cdp_string l conds
         | ldc_stc     => ldc_stc_string l conds
         | mcr_mrc     => mcr_mrc_string l conds
         | swi_ex      => swi_ex_string conds
         | _ => raise term_pp_types.UserPP_Failed
  end;

fun is_coproc n =
  let val xl = num2list 32 n
      val l = List.take(xl,28)
      val iclass = decode_inst (rev l)
  in
    mem iclass [cdp, undef, mcr_mrc, ldc_stc]
  end

(* ------------------------------------------------------------------------- *)

val comb_prec = 20;

open Portable term_pp_types;

fun add_comment pps sl =
  (begin_block pps INCONSISTENT 2;
   add_break pps (1,0);add_string pps "(*";
   foldl (fn (s,x) => (add_break pps (1,0); add_string pps s)) () sl;
   add_break pps (1,0);add_string pps "*)";
   end_block pps);
  
fun word_print f sys (pgrav, lgrav, rgrav) d pps t =
  let val sl = f t
      val _ = if sl = [] then raise UserPP_Failed else ()
      val (t1,t2) = dest_comb t 
      fun pbegin b = add_string pps (if b then "(" else "")
      fun pend b = add_string pps (if b then ")" else "")
      fun decdepth d = if d < 0 then d else d - 1

      val add_l =
        case lgrav of
           Prec (n, _) => (n >= comb_prec)
         | _ => false
      val add_r =
        case rgrav of
          Prec (n, _) => (n > comb_prec)
        | _ => false
      val addparens = add_l orelse add_r
      val prec = Prec(comb_prec, GrammarSpecials.fnapp_special)
      val lprec = if addparens then Top else lgrav
      val rprec = if addparens then Top else rgrav
  in
     pbegin addparens;
     begin_block pps INCONSISTENT 2;
     sys (prec, lprec, prec) (decdepth d) t1;
     add_break pps (1, 0);
     sys (prec, prec, rprec) (decdepth d) t2;
     end_block pps;
     add_comment pps sl;
     pend addparens
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

fun pr_psr t =
  ["CPSR: "^((psr_string o numeral2num o rhs o concl o
   REWRITE_CONV [armTheory.SUBST_def] o mk_comb) (t,``CPSR``))]
  handle Conv.UNCHANGED => [];

val pr_opcode = opcode_string o numeral2num;

(* - *)
fun pr_dp_psr t = pr_psr ((snd o dest_comb o (funpow 5 (fst o dest_comb))) t);

(* - *)
fun pr_pipe t = let
  val t1 = funpow 33 (fst o dest_comb) t
  val (t2,t3) = dest_comb t1
  val ireg = ["ireg: " ^ pr_opcode t3] handle HOL_ERR _ => []
  val (t4,t5) = (dest_comb o fst o dest_comb) t2
  val pipeb = ["pipeb: " ^ pr_opcode t5] handle HOL_ERR _ => []
  val pipea = ["pipea: " ^ (pr_opcode o snd o dest_comb o fst o dest_comb) t4]
                 handle HOL_ERR _ => []
in
  pipea @ pipeb @ ireg
end;

(* - *)
fun pr_arm_ex t =
  let val t1 = (snd o dest_comb o fst o dest_comb) t in
    ["ireg: " ^ pr_opcode t1] handle HOL_ERR _ => []
  end;

(* - *)
fun pr_arm t = pr_psr ((snd o dest_comb) t);

fun pp_word_psr() = Parse.temp_add_user_printer (
  {Tyop = "dp", Thy = "core"}, word_print pr_dp_psr);

fun pp_word_pipe() = Parse.temp_add_user_printer (
  {Tyop = "ctrl", Thy = "core"}, word_print pr_pipe);

fun pp_word_arm_ex() = Parse.temp_add_user_printer (
  {Tyop = "state_arm_ex", Thy = "arm"}, word_print pr_arm_ex);

fun pp_word_arm() = Parse.temp_add_user_printer (
  {Tyop = "state_arm", Thy = "arm"}, word_print pr_arm);

fun npp_word_psr() =
  (Parse.temp_remove_user_printer {Tyop = "dp", Thy = "core"};());

fun npp_word_pipe() =
  (Parse.temp_remove_user_printer {Tyop = "ctrl", Thy = "core"};());

fun npp_word_arm_ex() =
  (Parse.temp_remove_user_printer {Tyop = "state_arm_ex", Thy = "arm"};());

fun npp_word_arm() =
  (Parse.temp_remove_user_printer {Tyop = "state_arm", Thy = "arm"};());

val _ = pp_word_psr();
val _ = pp_word_pipe();
val _ = pp_word_arm_ex();
val _ = pp_word_arm();

(*
val _ = ``ARM6 (DP reg (\x. 0w) areg din alua alub dout)
        (CTRL 1w pipeaval 2w pipebval 3w iregval ointstart onewinst
           endinst obaselatch opipebll nxtic nxtis nopc1 oorst resetlatch
           onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
           aregn2 mrq2 nbw nrw sctrlreg psrfb oareg mask orp oorp mul mul2
           borrow2 mshift)``;
*)

end
