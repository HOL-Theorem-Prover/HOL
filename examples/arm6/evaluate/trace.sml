(* ========================================================================= *)
(* FILE          : trace.sml                                                 *)
(* DESCRIPTION   : TCL/TK front-end for evaluating the ARM specifications    *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2004 - 2005                                               *)
(* ========================================================================= *)

(* interactive use:
  load "evaluateLib"; use "trace.sml"; go();
*)

open HolKernel boolLib bossLib;
open evaluateLib;

(* ------------------------------------------------------------------------- *)

val EXC_HANDLER = "handler";

val concat = String.concat;
val _ = Meta.use "root_mosml.sml";
val _ = SmlTk.init();

open SmlTk

datatype mode = usr | fiq | irq | svc | abt | und
datatype exc = reset | undefined | software | pabort |
               dabort | interrupt | fast
type psr = {c : bool, f : bool, i : bool, mode : mode,
            n : bool, v : bool, z : bool}

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
val exc = ref reset
val psr = Array.array(6, {n = false, z = false, c = false, v = false,
                          i = false, f = false, mode = usr})

val trace_winId = newWinId()

val load_winId = newWinId()
val load_fnameId = newWidgetId()
val load_offsetId = newWidgetId()
val load_startId = newWidgetId()

val save_winId = newWinId()
val save_fnameId = newWidgetId()
val save_startId = newWidgetId()
val save_finishId = newWidgetId()

val line_winId = newWinId()
val line_entryId = newWidgetId()

val bl_key = ref 0wx0
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
         val _ = Array.modify
                   (fn _ => {n = false, z = false, c = false, v = false,
                             i = false, f = false, mode = usr}) psr
         val _ = mode := usr
         val _ = exc  := reset
         val _ = bl_key := (hd (mem_blocks()) handle _ => 0wx0)
     in
       ()
     end

(* --- *)

fun simple_text id = TextWid {
      widId = id, scrolltype = NoneScb, annotext = mtAT,
      packings = [Side Right], configs = [Width 40, Height 1], bindings = []}

fun simple_list (x,y) scrl id = Listbox {
      widId = id, scrolltype = if scrl then RightScb else NoneScb,
      packings = [], bindings = [],
      configs = [Font (Typewriter []),Width x, Height y]}

fun simple_frame p w = Frame {
      widId = newWidgetId(), bindings = [], configs = [],
      packings = p, widgets = w}
      
fun simple_label t = Label {
      widId = newWidgetId(), bindings = [], configs = [Text t],
      packings = [Side Left]}

fun simple_top_label t = Label {
      widId = newWidgetId(), bindings = [], configs = [Text t],
      packings = [Side Top]}

fun simple_tt_label id t = Label {
      widId = id, bindings = [], packings = [Side Left],
      configs = [Text t,Font (Typewriter []),Foreground Black]}

fun simple_entry id = Entry {
      widId = id, bindings = [], configs = [], packings = [Side Right]}

fun simple_entryw id w = Entry {
      widId = id, bindings = [], configs = [Width w], packings = [Side Right]}

fun simple_button p t c = Button {
      widId = newWidgetId(), configs = [Text t, Command c],
      packings = p, bindings = []}

fun bind_list (Listbox {bindings, configs, packings, scrolltype, widId}) d = 
      Listbox {bindings = d, configs = configs,
               packings = packings, scrolltype = scrolltype, widId = widId}
  | bind_list x _ = x

fun bind_entry (Entry {bindings, configs, packings, widId}) d = 
      Entry {bindings = d, configs = configs,
             packings = packings, widId = widId}
  | bind_entry x _ = x

fun copenWindow wid win = if occursWin wid then () else openWindow win

(* --- *)

fun projMark (Mark(x,_)) = x
  | projMark (MarkToEnd x) = x
  | projMark MarkEnd = 0

local
  fun nzeros_string n = funpow n (fn x => x ^ "0") ""

  fun toHexString8 n = let val x = Arbnum.toHexString n in
    nzeros_string (8 - size x) ^ x
  end

  fun line_string l n =
   (toHexString8 l) ^ ":  " ^ (toHexString8 n) ^ "    " ^
   (disassemblerLib.opcode_string n)

  fun plus4 x = Arbnum.+(x,Arbnum.fromInt 4);

  fun do_block n d = Array.foldl (fn (a,l) =>
                 (insertTextEnd mem_dumpId ((line_string l a));
                  plus4 l)) n d
in
  fun fill_block k =
        (clearText mem_dumpId;
         case mem_read_block k of
           NONE => ()
         | SOME d => ((do_block (block_start k) (#data d)); ()))

  fun view_block() =
       if readSelWindow() = SOME (mem_winId,mem_blockId) then
          let val k = mem_nth_block (projMark (readCursor mem_blockId))
              val _ = bl_key := k
          in
            fill_block k
          end
       else ()

  fun show_blocks() =
       (clearText mem_blockId;
        app (fn b => insertTextEnd mem_blockId (block_range b))
            (mem_blocks());
        fill_block (!bl_key))

  fun wipe_block() =
       ((if readSelWindow() = SOME (mem_winId,mem_blockId) then
           let val n = projMark (readCursor mem_blockId) in
             mem_rm_block (mem_nth_block n)
           end
         else ()); show_blocks())
end

fun load_load() =
  let val fname = readTextAll load_fnameId
      val offset = case Int.fromString (readTextAll load_offsetId) of
                     SOME n => n | _ => 0
      val start = Arbnum.fromHexString (readTextAll load_startId)
                     handle _ => Arbnum.zero
  in
     (load_data (if fname = "" then EXC_HANDLER else fname) offset start;
      closeWindow load_winId; show_blocks())
  end

(* ^^ add handle for failing to open file ^^ *)
 
local
  fun bind x = bind_entry x ([BindEv(KeyPress "Return", fn _ => load_load())])
in
  val load_fname = simple_frame [Side Top]
        (Pack [simple_label ("file name [default \"" ^ EXC_HANDLER ^ "\"]:"),
               bind (simple_entry load_fnameId)])

  val load_offset = simple_frame [Side Top]
        (Pack [simple_label "offset (bytes) [default 0]:",
               bind (simple_entry load_offsetId)])

  val load_start = simple_frame [Side Top]
        (Pack [simple_label "start address [default 0]:",
               bind (simple_entry load_startId)])
end

val load_buttons = simple_frame [Side Bottom]
      (Pack [simple_button [Side Left] "cancel"
               (fn _ => closeWindow load_winId),
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
      val start = Arbnum.fromHexString (readTextAll save_startId)
                     handle _ => Arbnum.zero
      val finish = Arbnum.fromHexString (readTextAll save_finishId)
                     handle _ => Arbnum.zero
  in
     (save_data fname start finish ((readVarValue "LE") = "1");
      closeWindow save_winId)
  end

(* ^^ add handle for failing to open file ^^ *)

local
  fun bind x = bind_entry x ([BindEv(KeyPress "Return", fn _ => save_save())])
in
  val save_fname = simple_frame [Side Top]
       (Pack [simple_label "file name:", bind (simple_entry save_fnameId)])
  val save_start = simple_frame [Side Top]
       (Pack [simple_label "first address:", bind (simple_entry save_startId)])
  val save_finish = simple_frame [Side Top]
       (Pack [simple_label "last address:", bind (simple_entry save_finishId)])
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
      (Pack [simple_button [Side Left]  "cancel"
               (fn _ => closeWindow save_winId),
             simple_button [Side Right] "save" save_save])

val save_win = mkWindow {
  winId    = save_winId,
  config   = [WinTitle "save block"],
  widgets  = Pack [save_fname,save_start,save_finish,save_ends,save_buttons],
  bindings = [],
  init     = save_le false}

(* --- *)

val line_address = ref Arbnum.zero

fun read_line() =
  if occursWin line_winId andalso (readSelWindow() =
      SOME (mem_winId,mem_dumpId)) then
    let open Arbnum
      val k = (fromInt o projMark o readCursor) mem_dumpId
      val n = (block_start (!bl_key)) + (k * (fromInt 4))
      val _ = line_address := n
      val d = mem_read_word n
      val s = disassemblerLib.opcode_string d
      val s = if s = "cdp_und" then toHexString d else s
    in
      (clearText line_entryId; insertTextEnd line_entryId s;
       changeTitle line_winId (mkTitle ("Edit address: 0x" ^ (toHexString n))))
    end
  else ()

fun line_update() =
  (assemble1 (!line_address) (readTextAll line_entryId);
   show_blocks(); fill_block (!bl_key))

val line_win = mkWindow {
  winId    = line_winId,
  config   = [],
  widgets  = Pack [bind_entry (simple_entryw line_entryId 30)
                     [BindEv(KeyPress "Return", fn _ => line_update())]],
  bindings = [],
  init     = noAction}

fun edit_mem_line() = (copenWindow line_winId line_win; read_line())

val delete_button = simple_button [Side Top] "wipe block" wipe_block

val load_button = simple_button [Side Top] "load"
   (fn _ => copenWindow load_winId load_win)

val save_button = simple_button [Side Top] "save"
   (fn _ => copenWindow save_winId save_win)

val mem_blocks_frame = simple_frame [Side Left] (
   Pack [simple_frame [Side Top] (Pack [simple_top_label "blocks",
           bind_list (simple_list (19,10) true mem_blockId)
              [BindEv(Double(ButtonPress (SOME 1)), fn _ => view_block())]]),
         delete_button,load_button,save_button])

val mem_content = simple_frame [Side Right]
  (Pack [simple_top_label "content",
           bind_list (simple_list (60,24) true mem_dumpId)
              [BindEv(Double(ButtonPress (SOME 1)), fn _ => edit_mem_line()),
               BindEv(ButtonPress (SOME 1), fn _ => read_line())]])

val mem_win = mkWindow {
  winId    = mem_winId,
  config   = [WinTitle "memory"],
  widgets  = Pack [mem_blocks_frame,mem_content],
  bindings = [],
  init     = show_blocks}

(* --- *)

val st_reg = simple_frame [Side Top,Fill X]
   (Pack [simple_label "registers:", simple_list (50,8) true st_regId])

val st_psr = simple_frame [Side Top,Fill X]
   (Pack [simple_label "status:", simple_list (50,6) false st_psrId])

val st_opcode = simple_frame [Side Top,Fill X]
   (Pack [simple_label "opcode:", simple_text st_opcId])

val st_exception = simple_frame [Side Top,Fill X]
   (Pack [simple_label "exception:", simple_text st_excId])

val in_opcode = simple_frame [Side Top,Fill X]
   (Pack [simple_label "fetch:", simple_text in_opcId])

val in_interrupt = simple_frame [Side Top,Fill X]
   (Pack [simple_label "interrupt:", simple_text in_intId])

val in_din = simple_frame [Side Top,Fill X]
   (Pack [simple_label "data-in:", simple_text in_dinId])

val dout = simple_frame [Side Top,Fill X]
   (Pack [simple_label "data-out:", simple_text doutId])

fun show_registers (l,r) =
  let val ks = patriciaLib.keys r
      val lks = length ks
  in
    (clearText st_regId;
     app (fn i => insertTextEnd st_regId
            ((reg_string i) ^ ": " ^ (term_to_string
               (#data (valOf (patriciaLib.member i r)))))) ks;
     if lks < 31 then
       insertTextEnd st_regId
         ((if (lks = 0) then "all: " else "rest: ") ^
          (term_to_string (if is_abs l then (snd o dest_abs) l else l)))
     else ())
  end

fun show_psrs psrs =
  (clearText st_psrId;
   let fun f n = (disassemblerLib.psr_string o eval_word) (Array.sub(psrs,n))
   in
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
      val ftch = List.nth(i,2)
      val din  = List.nth(i,3)
      fun write_text wid s = (setTextWidReadOnly wid false; clearText wid;
                              insertTextEnd wid s; setTextWidReadOnly wid true)
      fun write_opcode x = disassemblerLib.opcode_string (eval_word x)
                              handle HOL_ERR _ => term_to_string x
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
  widgets  = Pack [st_opcode,st_exception,st_reg,st_psr,in_opcode,
                   in_interrupt,in_din,dout,trace_scale],
  bindings = [],
  init= (fn () => (app (fn x => setTextWidReadOnly x true)
                     [st_opcId,st_excId,in_opcId,in_intId,in_dinId,doutId]))}

(* --- *)

(* Constructs and SUBST term *)
fun mk_subst m a b =
      let val ta = type_of a and tb = type_of b in
        subst [``a : ^(ty_antiq ta)`` |-> a,
               ``b : ^(ty_antiq tb)`` |-> b,
               ``m : ^(ty_antiq ((ta --> tb)))`` |-> m]
        ``((a:^(ty_antiq ta)) :- (b:^(ty_antiq tb))) m``
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
        foldl (fn (a,t) => mk_comb(t,a)) ``SET_IFMODE``
          [mk_bool i,mk_bool f,mk_mode m,n]

  fun mk_set_nzcv n z c v t =
        subst [``n:bool`` |-> mk_bool n, ``z:bool`` |-> mk_bool z,
               ``c:bool`` |-> mk_bool c, ``v:bool`` |-> mk_bool v,
               ``t:word32`` |-> t] ``SET_NZCV (n,z,c,v) t``

  fun mk_psr a =
      let val t = mk_set_ifmode (#i a) (#f a) (#mode a) ``0w:word32``
      in
        if is_nzcv_clear a then t
        else mk_set_nzcv (#n a) (#z a) (#c a) (#v a) t
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
          mk_subst t (num2reg i) (((mk_word o Arbnum.fromString) s)
            handle e => ``ARB:word32``)

  (* inst [alpha |-> ``:word32``] (Term ([QUOTE s]))) *)

  fun read_regid (i,regid,t) = (i,readTextAll regid,t)
  fun read_ex_reg (i,s,t) = (i + 9,s,t)
in
  fun mk_reg r = add_reg (8,readTextAll (Array.sub(r,15)),
       Array.foldli (add_reg o read_ex_reg)
         (Array.foldli (add_reg o read_regid) ``(\x. 0w):register->word32``
            (r,0,SOME 8)) (ex_regs,0,SOME 21))
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
           val i2 = ex_reg_index (!mode)
                      (if ((!mode) = usr) orelse ((!mode) = fiq) then i - 8
                       else i - 13)
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
      Array.appi (fn (i,t) => printn ((Int.toString i) ^ ": " ^ t))
      (ex_regs,0,NONE);
  *)

  fun read_top_regs() =
    let fun read_fiq_reg i = Array.sub(ex_regs,
          ex_reg_index (if ((!mode) = fiq) then fiq else usr) (i - 8))
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
                    {n = #n x, z = #z x, c = #c x, v = #v x,
                     i = #i x, f = #f x, mode = m})
      in addConf psrId [Text (mode_name m)] end

val psr_label = Label {
  widId = psr_nameId, packings = [Row 1, Column 1],
  bindings = [], configs = [Text "cpsr:"]}

fun register_string n =
  case n of
    13 => " sp"
  | 14 => " lr"
  | 15 => " pc"
  | _  => (if n < 10 then " r" else "r") ^ int_to_string n;

fun reg_label wid n = simple_tt_label wid (register_string n);
fun reg_entry n = simple_entry (Array.sub(regId,n))

fun mode_popup wid act = Menubutton {
      widId = wid,
      configs = [Font (Typewriter []), Relief Raised,
                 Tearoff false, Text (mode_name (!mode))],
      packings = [Side Right, Row 1, Column 8], bindings = [],
      mitems = map
        (fn m => MCommand [Font (Typewriter []),
                           Text (mode_name m),
                           Command (act m)]) [usr, fiq, irq, svc, abt, und]}

(* called when the exception is updated *)
fun set_exc e _ = (exc := e; addConf excId [Text (exc_name e)])

val exc_popup = simple_frame [Row 4,PadY 2]
    (Pack [simple_label "exception:",
      Menubutton {
        widId = excId, packings = [Side Right], bindings = [],
        configs = [Width 21, Font (Typewriter []), Relief Raised,
                   Tearoff false, Text (exc_name (!exc))],
        mitems = map
           (fn e => MCommand [Font (Typewriter []),
                              Text (exc_name e),
                              Command (set_exc e)])
                    [reset, undefined, software, pabort,
                     dabort, interrupt, fast]}])

fun TF_picker l act c =
      Checkbutton {
          widId = newWidgetId(), packings = [Row 1,Column c], bindings = [],
          configs = [Text l,Font (Typewriter []), Command act, Variable l]};

val psr_picker = simple_frame [Row 3]
   (Grid ([psr_label] @
          (map (fn (s,n) => TF_picker s set_psr (n + 2))
                [("N",0), ("Z",1), ("C",2), ("V",3), ("I",4), ("F",5)]) @
                [mode_popup psrId set_psr_mode]))

(* Registers r0-r7 are the same for all modes *)

val bot_registers = simple_frame [Side Left]
       (Pack (List.tabulate(8,fn i => simple_frame [Side Top]
          (Pack [reg_label (newWidgetId()) i,reg_entry i]))))

(* Registers r8-r14 are mode dependent; r15 (i = 7) is same for all modes. *)

val top_registers = simple_frame [Side Right]
       (Pack (List.tabulate(7,fn i => simple_frame [Side Top]
          (Pack [reg_label (Array.sub(reg_nameId,i)) (i + 8),
                 reg_entry (i + 8)])) @
                [simple_frame [Side Top]
                   (Pack [reg_label (newWidgetId()) 15,reg_entry 15])]))

val reg_frame = simple_frame [Row 2] (Pack [bot_registers,top_registers])

val mode_frame = simple_frame [Row 1, PadY 2]
   (Pack [simple_label "mode:",mode_popup modeId set_mode])

 (* val int_frame = simple_frame [Row 5, PadY 2]
      (Pack [simple_label "interrupt at time t:", simple_entry intId]) *)

fun execute _ =
   (write_top_regs();
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
           bind_entry (simple_entry maxcId)
             [BindEv(KeyPress "Return", execute)]])

val go_button = simple_button [Row 7, PadY 5] "execute" execute;

val win = mkWindow {
  winId    = newWinId(),
  config   = [WinTitle "HOL simulator for the ARM ISA"],
  widgets  = Grid [reg_frame,psr_picker,mode_frame,exc_popup,
                   maxc_frame,go_button],
  bindings = [],
  init     = reset_all}

(* ------------------------------------------------------------------------- *)

fun go() = (init();startTcl [win,mem_win]; the_thm_trace)

(* ------------------------------------------------------------------------- *)
