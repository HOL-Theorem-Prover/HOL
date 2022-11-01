open HolKernel boolLib bossLib
open relation_extraTheory

val () = new_theory "mm"

(* -------------------------------------------------------------------------
   Graph events and labels
   ------------------------------------------------------------------------- *)

(* - types ----------------------------------------------------------------- *)

Type ThreadId = ``: num``
Type Location = ``: num``
Type Value = ``: num``

Datatype: ThreadEvent = <|
    thread : ThreadId;
    index    : num;
    subindex : num
  |>
End

Datatype: ActID =
  | InitEvent Location
  | ThreadEvent ThreadEvent
End

Datatype: ReadMode =
  | Opln_read
  | OacqSC
  | OacqPC
End

Datatype: WriteMode =
  | Opln_write
  | Orel
End

Datatype: FenceMode =
  | Odmbst
  | Odmbld
  | Odmbsy
  | Oisb
End

Datatype: Load = <|
    exclusive : bool;
    order     : ReadMode;
    location  : Location;
    value     : Value
  |>
End

Datatype: Store = <|
    exclusive : bool;
    order     : WriteMode;
    location  : Location;
    value     : Value
  |>
End

(* tag events not included *)
Datatype: Label =
  | Aload Load
  | Astore Store
  | Afence FenceMode
  | Abranch
End

(* - definitions ----------------------------------------------------------- *)

Overload tid_init[inferior] = ``0n``

Definition tid:
  tid a =
  case a of
    InitEvent _ => tid_init
  | ThreadEvent e => e.thread
End

Definition is_tid:
  is_tid i a = (tid a = i)
End

Definition index:
  index a =
  case a of
    InitEvent _ => 0
  | ThreadEvent e => e.index
End

Definition is_init:
  is_init a =
  case a of
    InitEvent _ => T
  | ThreadEvent _ => F
End

Definition same_tid:
  same_tid a b = (tid a = tid b)
End

Definition loc:
  loc lab a =
  case lab a of
  | Aload l => SOME l.location
  | Astore s => SOME s.location
  | _ => NONE
End

Definition value:
  value lab a =
  case lab a of
  | Aload l => SOME l.value
  | Astore s => SOME s.value
  | _ => NONE
End

Definition is_r:
  is_r lab a =
  case lab a of
  | Aload l => T
  | _ => F
End

Definition is_w:
  is_w lab a =
  case lab a of
  | Astore s => T
  | _ => F
End

Definition is_f:
  is_f lab a =
  case lab a of
  | Afence _ => T
  | _ => F
End

Definition is_br:
  is_br lab a =
  case lab a of
  | Abranch => T
  | _ => F
End

Definition is_w_rel:
  is_w_rel lab a =
  case lab a of
  | Astore s => s.order = Orel
  | _ => F
End

Definition is_r_acqSC:
  is_r_acqSC lab a =
  case lab a of
  | Aload l => l.order = OacqSC
  | _ => F
End

Definition is_r_acqPC:
  is_r_acqPC lab a =
  case lab a of
  | Aload l => l.order = OacqPC
  | _ => F
End

Definition is_dmbst:
  is_dmbst lab a <=> lab a = Afence Odmbst
End

Definition is_dmbld:
  is_dmbld lab a <=> lab a = Afence Odmbld
End

Definition is_dmbsy:
  is_dmbsy lab a <=> lab a = Afence Odmbsy
End

Definition is_isb:
  is_isb lab a <=> lab a = Afence Oisb
End

Definition R_ex:
  R_ex lab a =
  case lab a of
  | Aload r => r.exclusive
  | _ => F
End

Definition same_loc:
  same_loc lab a b = (loc lab a = loc lab b)
End

(* Sequenced-Before *)
Definition ext_sb:
  ext_sb a b =
  case a, b of
  | _, InitEvent _ => F
  | InitEvent _, _ => T
  | ThreadEvent e, ThreadEvent e' => e.thread = e'.thread /\ e.index < e'.index
End

(* Same Instruction *)
Definition si_matching_label:
  si_matching_label label1 label2 =
  case label1, label2 of
  | Aload l1, Aload l2 => l1.exclusive = l2.exclusive /\
                          l1.order = l2.order
  | Astore s1, Astore s2 => s1.exclusive = s2.exclusive /\
                            s1.order = s2.order
  | Afence o1, Afence o2 => o1 = o2
  | Abranch, Abranch => T
  | _ => F
End

Definition ext_si:
  ext_si a b =
  case a, b of
  | InitEvent l, InitEvent l' => l = l'
  | ThreadEvent e, ThreadEvent e' => e.thread = e'.thread /\ e.index = e'.index
  | _ => F
End

(* -------------------------------------------------------------------------
   Executions
   ------------------------------------------------------------------------- *)

Datatype: Exec = <|
    acts : ActID list;
    lab  : ActID -> Label;
    iico_data : ActID -> ActID -> bool;   (* intrinsic data dependency *)
    iico_ctrl : ActID -> ActID -> bool;   (* intrinsic control dependency *)
    data : ActID -> ActID -> bool;   (* data dependency *)
    addr : ActID -> ActID -> bool;   (* address dependency *)
    ctrl : ActID -> ActID -> bool;   (* control dependency *)
    lxsx : ActID -> ActID -> bool;   (* load-exclusive -> store-exclusive *)
    amo  : ActID -> ActID -> bool;   (* read -> write of atomic operation *)
    rf   : ActID -> ActID -> bool;
    co   : ActID -> ActID -> bool
  |>
End

(* - overloads and definitions --------------------------------------------- *)

Overload loc      = ``\G. loc G.lab``
Overload value    = ``\G. value G.lab``
Overload same_loc = ``\G. same_loc G.lab``
Overload R        = ``\G. is_r G.lab``
Overload W        = ``\G. is_w G.lab``
Overload RW       = ``\G. R G UNION W G``
Overload Fence    = ``\G. is_f G.lab``
Overload Br       = ``\G. is_br G.lab``
Overload L        = ``\G. W G INTER is_w_rel G.lab``
Overload A        = ``\G. R G INTER is_r_acqSC G.lab``
Overload Q        = ``\G. R G INTER is_r_acqPC G.lab``
Overload F_dmbld  = ``\G. Fence G INTER is_dmbld G.lab``
Overload F_dmbst  = ``\G. Fence G INTER is_dmbst G.lab``
Overload F_dmbsy  = ``\G. Fence G INTER is_dmbsy G.lab``
Overload F_isb    = ``\G. Fence G INTER is_isb G.lab``

(*
Overload R_ex     = ``\G. R_ex G.lab``
Overload FR       = ``\G. Fence G UNION R G``
Overload FW       = ``\G. Fence G UNION W G``
*)

Definition acts_set:
  acts_set G x = MEM x G.acts
End

Overload E[inferior] = ``acts_set``

Definition po:
  po G = diag (E G) ⨾ ext_sb ⨾ diag (E G)
End

Definition si:
  si G = diag (E G) ⨾ ext_si ⨾ diag (E G)
End

(* Read-modify-write *)
Definition rmw:
  rmw G = G.lxsx RUNION G.amo
End

Definition fr:
  fr G = inv G.rf ⨾ G.co
End

Definition rfe:
  rfe G = G.rf RMINUS po G
End

Definition coe:
  coe G = G.co RMINUS po G
End

Definition fre:
  fre G = fr G RMINUS po G
End

Definition rfi:
  rfi G = G.rf RINTER po G
End

Definition coi:
  coi G = G.co RINTER po G
End

Definition fri:
  fri G = fr G RINTER po G
End

Definition deps:
  deps G = G.data RUNION G.addr RUNION G.ctrl
End

Definition W_ex:
  W_ex G = RRANGE (rmw G)
End

(* extended coherence order *)
Definition eco:
  eco G <=> G.rf RUNION G.co ⨾ RC G.rf RUNION fr G ⨾ RC G.rf
End

Definition sc_per_loc:
  sc_per_loc G = irreflexive (po G ⨾ eco G)
End

val well_formed = TotalDefn.multiDefine`
  (data_in_po G  <=> G.data RSUBSET po G) /\
  (wf_dataD G    <=> G.data = (diag (R G) ⨾ G.data ⨾ diag (W G))) /\
  (addr_in_po G  <=> G.addr RSUBSET po G) /\
  (wf_addrD G    <=> G.addr = (diag (R G) ⨾ G.data ⨾ diag (RW G))) /\
  (ctrl_in_po G  <=> G.ctrl RSUBSET po G) /\
  (wf_ctrlD G    <=> G.ctrl = (diag (R G) ⨾ G.ctrl)) /\
  (ctrl_po G     <=> G.ctrl ⨾ po G RSUBSET G.ctrl) /\
  (wf_rmwD G     <=> rmw G = (diag (R G) ⨾ rmw G ⨾ diag (W G))) /\
  (wf_rmwl G     <=> rmw G RSUBSET same_loc G) /\
  (wf_rmwi G     <=> rmw G RSUBSET immediate (po G)) /\
  (wf_siD G      <=> !x y. si G x y ==>
                           si_matching_label (G.lab x) (G.lab y)) /\
  (wf_sil G      <=> si G RINTER same_loc G = diag (E G)) /\
  (wf_si_data G  <=> (si G ⨾ G.data ⨾ si G) RSUBSET G.data) /\
  (wf_si_ctrl G  <=> (si G ⨾ G.ctrl ⨾ si G) RSUBSET G.ctrl) /\
  (wf_si_addr G  <=> (si G ⨾ G.addr ⨾ si G) RSUBSET G.addr) /\
  (si_lxsx G     <=> (si G ⨾ G.lxsx) = (G.lxsx ⨾ si G)) /\
  (si_amo G      <=> (si G ⨾ G.amo) = (G.amo ⨾ si G)) /\
  (wf_rfE G      <=> G.rf = (diag (E G) ⨾ G.rf ⨾ diag (E G))) /\
  (wf_rfD G      <=> G.rf = (diag (W G) ⨾ G.rf ⨾ diag (R G))) /\
  (wf_rfl G      <=> G.rf RSUBSET same_loc G) /\
  (wf_rfv G      <=> funeq (value G) G.rf) /\
  (wf_rff G      <=> functional (inv (G.rf))) /\
  (wf_coE G      <=> G.co = (diag (E G) ⨾ G.co ⨾ diag (E G))) /\
  (wf_coD G      <=> G.co = (diag (W G) ⨾ G.co ⨾ diag (W G))) /\
  (wf_col G      <=> G.co RSUBSET same_loc G) /\
  (co_trans G    <=> transitive G.co) /\
  (wf_co_total G <=> !ol. is_total
                            (E G INTER W G INTER (\x. loc G x = ol)) G.co) /\
  (co_irr G      <=> irreflexive G.co) /\
  (wf_init G     <=> !l. (?b. E G b /\ (loc G b = SOME l)) ==>
                         E G (InitEvent l)) /\
  (wf_init_lab G <=> !l. G.lab (InitEvent l) =
                         Astore  <| exclusive := F;
                                    order := Opln_write;
                                    location := l;
                                    value := 0 |>)`

Definition WellFormed:
  WellFormed G = EVERY (\p. p G)
  [data_in_po;
   wf_dataD;
   addr_in_po;
   wf_addrD;
   ctrl_in_po;
   wf_ctrlD;
   ctrl_po;
   wf_rmwD;
   wf_rmwl;
   wf_rmwi;
   wf_siD;
   wf_sil;
   wf_si_data;
   wf_si_ctrl;
   wf_si_addr;
   si_lxsx;
   si_amo;
   wf_rfE;
   wf_rfD;
   wf_rfl;
   wf_rfv;
   wf_rff;
   wf_coE;
   wf_coD;
   wf_col;
   co_trans;
   wf_co_total;
   co_irr;
   wf_init;
   wf_init_lab]
End

Definition complete:
  complete G <=> E G INTER R G SUBSET RRANGE G.rf
End

(* -------------------------------------------------------------------------
   End
   ------------------------------------------------------------------------- *)

val () = export_theory()
