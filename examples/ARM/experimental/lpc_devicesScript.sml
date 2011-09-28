
open HolKernel boolLib bossLib Parse;
open wordsTheory pred_setTheory;

open armTheory arm_stepTheory lpc_uartTheory;

val _ = new_theory "lpc_devices";


(* We define the type of a generic device *)

val _ = type_abbrev ("device",``:
   (* memory addresses that belong to this device, dependent on internal state of type 'a *)
   ('a -> word32 set) #
   (* if core executes a memory read, it sees the following data *)
   ('a -> word32 -> word8) #
   (* the next state relation for the devive  *)
   (num -> memory_access list -> 'a -> 'a -> bool) #
   (* an invariant that mst be true for this devie to make sense *)
   (num # 'a -> bool)``);


(* Devices can be composed *)

val ACCESS_ADDRESS_def = Define `
  (ACCESS_ADDRESS (MEM_READ w) = w) /\
  (ACCESS_ADDRESS (MEM_WRITE w v) = w)`;

val FILTER_ACCESSES_def = Define `
  FILTER_ACCESSES d = FILTER (\x. (ACCESS_ADDRESS x) IN d)`;

val COMPOSE_DEVICES_def = Define `
  COMPOSE_DEVICES ((a1,m1,n1,i1):'a device) ((a2,m2,n2,i2):'b device) =
     (* the combined addresses are the UNION of the two address sets *)
    ((\(x,y). a1 x UNION a2 y),
     (* memory reads are directed according to address ownership *)
     (\(x,y) addr. if addr IN a1 x then m1 x addr else m2 y addr),
     (* the combined next state relation filters memory accesses so that
        respective devices only see relevant memoy accesses *)
     (\t l (x1,y1) (x2,y2). n1 t (FILTER_ACCESSES (a1 x1) l) x1 x2 /\
                            n2 t (FILTER_ACCESSES (a2 y1) l) y1 y2),
     (* the invariant is the conjunction of part invariants and the condition
        that the space used by these devices does not overlap. *)
     (\(t,(x,y)). DISJOINT (a1 x) (a2 y) /\ i1 (t,x) /\ i2 (t,y))):('a # 'b) device`


(* The most basic device: the EMPTY_DEVICE *)

val EMPTY_DEVICE_def = Define `
  (EMPTY_DEVICE:unit device) = ((\x. {}),(\x y. ARB),(\n l x y. T),(\x. T))`;


(* RAM device *)

val domain_def = Define `domain r = { a | ~(r a = NONE) }`;

val UPDATE_RAM_def = Define `
  (UPDATE_RAM [] ram = ram) /\
  (UPDATE_RAM ((MEM_READ w)::xs) ram = UPDATE_RAM xs ram) /\
  (UPDATE_RAM ((MEM_WRITE w v)::xs) ram = UPDATE_RAM xs (\a. if a = w then SOME v else ram a))`;

val RAM_NEXT_def = Define `
  RAM_NEXT (t:num) l (r1:word32 -> word8 option) r2 = (r2 = UPDATE_RAM l r1)`;

val RAM_DEVICE_def = Define `
  (RAM_DEVICE:(word32 -> word8 option) device) =
    (domain, (\m addr. THE (m addr)), RAM_NEXT, (\x. T))`;


(* ROM device - disallows write accesses *)

val IS_WRITE_def = Define `
  (IS_WRITE (MEM_READ w) = F) /\
  (IS_WRITE (MEM_WRITE w v) = T)`;

val ROM_NEXT_def = Define `
  ROM_NEXT (t:num) l r1 r2 = (r2 = r1) /\ (FILTER IS_WRITE l = [])`;

val ROM_DEVICE_def = Define `
  (ROM_DEVICE:(word32 -> word8 option) device) =
    (domain, (\m addr. THE (m addr)), ROM_NEXT, (\x. T))`;


(* UART0 device *)

val UART0_DEVICE_def = Define `
  (UART0_DEVICE:uart0_state device) =
    ((\x. UART0_addresses), UART0_read, UART0_NEXT, \(x,y). uart0_ok x y)`;


(* The collection of all peripherals *)

val ALL_PERIPHERALS_def = Define `
  ALL_PERIPHERALS =
   (COMPOSE_DEVICES (ROM_DEVICE)
   (COMPOSE_DEVICES (RAM_DEVICE)
   (COMPOSE_DEVICES (UART0_DEVICE)
                    (EMPTY_DEVICE))))`;

val PERIPHERALS_NEXT_def = Define `
  PERIPHERALS_NEXT =
    let (addresses,mem,next,inv) = ALL_PERIPHERALS in
      \l (t1,x) (t2,y).
        next t1 l x y /\ (t2 = t1 + 1) /\
        (FILTER_ACCESSES (UNIV DIFF addresses x) l = [])`;

val PERIPHERALS_OK_def = Define `
  PERIPHERALS_OK =
    let (addresses,mem,next,inv) = ALL_PERIPHERALS in inv`;

val MEMORY_IMAGE_def = Define `
  MEMORY_IMAGE (t:num,s) =
    let (addresses,mem,next,inv) = ALL_PERIPHERALS in mem s`;

val PENDING_INTERRUPT_def = Define `
  PENDING_INTERRUPT p1 = NoInterrupt`;

val peripherals_type =
  ``PERIPHERALS_NEXT`` |> type_of |> dest_type |> snd |> el 2
                                  |> dest_type |> snd |> el 1

val _ = type_abbrev ("peripherals", peripherals_type)

val PER_READ_ROM_def = Define `PER_READ_ROM ((t,x,y):peripherals) a = THE (x a)`;
val PER_READ_RAM_def = Define `PER_READ_RAM ((t,x,y,z):peripherals) a = THE (y a)`;
val PER_READ_UART_def = Define `PER_READ_UART ((t,x,y,u,z):peripherals) a = u`;


(* The overall next-state relation *)

val LOAD_IMAGE_def = Define `
  LOAD_IMAGE (s:arm_state) m = s with <|memory := m; accesses := []|>`;

val LPC_NEXT_def = Define `
  LPC_NEXT (s1,p1) (s2,p2) =
    (ARM_NEXT (PENDING_INTERRUPT p1)
              (LOAD_IMAGE s1 (MEMORY_IMAGE p1)) = SOME s2) /\
    PERIPHERALS_NEXT s2.accesses p1 p2`;


(* Theorems *)

val domain_UPDATE_RAM = prove(
  ``!l p. (domain (UPDATE_RAM
            (FILTER (\x. ACCESS_ADDRESS x IN domain p) l) p) = domain p)``,
  SIMP_TAC std_ss [GSPECIFICATION] THEN Induct_on `l`
  THEN SIMP_TAC std_ss [UPDATE_RAM_def,listTheory.FILTER]
  THEN Cases_on `h` THEN SIMP_TAC std_ss [ACCESS_ADDRESS_def]
  THEN REPEAT STRIP_TAC THEN Cases_on `c IN domain p` THEN ASM_SIMP_TAC std_ss []
  THEN ASM_SIMP_TAC std_ss [UPDATE_RAM_def]
  THEN `domain p = domain (\a. if a = c then SOME c0 else p a)` by
   (FULL_SIMP_TAC std_ss [domain_def,GSPECIFICATION,EXTENSION]
    THEN REPEAT STRIP_TAC THEN Cases_on `x = c` THEN ASM_SIMP_TAC std_ss [])
  THEN ASM_SIMP_TAC std_ss []);

val IMP_PERIPHERALS_OK = store_thm("IMP_PERIPHERALS_OK",
  ``!p1 p2 l.
      PERIPHERALS_OK p1 /\ PERIPHERALS_NEXT l p1 p2 ==>
      PERIPHERALS_OK p2``,
  SIMP_TAC std_ss [PERIPHERALS_OK_def,ALL_PERIPHERALS_def,UART0_DEVICE_def,
    COMPOSE_DEVICES_def,ROM_DEVICE_def,RAM_DEVICE_def,EMPTY_DEVICE_def,
    pairTheory.FORALL_PROD,LET_DEF,PERIPHERALS_NEXT_def,FILTER_ACCESSES_def,
    listTheory.FILTER,ROM_NEXT_def,RAM_NEXT_def,UPDATE_RAM_def]
  THEN SIMP_TAC std_ss [domain_UPDATE_RAM,UART0_NEXT_def]);

val PERIPHERALS_NEXT_EXISTS = store_thm("PERIPHERALS_NEXT_EXISTS",
  ``!p1. PERIPHERALS_OK p1 ==> ?p2. PERIPHERALS_NEXT [] p1 p2``,
  SIMP_TAC std_ss [PERIPHERALS_OK_def,ALL_PERIPHERALS_def,UART0_DEVICE_def,
    COMPOSE_DEVICES_def,ROM_DEVICE_def,RAM_DEVICE_def,EMPTY_DEVICE_def,
    pairTheory.FORALL_PROD,LET_DEF,PERIPHERALS_NEXT_def,FILTER_ACCESSES_def,
    listTheory.FILTER,ROM_NEXT_def,RAM_NEXT_def,UPDATE_RAM_def,
    pairTheory.EXISTS_PROD] THEN METIS_TAC [UART0_NEXT_EXISTS]);


val _ = export_theory();
