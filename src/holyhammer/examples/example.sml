(* ===================================================================== *)
(* FILE          : example.sml                                           *)
(* DESCRIPTION   : Formalization of a security protocol using holyhammer *)
(*                                                                       *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

(* Tools to fetch and unfold definitions *)

fun is_def_of c (s,thm) =
  let  
    val thml = CONJUNCTS thm 
    val th1 = SPEC_ALL (hd thml)
    val tm1 = concl th1
    val (c1,_) = strip_comb (lhs tm1) 
  in
    same_const c c1 
  end
  handle _ => false

fun fetch_def c = 
  let 
    val {Name,Thy,Ty} = dest_thy_const c
    val thml = DB.thms Thy
    val thml1 = filter (is_def_of c) thml
  in
    (List.hd thml1)
  end

fun all_def term =
  let 
    val cl = filter (not o (same_const equality)) (find_terms is_const term) 
    val cl = mk_set cl
    val thml = map fetch_def cl;
  in
    thml
  end

fun all_rec_def term = 
  List.concat (map (all_def o concl o snd) (all_def cj)) 

fun unfold thml cj = 
  let val eqthm = REWRITE_CONV thml cj in
    (rhs (concl eqthm), eqthm)
  end

(* Formalizing a simple zero knowledge proof *)
(* 

An easy ZKP-based authentication scheme is one that uses a deck of shuffled playing cards and a paper bag:

Suppose Alice and Bob want to authenticate using the secret number "27". Alice takes the deck of cards, places her hands (with the cards) inside the bag and begins drawing card after card until she has reached the 27th card. She pulls this one card out of the bag and reveals it to herself and Bob.

Alice places the cards back on the deck in the same order she drew them (not destroying the original order).

Now it's Bob's turn. He is handed the deck of cards and hides his hands (and the counting of cards) in the paper bag. If he knows the secret number (27) then he should draw down to the 27th card and reveal the same card Alice did.

If Alice and Bob draw different cards then they did not draw the same number of cards.

Another one:

Suppose Alice and Bob want to authenticate using the secret number of "27" but don't want to reveal it to one another. In this scenario they use a third party, Charlie.

Charlie randomly comes up with a number (any number will do) -- we'll say 15 -- and whispers it to Alice. Alice then adds the secret number (27) to Charlie's number (15) and whispers the total (42) to Bob.

Bob subtracts the secret number (27) from the total (42) and whispers the result (15) to Charlie.

If Charlie is read back his own number (15) then he can declare Alice and Bob have successfully authenticated.
*)

(* Soundness: if C_start = C_end then A = B *)
(* Zero-Knowledge: if random C_start then (random (A + C_start) | B) *)

new_theory "zerok";
load "holyHammer";
open holyHammer;

new_constant("Alice_number",``:num``);
new_constant("Bob_number",``:num``);
new_constant("Key",``:num``);

val Alice_def = new_definition("Alice_def",``Alice = 0:num``);
val Bob_def = new_definition("Bob_def",``Bob = 1:num``);

val Number_of_def = new_recursive_definition
   {name = "Number_of_def",
    rec_axiom = prim_recTheory.num_Axiom, 
    def = ``(Number_of 0 = Alice_number) /\ (Number_of (SUC n) = Bob_number)``};

val cj = ``Number_of Alice = Alice_number``;
(* hh [] cj; *)
val lemmas = [fetch "zerok" "Number_of_def", fetch "zerok" "Alice_def"];
val th = save_thm ("Num_of_Alice",METIS_PROVE lemmas cj);

val Pknows_def = new_definition ("Pknows_def",
  ``(Pknows (p:num->bool)) = (!x. (p x ==> (Number_of x = Key)))``);
val Knows_def = new_definition ("Knows_def",
  ``Knows = @(p:num->bool). Pknows p``);
val Knows_witness_def = 
 new_definition ("Knows_witness_def",
  ``Knows_witness x = (Number_of x = Key)``);

(* Proof eliminating the epsilon operator *)
val th0 = INST_TYPE [alpha |-> ``:num->bool``] SELECT_AX;
val th1 = SPECL [``Pknows``,``Knows_witness``] th0;

val cj = ``!x . Knows x ==> (Number_of x = Key)``;
hh [th1] cj;

val lemmas = [fetch "zero_knowledge" "Pknows_def",
              fetch "zero_knowledge" "Knows_def",fetch "bool" "SELECT_AX",
              fetch "zero_knowledge" "Knows_witness_def"];

val th2 = save_thm ("KNOWING_THM",METIS_PROVE ([th1] @ lemmas) cj);
(* end *)

(* Completeness *)

val Authenticate_def = new_definition ("Authenticate_def",
  ``Authenticate x y = !z. (Number_of x + z - Number_of y) MOD Max = z MOD Max``);

val th17 = METIS_PROVE 
  [DB.fetch "zero_knowledge" "Authenticate_def",DB.fetch "zero_knowledge" "KNOWING_THM",
   DB.fetch "arithmetic" "ADD_SUB",DB.fetch "arithmetic" "ADD_SYM"] 
  ``Knows Alice ∧ Knows Bob ⇒ Authenticate Bob Alice``;

val cj = mk_imp (``Authenticate x y = !z. (Number_of x + z - Number_of y) MOD Max = z MOD Max``,
                 ``Knows Alice ∧ Knows Bob ⇒ Authenticate Bob Alice``);
hh cj;

val th_imp = METIS_PROVE 
   [DB.fetch "zero_knowledge" "Authenticate_def", DB.fetch "arithmetic" "ADD_SYM", 
    DB.fetch "arithmetic" "ADD_SUB", DB.fetch "zero_knowledge" "KNOWING_THM"] 
   ``(Authenticate (x :num) (y :num) ⇔
     ∀(z :num). (Number_of x + z − Number_of y) MOD Max = z MOD Max) ⇒
   Knows Alice ∧ Knows Bob ⇒
   Authenticate Bob Alice``;





(* Simple probabilities *)

val Max_def = new_definition ("Max_def",``Max = @(x:num). x >= 1``);
val th0 = INST_TYPE [alpha |-> ``:num``] SELECT_AX;
val th1 = save_thm ("hh0",SPECL [``\x.x>=(1:num)``,``1:num``] th0);


val cj = ``Max>=1``;
(* hh [th0,th1] cj; *)
val lemmas = [fetch "numeral" "numeral_lte", fetch "zerok" "Max_def",
              fetch "arithmetic" "GREATER_EQ",
              fetch "arithmetic" "NUMERAL_DEF"];
val th = save_thm ("MAX_THM",METIS_PROVE ([th0,th1] @ lemmas) cj);

val Check_def = new_definition ("Check_def",
  ``Check x y = !z. (x + z - y) MOD Max = z MOD Max``);




(* hh [th2] cj'; *)

val RandomAlice_def = new_definition ("Random_def", 
                  ``Random = x:num``);


Proba (\x:num. Authenticate x Alice) = 








Size_couple p = ``CARD (\x y. x < Max /\ y < Max /\ p x y)``;
Proba_couple p = ``rat_of_num (Size_couple p) / rat_of_num (Max*Max)``;

Proba_couple





@(p:num->bool). Pknows p``);


                           
Éé


Know_key Alice => Alice_number = Key
Bob knows => Bob_number = Key

not Know Alice


val conjecture = ``!x. Alice_number + x - Bob_number = x mod Max_size <==> Alice_number = Bob_number``;

(* Here is an interactive proof of knowledge of a discrete logarithm.[5]

    Alice want to prove to Bob that she knows x: the discrete logarithm of y = g^x to the base g.
    She picks a random v\in \Z_q, computes t = g^v and sends t to Bob.
    Bob picks a random c\in \Z^*_q and sends it to Alice.
    Alice computes r = v - cx and returns r to Bob.
    He checks if t \equiv g^ry^c (it holds, because g^ry^c = g^{v - cx}g^{xc} = g^v = t).

Fiat-Shamir heuristic allows to replace the interactive step 3 with a non-interactive random oracle access. In practice, we can use a cryptographic hash function instead.[6]

*)

(* Completeness *)
val goal = ``!y x. (y = pow g x) ==> (!v c. c <> 0 ==>  



(* Soundness : if g = 1 and y = 1 then it is not sound *)


pow ^

! v:num. pow g v = g 

  


