(* ===================================================================== *)
(* FILE          : homework.sml                                          *)
(* DESCRIPTION   : Formalization of a security protocol using holyhammer *)
(*                                                                       *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

(*-------------------------------------------------------------------------- 
  A simple zero-knowledge proof
  -------------------------------------------------------------------------- *)

(* 
    Suppose Alice and Bob want to authenticate using the secret number of 
    "27" but don't want to reveal it to one another. In this scenario they 
    use a third party, Charlie.

    Charlie randomly comes up with a number (any number will do) -- 
    we'll say 15 -- and whispers it to Alice. Alice then adds the secret 
    number (27) to Charlie's number (15) and whispers the total (42) to Bob.

    Bob subtracts the secret number (27) from the total (42) and whispers 
    the result (15) to Charlie.

    If Charlie is read back his own number (15) then he can declare Alice 
    and Bob have successfully authenticated.
*)

(* Soundness *)

(* Completeness *)

(* Zero-knowledge *)

(*-------------------------------------------------------------------------- 
  An interactive proof of knowledge of a discrete logarithm
  -------------------------------------------------------------------------- *)

(* 
    Alice want to prove to Bob that she knows x: the discrete logarithm of 
    y = g^x to the base g.
    She picks a random v in Z/qZ, computes t = g^v and sends t to Bob.
    Bob picks a random c in (Z/qZ)* and sends it to Alice.
    Alice computes r = v - cx and returns r to Bob.
    He checks if t = g^r * y^c 
    (it holds, because g^r * y^c = g^{v - cx} * g^{xc} = g^v = t).
*)

(* Soundness *)

(* Completeness *)

(* Zero-knowledge *)

