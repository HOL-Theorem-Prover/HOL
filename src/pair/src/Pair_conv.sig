(* ---------------------------------------------------------------------*)
(* 		Copyright (c) Jim Grundy 1992				*)
(*									*)
(* Jim Grundy, hereafter referred to as "the Author', retains the	*)
(* copyright and all other legal rights to the Software contained in	*)
(* this file, hereafter referred to as "the Software'.			*)
(* 									*)
(* The Software is made available free of charge on an "as is' basis.	*)
(* No guarantee, either express or implied, of maintenance, reliability	*)
(* or suitability for any purpose is made by the Author.		*)
(* 									*)
(* The user is granted the right to make personal or internal use	*)
(* of the Software provided that both:					*)
(* 1. The Software is not used for commercial gain.			*)
(* 2. The user shall not hold the Author liable for any consequences	*)
(*    arising from use of the Software.					*)
(* 									*)
(* The user is granted the right to further distribute the Software	*)
(* provided that both:							*)
(* 1. The Software and this statement of rights is not modified.	*)
(* 2. The Software does not form part or the whole of a system 		*)
(*    distributed for commercial gain.					*)
(* 									*)
(* The user is granted the right to modify the Software for personal or	*)
(* internal use provided that all of the following conditions are	*)
(* observed:								*)
(* 1. The user does not distribute the modified software. 		*)
(* 2. The modified software is not used for commercial gain.		*)
(* 3. The Author retains all rights to the modified software.		*)
(*									*)
(* Anyone seeking a licence to use this software for commercial purposes*)
(* is invited to contact the Author.					*)
(* ---------------------------------------------------------------------*)
(* CONTENTS: conversions for moveing qantifiers about.			*)
(* ---------------------------------------------------------------------*)
(*$Id$*)

signature Pair_conv =
    sig
   type conv = Abbrev.conv

	val NOT_PFORALL_CONV : conv
	val NOT_PEXISTS_CONV : conv
	val PEXISTS_NOT_CONV : conv
	val PFORALL_NOT_CONV : conv
	val PFORALL_AND_CONV : conv
	val PEXISTS_OR_CONV : conv
	val AND_PFORALL_CONV : conv
	val LEFT_AND_PFORALL_CONV : conv
	val RIGHT_AND_PFORALL_CONV : conv
	val OR_PEXISTS_CONV : conv
	val LEFT_OR_PEXISTS_CONV : conv
	val RIGHT_OR_PEXISTS_CONV : conv
	val PEXISTS_AND_CONV : conv
	val AND_PEXISTS_CONV : conv
	val LEFT_AND_PEXISTS_CONV : conv
	val RIGHT_AND_PEXISTS_CONV : conv
	val PFORALL_OR_CONV : conv
	val OR_PFORALL_CONV : conv
	val LEFT_OR_PFORALL_CONV : conv
	val RIGHT_OR_PFORALL_CONV : conv
	val PFORALL_IMP_CONV : conv
	val LEFT_IMP_PEXISTS_CONV : conv
	val RIGHT_IMP_PFORALL_CONV : conv
	val PEXISTS_IMP_CONV : conv
	val LEFT_IMP_PFORALL_CONV : conv
	val RIGHT_IMP_PEXISTS_CONV : conv
    end;
