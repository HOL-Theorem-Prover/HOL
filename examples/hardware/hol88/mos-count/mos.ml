% PROOF		: Transistor Implementation of a Counter		%
% FILE		: mos.ml						%
%									%
% DESCRIPTION	: Defines MOS primitives based on a four-valued		%
%		  logic where Zz and Er represent low impedence		%
%		  (or floating) and undefined/unknown respectively.	%
%		  Not is a negation function in the four-valued		%
%		  logic and U is the least upper bound function.	%
%									%
%		  The MOS primitives were originally motivated by	%
%		  models used by Inder Dhingra described in "Formal	%
%		  Validation of an Integrated Circuit Design Style",	%
%		  Hardware Verification Workshop, University of		%
%		  Calgary, January 1987, however, the transistor	%
%		  models differ slightly.				%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 31 March 1987						%

new_theory `mos`;;

loadt `misc`;;
loadt `types`;;

new_constant (`Er`,":^val");;
new_constant (`Hi`,":^val");;
new_constant (`Lo`,":^val");;
new_constant (`Zz`,":^val");;

let val_not_eq_ax = new_axiom (
	`val_not_eq_ax`,
	"((Er = Hi) = F) /\ ((Er = Lo) = F) /\ ((Er = Zz) = F) /\
	  ((Hi = Er) = F) /\ ((Hi = Lo) = F) /\ ((Hi = Zz) = F) /\
	  ((Lo = Er) = F) /\ ((Lo = Hi) = F) /\ ((Lo = Zz) = F) /\
	  ((Zz = Er) = F) /\ ((Zz = Hi) = F) /\ ((Zz = Lo) = F)");;

let Not = new_definition (
	`Not`,
	"Not v = (v = Hi) => Lo | ((v = Lo) => Hi | Er)");;

let U = new_infix_definition (
	`U`,
	"U (x:^val) (y:^val) =
	  ((x = y) => x |
	    (x = Zz) => y | (y = Zz) => x | Er)");;

let Vdd = new_definition (`Vdd`,"Vdd (o:^wire) = !t. o (t) = Hi");;

let Gnd = new_definition (`Gnd`,"Gnd (o:^wire) = !t. o (t) = Lo");;

let Ptran = new_definition (
	`Ptran`,
	"Ptran (g:^wire,i:^wire,o:^wire) =
	  !t. o t = (g t = Lo) => i t | ((g t = Hi) => Zz | Er)");;

let Ntran = new_definition (
	`Ntran`,
	"Ntran (g:^wire,i:^wire,o:^wire) =
	  !t. o t = (g t = Hi) => i t | ((g t = Lo) => Zz | Er)");;

let Join = new_definition (
	`Join`,
	"Join (i1:^wire,i2:^wire,o:^wire) = !t. o t = (i1 t U i2 t)");;

let Cap = new_definition (
	`Cap`,
	"Cap (i:^wire,o:^wire) = !t. o t = (~(i t = Zz)) => i t | i (t-1)");;

close_theory ();;
