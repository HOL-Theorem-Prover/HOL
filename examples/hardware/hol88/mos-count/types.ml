% PROOF		: Transistor Implementation of a Counter		%
% FILE		: types.ml						%
%									%
% DESCRIPTION	: Defines type abreviations for CMOS circuits.		%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 31 March 1987						%

let val = ":num";;
let time = ":num";;
let posn = ":num";;
let vec = ":^posn->^val";;
let wire = ":^time->^val";;
let bus = ":^time->^vec";;
let word = ":^posn->bool";;
let boolsig = ":^time->bool";;
let wordsig = ":^time->^word";;
let numsig = ":^time->num";;
