structure ctlSyntax =
struct

local 

open Globals HolKernel Parse

open bossLib
open pairTheory
open pred_setTheory
open pred_setLib
open stringLib
open listTheory
open simpLib
open pairSyntax 
open pairLib
open PrimitiveBddRules
open DerivedBddRules
open Binarymap
open PairRules
open pairTools
open setLemmasTheory
open boolSyntax
open Drule
open Tactical
open Conv
open Rewrite
open Tactic
open bddTools
open stringBinTree
open ctlTheory
open boolTheory
open ksTools
open holCheckTools

in 

infixr 5 C_AND

fun (l C_AND r) = ``C_AND2 (^l) (^r)``


fun list_C_AND l = 
if (List.null l) then ``C_BOOL B_TRUE`` 
else if (List.null (List.tl l)) then (List.hd l)
else (List.hd l) C_AND (list_C_AND (List.tl l))

fun C_OR(l,r) = ``C_OR2 (^l) (^r)``
infixr 5 C_OR

fun list_C_OR l = 
if (List.null l) then ``C_BOOL B_FALSE`` 
else if (List.null (List.tl l)) then (List.hd l)
else (List.hd l) C_OR (list_C_OR (List.tl l))

val C_T = ``C_BOOL B_TRUE``
val C_F = ``C_BOOL B_FALSE``

fun C_NOT tm = ``C_NOT ^tm``

fun C_IMP(l,r) = ``C_IMP2 ^l ^r``
infixr 2 C_IMP;

fun C_AX tm = ``C_AX ^tm``;

fun C_AG tm = ``C_AG ^tm``
fun C_EG tm = ``C_EG ^tm``
fun C_EF tm = ``C_EF ^tm``
fun C_AF tm = ``C_AF ^tm``
fun C_AU(l,r) = ``C_AU(^l,^r)`` 
infixr 1 C_AU;

fun C_IFF(l,r) = ``C_IFF (^l) (^r)``
infix C_IFF;

fun C_AP state p = ``C_BOOL (B_PROP ^(ksTools.mk_AP state p))``;

end 
end