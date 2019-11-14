
# AKS formalisation

The mechanisation of the AKS Algorithm is supported
by the development of various underlying theories:

## AKS Theories
* __theory__ for the theoretical basis of the AKS Main Theorem.
    * `theory/AKSintro`, introspective relation essential to the AKS proof.
    * `theory/AKSshift`, shifting introspective relation between rings.
    * `theory/AKSsets`, sets involved in the AKS proof.
    * `theory/AKSmaps`, mappings involved in the AKS proof.
    * `theory/AKStheorem`, the main theorem in the AKS proof.
    * `theory/AKSrevised`, revise the AKS proof for a general AKS parameter.
    * `theory/AKSimproved`, improve the bound constants in the AKS proof.
    * `theory/AKSclean`, a clean rewrite of the AKS proof.

## AKS Computations
* __compute__ for a computational study of the AKS algorithm.
    * `compute/computeInteger`, computations of `ulog`, the round-up value of logarithm to base 2.
    * `compute/computeBasic`, computations of `exp` and `root`, powers and integer roots.
    * `compute/computeOrder`, computation of `order`, the modular multiplicative order.
    * `compute/computeParam`, computation of an AKS parameter.
    * `compute/computePoly`, polynomial computations with modulus of `unity` of index k.
    * `compute/computeRing`, modulo polynomial computations in ring Z\_n.
    * `compute/computeAKS`, polynomial checks and all part of the AKS algorithm.

## AKS Machine and Codes
* __machine__ for a computational complexity analysis of the AKS algorithm.
    * `machine/countMonad`, a monad to track computational values and counts.
    * `machine/countMacro`, macro operations as subroutines in monadic style.
    * `machine/countBasic`, basic arithmetic functions in monadic style.
    * `machine/countModulo`, modulo arithmetic in monadic style.
    * `machine/countPower`, exponentiation, root extraction and power free test.
    * `machine/countPrime`, traditional primality testing algorithm.
    * `machine/countOrder`, modular exponentiation and multiplicative order.
    * `machine/countParam`, parameter search for AKS algorithm.
    * `machine/countPoly`, polynomial algorithmes for AKS algorithm.
    * `machine/countAKS`, combine with polynomial checks for AKS algorithm.
