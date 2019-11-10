
# AKS Machine Library

The machine model is based on a simulation of CPU with machine codes,
estimating the number of steps to run the AKS algorithm in this machine.

## Machine Model
* __countMonad__, a monad keeping track of computational values and counts.
* __countMacro__, fundamental operations and macro for subroutines.

## Simple Arithmetic
* __countBasic__, basic arithmetic algorithms in monadic style.
* __countPower__, exponentiation, root extraction and power free test.
* __countPrime__, traditional primality testing algorithm.

## Modulo Arithmetic
* __countModulo__, modulo arithmetic algorithms in monadic style.
* __countOrder__, multiplicative order by sequential search.
* __countParam__, search for the parameter suitable for AKS algorithm.

## Modulo Polynomial
* __countPoly__, polynomial computations in Z_n[X] with modulus (X\^k - 1).
* __countAKS__, combining various components for the AKS algorithm.
