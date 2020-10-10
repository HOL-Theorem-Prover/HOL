
# Number Theory of Fermat

These folders for number theories contain interesting proofs of theorems stated by Fermat.

## Fermat's Little Theorem
* __little__ includes the source code for the paper `A String of Pearls: Proofs of Fermat's Little Theorem`.
    * `little/necklace`, necklaces with colours.
    * `little/cycle`, cycle operation on lists.
    * `little/pattern`, cycle patterns, period and order.
    * `little/FLTnecklace`, proof using necklace cycles and patterns.
    * `little/FLTaction`, proof using group action on necklace cycles.
    * `little/FLTnumber`, proof using modular arithmetic only.
    * `little/FLTgroup`, proof using the modulo group of primes.
    * `little/FLTeuler`, proof using the modulo group of coprimes.
    * `little/FLTbinomial`, proof using prime binomial expansion.
    * `little/FLTfixedpoint`, proof using action fixed points on necklaces.
    * `little/FLTpetersen`, proof by Julius Petersen, formalised in HOL4.

## Fermat's Two Squares Theorem
* __twosq__ includes the source code for the paper `Windmills of the minds: an algorithm for Fermat's Two Squares Theorem`.
    * `twosq/helper`, useful library theorems.
    * `twosq/involute`, basic involution.
    * `twosq/involuteFix`, fixed points of involution.
    * `twosq/involuteAction`, group action with involution.
    * `twosq/iterate`, function iteration and period.
    * `twosq/iterateCompose`, iteration of composition of involutions.
    * `twosq/iterateCompute`, iteration period computation.
    * `twosq/windmill`, windmills and their involutions.
    * `twosq/twoSquares`, rework of a proof by Don Zagier, formalised in HOL4.

