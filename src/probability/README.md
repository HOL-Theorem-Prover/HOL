# HOL's Probability Theory

This directory contains HOL4's Measure, Lebesgue Integration and Probability theories.

## Preliminaries

     extrealScript.sml            * The (extended) theory of extended reals

## Measure, Integration and Probability Theory defined on extended reals

     sigma_algebraScript.sml      * Sigma-algebra and other systems of sets
     real_borelScript.sml         * Borel-measurable sets generated from reals
     measureScript.sml            * Measure Theory defined on extended reals
     borelScript.sml              * Borel sets and Borel measurable functions
     lebesgueScript.sml           * Lebesgue integration based on extended reals
     martingaleScript.sml         * Martingales based on σ-finite filtered measure space
     probabilityScript.sml        * Probability Theory based on extended reals

## Measure, Integration and Probability Theory defined on reals (obsoleted)

NOTE: The legacy measure, integration and probability theories based on finite measures
      are moved to `$(HOLDIR)/examples/probability/legacy`. They are used for building
      some official examples.

## Further extensions

     See `$(HOLDIR)/examples/probability`.
