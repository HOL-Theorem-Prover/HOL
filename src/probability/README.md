# HOL's Probability Theory

This directory contains HOL4's Measure, Lebesgue integral and Probability theories.

## Preliminaries

     sigma_algebraScript.sml      * Sigma algebra and other system of sets
     extrealScript.sml            * The theory of extended reals
     real_topologyScript.sml      * Elementary Topology in Euclidean Space (from HOL Light)

## Measure, Integral and Probability Theory defined on extended reals

     measureScript.sml            * Measure Theory defined on extended reals
     borelScript.sml              * Borel sets and Borel measurable functions
     lebesgueScript.sml           * The theory of Lebesgue Integral
     martingaleScript.sml         * The theory of martingales based on σ-finite filtered measure space
     probabilityScript.sml        * Probability Theory based on extended reals

## Measure, Integral and Probability Theory defined on reals

     real_measureScript.sml       * Measure Theory defined on reals
     real_borelScript.sml         * Borel measurable sets generated from reals
     real_lebesgueScript.sml      * The theory of Lebesgue Integral based on reals
     real_probabilityScript.sml   * Probability Theory based on reals

## Utilities

     hurdUtils.{sml|sig}          * Some useful tools originally defined by Joe Hurd
     util_probScript.sml          * Utility lemmas needed by other scripts
     iterateScript.sml            * Generic iterated operations and special cases of sums over N and R
     productScript.sml            * Products of natural numbers and real numbers
