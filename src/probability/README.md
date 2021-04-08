# HOL's Probability Theory

This directory contains HOL4's Measure, Lebesgue integral and Probability theories.

## Preliminaries

     extrealScript.sml            * The theory of extended reals
     real_topologyScript.sml      * Elementary Topology in Euclidean Space (from HOL Light)
     derivativeScript.sml         * Univariate Derivative Theory in R^1 (from HOL Light)
     integrationScript.sml        * Henstock-Kurzweil (gauge) Integral (from HOL Light)

## Measure, Integral and Probability Theory defined on extended reals

     sigma_algebraScript.sml      * Sigma-algebra and other system of sets
     measureScript.sml            * Measure Theory defined on extended reals 
     real_borelScript.sml         * Borel-measurable sets generated from reals 
     borelScript.sml              * Borel sets and Borel measurable functions
     lebesgueScript.sml           * Lebesgue integration theory
     martingaleScript.sml         * Martingales based on σ-finite filtered measure space
     probabilityScript.sml        * Probability Theory based on extended reals

## Measure, Integral and Probability Theory defined on reals

     real_measureScript.sml       * Measure Theory defined on reals
     real_lebesgueScript.sml      * Lebesgue integrals based on reals
     real_probabilityScript.sml   * Probability Theory based on reals

## Utilities

     hurdUtils.{sml|sig}          * Some useful tools originally defined by Joe Hurd
     util_probScript.sml          * Utility lemmas needed by other scripts
     iterateScript.sml            * Generic iterated operations and special cases of sums over N and R
