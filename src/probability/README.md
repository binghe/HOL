# HOL's Probability Theory

This directory contains HOL4's Measure, Lebesgue integral and
Probability theories.

## Measure, Integral and Probability Theory defined on extended reals (new)

     extrealScript.sml     * The theory of Extended Real Numbers
     measureScript.sml     * Measure Theory defined on extended reals
     borelScript.sml       * Borel sets and Borel measurable functions
     lebesgueScript.sml    * The theory of Lebesgue Integral
     martingaleScript.sml  * The theory of martingales based on σ-finite filtered measure space
     probabilityScript.sml * Probability Theory (toplevel)

## Measure and Probability Theory defined on reals (old)

     real_measureScript.sml
     real_borelScript.sml
     real_lebesgueScript.sml
     real_probabilityScript.sml

(These old scripts are used by `examples/miller` and `examples/diningcryptos`)

## Elementary Topology in Euclidean Space (from hol-light)

     real_topologyScript.sml

## Utilities

     hurdUtils.{sml|sig}   * some useful tools created by Joe Hurd
     util_probScript.sml   * utility lemmas needed by other scripts
     iterateScript.sml     * utility theory used by real_topologyScript.sml
     productScript.sml     * utility theory used by real_topologyScript.sml

## Contributors

- Valentina Bruno (hol-light)
- Aaron Coble
- John Harrison (hol-light)
- Osman Hasan
- Joe Hurd
- Marco Maggesi (hol-light)
- Tarek Mhamdi
- Muhammad Qasim
- Sofiene Tahar
- Chun Tian
