# Introduction

This work is part of a PhD Dissertation entitled "Formal Dependability Analysis using Higher-order-logic Theorem Proving".
This formaliation is carried out in HOL-latest repo version in mac platform and builds successfully.


List of files included in the project:

Theories | Description
--------- | ----------
 RBDScript.sml|Contains the formalization of RBD configurations
 FT_deepScript.sml|Contains the formalization of FT gates and PIE principle
 AvailabilityScript.sml|Contains the formalization of instantenous and steady availability theory based on FT and RBD
 VDCScript.sml|Formalization about the reliability analysis of virutal data center
 transform_FT_RBDscipt.sml|Lemmas about either way transformation of RBD and FT models
 smart_gridScript.sml|Formalization describing the dependability analysis of smart grid substation
 auto_smart_grid.ml|SML functions for automatic simplification and computation of dependability properties
 WSNScript.sml|Contains the formalization related to reliability analysis of WSN data transport protocol
 frogpScript.sml|Contains the formalization related to reliability analysis of oil and gas pipelines
 ASN_gatewayScript.sml|Formalization of communication gateway software for the next generation air traffic management system
 railwayScript.sml|Formal realiability analysis of railway traction system
 Makefile| Specify some useful options to build specific directory
 Holmakefile| Required to build ``Holmake`` with required dependencies


# Getting Started

For interested readers, the thesis can be found in [link](http://save.seecs.nust.edu.pk/Downloads/wahmad_thesis.pdf).

## Installation

To use the proof script, follow the steps below:

1. Install latest version of HOL by downloading it from  https://hol-theorem-prover.org/ or
(Follow the steps mentioned in http://save.seecs.nust.edu.pk/Downloads/Installation%20of%20HOL%20&%20HOL-LIGHT%20in%20Linux.pdf)
2. Fork and clone the repo ``https://github.com/ahmedwaqar/Formal-Dependability.git``
3. Goto directory folder ``cd Formal-Dependability``
4. Modify ``Makefile`` by specifying the ``HOLDIR`` variable to the path of your ``Holmake`` binary
5. Run ``make``
6. See ``Makefile`` to know specific directory build options

# Contact
Note: For any queries about this project contact:

Waqar Ahmed on email address waqar.ahmad@seecs.nust.edu.pk
