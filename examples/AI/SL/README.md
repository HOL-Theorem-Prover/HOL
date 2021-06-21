Below are instructions for the experiments accompanying the paper
Tree Neural Networks in HOL4.
The implementation of Tree Neural Networks (TNN) can be found under the 
`src/AI/machine_learning` directory.

## HOL4 install
1) Install PolyML and install HOL (see HOL/INSTALL file).
2) In the examples/AI_TNN directory (this directory) run `Holmake`
3) In the same directory, launch an interactive session by calling:
   `rlwrap ../../bin/hol` (or just `../../bin/hol`).

##Arithmetical expression evaluation
To train and test the TNN on the arithmetic datasets, 
first copy the folder `data_arith` 
from the repository `https://github.com/barakeel/arithmetic_dataset`
to `HOL/examples/AI_TNN/data_arith`.
Then run the following interactive commands:
    load "mleArith"; open mleArith;
    val tnn = train_fixed ();
    val r = test_fixed tnn;

##Propositional truth estimation
To train and test the TNN on the propositional datasets, 
first copy and rename the folder `data` 
from the repository `https://github.com/deepmind/logical-entailment-dataset`
to `HOL/examples/AI_TNN/data_entail`.
Then run the following interactive commands:
    load "mleEntail"; open mleEntail;
    val tnn = train_fixed ();
    val r = test_fixed tnn;
