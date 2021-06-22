Below are instructions for the experiments accompanying the paper
Deep Reinforcement Learning for Term Synthesis. 
The framework can be found under the `src/AI` directory

## HOL4 install
1) Install PolyML and install HOL (see HOL/INSTALL file).
2) In the examples/AI/RL sub-directories run `Holmake`
3) In the same sub-directory, launch an interactive session by calling:
   `rlwrap ../../../bin/hol` (or just `../../../bin/hol`).

## Training
To run the training, first modify the file `fooSynt.sml` to choose the number of cores by modifying the field ncore (default = 30).
You can choose your experiment name `your_expname` by modifying the field expname.
The results of the experiment will be stored under `eval/your_expname/log`:

    val rlparam =
    {expname = "experiment_name", exwindow = 200000,
     ncore = 30, ntarget = 200, nsim = 32000, decay = 1.0}

Download the training problems from and copy the combin_target folder
(and dioph_target) in the respective `examples/AI/RL` sub-directories.
Launch hol (rlwrap bin/hol or bin/hol) and execute the following commands 
to start training:

    load "aiLib"; open aiLib;
    load "mlReinforce"; open mlReinforce;
    load "mleCombinLib"; open mleCombinLib;
    load "mleCombinSynt"; open mleCombinSynt;
    val targetl = import_targetl "train";
    val targetd = mk_targetd targetl
    val r = rl_start (rlobj,extsearch) targetd;

## Final evaluation (todo)
It is possible to choose the TNN generation number by modifying the number 318 to the desired generation in the following command:
 
    val tnn = mlReinforce.retrieve_tnn rlobj 318;
