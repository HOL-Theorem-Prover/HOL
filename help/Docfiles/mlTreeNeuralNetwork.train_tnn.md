## `train_tnn`

``` hol4
mlTreeNeuralNetwork.train_tnn : schedule -> tnn -> tnnex * tnnex -> tnn
```

------------------------------------------------------------------------

Train a tree neural network (TNN) on a set of examples via
backpropagation to minimize mean square error.

Hyperparameters such as batch size, learning rate and number of epochs
can be set in the schedule arguments. The initial TNN can be constructed
by calling `mlTreeNeuralNetwork.random_tnn`. Examples consists of a term
`t` and a list `l`. The term `t` is expected to be lambda-free with each
operator appearing with a unique arity. The list `l` is expected to be a
list of real numbers between 0 and 1. In the case of a simple objective
each example `(t,l)` is to be written as `[(h(t),l)]` where `h` is a
variable representing the head network. For multiple objectives, one can
write `[(h1(t),l1),...,(hn(t),ln)]` for a single example. The created
list of examples is to be split into a training set and a test set
(possibly empty).

### Failure

Fails when dimension constraints are not respected (see
`mlTreeNeuralNetwork.random_tnn`) or a variable/constant from the
examples is not defined in the TNN.

### Comments

See the end of the file
`src/AI/machine_learning/mlTreeNeuralNetwork.sml` for a toy example.

### See also

[`mlTreeNeuralNetwork.random_tnn`](#mlTreeNeuralNetwork.random_tnn)
