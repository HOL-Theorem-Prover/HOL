## `random_tnn`

``` hol4
mlTreeNeuralNetwork.random_tnn : (term * int list) list -> tnn
```

------------------------------------------------------------------------

Creates a random tree neural network (TNN) with the precised dimensions
for each neural network operators.

To create an initial TNN, the user first needs to gather all operators
(constants or variables) appearing in the examples. Then, given an
embedding dimension `d`, for each operator `f` with arity `a` the list
of dimensions of is to be defined as `[a x d,u1,...,uk,d]`. The natural
numbers `u1,...,uk` are sizes of the intermediate layers that can be
freely chosen by the user. In the case of a head operator `h`, the input
dimension is to be `d` and the output dimension is to be the length of
the objective `l`.

### Failure

Fails if the list of dimensions is empty.

### Example

``` hol4
- val tnn = 
    random_tnn [(``h: bool -> bool``,[4,10,1]),(``$~``,[4,8,4]),(F,[0,4])];
> val tnn = <Redblackmap(3)>: tnn
```

### Comments

Precising a list of dimensions of length 1 results in an unusable empty
neural network for this operator.

### See also

[`mlTreeNeuralNetwork.train_tnn`](#mlTreeNeuralNetwork.train_tnn)
