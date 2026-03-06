## `ttt`

``` hol4
tacticToe.ttt : tactic
```

------------------------------------------------------------------------

General purpose tactic relying on a automatic selection of tactics
extracted from human-written proof scripts. It returns an automatically
generated proof script that solves the goal. A good practice is to
replace the call of `tacticToe.ttt` by the generated proof script.

Select relevant tactics and theorems for proving a goal using the
k-nearest neighbor premise selection algorithm and relies on Monte Carlo
tree search to expand multiple proof trees. In practice, this means that
the intermediate goals created by better ranked tactics are explored
more deeply.

### Failure

Fails if the supplied goal does not contain boolean terms only. Or if
the search saturates, this typically happens when there is not enough
recorded tactics. Or if the search times out. This timeout can be
modifed by `tacticToe.set_timeout`. Or if the proof fails to
reconstruct.

### Example

``` hol4
- load "tttUnfold"; load "tacticToe"; open tacticToe;
(* output omitted *)
> val it = () : unit

- tttUnfold.ttt_record (); (* takes multiple hours the first time it is called *)
(* output omitted *)
> val it = (): unit

- ttt ([],``1+1=2``);
Loading 3091 theorems 
Loading 12126 tactics
tactictoe found a proof:
  (SRW_TAC []) []
> val it = ([], fn): goal list * validation
```

### Comments

See `src/tactictoe/README` for more information on how to record the
tactic data. See more examples in `src/tactictoe/examples`.

### See also

[`tacticToe.tactictoe`](#tacticToe.tactictoe),
[`holyHammer.hh`](#holyHammer.hh)
