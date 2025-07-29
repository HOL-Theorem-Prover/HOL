## `ROTATE_LT`

``` hol4
Tactical.ROTATE_LT : int -> list_tactic
```

------------------------------------------------------------------------

Rotates a list of goals

`ROTATE_LT n gl` rotates a goal list `gl` by `n` places. For `n >= 0`,
this means moving the first `n` goals to the end of the list. A negative
`n` means rotating the list in the opposite direction.

### Failure

Never fails.

### Example

To bring the third goal to first position, leaving the others in order,
use

``` hol4
  SPLIT_LT 3 (ROTATE_LT ~1, ALL_LT)
```

### Comments

Using `SPLIT_LT`, `ROTATE_LT` and `REVERSE_LT`, any reordering of a list
of goals is possible.

### See also

[`proofManagerLib.rotate`](#proofManagerLib.rotate),
[`proofManagerLib.r`](#proofManagerLib.r),
[`Tactical.SPLIT_LT`](#Tactical.SPLIT_LT),
[`Tactical.REVERSE_LT`](#Tactical.REVERSE_LT),
[`Tactical.ALL_LT`](#Tactical.ALL_LT)
