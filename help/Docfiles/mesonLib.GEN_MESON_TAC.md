## `GEN_MESON_TAC`

``` hol4
mesonLib.GEN_MESON_TAC : int -> int -> int -> thm list -> tactic
```

------------------------------------------------------------------------

Performs first order proof search to prove the goal, using both the
given theorems and the assumptions in the search.

`GEN_MESON_TAC` is the function which provides the underlying
implementation of the model elimination solver used by both `MESON_TAC`
and `ASM_MESON_TAC`. The three integer parameters correspond to various
ways in which the search can be tuned.

The first is the minimum depth at which to search. Setting this to a
number greater than zero can save time if its clear that there will not
be a proof of such a small depth. `ASM_MESON_TAC` and `MESON_TAC` always
use a value of 0 for this parameter.

The second is the maximum depth to which to search. Setting this low
will stop the search taking too long, but may cause the engine to miss
proofs it would otherwise find. The setting of this variable for
`ASM_MESON_TAC` and `MESON_TAC` is done through the reference variable
`mesonLib.max_depth`. This is set to 30 by default, but most proofs do
not need anything like this depth.

The third parameter is the increment used to increase the depth of
search done by the proof search procedure.

The approach used is iterative deepening, so with a call to

``` hol4
  GEN_MESON_TAC mn mx inc
```

the algorithm looks for a proof of depth `mn`, then for one of depth
`mn + inc`, then at depth `mn + 2 * inc` etc. Once the depth gets
greater than `mx`, the proof search stops.

### Failure

`GEN_MESON_TAC` fails if it searches to a depth equal to the second
integer parameter without finding a proof. Shouldn't fail otherwise.

The construction of tailored versions of `MESON_TAC` and
`ASM_MESON_TAC`.

### See also

[`mesonLib.ASM_MESON_TAC`](#mesonLib.ASM_MESON_TAC),
[`mesonLib.MESON_TAC`](#mesonLib.MESON_TAC)
