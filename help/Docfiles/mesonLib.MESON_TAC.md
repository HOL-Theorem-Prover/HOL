## `MESON_TAC`

``` hol4
mesonLib.MESON_TAC : thm list -> tactic
```

------------------------------------------------------------------------

Performs first order proof search to prove the goal, using the given
theorems as additional assumptions in the search.

`MESON_TAC` performs first order proof using the model elimination
algorithm. This algorithm is semi-complete for pure first order logic.
It makes special provision for handling polymorphic and higher-order
values, and often this is sufficient. It does not handle conditional
expressions at all, and these should be eliminated before `MESON_TAC` is
applied.

`MESON_TAC` works by first converting the problem instance it is given
into an internal format where it can do proof search efficiently,
without having to do proof search at the level of HOL inference. If a
proof is found, this is translated back into applications of HOL
inference rules, proving the goal.

The feedback given by `MESON_TAC` is controlled by the level of the
integer reference variable `mesonLib.chatting`. At level zero, nothing
is printed. At the default level of one, a line of dots is printed out
as the proof progresses. At all other values for this variable,
`MESON_TAC` is most verbose. If the proof is progressing quickly then it
is often worth waiting for it to go quite deep into its search. Once a
proof slows down, it is not usually worth waiting for it after it has
gone through a few (no more than five or six) levels. (At level one, a
"level" is represented by the printing of a single dot.)

### Failure

`MESON_TAC` fails if it searches to a depth equal to the contents of the
reference variable `mesonLib.max_depth` (set to 30 by default, but
changeable by the user) without finding a proof. Shouldn't fail
otherwise.

`MESON_TAC` can only progress the goal to a successful proof of the
(whole) goal or not at all. In this respect it differs from tactics such
as simplification and rewriting. Its ability to solve existential goals
and to make effective use of transitivity theorems make it a
particularly powerful tactic.

### Comments

The assumptions of a goal are ignored when `MESON_TAC` is applied. To
include assumptions use `ASM_MESON_TAC`.

### See also

[`mesonLib.ASM_MESON_TAC`](#mesonLib.ASM_MESON_TAC),
[`mesonLib.GEN_MESON_TAC`](#mesonLib.GEN_MESON_TAC)
