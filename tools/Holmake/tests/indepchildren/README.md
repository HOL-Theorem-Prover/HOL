# Buggy behaviour 1

If we have a Holmake called across a bunch of `INCLUDES` (`dir1`, and `dir2` say), and both refer to a `base` then it is possible for the second call not to see `base` when it comes to generating dependency information for things under `dir1`.
When the system tries to load the corresponding thing, you get a failure.

In the wild, this was seen in CakeML, where it was possible to get files failing to include `lprefix_lub` theory as a dependency.

We set up a dependency graph that looks like

                                 ┌────> dir1 ───┐
       base ───> intermediate ───┤              ├───> ultimate
                                 └────> dir2 ───┘

The buggy behaviour fails to give `dir2Theory` its correct dependency on `baseTheory` if `dir1` is built first in the same session, as happens if `Holmake` is called in the directory containing `ultimate`.
If `dir1` and `dir2` are built independently everything works.

# Buggy behaviour 2

You need to also check that the graph above only recurses into `base` (and `intermediate`) once.
The test as written checks for this by having a (phony) makefile rule in `base` that fires on every call, and which creates first a file called `one` and then one called `two`. The existence of `base/two` is checked for in the top-level `Holmakefile`.
