Bug is the following sequence of steps:

1.  `thy1` is built in the current directory
2.  `heap` is built in `dir2`, incorporating `../thy1Theory`, but without using an `INCLUDES` line in the `Holmakefile` to see the parent explicitly.
3.  Result is that
    - `thy2Theory.sml` is created, with a dependency on  `thy1` (in the leading `link_parents` block);
    - `thy2Theory.uo` is created, but because the dependency analysis performed on `thy2Theory.sml` can’t see `thy1Theory` anywhere, the `thy1Theory` dependency is not recorded and dynamically loading `thy2Theory` will fail.
