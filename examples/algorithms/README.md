Assorted algorithms.

[spt_closure](spt_closureScript.sml):
Implementation and proof of correctness of a reachability/closure operation over
`num_set num_maps`.

[topological_sort](topological_sortScript.sml):
A topological-sort-like partitioning algorithm, using sptrees under-the-hood and
relying on [spt_closure](spt_closureScript.sml).
Strictly speaking this is not a topological sort because it allow cycles in the
dependencies.
The implementation is a divide-and-conquer algorithm.
