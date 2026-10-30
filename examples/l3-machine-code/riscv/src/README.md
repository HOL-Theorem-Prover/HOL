# L3 source of the RISC-V model

`riscv.spec` is the L3 specification from which everything in `../model` is
generated:

| Generated file | Export | Used by |
|---|---|---|
| `riscvScript.sml`, `riscvLib.sml`, `riscvLib.sig` | `HolExport.spec ("riscv.spec", "riscv")` | HOL4 (`riscvTheory`, the step, prog and decompiler libraries) |
| `riscv.sml`, `riscv.sig` | `SMLExport.spec ("riscv.spec", "riscv nointinf")` | the standalone SML emulator |

`checkDelegation.sml` is a hand-written HOL termination proof that the export
splices in for the `measure`-recursive function `checkDelegation`; L3 reads it
from the current directory, so both exports must run from here.

## Regenerating

Install L3-2018-02-09 (https://acjf3.github.io/l3/, `l3.tar.bz2`; `make` with
Poly/ML 5.7 or later), put its `bin` on `PATH`, then

```
make          # regenerate ../model
make check    # regenerate into a temporary directory and diff against ../model
```

`make check` is the test that the committed files are exactly what the spec
produces: it ignores only the timestamp on the first line. Two patches are
applied to L3's raw output and are part of what is committed: a trailing
newline, and `numLib.temp_prefer_num` instead of `numLib.prefer_num` in
`riscvLib.sml` (HOL commit `0a75ce84c`; the generator still emits the old name).

Commit the spec and the regenerated files together, one change per commit.
