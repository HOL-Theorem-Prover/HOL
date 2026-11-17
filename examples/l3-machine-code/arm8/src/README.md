ARMv8 L3 sources
================

The base and instruction sources originate from Anthony Fox's
[2019-11-04 ISA model release](https://acjf3.github.io/l3/isa-models.tar.bz2).
See COPYRIGHT. The release omits the encoding sources: v8-encode.spec
restores these from the HOL repository's existing generated arm8Script.sml.
Before adding floating point, the restored sources reproduced every existing
HOL definition exactly (the generated timestamp and final newline differ).
CountTrailing.tac contains the existing recursion termination argument.

Build [L3 2018-02-09](https://acjf3.github.io/l3/l3.tar.bz2) with `make`,
then run:

```
L3=/path/to/L3-2018-02-09/bin/l3 ./generate
cd ../model
Holmake arm8Theory.uo
```

`generate` exports all model definitions from L3. It retains the current
arm8Lib wrapper because L3's original wrapper template predates HOL's
Import.gen_inventory API. It does not regenerate the separate ML assembler,
whose parsing/printing sources were also omitted from the release.

v8-fp.spec adds scalar binary64 instructions and 32/64-bit general-register
transfers. FPCR rounding modes are supported, while trapping exceptions,
flush-to-zero, default-NaN and other FPCR controls are outside this partial
model and produce an unsupported-control exception. NaN results follow
the ASL: the first signalling NaN operand (quietened), else the first quiet
NaN operand, else the default NaN. FPSR cumulative IEEE
exception flags are maintained. The scalar FP register bank abstracts away
the upper 64 bits of SIMD registers. Integer conversion saturates on invalid
input. SIMD, binary16, and binary32 arithmetic remain unsupported.

The decoder and e_fp encode FMOV, FABS, FNEG, FSQRT, FADD, FSUB, FMUL, FDIV,
FMADD, FCMP, FCVTNS Wd,Dn and SCVTF Dd,Wn. CakeML's FPToInt/FPFromInt use the
reserved integer temporary x26 to transfer signed 32-bit results/inputs
between the FP and integer register banks.

Local regression checks use independently assembled opcode fixtures against
both Encode and Decode, register 31, signed-zero and NaN comparisons, and
32-bit transfers that must clear the upper half of the modeled FP register.
The fixtures were cross-checked with LLVM's `llvm-mc -triple=aarch64
-show-encoding`. These checks use proof-producing HOL conversions; the diagnostic scripts are
not part of the checked-in model sources.
