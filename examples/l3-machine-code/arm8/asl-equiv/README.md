Armv8 ISA specification equivalence proof.

Relates the L3 model to a model derived from Arm ASL, see:

- [Arm Exploration Tool](https://developer.arm.com/architectures/cpu-architecture/a-profile/exploration-tools)
- [MRA tool](https://github.com/alastairreid/mra_tools)
- [ASL Interpreter](https://github.com/alastairreid/asl-interpreter)
  (historical repository; now redirects to ISA Tools)
- [ASL to Sail](https://github.com/rems-project/asl_to_sail)
- [Sail](https://github.com/rems-project/sail)

A pre-generated HOL4 snapshot of the ASL model is available from
[armv8.6-asl-snapshot](https://github.com/HOL-Theorem-Prover/armv8.6-asl-snapshot).
Fetch the revision pinned by this directory's script with:

```shell
$ ./get-armv8.6-hol-snapshot
```

The script creates the separate, Git-ignored `armv8.6-asl-snapshot` checkout.
Its generated definitions are in `A64_ISA_v86A/armv86aScript.sml`.

With a built Poly/ML HOL4 installation, build from this directory with:

```shell
$ Holmake all
```

Holmake runs the fetch script automatically if the snapshot directory is
absent. The script requires Git, Perl and Python 3 and creates a new checkout;
run it explicitly only when that directory does not already exist. It also
disables the snapshot's oversized generated signature documentation.

The fetch script also corrects 14 reversed half-way comparisons in the
snapshot's nearest-rounding paths: `error <= 0.5` becomes `error > 0.5`,
with the existing tie tests retained. Without this correction, for example,
`FPToFixed` converts exact zero to integer one in ties-to-even mode.
The correction covers `FPRoundBase`, `FPRoundInt`, `FPRoundIntN` and
`FPToFixed`; it leaves NaN selection unchanged.

The script also corrects field extraction in 18 floating-point conversion
decoder blocks. These blocks bind a three-bit local `opcode` before reading
`rmode`, `ftype` and `sf`, so those fields incorrectly come from the truncated
value. The correction reads those fields before binding the local opcode.
For example, without it, `FMOV D0,X0` (`0x9E670000`) selects a 32-bit transfer
and loses the upper half of `X0`. The pinned revision stays unchanged; the
corrections apply to the working copy of the generated HOL definitions.

The floating-point part of `state_rel` relates each L3 `FP_REG` to the low
64 bits of the corresponding ASL `Z` register. It relates `FPCR` and `FPSR`
exactly, and permits arbitrary register contents, including NaN encodings.
The system-register assumptions enable FP access without trapping.

The L3 `CheckFP` permits only the rounding-mode bits (22 and 23) to be set
in FPCR: `FPCR && ~0x00C00000w = 0w`. Other settings raise an L3 exception.
The instruction relation `l3_models_asl_instr` requires a valid encoding and
compares execution from related states satisfying `asl_sys_regs_ok`, provided
the L3 execution finishes without an exception.

`FPUnpack64_no_flush` covers binary64 unpacking with flush-to-zero disabled.
`FPRound64` relates rounding of nonzero real inputs in all four L3 modes,
including exception flags, with the other FPCR controls clear.
`FPAdd64`, `FPSub64`, `FPMul64`, `FPDiv64` and `FPSqrt64` cover all binary64
inputs under the supported FPCR controls, with bit-equal results: the L3
model's `FPNaNResult` follows the ASL's NaN propagation. There are exact
`l3_models_asl_instr` theorems for every modelled floating-point instruction
family except FMADD. The general-register transfer theorems use the matching
width bit: `sf = 0w` for 32-bit transfers and `sf = 1w` for 64-bit transfers.

`FPCompare64` and `l3_models_asl_FCompare` give exact comparison and sticky
FPSR correspondence, including signalling NaNs. The exact conversion
theorems `l3_models_asl_FToInt32` and `l3_models_asl_FFromInt32` cover conversion
to and from signed 32-bit integers. `FToInt32` rounds ties to even, saturates
out-of-range results and updates the invalid-operation and inexact flags.
`FFromInt32` is exact for every signed 32-bit input and preserves FPSR;
integer zero converts to positive floating-point zero in every rounding mode.
Register-transfer and sign-bit instruction theorems preserve every input bit
they are specified to copy, including NaN payloads.
