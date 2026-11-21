# Proof traces

The converter turns native proof dumps into portable binary traces. The
merger selects exported theorems and their dependencies for kernel replay.

- [Conversion and target merging](pft-cli.md)
- [Portable PFT format](pft-format.md)
- [HOL4 ruleset](pft-ruleset-hol4.md) and [Candle ruleset](pft-ruleset-candle.md)
- [Native dump layout](tr-format.md)
- [Encountered-bug regressions](tests/README.md)

Replay supports AXIOM commands. Check each target's complete hypotheses
and conclusion, and apply the required axiom policy separately.
