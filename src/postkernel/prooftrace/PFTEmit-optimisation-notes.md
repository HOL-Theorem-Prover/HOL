# PFTEmit optimisation notes

Context: the current Candle emitter appears to replay broadly correctly. Candle compute setup has been split into a standalone compute preamble, so per-theory Candle PFT emission is now parallel-friendly in principle. These are potential performance / trace-size / clarity improvements to consider later. They are not currently implemented here.

## Lowest-risk trace-size and replay-speed improvements

### 1. Memoize common theorem commands

The Candle translation repeatedly emits identical theorem derivations. Since theorem IDs are immutable, many pure theorem commands can be safely memoized.

Candidates:

- `c_refl tm` keyed by `tm`
- `c_beta app_tm` keyed by `app_tm`
- `c_inst th subst` keyed by `(th, subst)`
- `c_inst_type th tysubst` keyed by `(th, tysubst)`
- possibly `do_beta_reduce (lam_tm, arg_tm)` keyed by `(lam_tm, arg_tm)`

Expected benefits:

- smaller traces
- faster replay
- faster PFTEmit execution

Likely high-value repeated pro-formas:

- `candle$MP`
- `candle$CONJ`
- `candle$CONJUNCT1`
- `candle$CONJUNCT2`
- `candle$EQT_INTRO`
- `candle$GEN`
- `candle$SPEC`
- `candle$EXISTS`
- `candle$CHOOSE`

Implementation caution: keys should use exact integer IDs and exact substitution-list order, unless a deliberate canonicalisation is added.

## Logical derivation improvements

### 2. Avoid unnecessary SUBST alpha bridge

The SUBST fix freshens binders under `ABS_THM` and then always bridges back to the original result names:

```sml
val conv_th = rconv [] source_id template_id
val result_id = tm concl_ptr
val conv_to_result = c_trans conv_th (c_refl result_id)
in r_eq_mp conv_to_result c_th end
```

This is safe but adds one `REFL` and one `TRANS` per SUBST proof.

Possible optimisation: make `rconv` return `(th_id, freshened)` and only bridge when freshening actually occurred.

Risk: touches delicate SUBST code; do after simpler memoization.

### 3. SUBST subtree skipping

Current `SUBST_prf` recursively descends through compound template terms even when no substitution variable occurs in a subtree. This is necessary in general because structural equality of source/template does not imply no substitution applies below, but if occurrence analysis proves no redex occurs below a subtree, we can return `REFL subtree` immediately.

Possible approach:

- Precompute the set of substitution redex variable IDs.
- Define `contains_redex_under_binders` / occurrence analysis on PFT terms.
- In `rconv`, before descending into COMB/ABS, if the template subtree contains no relevant redex, return `c_refl src_id` / `c_refl tmpl_id` when appropriate.

Expected benefit: substantially smaller traces for large SUBST templates.

Caution: must respect binders/shadowing exactly as current `binder_map` logic does.

### 4. Stronger preamble pro-formas

Many helpers reconstruct standard derived rules from small Candle core steps. Adding more tailored saved theorems to the Candle preamble could collapse repeated derivations.

High-impact candidates:

- `do_MP`
- `do_DISCH`
- `do_GEN`
- `do_SPEC`
- `do_EXISTS`
- `CHOOSE`-related helpers
- beta-specialisation helpers

Example: `do_SPEC` currently instantiates `SPEC`, performs MP, beta-reduces predicate application, and uses `EQ_MP`. A stronger pro-forma closer to `∀x. P x ==> P t` could reduce several commands per specialization.

Most promising high-frequency helper: `do_MP`, since it appears widely and currently uses `DEDUCT_ANTISYM_RULE` + `EQ_MP` plumbing.

## Code simplification / clarity improvements

### 5. Keep GENL_prf simple

The older fresh-binder GENL implementation was simplified back to using the actual conclusion structure rather than generating fresh binders and manually reconstructing foralls. This should remain simpler and produce fewer synthetic `pft%` names.

`pft_rename_free` is still useful for SUBST alpha-freshening. Despite the name, it is an internal free-occurrence replacement helper, not related to the removed PFTRename post-processing tool.

### 6. Document raw/capture-unsafe PFT substitution

`pft_subst_tm` performs raw structural replacement under binders. This is appropriate only when the caller has ensured no capture/shadowing issue. Consider documenting or renaming it to make this clear.

`pft_rename_free` is the safer free-occurrence replacement helper.

### 7. Consistent structural access helpers

Use `tm_part1_of` / `tm_part2_of` in structural walkers over arbitrary terms, because VAR/CONST IDs may not have corresponding `tm_part` array entries.

Use partial destructors like `pft_dest_comb` / `pft_dest_abs` only when the caller has an invariant that the term is compound.

### 8. Potential future helper for safe ABS_THM under hypotheses

The SUBST fix hand-inlines a useful pattern:

1. choose fresh synthetic binder
2. alpha-rename bodies to the fresh binder
3. apply `ABS_THM` to the fresh binder
4. bridge back to desired bound names if needed

If similar failures occur in other derived translations, factor this into a helper to avoid repeating subtle logic.

Potential future sites to revisit if replay fails:

- `Def_spec_prf` congruence: `else c_abs f (cong x)`
- `GEN_ABS_prf` c_abs sites

## Larger / higher-risk possibilities

### 9. Def_spec_prf and Def_tyop_prf preamble support

These are large hand-written derivations. If they dominate trace size, consider moving more of their logical work into Candle preamble theorems.

`Def_tyop_prf` in particular reconstructs substantial type-definition infrastructure manually. A more targeted preamble lemma could reduce trace size, but this is higher-risk and should be done only after profiling.

### 10. Always-fresh heap lambda binders for simplicity

The current emitter tries to preserve plain binder names when safe using heap/PFT free-variable analysis. If simplicity is preferred over nicer names, this machinery could be removed by always using fresh binder names for emitted heap `Abs` terms.

Tradeoff:

- simpler and more robust PFTEmit code
- more `pft%` names in output

Given the current goal of avoiding `pft%` names where possible, keep the existing analysis unless it causes issues. The `pft%` fallback names themselves are still intentional; what has been removed is the separate PFTRename post-processing pass that tried to strip them afterwards.
