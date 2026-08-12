# Lean verification: deterministic tail-index SIS core

This public, self-contained Lean 4 project verifies the deterministic bridge
from a uniform score bound to score separation, sure screening, and exact
recovery. It intentionally contains no article PDF, data, experimental output,
or other private source material.

## Verified statements

- `score_separation`: uniform error `< gap / 2`, active population scores at
  most `baseline - gap`, and inactive population scores equal to `baseline`
  imply strict active/inactive separation of estimated scores.
- `sure_screening_of_separation`: selecting at least `|active|` lowest scores
  contains every active index.
- `exact_recovery_of_separation`: selecting exactly `|active|` lowest scores
  recovers the active set.
- Two end-to-end theorems compose these facts.

`IsLowestSelection` abstracts the deterministic tie-broken selection of the
`d` smallest scores by the exact ordering property needed in the proof.

## Reproduce locally

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake build
```

The toolchain and mathlib revision are pinned to Lean/mathlib `v4.19.0`.
The source uses no `sorry`, `admit`, custom axioms, or unsafe escape hatches.
