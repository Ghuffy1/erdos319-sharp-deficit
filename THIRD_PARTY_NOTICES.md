# Third-party notices

The repository's code uses Apache-2.0 licensing. Existing copyright and source-attribution headers remain in the included files.

## Density-one baseline

`Erdos319.lean` and `Submission.lean` are taken from the H0W4RD-dev density-one project at proof commit `ed555ed4120225800a6c642e6ba81704d5ed6b11`, retained in evidence commit `3c1e1c6f349b6b5628fdc01386a6ac5ed55b7b61`. This project is credited in [PRIOR_WORK.md](PRIOR_WORK.md). Its mathematical conclusion and background proofs retain their original attribution.

Several sharp modules adapt the baseline's finite Fourier classification, regular cleaning, exact rational targets, divisor counting, sieve comparisons, and elementary analytic bounds. The local source files describe these dependencies. The added parameter estimates, sharp bounds and final assembly are part of the present contribution.

## plby/lean-proofs

The analytic background in the baseline and the selected sources under `Erdos319Sharp/Imported/` adapt `plby/lean-proofs` at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. Their source notices identify the original paths. Compatibility changes support the pinned Lean and Mathlib versions.

The source license notice is preserved in [licenses/plby-source-LICENSE.txt](licenses/plby-source-LICENSE.txt). Its Apache-2.0 external-source terms and the upstream notices apply to the included material.

## SALT

The selected `Salt/` files are from `jyh/salt` at commit `9b4b5a891ed4eb5219322e8b27a85c8f656c5360`. Original source headers are retained and the Apache-2.0 text is preserved in [licenses/salt-LICENSE.txt](licenses/salt-LICENSE.txt).

## Other dependencies and mathematical sources

The exact-module utility in `scripts/Replay.lean` adapts `replayFromImports` from Lean's `src/LeanChecker.lean`, by Kim Morrison and Sebastian Ullrich. The upstream source bears `Copyright (c) 2023 Kim Morrison. All rights reserved.` and is released under Apache-2.0. The adaptation accepts one exact module name and reports a successful replay marker. The original notice is also retained in [NOTICE](NOTICE). [Pinned upstream source](https://github.com/leanprover/lean4/blob/v4.35.0-rc2/src/LeanChecker.lean).

Mathlib, Lean and the dependency packages downloaded through Lake retain their respective licenses. Their exact versions are in `lake-manifest.json` and `lean-toolchain`. Mathematical papers and the earlier density-one manuscripts are cited in the paper and [PRIOR_WORK.md](PRIOR_WORK.md). Their contents have not been relicensed as new work by this team.

The quantitative completion uses the earlier prime-thinning strategy of peilinliu66-dev, with the method credit given in the source record. No ownership of that earlier contribution is claimed.
