# The sharp deficit in primitive signed reciprocal relations

This repository contains the mathematical paper and complete Lean proof for the sharp asymptotic in Erdős Problem 319, catalogued by the Justin Sun Prize as JSP-000265.

For the maximum cardinality `c(N)` of a subset of `{1, …, N}` admitting a primitive signed reciprocal relation, the result is

\[
N-c(N)\sim e^{-\gamma}\frac{N\log\log\log N}{\log\log N}.
\]

The signing is fixed when testing every nonempty proper subset. The maximum ranges over all qualifying supports and all signings.

## Paper and formal endpoints

- [Mathematical paper](paper/Erdos319_Sharp_Deficit.pdf), Theorem 1.1, with the construction, the converse, and the analytic appendix.
- [Paper source](paper/Erdos319_Sharp_Deficit.tex).
- [Submission endpoints](Solution.lean), including `Erdos319Jsp.full_solution`, `sharp_asymptotic`, and `sharp_asymptotic_ratio`.
- [Literal original-statement bridge](Submission.lean).
- [Sharp proof endpoint](Erdos319Sharp/SharpFinal.lean).
- [Statement correspondence and coverage](STATEMENT.md).

## Authors and submission ownership

Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer are credited as equal contributors. The author order is alphabetical by surname.

The designated repository owner and main submitter is **Ghuffy1**, Grant Huffman. The other equal contributors are **H0W4RD-dev**, Will Howe, **JENW1N**, Jensen Kohlmeyer, and **lkruer**, Liam Kruer. Repository administration is assigned to Ghuffy1. The equal-contribution attribution applies to the mathematical contribution and its accompanying formalization. See [authorship](AUTHORSHIP.md), [AI assistance](AI_ASSISTANCE.md), and [prior work](PRIOR_WORK.md).

## Reproduce

The pinned environment is Lean **4.35.0-rc2**, Mathlib **065356127b1dc0016f66b7283ce0ce2c4055aa55**, and the transitive revisions in [lake-manifest.json](lake-manifest.json).

The internal Lake package identifier `Erdos319SharpPrivate` is retained from the checked development project to preserve build-cache compatibility. The repository and submission ownership are assigned to Ghuffy1 as recorded above.

From a checkout of the selected proof commit, with the pinned Lean toolchain available, run

```sh
python scripts/verify.py --setup --clean
```

The verifier validates dependency revisions and source hashes, builds the local modules sequentially, runs the normal default build, checks the original-statement bridge and target axiom closures, and separately replays every local module. Its output goes to `.verification/`. Cached external dependencies may be reused. Every local proof module is rebuilt when `--clean` is supplied.

An explicit Lake executable may be supplied with `--lake /path/to/lake`. This supports an existing installation of the exact pinned toolchain. No toolchain upgrade is part of reproduction.

Core commands after dependency setup are

```sh
lake --no-cache --fail-fast build
lake env lean -DwarningAsError=true verification/Targets.lean
lake env lean -DwarningAsError=true Challenge.lean
lake env lean --run scripts/Replay.lean Solution
```

The final command replays one exact module. The verifier repeats it for the entire local import closure. See [verification methodology](verification/README.md) for the trust boundary and report locations.

## Provenance and licensing

The new sharp theorem extends previously published density-one work. Its proof uses attributed mathematical and formal dependencies described in [sources](SOURCES.md), [third-party notices](THIRD_PARTY_NOTICES.md), and [prior work](PRIOR_WORK.md). No first-discovery claim is inferred from a local commit date.

The code is distributed under the existing Apache-2.0 license in [LICENSE](LICENSE), with upstream notices retained. The mathematical paper retains the authors' copyright. The repository contains no vendored compiler or dependency checkout.

This package is prepared for a combined mathematical and formal submission. JSP's mathematical review, attribution review, acceptance, recipient identity confirmation, and award decisions are carried out by the prize organizers under their published process.
