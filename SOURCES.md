# Mathematical and formal sources

The manuscript bibliography supplies the principal mathematical references. The following sources identify the formal dependencies and their roles.

| Source | Fixed revision | Role |
| --- | --- | --- |
| Lean | `leanprover/lean4:v4.35.0-rc2` | Kernel, elaborator, standard library and adapted exact-module replay utility, with upstream credit in THIRD_PARTY_NOTICES.md and NOTICE |
| Mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` | Foundational mathematical library and tactics |
| H0W4RD-dev/erdos319-density-one | proof `ed555ed4120225800a6c642e6ba81704d5ed6b11`, evidence `3c1e1c6f349b6b5628fdc01386a6ac5ed55b7b61` | `Erdos319.lean` and `Submission.lean`, and attributed analytic proof techniques extended by the sharp modules |
| plby/lean-proofs | `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` | Adapted analytic and modular inverse proof sources, including the selected modules under `Erdos319Sharp/Imported/` |
| jyh/salt | `9b4b5a891ed4eb5219322e8b27a85c8f656c5360` | Selected Mertens and sieve proof dependencies under `Salt/` |
| peilinliu66-dev/jsp265-erdos319-density-one | `72545d3e68e8881e2f89f4744067583aaa61fc9e` | Prior thinned-prime completion strategy, credited as a method source |

All runtime dependencies are pinned by [lake-manifest.json](lake-manifest.json). Selected formal source files are included directly so the submitted proof has a complete local import closure. Compiler distributions, Mathlib checkouts, and other downloaded dependency checkouts remain outside the tracked repository.

[verification/source-modules.json](verification/source-modules.json) records the exact local source hashes and module order. [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) records licensing and adaptation details.
