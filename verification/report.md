# Verification passed

The selected source commit `003f453d2844709337770e7d67f527a516d83d78` proves the sharp unrestricted asymptotic for the original fixed-sign maximum in Erdős Problem 319, catalogued as JSP-000265. Complete clean-checkout verification passed.

## Conclusions and coverage

| Check | Observed result |
| --- | --- |
| Original mathematical statement | The independent support-sign definition, attained maximum, and unrestricted limit match the original question. |
| Clean source build | All 187 local modules built successfully in dependency order, followed by the normal default build. |
| Complete kernel replay | All 187 local modules passed exact-module replay in the clean CI run. |
| Target axiom audit | All 17 selected targets passed. Every transitive axiom set is contained in `{propext, Classical.choice, Quot.sound}`. |
| Source and dependency identity | Pinned toolchain, nine locked dependencies, committed source hashes and unchanged verification inputs were checked. |
| Additional local execution | Normal build and all 17 target audits passed. A prefix of 108 module replays passed before the duplicate run was stopped following the complete CI success. |

The theorem is `N-c(N) ~ exp(-gamma) N logloglog(N)/loglog(N)`. The exact maximum ranges over all finite subsets of `{1,...,N}` and all fixed signings. The same signs are used in every proper nonempty subsum. The [statement matrix](../STATEMENT.md), [literal definition check](../Challenge.lean), and [submitted theorem](../Solution.lean) give the precise correspondence. The original source is Erdős–Graham, 1980, printed page 43, PDF page 39 in the [source scan](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf#page=39).

## Complete clean-checkout execution

The GitHub run checked out exactly `003f453d2844709337770e7d67f527a516d83d78` on Ubuntu 24.04 and installed the pinned Lean 4.35.0-rc2 environment. It ran

```sh
python3 scripts/verify.py --clean
```

The verifier binds its inputs to the selected Git commit, checks all dependency revisions, builds every local module, executes the target audit, replays every local module and confirms unchanged input hashes. The captured job succeeded. Its log contains all 187 ordered build markers, all 187 ordered replay markers, the target-audit marker, the normal-build marker and the final verifier success marker. Those lists were independently compared with the committed module manifest when this evidence was packaged.

The job started `2026-11-12T05:50:27Z` and completed `2026-11-12T06:45:47Z`. The [CI record](ci-run.json) identifies the selected commit, job steps and coverage. The [complete job log](logs/clean-ci.log) preserves the execution evidence. Terminal color sequences were removed from the distributed log, with both original and distributed hashes retained in the record.

## Local execution and evidence integrity

The local run began `2026-11-12T00:49:07.535812-05:00`. Its normal build and 17 target audits passed. Its 108 completed exact-module replays also passed, and their object hashes were checked again during packaging. Once the clean CI run had completed the whole closure, the remaining duplicate local replays were stopped. The [local record](local-results.json) preserves that scope and its actual stop status.

Every recorded local command completed with exit code zero. The local input hashes were identical before verification and after stopping, and each checked input was compared with its selected committed Git object. The report retains the completed command logs and their hashes. An early audit-parser issue involving printed universe annotations was corrected in the selected revision and tested against all 17 actual reports and six regression cases.

The local normal-build log contains 109 inherited lint or deprecation warning lines. Their full text is preserved in the [normal build log](logs/default-build.log). The target audit passed with warnings treated as errors.

## Trust and mathematical review

The trusted basis is the pinned Lean kernel and its imported standard-library, Mathlib and dependency environment. Exact-module replay checks the local declarations against that imported environment. These are author-controlled automated executions. Organizer mathematical review, attribution review and acceptance have their own evidentiary requirements.

The mathematical paper is a proof-only presentation. Some auxiliary quantitative bounds in the formal source use a different presentation, with the same sharp final theorem. The original-statement matrix identifies the correspondence. [Prior work](../PRIOR_WORK.md) preserves the earlier mathematical constructions, formal sources and related JSP submissions.

## Evidence and revision

- [Combined machine-readable result](results.json).
- [Target types and axiom output](logs/target-axioms.log).
- [Module source manifest](source-modules.json) and [target manifest](targets.json).
- [Local command and object-hash record](local-results.json).
- [Clean CI execution record](ci-run.json) and [complete log](logs/clean-ci.log).

This report is added after the selected proof commit in a separate evidence commit. It describes the selected proof revision above. Private branch membership and Git file hashes were read back after upload. Public access awaits the user's publication authorization. Priority, identity, award level and payment are assessed through the JSP process.
