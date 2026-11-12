# Final submission verification

The complete author-side verification passed for source commit `43f24b821a8cb8052707fcadc9adcc2cd1678c13`. This revision includes the mathematical paper, the complete formal proof and the explicit upstream attribution for the replay utility.

## Mathematical statement

The submitted theorem is `N-c(N) ~ exp(-gamma) N logloglog(N)/loglog(N)` for the original fixed-sign maximum in Erdős Problem 319, JSP-000265. A single signing is used for the total and every nonempty proper subsum. The support ranges over all finite subsets of `{1,...,N}`, and the limit is taken through all sufficiently large integers.

The original Erdős–Graham question is on printed page 43, PDF page 39 of the [source scan](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf#page=39). The [statement matrix](../STATEMENT.md), [literal reconstruction](../Challenge.lean) and [submission theorem](../Solution.lean) give the correspondence. The mathematical manuscript, construction, converse and analytic appendix were reread. All 15 rendered pages were inspected and all 26 fonts are embedded.

## Complete clean verification

The clean Ubuntu 24.04 job checked out exactly `43f24b821a8cb8052707fcadc9adcc2cd1678c13` and ran

```sh
python3 scripts/verify.py --clean
```

The job started `2026-11-12T06:59:58Z` and finished `2026-11-12T08:13:47Z`. All 187 local modules built in dependency order and passed exact-module kernel replay. The normal default build and all 17 target axiom audits also passed. The verifier checked the pinned Lean version, all nine dependency revisions, committed input hashes, replay markers and unchanged source inputs.

The [CI record](ci-run.json) and [complete job log](logs/clean-ci.log) identify the exact revision and outcome. Packaging checks compared every ordered build and replay marker with the committed 187-module manifest. Terminal color sequences were removed from the distributed log, with original and distributed hashes retained in the record.

Every audited target uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. The [target manifest](targets.json) lists the declarations and original-problem requirements. [Target output](logs/target-axioms.log) from the earlier local execution is retained, whose executable inputs match this revision byte for byte.

## Source, paper and submission checks

All 329 files of the selected revision were checked against their Git blobs. The 187 proof-module source hashes match the manifest. The paper is unchanged from its reviewed final PDF. The release review checked authorship, alphabetical author order, supplied emails, AI assistance, source provenance, licenses, citation metadata, internal references and the permitted catalog scope. The official catalog validator and all 50 upstream regression tests passed.

The release adds the copyright and author credit for the adapted `LeanChecker` utility to [NOTICE](../NOTICE) and [third-party notices](../THIRD_PARTY_NOTICES.md). The mathematical and formal contributions of Will Howe, Grant Huffman, Jensen Kohlmeyer and Liam Kruer are credited equally, with Ghuffy1 designated as the owner and main submitter. [Prior work](../PRIOR_WORK.md) preserves earlier mathematical constructions and related JSP submissions.

## Earlier local checks and warnings

The earlier [local record](local-results.json) checked source commit `003f453d2844709337770e7d67f527a516d83d78`. Its executable inputs are identical to the selected revision. That run completed the normal build, all 17 target audits and 108 exact-module replays before its remaining duplicate work was stopped after a successful complete CI run. This local record is supplementary to the new complete clean run above.

The earlier axiom-output parser was corrected to handle printed universe annotations, with regression checks. The retained local build log has 109 inherited lint or deprecation warning lines. The target audit uses warnings as errors and passed. All warning text is preserved in the [build log](logs/default-build.log).

## Trust and review scope

The trusted basis is the pinned Lean kernel and imported standard-library, Mathlib and dependency environment. Exact-module replay checks local declarations against that imported environment. These are author-controlled automated and mathematical checks. JSP mathematical review, attribution, priority assessment and acceptance remain organizer responsibilities.

The manuscript and formal proof use some different auxiliary quantitative bounds while proving the same sharp final theorem. The original-statement matrix records the correspondence. The [combined result](results.json) and [release-check record](release-checks.json) provide the machine-readable summary.

This report is stored in a later evidence commit and describes the selected source commit above. The selected commit is retained in the repository's `main` branch.
