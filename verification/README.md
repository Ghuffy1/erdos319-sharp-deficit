# Verification methodology

The [completed verification report](report.md) records the selected source revision. The clean CI run built and replayed all 187 local modules and completed the 17 target audits. The additional local run completed its normal build, all target audits and 108 module replays before the complete CI result made further duplicate checking unnecessary.

Run `python scripts/verify.py --setup --clean` from the selected source revision. The exact toolchain and dependency lockfile are retained.

The verifier checks the local import closure and source hashes, verifies the checked-out dependency revisions, builds every local module in dependency order, runs the normal default build, elaborates the theorem and statement audits, and replays each exact local module against its imported environment. It validates the replay markers and the target axiom output before reporting success.

All processes run with one Lean worker thread. Logs, process results, source hashes, and generated artifacts are written beneath `.verification/`. The script supports `--lake` for an explicit installation and `--output` for a separate evidence directory. A clean run removes only this checkout's validated `.lake/build` path. It does not remove dependency checkouts or external caches.

`Targets.lean` prints the original definitions, target types and transitive axiom dependencies. The root `Challenge.lean` writes the literal sign condition independently and checks the exact maximum and submitted limit. `scripts/Replay.lean` uses the pinned `Lean.Replay` kernel replay routine on one exact module.

Kernel replay checks each local module against its imported environment. The pinned Lean standard library and external Mathlib/dependency environment remain trusted imports. The replay does not claim a separate reconstruction of every Mathlib theorem, an independent human referee report, or organizer acceptance.

The source version under review and any later evidence-only commit are identified separately in the verification report. A report for one source revision is not presented as verification of a different proof revision.
