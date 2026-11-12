# Original statement and formal correspondence

The original source is P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, 1980, printed page 43, PDF page 39 in [this scan](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf#page=39). The corresponding catalogue entries are [Erdős 319](https://www.erdosproblems.com/319) and [JSP-000265](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000265).

For each positive integer N, maximize the cardinality of a set A contained in `{1, …, N}` for which there is one assignment of signs ±1 satisfying zero total signed reciprocal sum and nonzero signed reciprocal sum on every nonempty proper subset. The same signs are used throughout. The zero convention for an empty feasible family is included in the maximum.

The submitted result is the sharp asymptotic

\[
\lim_{N\to\infty}\frac{(N-c(N))\log\log N}{N\log\log\log N}=e^{-\gamma}.
\]

The equivalent ratio formulation has limit one. Both bounds hold over every sufficiently large integer N and over the unrestricted original class of supports.

| Original requirement | Definition or theorem | Correspondence |
| --- | --- | --- |
| Distinct positive integer denominators at most N | `Finset.Icc 1 N`, `Finset ℕ` | Both endpoints are included. Finsets exclude multiplicity. |
| Signs ±1 | `Erdos319Submission.LiteralPrimitive` | The signs are integer-valued and explicitly constrained to ±1. |
| Zero total and fixed signs on proper subsums | `LiteralPrimitive`, `literalPrimitive_iff` | One sign function is used for the total and all subfamilies. |
| Every nonempty proper subset | `LiteralPrimitive` | Both nonemptiness and strict inclusion are explicit. |
| Unrestricted exact maximum | `literal_maximum`, `Erdos319Jsp.maximum_correspondence` | `IsGreatest` ranges over every qualifying support and signing. |
| Nonempty large supports | `original_problem_nonempty_witnesses` | Explicit witnesses exist for every sufficiently large N. |
| Upper bound for the deficit | `Erdos319Sharp.sharpUpperWitnesses_proved` | A primitive construction supplies the asymptotically optimal lower bound for the support. |
| Lower bound for the deficit | `Erdos319Sharp.sharpLowerBound_proved` | Every original primitive support satisfies the converse bound. |
| Exact leading constant and all-integer limit | `Erdos319Jsp.sharp_asymptotic`, `sharp_asymptotic_ratio` | The limit is `Real.exp (-Real.eulerMascheroniConstant)`. |
| Combined original-statement endpoint | `Erdos319Jsp.full_solution` | The attained literal maximum and its sharp limit are asserted together without additional mathematical premises. |

`Challenge.lean` independently writes the sign condition on the support and the exact-maximum property, then checks the submitted limit. `Solution.lean` also checks the limit for every function satisfying that original maximum property. `verification/Targets.lean` prints the relevant definitions, theorem types, and complete transitive axiom sets.

The natural logarithms at small N use Lean's total real functions. The asymptotic statement concerns `atTop`, so only eventually positive logarithms enter the limiting argument. No assumption of prime N, a subsequence, a modular construction class, or an unproved analytic input is present in the final theorem.

The manuscript and the formal implementation use quantitatively different auxiliary cutoffs and compatible completion estimates. They prove the same stated sharp asymptotic. The definition and conclusion correspondence is the object of the target and bridge checks.
