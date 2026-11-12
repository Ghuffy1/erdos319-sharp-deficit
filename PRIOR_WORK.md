# Prior work and related JSP submissions

This submission concerns the sharp deficit

\[
N-c(N)\sim e^{-\gamma}N\log\log\log N/\log\log N.
\]

The earlier density-one conclusion is `c(N)/N → 1`. The sharp theorem specifies the order and leading coefficient of its deficit. The earlier construction and analytic ingredients retain their attribution.

## Mathematical and formal sources

- Erdős and Graham posed the fixed-sign maximum question in 1980, printed page 43. [Original scan](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf#page=39).
- Adenwalla observed the support bound `(1-1/e+o(1))N` obtained from Croot's short-interval theorem. [Problem page](https://www.erdosproblems.com/319), [Croot](https://doi.org/10.4064/aa99-2-1).
- g-01234, also known as popular_12345, proposed a density-one construction on July 16, 2026. Its protected-prime family and coprime completion strategy are credited in the paper. [Pinned manuscript](https://github.com/g-01234/erdos-319-density-one/blob/f55a25a29dcb17193918d27506be5e7a5b5d7d40/docs/proof.md).
- Yang P. Liu and Mehtaab Sawhney developed the exact rational representation machinery. The mathematical appendix gives the precise divisor and Fourier details used here. [Published article](https://doi.org/10.1093/imrn/rnaf382), [preprint](https://arxiv.org/abs/2404.07113).
- RexHannes gave a large-prime obstruction for the support deficit. [Mathematical note](https://github.com/RexHannes/Erdos-Upper-Bound-319-lean/blob/main/docs/erdos319_large_prime_obstruction.md).
- The H0W4RD-dev density-one project supplies the verified baseline and attributed analytic background extended by this repository. [Proof version](https://github.com/H0W4RD-dev/erdos319-density-one/tree/ed555ed4120225800a6c642e6ba81704d5ed6b11), [evidence version](https://github.com/H0W4RD-dev/erdos319-density-one/tree/3c1e1c6f349b6b5628fdc01386a6ac5ed55b7b61).
- The prime-pool strategy in peilinliu66-dev's October 3 project is credited as a source for the thinned-prime completion approach. Its proof is an earlier density-one contribution. [Pinned source](https://github.com/peilinliu66-dev/jsp265-erdos319-density-one/tree/72545d3e68e8881e2f89f4744067583aaa61fc9e).

## Related prize records checked on November 12, 2026

The all-state search for JSP-000265 returned the following six PRs. Both open October submissions concern the density-one result. The sharp result supplied here is identified separately in the proposed catalog update.

| PR | State at check | Scope of the record |
| --- | --- | --- |
| [904](https://github.com/TheJustinSunPrize/awards/pull/904) | Closed, unmerged | A primitive three-term reciprocal relation. The submitter expressly excludes the maximum-size question from the claim. |
| [2234](https://github.com/TheJustinSunPrize/awards/pull/2234) | Closed, unmerged | A scoped formalization record. Prior source inspection found only trivial proposition targets in its cited file. |
| [2598](https://github.com/TheJustinSunPrize/awards/pull/2598) | Closed, unmerged | Three-term and six-term primitive examples. These examples do not give the unrestricted asymptotic maximum. |
| [3087](https://github.com/TheJustinSunPrize/awards/pull/3087) | Closed, unmerged | A record identifying JSP-000265 with Erdős 265. The reciprocal maximum is Erdős 319. |
| [4669](https://github.com/TheJustinSunPrize/awards/pull/4669) | Open | peilinliu66-dev's complete density-one formalization at the source version linked above. |
| [5071](https://github.com/TheJustinSunPrize/awards/pull/5071) | Open | The submitting team's earlier alternative density-one presentation and formalization. This repository extends its baseline. |

The new submission seeks review of its sharp theorem and the associated formal development. The earlier PRs and author credits should be retained. A priority decision for a previously submitted contribution requires the organizers' comparison of its actual scope and dated public evidence. A local commit date supplies no independently established public priority.

The two October submissions were not shown as accepted or awarded in the inspected catalog and registers. Their open status is recorded as of the check date. Later publication or review changes must be checked when the prepared submission is released.
