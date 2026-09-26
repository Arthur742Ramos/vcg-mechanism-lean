# VCG mechanism formalization

This project formalizes a finite Vickrey–Clarke–Groves mechanism with
quasi-linear utilities and Clarke pivot payments. A valuation is a function
`N → A → ℝ`, where `N` is the finite, nonempty type of agents and `A` is the
finite, nonempty type of alternatives. Both types have decidable equality.
For a reported profile `v`, `welfare v a` is the sum of reported values at
alternative `a`; `xstar v` is a selected welfare-maximizing alternative.
`pivotTerm v i` is the maximum reported welfare of agents other than `i`, and
`clarkePayment v i` is that maximum minus those agents' welfare at `xstar v`.
The functions `utility` and `trueUtility` subtract the Clarke payment from,
respectively, agent `i`'s reported or true value at the selected alternative.

## Results

All four theorems quantify over finite, nonempty types `N` and `A`, with
decidable equality on both types.

- **Efficiency (`VCG.vcg_efficient`).** For every valuation profile `v` and
  alternative `a`, `welfare v a ≤ welfare v (xstar v)`. The selected
  alternative maximizes the welfare reported in `v`.
- **Dominant-strategy truthfulness (`VCG.vcg_truthful`).** For every true
  profile `v`, agent `i`, and report `r : A → ℝ`,
  `trueUtility v (Function.update v i r) i ≤ trueUtility v v i`. The update
  changes agent `i`'s report to `r` and leaves every other agent's report as
  given by `v`.
- **Individual rationality under nonnegative valuations
  (`VCG.vcg_individualRational`).** For every profile `v` and agent `i`, under
  the exact hypothesis `hnn : ∀ j a, 0 ≤ v j a`, the theorem concludes
  `0 ≤ utility v i`.
- **No deficit (`VCG.vcg_noDeficit`).** For every profile `v`,
  `0 ≤ ∑ i ∈ Finset.univ, clarkePayment v i`.

The challenge declarations are independent of the VCG library and contain
intentional placeholders for the comparator. `Solution.lean` imports the
library containing the definitions and proofs.
