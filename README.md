# Green–Laffont characterization of Groves payments

This project formalizes the Green–Laffont characterization for a finite
direct mechanism with quasi-linear utility. Let `N` be a finite, nonempty type
of agents and `A` a finite, nonempty type of alternatives, both with decidable
equality. A valuation is `v : N → A → ℝ`; `welfare v a` sums reported values
over agents, and `othersWelfare v i a` sums them over agents other than `i`.

## Headline result

`VCG.vcg_greenLaffont` takes an allocation rule
`x : Valuation N A → A` and a payment rule
`p : Valuation N A → N → ℝ`. Its efficiency hypothesis is
`∀ v a, welfare v a ≤ welfare v (x v)`. Its dominant-strategy incentive
compatibility hypothesis is
`∀ v i r, v i (x (Function.update v i r)) -
p (Function.update v i r) i ≤ v i (x v) - p v i`, where the agent's utility
is its value for the selected alternative minus its payment. The conclusion is
that there exists `h : N → Valuation N A → ℝ` such that
`∀ i v w, (∀ j, j ≠ i → v j = w j) → h i v = h i w` and
`∀ v i, p v i = h i v - othersWelfare v i (x v)`. Thus each payment has Groves
form, and its term `h i` depends only on reports other than agent `i`'s.

## Research contribution

The result formalizes the Green–Laffont (1977) / Holmström (1979) uniqueness
characterization: efficiency together with dominant-strategy incentive
compatibility forces payments to be of Groves form. In this finite model, this
shows that a mechanism satisfying those hypotheses has the VCG/Groves payment
structure, up to an arbitrary term depending only on other agents' reports.

## Supporting VCG properties

All four supporting theorems quantify over the same finite, nonempty types `N`
and `A`, with decidable equality on both.

- **Efficiency (`VCG.vcg_efficient`).** For every profile `v` and alternative
  `a`, `welfare v a ≤ welfare v (xstar v)`.
- **Dominant-strategy truthfulness (`VCG.vcg_truthful`).** For every true
  profile `v`, agent `i`, and report `r : A → ℝ`,
  `trueUtility v (Function.update v i r) i ≤ trueUtility v v i`.
- **Individual rationality (`VCG.vcg_individualRational`).** Under the exact
  hypothesis `hnn : ∀ j a, 0 ≤ v j a`, the conclusion is
  `0 ≤ utility v i`.
- **No deficit (`VCG.vcg_noDeficit`).** For every profile `v`,
  `0 ≤ ∑ i ∈ Finset.univ, clarkePayment v i`.

The comparator statements are in `Challenge.lean`; the implementation and
proofs are in the `VCG` modules imported by `Solution.lean`.
