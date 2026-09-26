import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic

/-!
# VCG mechanism statements

This module states the VCG definitions and results independently of the
implementation library. The proof and definition bodies are placeholders for
the Palomar comparator.
-/

namespace VCG

/-- A valuation assigns a real value to each agent and alternative. -/
abbrev Valuation (N A : Type*) := N → A → ℝ

/-- The total reported value of an alternative. -/
def welfare {N A : Type*} [Fintype N] (v : Valuation N A) (a : A) : ℝ := sorry

/-- An alternative selected to maximize reported welfare. -/
noncomputable def xstar {N A : Type*}
    [Fintype N] [Nonempty N] [DecidableEq N]
    [Fintype A] [Nonempty A] [DecidableEq A]
    (v : Valuation N A) : A := sorry

/-- The reported welfare of all agents except `i`. -/
def othersWelfare {N A : Type*} [Fintype N] [DecidableEq N]
    (v : Valuation N A) (i : N) (a : A) : ℝ := sorry

/-- The maximum welfare available to agents other than `i`. -/
noncomputable def pivotTerm {N A : Type*}
    [Fintype N] [Nonempty N] [DecidableEq N]
    [Fintype A] [Nonempty A] [DecidableEq A]
    (v : Valuation N A) (i : N) : ℝ := sorry

/-- The Clarke pivot payment charged to agent `i`. -/
noncomputable def clarkePayment {N A : Type*}
    [Fintype N] [Nonempty N] [DecidableEq N]
    [Fintype A] [Nonempty A] [DecidableEq A]
    (v : Valuation N A) (i : N) : ℝ := sorry

/-- Agent `i`'s reported value at the selected alternative, net of payment. -/
noncomputable def utility {N A : Type*}
    [Fintype N] [Nonempty N] [DecidableEq N]
    [Fintype A] [Nonempty A] [DecidableEq A]
    (v : Valuation N A) (i : N) : ℝ := sorry

/-- Agent `i`'s true utility when the mechanism receives reported profile `w`. -/
noncomputable def trueUtility {N A : Type*}
    [Fintype N] [Nonempty N] [DecidableEq N]
    [Fintype A] [Nonempty A] [DecidableEq A]
    (v w : Valuation N A) (i : N) : ℝ := sorry

theorem vcg_efficient {N A : Type*}
    [Fintype N] [Nonempty N] [DecidableEq N]
    [Fintype A] [Nonempty A] [DecidableEq A]
    (v : Valuation N A) (a : A) :
    welfare v a ≤ welfare v (xstar v) := sorry

theorem vcg_truthful {N A : Type*}
    [Fintype N] [Nonempty N] [DecidableEq N]
    [Fintype A] [Nonempty A] [DecidableEq A]
    (v : Valuation N A) (i : N) (r : A → ℝ) :
    trueUtility v (Function.update v i r) i ≤ trueUtility v v i := sorry

theorem vcg_individualRational {N A : Type*}
    [Fintype N] [Nonempty N] [DecidableEq N]
    [Fintype A] [Nonempty A] [DecidableEq A]
    (v : Valuation N A) (i : N)
    (hnn : ∀ j a, 0 ≤ v j a) :
    0 ≤ utility v i := sorry

theorem vcg_noDeficit {N A : Type*}
    [Fintype N] [Nonempty N] [DecidableEq N]
    [Fintype A] [Nonempty A] [DecidableEq A]
    (v : Valuation N A) :
    0 ≤ ∑ i ∈ Finset.univ, clarkePayment v i := sorry

theorem vcg_greenLaffont {N A : Type*}
    [Fintype N] [Nonempty N] [DecidableEq N]
    [Fintype A] [Nonempty A] [DecidableEq A]
    (x : Valuation N A → A) (p : Valuation N A → N → ℝ)
    (heff : ∀ (v : Valuation N A) (a : A), welfare v a ≤ welfare v (x v))
    (hdsic : ∀ (v : Valuation N A) (i : N) (r : A → ℝ),
      v i (x (Function.update v i r)) - p (Function.update v i r) i ≤
        v i (x v) - p v i) :
    ∃ (h : N → Valuation N A → ℝ),
      (∀ i v w, (∀ j, j ≠ i → v j = w j) → h i v = h i w) ∧
      ∀ v i, p v i = h i v - othersWelfare v i (x v) := sorry

end VCG
