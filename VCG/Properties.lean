import VCG.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option linter.unusedSectionVars false

/-!
# Individual rationality and no deficit for the VCG mechanism

This file proves that Clarke pivot payments are nonnegative and that agents
with nonnegative valuations receive nonnegative utility.
-/

namespace VCG

variable {N A : Type*}
variable [Fintype N] [Nonempty N] [DecidableEq N]
variable [Fintype A] [Nonempty A] [DecidableEq A]

/-- Every Clarke pivot payment is nonnegative. -/
lemma clarkePayment_nonneg (v : Valuation N A) (i : N) :
    0 ≤ clarkePayment v i := by
  unfold clarkePayment
  exact sub_nonneg_of_le (pivotTerm_isMax v i (xstar v))

/-- The sum of Clarke pivot payments is nonnegative. -/
theorem vcg_noDeficit (v : Valuation N A) :
    0 ≤ ∑ i ∈ Finset.univ, clarkePayment v i := by
  exact Finset.sum_nonneg fun i hi => clarkePayment_nonneg v i

/-- Nonnegative valuations give every agent nonnegative utility. -/
theorem vcg_individualRational (v : Valuation N A) (i : N)
    (hnn : ∀ j a, 0 ≤ v j a) :
    0 ≤ utility v i := by
  obtain ⟨a₀, ha₀⟩ := pivotTerm_attained v i
  have hsum (a : A) : welfare v a = v i a + othersWelfare v i a := by
    unfold welfare othersWelfare
    exact (Finset.univ.add_sum_erase (fun j => v j a) (Finset.mem_univ i)).symm
  calc
    0 ≤ v i a₀ := hnn i a₀
    _ = (v i a₀ + othersWelfare v i a₀) - pivotTerm v i := by
      rw [ha₀]
      ring
    _ = welfare v a₀ - pivotTerm v i := by
      rw [← hsum a₀]
    _ ≤ welfare v (xstar v) - pivotTerm v i :=
      sub_le_sub_right (xstar_isMax v a₀) (pivotTerm v i)
    _ = utility v i := (utility_eq v i).symm

end VCG
