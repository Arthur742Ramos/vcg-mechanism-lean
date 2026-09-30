module

public import VCG.Basic

set_option linter.unusedSectionVars false

/-!
# Truthfulness and efficiency of the VCG mechanism

This file proves dominant-strategy truthfulness and welfare efficiency for the
Clarke pivot mechanism defined in `VCG.Basic`.
-/

namespace VCG

variable {N A : Type*}
variable [Fintype N] [Nonempty N] [DecidableEq N]
variable [Fintype A] [Nonempty A] [DecidableEq A]

/-- Agent `i`'s true utility when the mechanism is run on reported profile `w`. -/
@[expose] public noncomputable def trueUtility (v w : Valuation N A) (i : N) : ℝ :=
  v i (xstar w) - clarkePayment w i

/-- Changing agent `i`'s report does not change the welfare of the other agents. -/
public theorem othersWelfare_update (v : Valuation N A) (i : N) (r : A → ℝ) (a : A) :
    othersWelfare (Function.update v i r) i a = othersWelfare v i a := by
  unfold othersWelfare
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- Agent `i`'s maximum attainable welfare from the other agents is unaffected
by a change to `i`'s own report. -/
public theorem pivotTerm_update (v : Valuation N A) (i : N) (r : A → ℝ) :
    pivotTerm (Function.update v i r) i = pivotTerm v i := by
  apply le_antisymm
  · obtain ⟨a, ha⟩ := pivotTerm_attained (Function.update v i r) i
    calc
      pivotTerm (Function.update v i r) i = othersWelfare (Function.update v i r) i a := ha.symm
      _ = othersWelfare v i a := othersWelfare_update v i r a
      _ ≤ pivotTerm v i := pivotTerm_isMax v i a
  · obtain ⟨a, ha⟩ := pivotTerm_attained v i
    calc
      pivotTerm v i = othersWelfare v i a := ha.symm
      _ = othersWelfare (Function.update v i r) i a := (othersWelfare_update v i r a).symm
      _ ≤ pivotTerm (Function.update v i r) i := pivotTerm_isMax (Function.update v i r) i a

/-- If all other agents report truthfully, true utility is total welfare at the
chosen alternative minus the pivot term. -/
public theorem trueUtility_eq_of_agree (v w : Valuation N A) (i : N)
    (h : ∀ j, j ≠ i → w j = v j) :
    trueUtility v w i = welfare v (xstar w) - pivotTerm w i := by
  have hothers (a : A) : othersWelfare w i a = othersWelfare v i a := by
    unfold othersWelfare
    apply Finset.sum_congr rfl
    intro j hj
    rw [h j (Finset.ne_of_mem_erase hj)]
  have hsum (a : A) : v i a + othersWelfare w i a = welfare v a := by
    calc
      v i a + othersWelfare w i a = v i a + othersWelfare v i a := by rw [hothers]
      _ = welfare v a := by
        unfold othersWelfare welfare
        exact Finset.univ.add_sum_erase (fun j => v j a) (Finset.mem_univ i)
  unfold trueUtility clarkePayment
  calc
    v i (xstar w) - (pivotTerm w i - othersWelfare w i (xstar w)) =
        (v i (xstar w) + othersWelfare w i (xstar w)) - pivotTerm w i := by ring
    _ = welfare v (xstar w) - pivotTerm w i := by rw [hsum]

/-- Reporting one's true valuation weakly maximizes one's utility. -/
public theorem vcg_truthful (v : Valuation N A) (i : N) (r : A → ℝ) :
    trueUtility v (Function.update v i r) i ≤ trueUtility v v i := by
  let w := Function.update v i r
  have hagree : ∀ j, j ≠ i → w j = v j := by
    intro j hj
    exact Function.update_of_ne hj r v
  calc
    trueUtility v w i = welfare v (xstar w) - pivotTerm w i :=
      trueUtility_eq_of_agree v w i hagree
    _ = welfare v (xstar w) - pivotTerm v i := by rw [pivotTerm_update]
    _ ≤ welfare v (xstar v) - pivotTerm v i := by
      exact sub_le_sub_right (xstar_isMax v (xstar w)) (pivotTerm v i)
    _ = utility v i := (utility_eq v i).symm
    _ = trueUtility v v i := rfl

/-- The selected alternative maximizes total welfare. -/
public theorem vcg_efficient (v : Valuation N A) (a : A) :
    welfare v a ≤ welfare v (xstar v) :=
  xstar_isMax v a

end VCG
