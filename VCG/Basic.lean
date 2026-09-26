import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

/-!
# Core definitions for the VCG mechanism

This file defines valuations, welfare maximization, Clarke pivot payments, and
the resulting utility for a finite set of agents and alternatives.
-/

namespace VCG

/-- A valuation assigns a real value to each agent and alternative. -/
abbrev Valuation (N A : Type*) := N → A → ℝ

variable {N A : Type*}
variable [Fintype N] [Nonempty N] [DecidableEq N]
variable [Fintype A] [Nonempty A] [DecidableEq A]

/-- The total value of an alternative, summed over all agents. -/
def welfare (v : Valuation N A) (a : A) : ℝ :=
  Finset.univ.sum fun i => v i a

/-- There is a welfare-maximizing alternative. -/
private theorem welfare_maximizer_exists (v : Valuation N A) :
    Nonempty {a : A // ∀ a', welfare v a' ≤ welfare v a} := by
  obtain ⟨a, _, hmax⟩ :=
    Finset.exists_max_image Finset.univ (welfare v) Finset.univ_nonempty
  exact ⟨⟨a, fun a' => hmax a' (Finset.mem_univ a')⟩⟩

/-- An alternative with maximum welfare for the valuation profile `v`. -/
noncomputable def xstar (v : Valuation N A) : A :=
  (Classical.choice (welfare_maximizer_exists v)).val

/-- The selected alternative maximizes welfare. -/
theorem xstar_isMax (v : Valuation N A) (a : A) :
    welfare v a ≤ welfare v (xstar v) := by
  exact (Classical.choice (welfare_maximizer_exists v)).property a

/-- The total value of an alternative for all agents other than `i`. -/
def othersWelfare (v : Valuation N A) (i : N) (a : A) : ℝ :=
  (Finset.univ.erase i).sum fun j => v j a

/-- There is an alternative maximizing welfare among agents other than `i`. -/
private theorem othersWelfare_maximizer_exists (v : Valuation N A) (i : N) :
    Nonempty {a : A // ∀ a', othersWelfare v i a' ≤ othersWelfare v i a} := by
  obtain ⟨a, _, hmax⟩ :=
    Finset.exists_max_image Finset.univ (othersWelfare v i) Finset.univ_nonempty
  exact ⟨⟨a, fun a' => hmax a' (Finset.mem_univ a')⟩⟩

/-- The maximum welfare attainable by agents other than `i`. -/
noncomputable def pivotTerm (v : Valuation N A) (i : N) : ℝ :=
  othersWelfare v i (Classical.choice (othersWelfare_maximizer_exists v i)).val

/-- The pivot term bounds the other agents' welfare at every alternative. -/
theorem pivotTerm_isMax (v : Valuation N A) (i : N) (a : A) :
    othersWelfare v i a ≤ pivotTerm v i := by
  exact (Classical.choice (othersWelfare_maximizer_exists v i)).property a

/-- The pivot term is attained by some alternative. -/
theorem pivotTerm_attained (v : Valuation N A) (i : N) :
    ∃ a, othersWelfare v i a = pivotTerm v i := by
  refine ⟨(Classical.choice (othersWelfare_maximizer_exists v i)).val, ?_⟩
  rfl

/-- The Clarke pivot payment charged to agent `i`. -/
noncomputable def clarkePayment (v : Valuation N A) (i : N) : ℝ :=
  pivotTerm v i - othersWelfare v i (xstar v)

/-- Agent `i`'s value for the chosen alternative, net of its Clarke payment. -/
noncomputable def utility (v : Valuation N A) (i : N) : ℝ :=
  v i (xstar v) - clarkePayment v i

/-- Utility is total welfare at the chosen alternative minus the pivot term. -/
theorem utility_eq (v : Valuation N A) (i : N) :
    utility v i = welfare v (xstar v) - pivotTerm v i := by
  have hsum (a : A) : v i a + othersWelfare v i a = welfare v a := by
    unfold othersWelfare welfare
    exact Finset.univ.add_sum_erase (fun j => v j a) (Finset.mem_univ i)
  unfold utility clarkePayment
  calc
    v i (xstar v) - (pivotTerm v i - othersWelfare v i (xstar v)) =
        (v i (xstar v) + othersWelfare v i (xstar v)) - pivotTerm v i := by ring
    _ = welfare v (xstar v) - pivotTerm v i := by rw [hsum]

end VCG
