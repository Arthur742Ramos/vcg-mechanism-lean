module

public import VCG.Truthful
public import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# The Green–Laffont characterization for Groves mechanisms

An efficient, dominant-strategy incentive-compatible direct mechanism with
quasi-linear utility has Groves-form payments.
-/

namespace VCG

variable {N A : Type*}
variable [Fintype N] [Nonempty N] [DecidableEq N]
variable [Fintype A] [Nonempty A] [DecidableEq A]

/-- Total welfare splits into agent `i`'s value and the other agents' welfare. -/
public theorem welfare_eq (v : Valuation N A) (i : N) (a : A) :
    welfare v a = v i a + othersWelfare v i a := by
  unfold welfare othersWelfare
  exact (Finset.univ.add_sum_erase (fun j => v j a) (Finset.mem_univ i)).symm

/-- Efficient, strategy-proof payments have the same value plus others'
welfare at profiles that agree outside the reporting agent. -/
public lemma groves_key (x : Valuation N A → A) (p : Valuation N A → N → ℝ)
    (heff : ∀ (v : Valuation N A) (a : A), welfare v a ≤ welfare v (x v))
    (hdsic : ∀ (v : Valuation N A) (i : N) (r : A → ℝ),
      v i (x (Function.update v i r)) - p (Function.update v i r) i ≤
        v i (x v) - p v i)
    (i : N) (v w : Valuation N A)
    (hagree : ∀ j, j ≠ i → v j = w j) :
    p w i + othersWelfare w i (x w) = p v i + othersWelfare v i (x v) := by
  have hupdate_vw : Function.update v i (w i) = w := by
    funext j a
    by_cases hji : j = i
    · subst j
      simp
    · rw [Function.update_of_ne hji]
      exact congrFun (hagree j hji) a
  have hupdate_wv : Function.update w i (v i) = v := by
    funext j a
    by_cases hji : j = i
    · subst j
      simp
    · rw [Function.update_of_ne hji]
      exact congrFun (hagree j hji).symm a
  have hothers_w : othersWelfare v i (x w) = othersWelfare w i (x w) := by
    unfold othersWelfare
    apply Finset.sum_congr rfl
    intro j hj
    exact congrFun (hagree j (Finset.ne_of_mem_erase hj)) (x w)

  -- With the other reports fixed, equal selected alternatives imply equal
  -- payments by applying DSIC in both directions.
  have hpay_same (r s : A → ℝ)
      (hout : x (Function.update v i r) = x (Function.update v i s)) :
      p (Function.update v i r) i = p (Function.update v i s) i := by
    have hupdate (r s : A → ℝ) :
        Function.update (Function.update v i r) i s = Function.update v i s := by
      funext j a
      by_cases hji : j = i
      · subst j
        simp
      · simp [Function.update_of_ne hji]
    have hA := hdsic (Function.update v i r) i s
    rw [hupdate r s] at hA
    simp only [Function.update_self] at hA
    rw [hout] at hA
    have hB := hdsic (Function.update v i s) i r
    rw [hupdate s r] at hB
    simp only [Function.update_self] at hB
    rw [hout] at hB
    linarith

  by_cases hxy : x v = x w
  · have hA := hdsic v i (w i)
    rw [hupdate_vw, hxy] at hA
    have hB := hdsic w i (v i)
    rw [hupdate_wv, hxy] at hB
    have hp : p w i = p v i := by linarith
    rw [hxy, hothers_w]
    linarith
  · let a := x v
    let b := x w
    have hab : a ≠ b := by simpa [a, b] using hxy
    let report (c : A) (ε : ℝ) : A → ℝ := fun d =>
      -othersWelfare v i d + if d = c then ε else 0
    let profile (c : A) (ε : ℝ) : Valuation N A :=
      Function.update v i (report c ε)
    have hscore (c : A) (ε : ℝ) (d : A) :
        welfare (profile c ε) d = if d = c then ε else 0 := by
      dsimp [profile, report]
      rw [welfare_eq, othersWelfare_update]
      simp only [Function.update_self]
      ring
    have hforce (c : A) (ε : ℝ) (hε : 0 < ε) :
        x (profile c ε) = c := by
      by_contra hne
      have hmax := heff (profile c ε) c
      rw [hscore c ε c, hscore c ε (x (profile c ε))] at hmax
      simp [hne] at hmax
      linarith
    have hprofile_update (c d : A) (ε δ : ℝ) :
        Function.update (profile c ε) i (report d δ) = profile d δ := by
      funext j z
      by_cases hji : j = i
      · subst j
        simp [profile]
      · simp [profile, Function.update_of_ne hji]
    have hbase_v : Function.update v i (v i) = v := by
      funext j z
      by_cases hji : j = i
      · subst j
        simp
      · rw [Function.update_of_ne hji]
    have hout_v : x (Function.update v i (v i)) = x (profile a 1) := by
      calc
        x (Function.update v i (v i)) = x v := by rw [hbase_v]
        _ = a := rfl
        _ = x (profile a 1) := (hforce a 1 (by norm_num)).symm
    have hpv := hpay_same (v i) (report a 1) hout_v
    rw [hbase_v] at hpv
    have hout_w : x (Function.update v i (w i)) = x (profile b 1) := by
      calc
        x (Function.update v i (w i)) = x w := by rw [hupdate_vw]
        _ = b := rfl
        _ = x (profile b 1) := (hforce b 1 (by norm_num)).symm
    have hpw := hpay_same (w i) (report b 1) hout_w
    rw [hupdate_vw] at hpw
    have hpA (ε : ℝ) (hε : 0 < ε) :
        p (profile a ε) i = p (profile a 1) i := by
      apply hpay_same (report a ε) (report a 1)
      rw [hforce a ε hε, hforce a 1 (by norm_num)]
    have hpB (ε : ℝ) (hε : 0 < ε) :
        p (profile b ε) i = p (profile b 1) i := by
      apply hpay_same (report b ε) (report b 1)
      rw [hforce b ε hε, hforce b 1 (by norm_num)]
    have hbound_lower (ε : ℝ) (hε : 0 < ε) :
        othersWelfare v i a - othersWelfare v i b ≤ p w i - p v i + ε := by
      have hds := hdsic (profile a ε) i (report b ε)
      rw [hprofile_update a b ε ε] at hds
      simp only [profile, Function.update_self] at hds
      rw [hforce a ε hε, hforce b ε hε] at hds
      rw [hpB ε hε, hpA ε hε, ← hpw, ← hpv] at hds
      have hreport_a : report a ε a = -othersWelfare v i a + ε := by
        simp [report]
      have hreport_b : report a ε b = -othersWelfare v i b := by
        simp [report, Ne.symm hab]
      rw [hreport_b, hreport_a] at hds
      linarith
    have hbound_upper (ε : ℝ) (hε : 0 < ε) :
        p w i - p v i ≤ othersWelfare v i a - othersWelfare v i b + ε := by
      have hds := hdsic (profile b ε) i (report a ε)
      rw [hprofile_update b a ε ε] at hds
      simp only [profile, Function.update_self] at hds
      rw [hforce b ε hε, hforce a ε hε] at hds
      rw [hpA ε hε, hpB ε hε, ← hpv, ← hpw] at hds
      have hreport_a : report b ε a = -othersWelfare v i a := by
        simp [report, hab]
      have hreport_b : report b ε b = -othersWelfare v i b + ε := by
        simp [report]
      rw [hreport_a, hreport_b] at hds
      linarith
    have hlower : othersWelfare v i a - othersWelfare v i b ≤ p w i - p v i := by
      apply _root_.le_of_forall_pos_le_add
      intro ε hε
      exact hbound_lower ε hε
    have hupper : p w i - p v i ≤ othersWelfare v i a - othersWelfare v i b := by
      apply _root_.le_of_forall_pos_le_add
      intro ε hε
      exact hbound_upper ε hε
    have hp : p w i - p v i =
        othersWelfare v i a - othersWelfare v i b := le_antisymm hupper hlower
    change p w i + othersWelfare w i b =
      p v i + othersWelfare v i a
    rw [← hothers_w]
    linarith

/-- Green–Laffont characterization: efficiency and DSIC force payments to have
Groves form, with each agent's Groves term independent of that agent's report.
-/
public theorem vcg_greenLaffont (x : Valuation N A → A) (p : Valuation N A → N → ℝ)
    (heff : ∀ (v : Valuation N A) (a : A), welfare v a ≤ welfare v (x v))
    (hdsic : ∀ (v : Valuation N A) (i : N) (r : A → ℝ),
      v i (x (Function.update v i r)) - p (Function.update v i r) i ≤
        v i (x v) - p v i) :
    ∃ (h : N → Valuation N A → ℝ),
      (∀ i v w, (∀ j, j ≠ i → v j = w j) → h i v = h i w) ∧
      ∀ v i, p v i = h i v - othersWelfare v i (x v) := by
  let h : N → Valuation N A → ℝ := fun i v =>
    p (Function.update v i (fun _ => 0)) i +
      othersWelfare (Function.update v i (fun _ => 0)) i
        (x (Function.update v i (fun _ => 0)))
  refine ⟨h, ?_, ?_⟩
  · intro i v w hagree
    have hupdate : Function.update v i (fun _ => (0 : ℝ)) =
        Function.update w i (fun _ => (0 : ℝ)) := by
      funext j a
      by_cases hji : j = i
      · subst j
        simp
      · rw [Function.update_of_ne hji, Function.update_of_ne hji]
        exact congrFun (hagree j hji) a
    dsimp [h]
    simp only [hupdate]
  · intro v i
    let w := Function.update v i (fun _ => (0 : ℝ))
    have hagree : ∀ j, j ≠ i → v j = w j := by
      intro j hji
      dsimp [w]
      exact (Function.update_of_ne hji _ _).symm
    have hkey := groves_key x p heff hdsic i v w hagree
    change p v i =
      (p w i + othersWelfare w i (x w)) - othersWelfare v i (x v)
    linarith

end VCG
