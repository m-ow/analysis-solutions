import Mathlib.Tactic
import Mathlib.Topology.Instances.Irrational
import Analysis.Section_11_4

/-!
# Analysis I, Section 11.7: A non-Riemann integrable function

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- An example of a bounded function on a compact interval that is not Riemann integrable.

-/

namespace Chapter11
open BoundedInterval Chapter9

/-- Proposition 11.7.1 -/
theorem not_integrable : BddOn f_9_3_21 (Icc 0 1) ∧ ¬ IntegrableOn f_9_3_21 (Icc 0 1) := by
  -- This proof is adapted from the structure of the original text.
  have hbdd: BddOn f_9_3_21 (Icc 0 1):= by
    use 1; intro x hx
    by_cases h: ∃ y:ℚ, y = x <;> simp [f_9_3_21, h]
  refine ⟨ hbdd, ?_ ⟩
  have hsup (P: Partition (Icc 0 1)) : ∀ J ∈ P.intervals, (sSup (f_9_3_21 '' (J:Set ℝ))) * |J|ₗ = |J|ₗ := by
    intro J hJ; by_cases hJ0: |J|ₗ = 0
    . simp [hJ0]
    have hJ0' := hJ0
    rw [←length_of_subsingleton] at hJ0
    convert (one_mul _)
    apply le_antisymm
    . apply csSup_le
      . contrapose! hJ0
        simp at hJ0
        simp [hJ0]
      intro s hs; simp at hs; obtain ⟨ x, hx, rfl ⟩ := hs
      by_cases h: ∃ y:ℚ, y = x <;> simp [f_9_3_21, h]
    apply le_csSup_of_le _ _ (show (1:ℝ) ≤ 1 by norm_num)
    . rw [bddAbove_def]
      use 1
      intro s hs; simp at hs; obtain ⟨ x, hx, rfl ⟩ := hs
      by_cases h: ∃ y:ℚ, y = x <;> simp [f_9_3_21, h]
    simp at hJ0'
    obtain ⟨ z, hz, hz' ⟩ := Dense.exists_between (Rat.denseRange_cast (𝕜 := ℝ)) hJ0'
    simp at hz hz' ⊢
    obtain ⟨ q, rfl ⟩ := hz
    refine ⟨ ↑q, ?_, q, rfl ⟩
    have := Ioo_subset J
    rw [subset_iff] at this
    apply this
    simp [hz']
  have hupper (P: Partition (Icc 0 1)) : upper_riemann_sum f_9_3_21 P = 1 := by
    simp [upper_riemann_sum]
    calc
      _ = ∑ J ∈ P.intervals, |J|ₗ := by
        apply Finset.sum_congr rfl
        intro J hJ
        rw [hsup P J hJ]
      _ = _ := by simp [Partition.sum_of_length _ P]
  replace hupper : upper_integral f_9_3_21 (Icc 0 1) = 1 := by
    rw [upper_integ_eq_inf_upper_sum hbdd]
    simp [hupper]
  have hinf (P: Partition (Icc 0 1)) : ∀ J ∈ P.intervals, (sInf (f_9_3_21 '' (J:Set ℝ))) * |J|ₗ = 0 := by
    intro J hJ; by_cases hJ0: |J|ₗ = 0
    . simp [hJ0]
    have hJ0' := hJ0
    rw [←length_of_subsingleton] at hJ0
    convert (zero_mul _)
    apply le_antisymm
    . apply csInf_le_of_le _ _ (show (0:ℝ) ≤ 0 by norm_num)
      . rw [bddBelow_def]
        use 0
        intro s hs; simp at hs; obtain ⟨ x, hx, rfl ⟩ := hs
        by_cases h: ∃ y:ℚ, y = x <;> simp [f_9_3_21, h]
      simp at hJ0'
      obtain ⟨ z, hz, hz' ⟩ := Dense.exists_between dense_irrational hJ0'
      simp at hz hz' ⊢
      refine ⟨ z, ?_, ?_ ⟩
      . have := Ioo_subset J
        rw [subset_iff] at this
        apply this
        simp [hz']
      intro q
      contrapose! hz
      simp [←hz]
    apply le_csInf
    . contrapose! hJ0
      simp at hJ0
      simp [hJ0]
    intro s hs; simp at hs; obtain ⟨ x, hx, rfl ⟩ := hs
    by_cases h: ∃ y:ℚ, y = x <;> simp [f_9_3_21, h]
  have hlower (P: Partition (Icc 0 1)) : lower_riemann_sum f_9_3_21 P = 0 := by
    simp [lower_riemann_sum]
    calc
      _ = ∑ J ∈ P.intervals, (0:ℝ) := by
        apply Finset.sum_congr rfl
        intro J hJ
        rw [hinf P J hJ]
      _ = _ := by simp
  replace hlower : lower_integral f_9_3_21 (Icc 0 1) = 0 := by
    rw [lower_integ_eq_sup_lower_sum hbdd]
    simp [hlower]
  intro h
  simp [IntegrableOn, hlower, hupper] at h


end Chapter11
