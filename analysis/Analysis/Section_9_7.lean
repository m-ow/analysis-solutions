import Mathlib.Tactic
import Analysis.Section_9_3
import Analysis.Section_9_4


/-!
# Analysis I, Section 9.7

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- The intermediate value theorem
-/

namespace Chapter9

/-- Theorem 9.7.1 (Intermediate value theorem) -/
theorem intermediate_value {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (Set.Icc a b)) {y:ℝ} (hy: y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f a) (f b)) :
  ∃ c ∈ Set.Icc a b, f c = y := by
  -- This proof is written to follow the structure of the original text.
  rcases hy with hy_left | hy_right
  . by_cases hya : y = f a
    . use a; simp [hya, le_of_lt hab]
    by_cases hyb : y = f b
    . use b; simp [hyb, le_of_lt hab]
    simp at hy_left
    replace hya : f a < y := by contrapose! hya; linarith
    replace hyb : y < f b := by contrapose! hyb; linarith
    set E := {x | x ∈ Set.Icc a b ∧ f x < y}
    have hE : E ⊆ Set.Icc a b := by
      rintro x ⟨hx₁, hx₂⟩; exact hx₁
    have hE_bdd : BddAbove E := BddAbove.mono hE bddAbove_Icc
    have hEa : a ∈ E := by
      simp [E, hya, le_of_lt hab]
    have hE_nonempty : E.Nonempty := by
      use a
    set c := sSup E
    have hc : c ∈ Set.Icc a b := by
      simp
      constructor
      . exact ConditionallyCompleteLattice.le_csSup _ _ hE_bdd hEa
      convert csSup_le_csSup bddAbove_Icc hE_nonempty hE
      exact (csSup_Icc (le_of_lt hab)).symm
    use c, hc
    have hfc_upper : f c ≤ y := by
      have hxe (n:ℕ) : ∃ x ∈ E, c - 1/(n+1:ℝ) < x := by
        have : 1/(n+1:ℝ) > 0 := by positivity
        replace : c - 1/(n+1:ℝ) < sSup E := by linarith
        exact exists_lt_of_lt_csSup hE_nonempty this
      set x := fun n ↦ (hxe n).choose
      have hx1 (n:ℕ) : x n ∈ E := (hxe n).choose_spec.1
      have hx2 (n:ℕ) : c - 1/(n+1:ℝ) < x n := (hxe n).choose_spec.2
      have : Filter.Tendsto x Filter.atTop (nhds c) := by
        apply Filter.Tendsto.squeeze (g := fun j ↦ c - 1/(j+1:ℝ)) (h := fun j ↦ c) (f := x)
        . convert Filter.Tendsto.const_sub c (c:=0) _
          . simp
          exact tendsto_one_div_add_atTop_nhds_zero_nat
        . exact tendsto_const_nhds
        . exact fun n ↦ le_of_lt (hx2 n)
        exact fun n ↦ ConditionallyCompleteLattice.le_csSup _ _ hE_bdd (hx1 n)
      replace := Filter.Tendsto.comp_of_continuous hc (hf.continuousWithinAt hc) (fun n ↦ hE (hx1 n)) this
      have hfxny (n:ℕ) : f (x n) ≤ y := by
        specialize hx1 n
        simp [E] at hx1
        exact le_of_lt hx1.2
      exact le_of_tendsto' this hfxny
    have hne : c ≠ b := by
      contrapose! hfc_upper
      rwa [hfc_upper]
    replace hne : c < b := by contrapose! hne; simp at hc; linarith
    have hfc_lower : y ≤ f c := by
      have : ∃ N:ℕ, ∀ n ≥ N, (c+1/(n+1:ℝ)) < b := by
        obtain ⟨ N, hN ⟩ := exists_nat_gt (1/(b-c))
        use N
        intro n hn
        have hpos : 0 < b-c := by linarith
        have : 1/(n+1:ℝ) < b-c := by
          rw [one_div_lt (by positivity) (by positivity)]
          apply hN.trans; norm_cast; linarith
        linarith
      obtain ⟨ N, hN ⟩ := this
      have hmem : ∀ n ≥ N, (c + 1/(n+1:ℝ)) ∈ Set.Icc a b := by
        intro n hn
        simp only [Set.mem_Icc, le_of_lt (hN n hn), and_true]
        have : 1/(n+1:ℝ) > 0 := by positivity
        replace : c + 1/(n+1:ℝ) > c := by linarith
        simp at hc
        linarith
      have : ∀ n ≥ N, c + 1/(n+1:ℝ) ∉ E := by
        intro n _
        have : 1/(n+1:ℝ) > 0 := by positivity
        replace : c + 1/(n+1:ℝ) > c := by linarith
        exact notMem_of_csSup_lt this hE_bdd
      replace : ∀ n ≥ N, f (c + 1/(n+1:ℝ)) ≥ y := by
        intro n hn
        specialize this n hn
        contrapose! this
        simp only [Set.mem_Icc, Set.mem_setOf_eq, E, this, le_of_lt (hN n hn), and_true]
        have := hmem n hn
        simp only [Set.mem_Icc] at this
        tauto
      have hconv : Filter.Tendsto (fun n:ℕ ↦ c + 1/(n+1:ℝ)) Filter.atTop (nhds c) := by
        convert Filter.Tendsto.const_add c (c:=0) _
        . simp
        exact tendsto_one_div_add_atTop_nhds_zero_nat
      replace hf := (hf.continuousWithinAt hc).tendsto
      rw [nhdsWithin.eq_1] at hf
      have hconv' : Filter.Tendsto (fun n:ℕ ↦ c + 1/(n+1:ℝ)) Filter.atTop (Filter.principal (Set.Icc a b)) := by
        simp only [Filter.tendsto_principal, Filter.eventually_atTop]
        use N
      replace hconv' := Filter.tendsto_inf.mpr ⟨ hconv, hconv' ⟩
      apply ge_of_tendsto (Filter.Tendsto.comp hf hconv') _
      simp only [Function.comp_apply, Filter.eventually_atTop]
      use N
    linarith
  sorry

open Classical in
noncomputable abbrev f_9_7_1 : ℝ → ℝ := fun x ↦ if x ≤ 0 then -1 else 1

example : 0 ∈ Set.Icc (f_9_7_1 (-1)) (f_9_7_1 1) ∧ ¬ ∃ x ∈ Set.Icc (-1) 1, f_9_7_1 x = 0 := by
  sorry

/-- Remark 9.7.2 -/
abbrev f_9_7_2 : ℝ → ℝ := fun x ↦ x^3 - x

example : f_9_7_2 (-2) = -6 := by sorry
example : f_9_7_2 2 = 6 := by sorry
example : f_9_7_2 (-1) = 0 := by sorry
example : f_9_7_2 0 = 0 := by sorry
example : f_9_7_2 1 = 0 := by sorry

/-- Remark 9.7.3 -/
example : ∃ x:ℝ, 0 ≤ x ∧ x ≤ 2 ∧ x^2 = 2 := by sorry

/-- Corollary 9.7.4 (Images of continuous functions) / Exercise 9.7.1 -/
theorem continuous_image_Icc {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (Set.Icc a b)) {y:ℝ} (hy: sInf (f '' Set.Icc a b) ≤ y ∧ y ≤ sSup (f '' Set.Icc a b)) : ∃ c ∈ Set.Icc a b, f c = y := by
  sorry

theorem continuous_image_Icc' {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (Set.Icc a b)) : f '' Set.Icc a b = Set.Icc (sInf (f '' Set.Icc a b)) (sSup (f '' Set.Icc a b)) := by
  sorry

/-- Exercise 9.7.2 -/
theorem exists_fixed_pt {f:ℝ → ℝ} (hf: ContinuousOn f (Set.Icc 0 1)) (hmap: f '' Set.Icc 0 1 ⊆ Set.Icc 0 1) : ∃ x ∈ Set.Icc 0 1, f x = x := by
  sorry

end Chapter9
