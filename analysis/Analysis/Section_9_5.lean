import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_3
import Analysis.Section_9_4

/-!
# Analysis I, Section 9.5: Left and right limits

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Left and right limits.
-/

namespace Chapter9

/-- Definition 9.5.1.  We give left and right limits the "junk" value of 0 if the limit does not exist. -/
abbrev RightLimitExists (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop := ∃ L, Filter.Tendsto f ((nhds x₀) ⊓ Filter.principal (X ∩ Set.Ioi x₀)) (nhds L)

open Classical in
noncomputable abbrev right_limit (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : ℝ := if h : RightLimitExists X f x₀ then h.choose else 0

abbrev LeftLimitExists (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop := ∃ L, Filter.Tendsto f ((nhds x₀) ⊓ Filter.principal (X ∩ Set.Iio x₀)) (nhds L)

open Classical in
noncomputable abbrev left_limit (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : ℝ := if h: LeftLimitExists X f x₀ then h.choose else 0

theorem right_limit.eq {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ Set.Ioi x₀))
  (h: Filter.Tendsto f ((nhds x₀) ⊓ Filter.principal (X ∩ Set.Ioi x₀)) (nhds L)) : RightLimitExists X f x₀ ∧ right_limit X f x₀ = L := by
  have h' : RightLimitExists X f x₀ := by use L
  simp [right_limit, h']
  have hne : (nhds x₀ ⊓ Filter.principal (X ∩ Set.Ioi x₀)).NeBot := by
    rwa [←nhdsWithin.eq_1, ←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

theorem left_limit.eq {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ Set.Iio x₀))
  (h: Filter.Tendsto f ((nhds x₀) ⊓ Filter.principal (X ∩ Set.Iio x₀))
  (nhds L)) : LeftLimitExists X f x₀ ∧ left_limit X f x₀ = L := by
  have h' : LeftLimitExists X f x₀ := by use L
  simp [left_limit, h']
  have hne : (nhds x₀ ⊓ Filter.principal (X ∩ Set.Iio x₀)).NeBot := by
    rwa [←nhdsWithin.eq_1, ←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

theorem right_limit.eq' {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: RightLimitExists X f x₀) :
  Filter.Tendsto f ((nhds x₀) ⊓ Filter.principal (X ∩ Set.Ioi x₀)) (nhds (right_limit X f x₀)) := by
  simp [right_limit, h]; exact h.choose_spec

theorem left_limit.eq' {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: LeftLimitExists X f x₀) :
  Filter.Tendsto f ((nhds x₀) ⊓ Filter.principal (X ∩ Set.Iio x₀)) (nhds (left_limit X f x₀)) := by
  simp [left_limit, h]; exact h.choose_spec

/-- Example 9.5.2.  The second part of this example is no longer operative as we assign "junk" values to our functions instead of leaving them undefined. -/
example : right_limit Set.univ Real.sign 0 = 1 := by sorry

example : left_limit Set.univ Real.sign 0 = -1 := by sorry

theorem right_limit.conv {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (had: AdherentPt x₀ (X ∩ Set.Ioi x₀))
  (h: RightLimitExists X f x₀)
  (a:ℕ → ℝ) (ha: ∀ n, a n ∈ X ∩ Set.Ioi x₀)
  (hconv: Filter.Tendsto a Filter.atTop (nhds x₀)) :
  Filter.Tendsto (fun n ↦ f (a n)) Filter.atTop (nhds (right_limit X f x₀)) := by
  obtain ⟨ L, hL ⟩ := h
  apply Convergesto.comp had _ ha hconv
  rwa [Convergesto.iff, (right_limit.eq had hL).2]

theorem left_limit.conv {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (had: AdherentPt x₀ (X ∩ Set.Iio x₀))
  (h: LeftLimitExists X f x₀)
  (a:ℕ → ℝ) (ha: ∀ n, a n ∈ X ∩ Set.Iio x₀)
  (hconv: Filter.Tendsto a Filter.atTop (nhds x₀)) :
  Filter.Tendsto (fun n ↦ f (a n)) Filter.atTop (nhds (left_limit X f x₀)) := by
  obtain ⟨ L, hL ⟩ := h
  apply Convergesto.comp had _ ha hconv
  rwa [Convergesto.iff, (left_limit.eq had hL).2]

/-- Proposition 9.5.3 -/
theorem ContinuousAt.iff_eq_left_right_limit {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: x₀ ∈ X)
  (had_left: AdherentPt x₀ (X ∩ Set.Iio x₀)) (had_right: AdherentPt x₀ (X ∩ Set.Ioi x₀)) :
  ContinuousWithinAt f X x₀ ↔ (RightLimitExists X f x₀ ∧ right_limit X f x₀ = f x₀) ∧ (LeftLimitExists X f x₀ ∧ left_limit X f x₀ = f x₀) := by
  -- This proof is written to follow the structure of the original text.
  constructor
  . sorry
  intro ⟨ ⟨ hre, hright⟩, ⟨ hle, lheft ⟩ ⟩
  set L := f x₀
  have := (ContinuousWithinAt.tfae X f h).out 0 2
  rw [this]
  intro ε hε
  replace hre := right_limit.eq' hre
  replace hle := left_limit.eq' hle
  rw [hright, ←Convergesto.iff] at hre
  rw [lheft, ←Convergesto.iff] at hle
  simp [Convergesto, Real.CloseNear, Real.CloseFn] at hre hle
  specialize hre ε hε; obtain ⟨ δ_plus, hδ_plus, hre ⟩ := hre
  specialize hle ε hε; obtain ⟨ δ_minus, hδ_minus, hle ⟩ := hle
  use min δ_plus δ_minus, (by positivity)
  intro x hx hxx₀
  rcases lt_trichotomy x x₀ with hlt | heq | hgt
  . sorry
  . sorry
  sorry

abbrev HasJumpDiscontinuity (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop :=
  RightLimitExists X f x₀ ∧ LeftLimitExists X f x₀ ∧ right_limit X f x₀ ≠ left_limit X f x₀

example : HasJumpDiscontinuity Set.univ Real.sign 0 := by sorry

abbrev HasRemovableDiscontinuity (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop :=
  RightLimitExists X f x₀ ∧ LeftLimitExists X f x₀ ∧ right_limit X f x₀ = left_limit X f x₀
  ∧ right_limit X f x₀ ≠ f x₀

example : HasRemovableDiscontinuity Set.univ f_9_3_17 0 := by sorry

example : ¬ HasRemovableDiscontinuity Set.univ (fun x ↦ 1/x) 0 := by sorry

example : ¬ HasJumpDiscontinuity Set.univ (fun x ↦ 1/x) 0 := by sorry

/- Exercise 9.5.1: Write down a definition of what it would mean for a limit of a function to be `+∞` or `-∞`, apply to `fun x ↦ 1/x`, and state and prove a version of Proposition 9.3.9. -/


end Chapter9
