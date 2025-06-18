import Mathlib.Tactic
import Analysis.Section_6_1
import Analysis.Section_6_2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Analysis I, Section 6.3

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Suprema and infima of sequences

-/

namespace Chapter6

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.sup (a:Sequence) : EReal := sSup { x | ∃ n ≥ a.m, x = a n }

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.inf (a:Sequence) : EReal := sInf { x | ∃ n ≥ a.m, x = a n }

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).sup = 1 := by sorry

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).inf = -1 := by sorry

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).sup = 1 := by sorry

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).inf = 0 := by sorry

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).sup = ⊤ := by sorry

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).inf = 1 := by sorry

abbrev Sequence.bddAboveBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≤ M

abbrev Sequence.bddAbove (a:Sequence) : Prop := ∃ M, a.bddAboveBy M

abbrev Sequence.bddBelowBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≥ M

abbrev Sequence.bddBelow (a:Sequence) : Prop := ∃ M, a.bddBelowBy M

theorem Sequence.bounded_iff (a:Sequence) : a.isBounded ↔ a.bddAbove ∧ a.bddBelow := by sorry

theorem Sequence.sup_of_bounded {a:Sequence} (h: a.isBounded) : a.sup.isFinite := by sorry

theorem Sequence.inf_of_bounded {a:Sequence} (h: a.isBounded) : a.inf.isFinite := by sorry

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.le_sup {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≤ a.sup := by sorry

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.sup_le_upper {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≤ M) : a.sup ≤ M := by sorry

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.exists_between_lt_sup {a:Sequence} {y:EReal} (h: y < a.sup ) :
    ∃ n ≥ a.m, y < a n ∧ a n ≤ a.sup := by sorry

/-- Remark 6.3.7 -/
theorem Sequence.ge_inf {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≥ a.inf := by sorry

/-- Remark 6.3.7 -/
theorem Sequence.inf_ge_lower {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≥ M) : a.inf ≥ M := by sorry

/-- Remark 6.3.7 -/
theorem Sequence.exists_between_gt_inf {a:Sequence} {y:EReal} (h: y > a.inf ) :
    ∃ n ≥ a.m, y > a n ∧ a n ≥ a.inf := by sorry

abbrev Sequence.isMonotone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≥ a n

abbrev Sequence.isAntitone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≤ a n

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.convergent_of_monotone {a:Sequence} (hbound: a.bddAbove) (hmono: a.isMonotone) :
    a.convergent := by sorry

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.lim_of_monotone {a:Sequence} (hbound: a.bddAbove) (hmono: a.isMonotone) :
    lim a = a.sup := by sorry

theorem Sequence.convergent_of_antitone {a:Sequence} (hbound: a.bddBelow) (hmono: a.isAntitone) :
    a.convergent := by sorry

theorem Sequence.lim_of_antitone {a:Sequence} (hbound: a.bddBelow) (hmono: a.isAntitone) :
    lim a = a.inf := by sorry

theorem Sequence.convergent_iff_bounded_of_monotone {a:Sequence} (ha: a.isMonotone) :
    a.convergent ↔ a.isBounded := by sorry

theorem Sequence.bounded_iff_convergent_of_antitone {a:Sequence} (ha: a.isAntitone) :
    a.convergent ↔ a.isBounded := by sorry

/-- Example 6.3.9 -/
noncomputable abbrev Example_6_3_9 (n:ℕ) := ⌊ Real.pi * 10^n ⌋ / (10:ℝ)^n

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).isMonotone := by sorry

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).bddAboveBy 4 := by sorry

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).convergent := by sorry

/-- Example 6.3.9 -/
example : lim (Example_6_3_9:Sequence) ≤ 4 := by sorry

/-- Proposition 6.3.1-/
theorem lim_of_exp {x:ℝ} (hpos: 0 < x) (hbound: x < 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).convergent ∧ lim ((fun (n:ℕ) ↦ x^n):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ x^n):Sequence)
  have why : a.isAntitone := sorry
  have hbound : a.bddBelowBy 0 := by
    intro n hn; positivity
  have hbound' : a.bddBelow := by use 0
  have hconv := a.convergent_of_antitone hbound' why
  set L := lim a
  have : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = x * L := calc
    _ = lim (x • ((fun (n:ℕ) ↦ x^n):Sequence)) := by
      congr; ext n
      by_cases h: n ≥ 0
      all_goals simp [h, pow_succ']
    _ = x * lim ((fun (n:ℕ) ↦ x^n):Sequence) := by
      exact (Sequence.lim_smul x hconv).2
    _ = _ := rfl
  have why2 :lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = lim ((fun (n:ℕ) ↦ x^n):Sequence) := by sorry
  rw [this] at why2
  change x * L = L at why2
  replace why2 : x * L = 1 * L := by simp [why2]
  have hx : x ≠ 1 := by linarith
  simp only [mul_eq_mul_right_iff, hx, false_or] at why2
  simp [hconv, why2]

/-- Exercise 6.3.4 -/
theorem lim_of_exp' {x:ℝ} (hbound: x > 1) : ¬((fun (n:ℕ) ↦ x^n):Sequence).convergent := by sorry

end Chapter6
