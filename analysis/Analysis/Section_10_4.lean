import Mathlib.Tactic
import Analysis.Section_9_3
import Analysis.Section_9_4
import Analysis.Section_10_1

/-!
# Analysis I, Section 10.4

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- The inverse function theorem

-/

open Chapter9
namespace Chapter10

/-- Lemma 10.4.1 -/
theorem _root_.HasDerivWithinAt.of_inverse {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgf: ∀ x ∈ X, g (f x) = x)
  {x₀ y₀ f'x₀ g'y₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (Filter.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'y₀ Y y₀) :
  g'y₀ * f'x₀ = 1 := by
  -- This proof is written to follow the structure of the original text.
  have h1 : HasDerivWithinAt (fun x ↦ x) (g'y₀ * f'x₀) X x₀ := by
    apply HasDerivWithinAt.congr (HasDerivWithinAt.of_comp hfx₀ hfXY hf hg) _ (hgf x₀ hx₀).symm
    intro x hx; simp [hgf x hx]
  have h2 : HasDerivWithinAt (fun x ↦ x) 1 X x₀ := by exact hasDerivWithinAt_id _ _
  exact derivative_unique hcluster h1 h2


theorem _root_.HasDerivWithinAt.of_inverse' {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgf: ∀ x ∈ X, g (f x) = x)
  {x₀ y₀ f'x₀ g'y₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (Filter.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'y₀ Y y₀) :
  g'y₀ = 1/f'x₀ :=
    eq_one_div_of_mul_eq_one_left (HasDerivWithinAt.of_inverse hfXY hgf hx₀ hfx₀ hcluster hf hg)

theorem _root_.HasDerivWithinAt.of_inverse_of_zero_deriv {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgf: ∀ x ∈ X, g (f x) = x)
  {x₀ y₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (Filter.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f 0 X x₀) :
  ¬ DifferentiableWithinAt ℝ g Y y₀ := by
  by_contra this
  rw [DifferentiableWithinAt.iff] at this
  obtain ⟨ L, hg ⟩ := this
  replace hg := HasDerivWithinAt.of_inverse hfXY hgf hx₀ hfx₀ hcluster hf hg
  simp at hg

example : ¬ DifferentiableWithinAt ℝ (fun x:ℝ ↦ x^(1/3:ℝ)) (Set.Ici 0) 0 := by sorry

/-- Theorem 10.4.2 (Inverse function theorem) -/
theorem inverse_function_theorem {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgYX: ∀ y ∈ Y, g y ∈ X)
  (hgf: ∀ x ∈ X, g (f x) = x) (hfg: ∀ y ∈ Y, f (g y) = y)
  {x₀ y₀ f'x₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀) (hne : f'x₀ ≠ 0)
  (hcluster: ClusterPt x₀ (Filter.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: ContinuousWithinAt g Y y₀) :
    HasDerivWithinAt g (1/f'x₀) Y y₀ := by
    -- This proof is written to follow the structure of the original text.
    have had : AdherentPt y₀ (Y \ {y₀}) := by
      simp [←AdherentPt_def, limit_of_AdherentPt] at hcluster ⊢
      obtain ⟨ x, hx, hconv ⟩ := hcluster
      use f ∘ x
      constructor
      . intro n
        constructor
        . aesop
        . have hx2 := (hx n).2
          contrapose! hx2
          apply_fun g at hx2
          simp [←hfx₀, hgf _ hx₀, hgf _ (hx n).1] at hx2
          exact hx2
      rw [←hfx₀]
      apply Filter.Tendsto.comp_of_continuous hx₀ _ (fun n ↦ (hx n).1) hconv
      exact ContinuousWithinAt.of_differentiableWithinAt (DifferentiableWithinAt.of_hasDeriv hf)
    rw [HasDerivWithinAt.iff, ←Convergesto.iff, Convergesto.iff_conv _ _ had]
    intro y hy hconv
    set x : ℕ → ℝ := fun n ↦ g (y n)
    have hy' : ∀ n, y n ∈ Y := by aesop
    have hy₀: y₀ ∈ Y := by aesop
    have hx : ∀ n, x n ∈ X \ {x₀}:= by
      sorry
    replace hconv := Filter.Tendsto.comp_of_continuous hy₀ hg hy' hconv
    have had' : AdherentPt x₀ (X \ {x₀}) := by rwa [AdherentPt_def]
    have hgy₀ : g y₀ = x₀ := by aesop
    rw [hgy₀] at hconv
    rw [HasDerivWithinAt.iff, ←Convergesto.iff, Convergesto.iff_conv _ _ had'] at hf
    specialize hf x hx hconv
    convert Filter.Tendsto.inv₀ hf hne using 2 with n
    . simp [hgy₀, x, ←hfx₀, hfg _ (hy' n), hgf _ hx₀]
    simp

/-- Exercise 10.4.1(a) -/
example {n:ℕ} (hn: n > 0) : ContinuousOn (fun x:ℝ ↦ x^(1/n:ℝ)) (Set.Ici 0) := by sorry

/-- Exercise 10.4.1(b) -/
example {n:ℕ} (hn: n > 0) {x:ℝ} (hx: x ∈ Set.Ici 0) : HasDerivWithinAt (fun x:ℝ ↦ x^(1/n:ℝ))
  ((n:ℝ)⁻¹ * x^((n:ℝ)⁻¹-1)) (Set.Ici 0) x := by sorry

/-- Exercise 10.4.2(a) -/
example (q:ℚ) {x:ℝ} (hx: x ∈ Set.Ici 0) :
  HasDerivWithinAt (fun x:ℝ ↦ x^(q:ℝ)) (q * x^(q-1:ℝ)) (Set.Ici 0) x := by
  sorry

/-- Exercise 10.4.2(b) -/
example (q:ℚ) : Filter.Tendsto (fun x:ℝ ↦ (x^(q:ℝ)-1)/(x-1))
                (nhds 1 ⊓ Filter.principal (Set.Ici 0 \ {1})) (nhds q) := by
  sorry

/-- Exercise 10.4.3(a) -/
example (α:ℝ) : Filter.Tendsto (fun x:ℝ ↦ (x^α-1^α)/(x-1))
                (nhds 1 ⊓ Filter.principal (Set.Ici 0 \ {1})) (nhds α) := by
  sorry

/-- Exercise 10.4.2(b) -/
example (α:ℝ) {x:ℝ} (hx: x ∈ Set.Ici 0) :
  HasDerivWithinAt (fun x:ℝ ↦ x^α) (α * x^(α-1)) (Set.Ici 0) x := by
  sorry


end Chapter10
