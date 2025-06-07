import Mathlib.Tactic
import Analysis.Section_5_4


/-!
# Analysis I, Section 5.5

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

In this section we begin to use the Mathlib API for sets; the Chapter 3 set theory is deprecated in favor of this API.

Main constructions and results of this section:

- Upper bound and least upper bound on the real line
-/

namespace Chapter5

/-- Definition 5.5.1 (upper bounds).  Here we use the `upperBounds` set defined in Mathlib. -/
theorem Real.upperBound_def (E: Set Real) (M: Real) : M ∈ upperBounds E ↔ ∀ x ∈ E, x ≤ M := mem_upperBounds

/-- API for Example 5.5.2 -/
theorem Real.Icc_def (x y:Real) : Set.Icc x y = { z | x ≤ z ∧ z ≤ y } := rfl

/-- API for Example 5.5.2 -/
theorem Real.mem_Icc (x y z:Real) : z ∈ Set.Icc x y ↔ x ≤ z ∧ z ≤ y := by
  simp [Real.Icc_def]

/-- Example 5.5.2 -/
example (M: Real) : M ∈ upperBounds (Set.Icc 0 1) ↔ M ≥ 1 := by sorry

/-- API for Example 5.5.3 -/
theorem Real.Ioi_def (x:Real) : Set.Ioi x = { z | z > x } := rfl

/-- Example 5.5.3 -/
example : ¬ ∃ M, M ∈ upperBounds (Set.Ioi 0) := by sorry

/-- Example 5.5.4 -/
example : ∀ M, M ∈ upperBounds (∅ : Set Real) := by sorry

theorem Real.upperBound_upper {M M': Real} (h: M ≤ M') {E: Set Real} (hb: M ∈ upperBounds E) : M' ∈ upperBounds E := by sorry

/-- Definition 5.5.5 (least upper bound).  Here we use the `isLUB` predicate defined in Mathlib. -/
theorem Real.isLUB_def (E: Set Real) (M: Real) : IsLUB E M ↔ M ∈ upperBounds E ∧ ∀ M' ∈ upperBounds E, M' ≥ M := by
  simp_rw [ge_iff_le]
  rfl

/-- Example 5.5.6 -/
example : IsLUB (Set.Icc 0 1) 1 := by sorry

/-- Example 5.5.7 -/
example : ¬∃ M, IsLUB (∅: Set Real) M := by sorry

/-- Proposition 5.5.8 (Uniqueness of least upper bound)-/
theorem Real.LUB_unique {E: Set Real} {M M': Real} (h1: IsLUB E M) (h2: IsLUB E M') : M = M' := by
  -- This proof is written to follow the structure of the original text.
  rw [Real.isLUB_def] at h1 h2
  have h3 := h1.2 _ h2.1
  have h4 := h2.2 _ h1.1
  linarith

/-- Theorem 5.5.9 (Existence of least upper bound)-/
theorem Real.LUB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: ∃ M, M ∈ upperBounds E): ∃ S, IsLUB E S := by
  -- This proof is written to follow the structure of the original text.
  set x₀ := Set.Nonempty.some hE
  have hx₀ : x₀ ∈ E := Set.Nonempty.some_mem hE
  have claim1 (n:ℕ) : ∃! m:ℤ, (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E ∧ ¬ (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∈ upperBounds E := by
    set ε := ((1/(n+1):ℚ):Real)
    have hpos : ε.isPos := by
      simp [isPos_iff, ε, ←lt_of_coe]
      positivity
    apply existsUnique_of_exists_of_unique
    . obtain ⟨ M, hbound ⟩ := hbound
      obtain ⟨ K, _, hK ⟩ := le_mul hpos M
      obtain ⟨ L', _, hL ⟩ := le_mul hpos (-x₀)
      set L := -(L':ℤ)
      have claim1_1 : L * ε < x₀ := by
        simp [L]; linarith
      have claim1_2 : L * ε ∉ upperBounds E := by
        contrapose! claim1_1
        rw [upperBound_def] at claim1_1
        exact claim1_1 _ hx₀
      have claim1_3 : (K:Real) > (L:Real) := by
        contrapose! claim1_2
        replace claim1_2 := mul_le_mul_left claim1_2 hpos
        simp_rw [mul_comm] at claim1_2
        replace claim1_2 := lt_of_lt_of_le hK claim1_2
        exact upperBound_upper (le_of_lt claim1_2) hbound
      have claim1_4 : ∃ m:ℤ, L < m ∧ m ≤ K ∧ m*ε ∈ upperBounds E ∧ ¬ (m-1)*ε ∈ upperBounds E := by
        -- Exercise 5.5.2
        sorry
      obtain ⟨ m, _, _, hm, hm' ⟩ := claim1_4
      use m
      have : (m/(n+1):ℚ) = m*ε := by
        simp [ε,mul_of_ratCast]
        field_simp
      constructor
      . convert hm
      convert hm'
      simp [sub_of_ratCast, this, sub_mul, ε]
    -- Exercise 5.5.3
    sorry
  set m : ℕ → ℤ := fun n ↦ (claim1 n).exists.choose
  set a : ℕ → ℚ := fun n ↦ (m n:ℚ) / (n+1)
  set b : ℕ → ℚ := fun n ↦ 1 / (n+1)
  have hb : (b:Sequence).isCauchy := Cauchy_of_harmonic
  have hm1 (n:ℕ) : (a n:Real) ∈ upperBounds E := (claim1 n).exists.choose_spec.1
  have hm2 (n:ℕ) : ¬ ((a - b) n: Real) ∈ upperBounds E := (claim1 n).exists.choose_spec.2
  have claim2 (N:ℕ) : ∀ n ≥ N, ∀ n' ≥ N, |a n - a n'| ≤ 1 / (N+1) := by
    intro n hn n' hn'
    rw [abs_le]
    constructor
    . specialize hm1 n; specialize hm2 n'
      have bound1 : ((a-b) n') < a n := by
        rw [lt_of_coe]
        contrapose! hm2
        exact upperBound_upper hm2 hm1
      have bound2 : ((a-b) n') = a n' - 1 / (n'+1) := by simp [b]
      have bound3 : 1/((n':ℚ)+1) ≤ 1/(N+1) := by gcongr
      linarith
    specialize hm1 n'; specialize hm2 n
    have bound1 : ((a-b) n) < a n' := by
      rw [lt_of_coe]
      contrapose! hm2
      exact upperBound_upper hm2 hm1
    have bound2 : ((a-b) n) = a n - 1 / (n+1) := by simp [b]
    have bound3 : 1/((n+1):ℚ) ≤ 1/(N+1) := by gcongr
    -- weirdly, `linarith` times out here
    rw [bound2] at bound1
    apply le_of_lt (lt_of_lt_of_le _ bound3)
    rwa [sub_lt_comm]
  have claim3 : (a:Sequence).isCauchy := by
    -- Exercise 5.5.4
    sorry
  set S := LIM a
  have claim4 : S = LIM (a - b) := by
    have : LIM b = 0 := LIM_of_harmonic
    simp [←sub_of_LIM claim3 hb, S, this]
  use S
  rw [isLUB_def, upperBound_def]
  constructor
  . intro x hx
    change LIM a ≥ x
    apply Real.LIM_of_ge claim3
    intro n
    specialize hm1 n
    rw [upperBound_def] at hm1
    exact hm1 x hx
  intro y hy
  have claim5 (n:ℕ) : y ≥ (a-b) n := by
    contrapose! hm2
    use n
    exact upperBound_upper (le_of_lt hm2) hy
  rw [claim4]
  apply LIM_of_le _ claim5
  exact sub_of_cauchy claim3 hb


end Chapter5
