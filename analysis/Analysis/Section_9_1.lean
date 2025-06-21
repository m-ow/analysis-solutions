import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Analysis I, Section 9.1

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Intervals
- Adherent points, limit points, isolated points
- Closed sets and closure
- The Heine-Borel theorem for the real line

-/

/- Definition 9.1.1 (Intervals) -/
#check Set.Icc_def
#check Set.Ico_def
#check Set.Ioc_def
#check Set.Ioo_def
#check Set.Ici_def
#check Set.Ioi_def
#check Set.Iic_def
#check Set.Iio_def

#check EReal.image_coe_Icc
#check EReal.image_coe_Ico
#check EReal.image_coe_Ioc
#check EReal.image_coe_Ioo
#check EReal.image_coe_Ici
#check EReal.image_coe_Ioi
#check EReal.image_coe_Iic
#check EReal.image_coe_Iio

/-- Example 9.1.4 -/
example {a b: EReal} (h: a > b) : Set.Icc a b = ∅ := by
  sorry

example {a b: EReal} (h: a ≥ b) : Set.Ico a b = ∅ := by
  sorry

example {a b: EReal} (h: a ≥ b) : Set.Ioc a b = ∅ := by
  sorry

example {a b: EReal} (h: a ≥ b) : Set.Ioo a b = ∅ := by
  sorry

example {a b: EReal} (h: a = b) : Set.Icc a a = {a} := by
  sorry

/-- Definition 9.1.5.  Note that a slightly different `Real.adherent` was defined in Chapter 6.4 -/
abbrev Real.adherent' (ε:ℝ) (x:ℝ) (X: Set ℝ) := ∃ y ∈ X, |x - y| ≤ ε

/-- Example 9.1.7 -/
example : (0.5:ℝ).adherent' 1.1 (Set.Ioo 0 1) := by sorry

example : ¬ (0.1:ℝ).adherent' 1.1 (Set.Ioo 0 1) := by sorry

example : (0.5:ℝ).adherent' 1.1 {1,2,3} := by sorry


namespace Chapter9

/-- Definition 9.1.ℝ-/
abbrev AdherentPt (x:ℝ) (X:Set ℝ) := ∀ ε > (0:ℝ), ε.adherent' x X

example : AdherentPt 1 (Set.Ioo 0 1) := by sorry

example : ¬ AdherentPt 2 (Set.Ioo 0 1) := by sorry

/-- Definition 9.1.10 (Closure).  Here we identify this definition with the Mathilb version. -/
theorem closure_def (X:Set ℝ) : closure X = { x | AdherentPt x X } := by
  ext x
  simp [Real.mem_closure_iff, AdherentPt, Real.adherent']
  constructor
  . intro h ε hε
    obtain ⟨ y, hy, hxy ⟩ := h ε hε
    refine ⟨ y, hy, ?_ ⟩
    rw [abs_sub_comm]; linarith
  intro h ε hε
  obtain ⟨ y, hy, hxy ⟩ := h (ε/2) (half_pos hε)
  refine ⟨ y, hy, ?_ ⟩
  rw [abs_sub_comm]; linarith

theorem closure_def' (X:Set ℝ) (x :ℝ) : x ∈ closure X ↔ AdherentPt x X := by
  simp [closure_def]

/-- identification of `AdherentPt` with Mathlib's `ClusterPt` -/
theorem AdherentPt_def (x:ℝ) (X:Set ℝ) : AdherentPt x X = ClusterPt x (Filter.principal X) := by
  rw [←closure_def', mem_closure_iff_clusterPt]

/-- Lemma 9.1.11 / Exercise 9.1.2 -/
theorem subset_closure (X:Set ℝ): X ⊆ closure X := by sorry

/-- Lemma 9.1.11 / Exercise 9.1.2 -/
theorem closure_union (X Y:Set ℝ): closure (X ∪ Y) = closure X ∪ closure Y := by sorry

/-- Lemma 9.1.11 / Exercise 9.1.2 -/
theorem closure_inter (X Y:Set ℝ): closure (X ∩ Y) ⊆ closure X ∩ closure Y := by sorry

/-- Lemma 9.1.11 / Exercise 9.1.2 -/
theorem closure_subset {X Y:Set ℝ} (h: X ⊆ Y): closure X ⊆ closure Y := by sorry

/-- Exercise 9.1.1 -/
theorem closure_of_subset_closure {X Y:Set ℝ} (h: X ⊆ Y) (h' : Y ⊆ closure X): closure Y = closure X := by sorry

/-- Lemma 9.1.12 -/
theorem closure_of_Ioo {a b:ℝ} (h:a < b) : closure (Set.Ioo a b) = Set.Icc a b := by
  -- This proof is written to follow the structure of the original text.
  ext x; simp [closure_def, AdherentPt, Real.adherent']
  constructor
  . intro h
    contrapose! h
    rcases le_or_gt a x with h' | h'
    . specialize h h'
      use x-b, by linarith
      rintro y ⟨ h1, h2 ⟩
      apply lt_of_lt_of_le _ (le_abs_self _)
      linarith
    use a-x, by linarith
    rintro y ⟨ h1, h2 ⟩
    apply lt_of_lt_of_le _ (neg_le_abs _)
    linarith
  rintro ⟨ h1, h2 ⟩
  by_cases ha : x = a
  . sorry
  by_cases hb : x = b
  . sorry
  intro ε hε
  use x, ⟨ by contrapose! ha; linarith, by contrapose! hb; linarith ⟩
  simp [le_of_lt hε]

theorem closure_of_Ioc {a b:ℝ} (h:a < b) : closure (Set.Ioc a b) = Set.Icc a b := by
  sorry

theorem closure_of_Ico {a b:ℝ} (h:a < b) : closure (Set.Ico a b) = Set.Icc a b := by
  sorry

theorem closure_of_Icc {a b:ℝ} (h:a ≤ b) : closure (Set.Icc a b) = Set.Icc a b := by
  sorry

theorem closure_of_Ioi {a:ℝ} : closure (Set.Ioi a) = Set.Ici a := by
  sorry

theorem closure_of_Ici {a:ℝ} : closure (Set.Ici a) = Set.Ici a := by
  sorry

theorem closure_of_Iio {a:ℝ} : closure (Set.Iio a) = Set.Iic a := by
  sorry

theorem closure_of_Iic {a:ℝ} : closure (Set.Iic a) = Set.Iic a := by
  sorry

theorem closure_of_R : closure (Set.univ: Set ℝ) = Set.univ := by sorry

/-- Lemma 9.1.13 / Exercise 9.1.3 -/
theorem closure_of_N :
  closure ((fun n:ℕ ↦ (n:ℝ)) '' Set.univ) = ((fun n:ℕ ↦ (n:ℝ)) '' Set.univ) := by
    sorry

/-- Lemma 9.1.13 / Exercise 9.1.3 -/
theorem closure_of_Z :
  closure ((fun n:ℤ ↦ (n:ℝ)) '' Set.univ) = ((fun n:ℤ ↦ (n:ℝ)) '' Set.univ) := by
    sorry

/-- Lemma 9.1.13 / Exercise 9.1.3 -/
theorem closure_of_Q :
  closure ((fun n:ℚ ↦ (n:ℝ)) '' Set.univ) = Set.univ := by
    sorry

/-- Lemma 9.1.14 / Exercise 9.1.5 -/
theorem limit_of_AdherentPt (X: Set ℝ) (x:ℝ) :
  AdherentPt x X ↔ ∃ a : ℕ → ℝ, (∀ n, a n ∈ X) ∧ Filter.Tendsto a Filter.atTop (nhds x) := by
    sorry

theorem AdherentPt.of_mem {X: Set ℝ} {x: ℝ} (h: x ∈ X) : AdherentPt x X := by
  rw [limit_of_AdherentPt]
  use fun _ ↦ x
  simp [h]

/-- Definition 9.1.15.  Here we use the Mathlib definition. -/
theorem isClosed_def (X:Set ℝ): IsClosed X ↔ closure X = X :=
  closure_eq_iff_isClosed.symm

theorem isClosed_def' (X:Set ℝ): IsClosed X ↔ ∀ x, AdherentPt x X → x ∈ X := by
  simp [isClosed_def, subset_antisymm_iff, subset_closure]
  simp [closure_def]
  rfl

/-- Examples 9.1.16 -/
theorem Icc_closed {a b:ℝ} (h: a ≤ b) : IsClosed (Set.Icc a b) := by sorry

/-- Examples 9.1.16 -/
theorem Ici_closed (a:ℝ) : IsClosed (Set.Ici a) := by sorry

/-- Examples 9.1.16 -/
theorem Iic_closed (a:ℝ) : IsClosed (Set.Iic a) := by sorry

/-- Examples 9.1.16 -/
theorem R_closed : IsClosed (Set.univ : Set ℝ) := by sorry

/-- Examples 9.1.16 -/
theorem Ico_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (Set.Ico a b) := by sorry

/-- Examples 9.1.16 -/
theorem Ioc_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (Set.Ioc a b) := by sorry

/-- Examples 9.1.16 -/
theorem Ioo_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (Set.Ioo a b) := by sorry

/-- Examples 9.1.16 -/
theorem Ioi_not_closed (a:ℝ) : ¬ IsClosed (Set.Ioi a) := by sorry

/-- Examples 9.1.16 -/
theorem Iio_not_closed (a:ℝ) : ¬ IsClosed (Set.Iio a) := by sorry

/-- Examples 9.1.16 -/
theorem N_closed : IsClosed ((fun n:ℕ ↦ (n:ℝ)) '' Set.univ) := by sorry

/-- Examples 9.1.16 -/
theorem Z_closed : IsClosed ((fun n:ℤ ↦ (n:ℝ)) '' Set.univ) := by sorry

/-- Examples 9.1.16 -/
theorem Q_not_closed : ¬ IsClosed ((fun n:ℚ ↦ (n:ℝ)) '' Set.univ) := by sorry

/-- Corollary 9.1.17 -/
theorem isClosed_iff_limits_mem (X: Set ℝ) :
  IsClosed X ↔ ∀ (a:ℕ → ℝ) (L:ℝ), (∀ n, a n ∈ X) → Filter.Tendsto a Filter.atTop (nhds L) → L ∈ X := by
  rw [isClosed_def']
  constructor
  . intro h a L ha hL
    apply h L
    rw [limit_of_AdherentPt]
    exact ⟨a, ha, hL ⟩
  intro h x hx
  rw [limit_of_AdherentPt] at hx
  obtain ⟨ a, ha, hL ⟩ := hx
  exact h a x ha hL

/-- Definition 9.1.18 (Limit points) -/
abbrev LimitPt (x:ℝ) (X: Set ℝ) := AdherentPt x (X \ {x})

/-- Identification with Mathlib's `AccPt`-/
theorem LimitPt.iff_AccPt (x:ℝ) (X: Set ℝ) : LimitPt x X ↔ AccPt x (Filter.principal X) := by
  rw [accPt_principal_iff_clusterPt,←AdherentPt_def]

/-- Definition 9.1.18 (Isolated points) -/
abbrev IsolatedPt (x:ℝ) (X: Set ℝ) := x ∈ X ∧ ∃ ε>0, ∀ y ∈ X \ {x}, |x-y| > ε

/-- Example 9.1.19 -/
example : AdherentPt 3 ((Set.Ioo 1 2) ∪ {3}) := by sorry

example : ¬ LimitPt 3 ((Set.Ioo 1 2) ∪ {3}) := by sorry

example : ¬ IsolatedPt 3 ((Set.Ioo 1 2) ∪ {3}) := by sorry

/-- Remark 9.1.20 -/
theorem LimitPt.iff_limit (x:ℝ) (X: Set ℝ) :
  LimitPt x X ↔ ∃ a : ℕ → ℝ, (∀ n, a n ∈ X \ {x}) ∧ Filter.Tendsto a Filter.atTop (nhds x) := by
  simp [limit_of_AdherentPt]


open Filter in
/-- This lemma is in more recent versions of Mathlib and can be deleted once Mathlib is updated. -/
theorem tendsto_mul_add_inv_atTop_nhds_zero (a c : ℝ) (ha : a ≠ 0) :
    Tendsto (fun x => (a * x + c)⁻¹) atTop (nhds 0) := by
  obtain ha' | ha' := lt_or_gt_of_ne ha
  · exact tendsto_inv_atBot_zero.comp
      (tendsto_atBot_add_const_right _ c (tendsto_id.const_mul_atTop_of_neg ha'))
  · exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ c (tendsto_id.const_mul_atTop ha'))

/-- Lemma 9.1.21 -/
theorem mem_Icc_isLimit {a b x:ℝ} (h: a < b) (hx: x ∈ Set.Icc a b) : LimitPt x (Set.Icc a b) := by
  -- This proof is written to follow the structure of the original text, with some slight simplifications.
  simp at hx
  rw [LimitPt.iff_limit]
  rcases le_iff_lt_or_eq.1 hx.2 with hxb | hxb
  . use (fun n:ℕ ↦ (x + 1/(n+(b-x)⁻¹)))
    constructor
    . intro n
      simp
      have : b - x > 0 := by linarith
      have : (b - x)⁻¹ > 0 := by positivity
      have : n + (b - x)⁻¹ > 0 := by linarith
      refine ⟨ ⟨ ?_, ?_⟩, by linarith ⟩
      . have : (n+(b - x)⁻¹)⁻¹ > 0 := by positivity
        linarith
      have : (b-x)⁻¹ ≤ n + (b - x)⁻¹ := by linarith
      have : (n + (b - x)⁻¹)⁻¹ ≤ b-x := by rwa [inv_le_comm₀ (by positivity) (by positivity)]
      linarith
    convert Filter.Tendsto.const_add x (c := 0) _
    . simp
    convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/(k+(b-x)⁻¹)) (y := Filter.atTop) _ _
    . convert tendsto_mul_add_inv_atTop_nhds_zero 1 (b - x)⁻¹ (by norm_num) using 2 with n
      simp
    exact tendsto_natCast_atTop_atTop
  sorry




theorem mem_Ico_isLimit {a b x:ℝ} (hx: x ∈ Set.Ico a b) : LimitPt x (Set.Ico a b) := by
  sorry

theorem mem_Ioc_isLimit {a b x:ℝ} (hx: x ∈ Set.Ioc a b) : LimitPt x (Set.Ioc a b) := by
  sorry

theorem mem_Ioo_isLimit {a b x:ℝ} (hx: x ∈ Set.Ioo a b) : LimitPt x (Set.Ioo a b) := by
  sorry

theorem mem_Ici_isLimit {a x:ℝ} (hx: x ∈ Set.Ici a) : LimitPt x (Set.Ici a) := by
  sorry

theorem mem_Ioi_isLimit {a x:ℝ} (hx: x ∈ Set.Ioi a) : LimitPt x (Set.Ioi a) := by
  sorry

theorem mem_Iic_isLimit {a x:ℝ} (hx: x ∈ Set.Iic a) : LimitPt x (Set.Iic a) := by
  sorry

theorem mem_Iio_isLimit {a x:ℝ} (hx: x ∈ Set.Iio a) : LimitPt x (Set.Iio a) := by
  sorry

theorem mem_R_isLimit {x:ℝ} : LimitPt x (Set.univ) := by
  sorry

/-- Definition 9.1.22.  We use here Mathlib's `Bornology.IsBounded`-/

theorem isBounded_def (X: Set ℝ) : Bornology.IsBounded X ↔ ∃ M > 0, X ⊆ Set.Icc (-M) M := by
  simp [isBounded_iff_forall_norm_le]
  constructor
  . intro h
    obtain ⟨ C, hC ⟩ := h
    use (max C 1)
    constructor
    . apply lt_of_lt_of_le _ (le_max_right _ _)
      norm_num
    intro x hx
    specialize hC x hx
    rw [abs_le'] at hC
    simp [hC.1, hC.2]
    have := le_max_left C 1
    linarith
  intro h
  obtain ⟨ M, hM, hXM ⟩ := h
  use M
  intro x hx
  replace hXM := hXM hx
  simp [abs_le'] at hXM ⊢
  simp [hXM]
  linarith [hXM.1]

/-- Example 9.1.23 -/
theorem Icc_bounded (a b:ℝ) : Bornology.IsBounded (Set.Icc a b) := by sorry

/-- Example 9.1.23 -/
theorem Ici_unbounded (a: ℝ) : ¬ Bornology.IsBounded (Set.Ici a) := by sorry

/-- Example 9.1.23 -/
theorem N_unbounded (a: ℝ) : ¬ Bornology.IsBounded ((fun n:ℕ ↦ (n:ℝ)) '' Set.univ) := by sorry

/-- Example 9.1.23 -/
theorem Z_unbounded (a: ℝ) : ¬ Bornology.IsBounded ((fun n:ℤ ↦ (n:ℝ)) '' Set.univ) := by sorry

/-- Example 9.1.23 -/
theorem Q_unbounded (a: ℝ) : ¬ Bornology.IsBounded ((fun n:ℚ ↦ (n:ℝ)) '' Set.univ) := by sorry

/-- Example 9.1.23 -/
theorem R_unbounded (a: ℝ) : ¬ Bornology.IsBounded (Set.univ: Set ℝ) := by sorry

/-- Theorem 9.1.24 / Exercise 9.1.13 (Heine-Borel theorem for the line)-/
theorem Heine_Borel (X: Set ℝ) :
  IsClosed X ∧ Bornology.IsBounded X ↔ ∀ a : ℕ → ℝ, (∀ n, a n ∈ X) →
  (∃ n : ℕ → ℕ, StrictMono n
    ∧ ∃ L ∈ X, Filter.Tendsto (fun j ↦ a (n j)) Filter.atTop (nhds L)) := by
  sorry

/-- Exercise 9.1.4 -/
example : ∃ (X Y:Set ℝ), closure (X ∩ Y) ≠ closure X ∩ closure Y := by
  sorry

/-- Exercise 9.1.6 -/
example (X:Set ℝ) : IsClosed (closure X) := by
  sorry

/-- Exercise 9.1.6 -/
example {X Y:Set ℝ} (hY: IsClosed Y) (hXY: X ⊆ Y) : closure X ⊆ Y := by
  sorry

/-- Exercise 9.1.7 -/
example {n:ℕ} (hn: n ≥ 1) (X: Fin n → Set ℝ) (hX: ∀ i, IsClosed (X i)) :
  IsClosed (⋃ i, X i) := by
  sorry

/-- Exercise 9.1.8 -/
example {I:Type} (X: I → Set ℝ) (hX: ∀ i, IsClosed (X i)) :
  IsClosed (⋂ i, X i) := by
  sorry

/-- Exercise 9.1.9 -/
example {X:Set ℝ} {x:ℝ} (hx: AdherentPt x X) : LimitPt x X ∨ IsolatedPt x X := by
  sorry

/-- Exercise 9.1.9 -/
example {X:Set ℝ} {x:ℝ} (hx: AdherentPt x X) : ¬ (LimitPt x X ∧ IsolatedPt x X) := by
  sorry

/-- Exercise 9.1.10 -/
example {X:Set ℝ} (hX: X ≠ ∅) : Bornology.IsBounded X ↔
  sSup ((fun x:ℝ ↦ (x:EReal)) '' X) < ⊤ ∧
  sInf ((fun x:ℝ ↦ (x:EReal)) '' X) > ⊥ := by
  sorry

/-- Exercise 9.1.11 -/
example {X:Set ℝ} (hX: Bornology.IsBounded X) : Bornology.IsBounded (closure X) := by
  sorry

/-- Exercise 9.1.12.  As a followup: prove or disprove this exercise with `[Fintype I]` removed. -/
example {I:Type} [Fintype I] (X: I → Set ℝ) (hX: ∀ i, Bornology.IsBounded (X i)) :
  Bornology.IsBounded (⋃ i, X i) := by
  sorry

/-- Exercise 9.1.14 -/
example (I: Finset ℝ) : IsClosed (I:Set ℝ) ∧ Bornology.IsBounded (I:Set ℝ) := by
  sorry

/-- Exercise 9.1.15 -/
example {E:Set ℝ} (hE: Bornology.IsBounded E) : AdherentPt (sSup E) E ∧ AdherentPt (sSup E) Eᶜ := by
  sorry





end Chapter9
