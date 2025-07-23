import Mathlib.Tactic
import Mathlib.Topology.Instances.Irrational
import Analysis.Section_11_6

/-!
# Analysis I, Section 11.8: The Riemann-Stieltjes integral

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Definition of α-length.
- The piecewise constant Riemann-Stieltjes integral.
- The full Riemann-Stieltjes integral.

Technical notes:
- In Lean it is more convenient to make definitions such as α-length and the Riemann-Stieltjes
  integral totally defined, thus assigning "junk" values to the cases where the definition is
  not intended to be applied. For the definition of α-length, the definition is intended to be
  applied in contexts where left and right limits exist, and the function is extended by
  constants to the left and right of its intended domain of definition; for instance, if a
  function `f` is defined on `Icc 0 1`, then it is intended that `f x = f 1` for all `x ≥ 1`
  and `f x = f 0` for all `x ≤ 0`; in particular, at a right endpoint, the value of a function
  is intended to agree with its right limit, and similarly for the left endpoint, although we
  do not enforce this in our definition of α-length. (For functions defined on open intervals,
  the extension is immaterial.)
- The notion of α-length and piecewise constant Riemann-Stieltjes integral is intended for
  situations where left and right limits exist, such as for monotone functions or continuous
  functions, though technically they make sense without these hypotheses. The full Riemann-Stieltjes
  integral is intended for functions that are of bounded variation, though we shall restrict
  attention to the special case of monotone increasing functions for the most part.
-/

namespace Chapter11

open BoundedInterval Chapter9

/-- Left and right limits. A junk value is assigned if the limit does not exist. -/
noncomputable abbrev right_lim (f: ℝ → ℝ) (x₀:ℝ) : ℝ :=
  lim (Filter.map f (nhdsWithin x₀ (Set.Ioi x₀)))

noncomputable abbrev left_lim (f: ℝ → ℝ) (x₀:ℝ) : ℝ :=
  lim (Filter.map f (nhdsWithin x₀ (Set.Iio x₀)))

theorem right_lim_def {f: ℝ → ℝ} {x₀ L:ℝ} (h: Convergesto (Set.Ioi x₀) f L x₀) :
  right_lim f x₀ = L := by
  apply lim_eq
  rwa [Convergesto.iff, ←nhdsWithin.eq_1, Filter.Tendsto.eq_1] at h

theorem left_lim_def {f: ℝ → ℝ} {x₀ L:ℝ} (h: Convergesto (Set.Iio x₀) f L x₀) :
  left_lim f x₀ = L := by
  apply lim_eq
  rwa [Convergesto.iff, ←nhdsWithin.eq_1, Filter.Tendsto.eq_1] at h

noncomputable abbrev jump (f: ℝ → ℝ) (x₀:ℝ) : ℝ :=
  right_lim f x₀ - left_lim f x₀

/-- Right limits exist for continuous functions -/
theorem right_lim_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : ∃ ε>0, Set.Ico x₀ (x₀+ε) ⊆ X) (hf: ContinuousWithinAt f X x₀) :
  right_lim f x₀ = f x₀ := by
  obtain ⟨ ε, hε, hX ⟩ := h
  apply right_lim_def
  rw [ContinuousWithinAt.eq_1] at hf
  replace hf : Filter.Tendsto f (nhdsWithin x₀ (Set.Ioo x₀ (x₀ + ε))) (nhds (f x₀)) := by
    apply tendsto_nhdsWithin_mono_left _ hf
    exact Set.Ioo_subset_Ico_self.trans hX
  rw [Convergesto.iff, ←nhdsWithin.eq_1]
  convert hf using 1
  have h1 : Set.Ioo x₀ (x₀ + ε) ∈ nhdsWithin x₀ (Set.Ioi x₀) := by
    convert inter_mem_nhdsWithin (t := Set.Ioo (x₀-ε) (x₀+ε)) _ _
    . ext; simp; intros; linarith
    exact Ioo_mem_nhds (by linarith) (by linarith)
  rw [←nhdsWithin_inter_of_mem h1]
  congr 1
  simp [Set.Ioo_subset_Ioi_self]

/-- Left limits exist for continuous functions -/
theorem left_lim_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : ∃ ε>0, Set.Ioc (x₀-ε) x₀ ⊆ X) (hf: ContinuousWithinAt f X x₀) :
  left_lim f x₀ = f x₀ := by
  obtain ⟨ ε, hε, hX ⟩ := h
  apply left_lim_def
  rw [ContinuousWithinAt.eq_1] at hf
  replace hf : Filter.Tendsto f (nhdsWithin x₀ (Set.Ioo (x₀ - ε) x₀)) (nhds (f x₀)) := by
    apply tendsto_nhdsWithin_mono_left _ hf
    exact Set.Ioo_subset_Ioc_self.trans hX
  rw [Convergesto.iff, ←nhdsWithin.eq_1]
  convert hf using 1
  have h1 : Set.Ioo (x₀-ε) x₀ ∈ nhdsWithin x₀ (Set.Iio x₀) := by
    convert inter_mem_nhdsWithin (t := Set.Ioo (x₀-ε) (x₀+ε)) _ _
    . ext; simp; constructor
      . intro ⟨ h1, h2 ⟩; simp [h1, h2]; linarith
      aesop
    exact Ioo_mem_nhds (by linarith) (by linarith)
  rw [←nhdsWithin_inter_of_mem h1]
  congr 1; simp [Set.Ioo_subset_Iio_self]

/-- No jump for continuous functions -/
theorem jump_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : X ∈ nhds x₀) (hf: ContinuousWithinAt f X x₀) :
  jump f x₀ = 0 := by
  rw [mem_nhds_iff_exists_Ioo_subset] at h
  obtain ⟨ l, u, hx₀, hX ⟩ := h
  simp at hx₀
  have hl : ∃ ε>0, Set.Ioc (x₀-ε) x₀ ⊆ X := by
    refine ⟨ x₀-l, by linarith, ?_ ⟩
    apply Set.Subset.trans _ hX
    intro x hx; simp at hx ⊢; exact ⟨ hx.1, by linarith ⟩
  have hu : ∃ ε>0, Set.Ico x₀ (x₀+ε) ⊆ X := by
    refine ⟨ u-x₀, by linarith, ?_ ⟩
    apply Set.Subset.trans _ hX
    intro x hx; simp at hx ⊢; exact ⟨ by linarith, hx.2 ⟩
  simp [jump, left_lim_of_continuous hl hf, right_lim_of_continuous hu hf]

/-- Right limits exist for monotone functions -/
theorem right_lim_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  Convergesto (Set.Ioi x₀) f (sInf (f '' Set.Ioi x₀)) x₀ := by
  rw [Convergesto.iff, ←nhdsWithin.eq_1]
  apply MonotoneOn.tendsto_nhdsGT
  . exact Monotone.monotoneOn hf _
  rw [bddBelow_def]
  use f x₀
  intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy
  apply hf; linarith

theorem right_lim_of_monotone' {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  right_lim f x₀ = sInf (f '' Set.Ioi x₀) := by
  apply right_lim_def
  apply right_lim_of_monotone x₀ hf

/-- Left limits exist for monotone functions -/
theorem left_lim_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  Convergesto (Set.Iio x₀) f (sSup (f '' Set.Iio x₀)) x₀ := by
  rw [Convergesto.iff, ←nhdsWithin.eq_1]
  apply MonotoneOn.tendsto_nhdsLT
  . exact Monotone.monotoneOn hf _
  rw [bddAbove_def]
  use f x₀
  intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy
  apply hf; linarith

theorem left_lim_of_monotone' {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  left_lim f x₀ = sSup (f '' Set.Iio x₀) := by
  apply left_lim_def
  apply left_lim_of_monotone x₀ hf

theorem jump_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  0 ≤ jump f x₀  := by
  simp [jump, left_lim_of_monotone' x₀ hf, right_lim_of_monotone' x₀ hf]
  apply csSup_le
  . simp
  intro a ha
  apply le_csInf
  . simp
  intro b hb; simp at ha hb
  obtain ⟨ x, hx, rfl ⟩ := ha
  obtain ⟨ y, hy, rfl ⟩ := hb
  apply hf; linarith

theorem right_lim_le_left_lim_of_monotone {f:ℝ → ℝ} {a b:ℝ} (hab: a < b)
  (hf: Monotone f) :
  right_lim f a ≤ left_lim f b := by
  rw [left_lim_of_monotone' b hf, right_lim_of_monotone' a hf]
  calc
    _ ≤ f ((a+b)/2) := by
      apply ConditionallyCompleteLattice.csInf_le _ _ _ _
      . rw [bddBelow_def]
        use f a
        intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy
        apply hf; linarith
      simp; use (a+b)/2; simp; linarith
    _ ≤ _ := by
      apply ConditionallyCompleteLattice.le_csSup _ _ _ _
      . rw [bddAbove_def]
        use f b
        intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy
        apply hf; linarith
      simp; use (a+b)/2; simp; linarith

/-- Definition 11.8.1 -/
noncomputable abbrev α_length (α: ℝ → ℝ) (I: BoundedInterval) : ℝ := match I with
| Icc a b => if a ≤ b then (right_lim α b) - (left_lim α a) else 0
| Ico a b => if a ≤ b then (left_lim α b) - (left_lim α a) else 0
| Ioc a b => if a ≤ b then (right_lim α b) - (right_lim α a) else 0
| Ioo a b => if a < b then (left_lim α b) - (right_lim α a) else 0

notation3:max α"["I"]ₗ" => α_length α I

theorem α_length_of_empty (α: ℝ → ℝ) {I: BoundedInterval} (hI: (I:Set ℝ) = ∅) : α[I]ₗ = 0 :=
  match I with
  | Icc a b => by
      simp [Set.Icc_eq_empty_iff] at hI ⊢
      intros; linarith
  | Ico a b => by
      simp [Set.Ico_eq_empty_iff] at hI ⊢
      intros; have : a = b := by linarith
      simp [this]
  | Ioc a b => by
      simp [Set.Ioc_eq_empty_iff] at hI ⊢
      intros; have : a = b := by linarith
      simp [this]
  | Ioo a b => by
      simp [Set.Ioo_eq_empty_iff] at hI ⊢
      intros; linarith

@[simp]
theorem α_length_of_pt {α: ℝ → ℝ} (a:ℝ) : α[Icc a a]ₗ = jump α a := by
  simp [α_length, jump]

theorem α_length_of_cts {α:ℝ → ℝ} {I: BoundedInterval} {a b: ℝ}
  (haa: a < I.a) (hab: I.a ≤ I.b) (hbb: I.b < b)
  (hI : I ⊆ Ioo a b) (hα: ContinuousOn α (Ioo a b)) :
  α[I]ₗ = α I.b - α I.a := by
  have ha_left : left_lim α I.a = α I.a := by
    apply left_lim_of_continuous _ (ContinuousOn.continuousWithinAt hα _)
    . refine ⟨ I.a - a, by linarith, ?_ ⟩
      intro x; simp; intro h1 h2
      exact ⟨ h1, by linarith ⟩
    simp [haa]; linarith
  have ha_right : right_lim α I.a = α I.a := by
    apply right_lim_of_continuous _ (ContinuousOn.continuousWithinAt hα _)
    . refine ⟨ b - I.a, by linarith, ?_ ⟩
      intro x; simp; intro h1 h2
      exact ⟨ by linarith, h2 ⟩
    simp [haa]; linarith
  have hb_left : left_lim α I.b = α I.b := by
    apply left_lim_of_continuous _ (ContinuousOn.continuousWithinAt hα _)
    . refine ⟨ I.b - a, by linarith, ?_ ⟩
      intro x; simp; intro h1 h2
      exact ⟨ h1, by linarith ⟩
    simp [hbb]; linarith
  have hb_right : right_lim α I.b = α I.b := by
    apply right_lim_of_continuous _ (ContinuousOn.continuousWithinAt hα _)
    . refine ⟨ b - I.b, by linarith, ?_ ⟩
      intro x; simp; intro h1 h2
      exact ⟨ by linarith, h2 ⟩
    simp [hbb]; linarith
  cases I with
  | Icc a' b' =>
    simp [α_length, hb_right, ha_left, hab]
  | Ico a' b' =>
    simp [α_length, hb_left, ha_left, hab]
  | Ioc a' b' =>
    simp [α_length, hb_right, ha_right, hab]
  | Ioo a' b' =>
    simp [α_length, hb_left, ha_right]
    intro h; replace h : a' = b' := by linarith
    simp [h]

/-- Example 11.8.2-/
example : (fun x ↦ x^2)[Icc 2 3]ₗ = 5 := by
  sorry

example : (fun x ↦ x^2)[Icc 2 2]ₗ = 0 := by
  sorry

example : (fun x ↦ x^2)[Ioo 2 2]ₗ = 0 := by
  sorry

/-- Example 11.8.3-/
@[simp]
theorem α_len_of_id (I: BoundedInterval) : (fun x ↦ x)[I]ₗ = |I|ₗ := by
  sorry

/-- An improved version of BoundedInterval.joins that also controls α-length. -/
abbrev BoundedInterval.joins' (K I J: BoundedInterval) : Prop :=
  K.joins I J ∧ ∀ α:ℝ → ℝ, α[K]ₗ = α[I]ₗ + α[J]ₗ

theorem BoundedInterval.join_Icc_Ioc' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins' (Icc a b) (Ioc b c) := by
  refine ⟨ join_Icc_Ioc hab hbc, ?_ ⟩
  simp [α_length, BoundedInterval.a, BoundedInterval.b,
        show a ≤ b by linarith, show b ≤ c by linarith, show a ≤ c by linarith]

theorem BoundedInterval.join_Icc_Ioo' {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ico a c).joins' (Icc a b) (Ioo b c) := by
  refine ⟨ join_Icc_Ioo hab hbc, ?_ ⟩
  simp [α_length, BoundedInterval.a, BoundedInterval.b,
        show a ≤ b by linarith, show b < c by linarith, show a ≤ c by linarith]

theorem BoundedInterval.join_Ioc_Ioc' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ioc a c).joins' (Ioc a b) (Ioc b c) := by
  refine ⟨ join_Ioc_Ioc hab hbc, ?_ ⟩
  simp [α_length, BoundedInterval.a, BoundedInterval.b,
        show a ≤ b by linarith, show b ≤ c by linarith, show a ≤ c by linarith]

theorem BoundedInterval.join_Ioc_Ioo' {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ioo a c).joins' (Ioc a b) (Ioo b c) := by
  refine ⟨ join_Ioc_Ioo hab hbc, ?_ ⟩
  simp [α_length, BoundedInterval.a, BoundedInterval.b,
        show a ≤ b by linarith, show b < c by linarith, show a < c by linarith]

theorem BoundedInterval.join_Ico_Icc' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins' (Ico a b) (Icc b c) := by
  refine ⟨ join_Ico_Icc hab hbc, ?_ ⟩
  simp [α_length, BoundedInterval.a, BoundedInterval.b,
        show a ≤ b by linarith, show b ≤ c by linarith, show a ≤ c by linarith]

theorem BoundedInterval.join_Ico_Ico' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ico a c).joins' (Ico a b) (Ico b c) := by
  refine ⟨ join_Ico_Ico hab hbc, ?_ ⟩
  simp [α_length, BoundedInterval.a, BoundedInterval.b,
        show a ≤ b by linarith, show b ≤ c by linarith, show a ≤ c by linarith]

theorem BoundedInterval.join_Ioo_Icc' {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioc a c).joins' (Ioo a b) (Icc b c) := by
  refine ⟨ join_Ioo_Icc hab hbc, ?_ ⟩
  simp [α_length, BoundedInterval.a, BoundedInterval.b,
        show a < b by linarith, show b ≤ c by linarith, show a ≤ c by linarith]

theorem BoundedInterval.join_Ioo_Ico' {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioo a c).joins' (Ioo a b) (Ico b c) := by
  refine ⟨ join_Ioo_Ico hab hbc, ?_ ⟩
  simp [α_length, BoundedInterval.a, BoundedInterval.b,
        show a < b by linarith, show b ≤ c by linarith, show a < c by linarith]

/-- Theorem 11.8.4 / Exercise 11.8.1 -/
theorem Partition.sum_of_α_length  {I: BoundedInterval} (P: Partition I) (α: ℝ → ℝ) :
  ∑ J ∈ P.intervals, α[J]ₗ = α[I]ₗ := by
  sorry

/-- Definition 11.8.5 (Piecewise constant RS integral)-/
noncomputable abbrev PiecewiseConstantWith.RS_integ (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) (α: ℝ → ℝ)   :
  ℝ := ∑ J ∈ P.intervals, constant_value_on f (J:Set ℝ) * α[J]ₗ

/-- Example 11.8.6 -/
noncomputable abbrev f_11_8_6 (x:ℝ) : ℝ := if x < 2 then 4 else 2

noncomputable abbrev P_11_8_6 : Partition (Icc 1 3) :=
  (⊥: Partition (Ico 1 2)).join (⊥ : Partition (Icc 2 3))
  (join_Ico_Icc (by norm_num) (by norm_num) )

theorem f_11_8_6_RS_integ : PiecewiseConstantWith.RS_integ f_11_8_6 P_11_8_6 (fun x ↦ x) = 22 := by
  sorry

/-- Example 11.8.7 -/
theorem PiecewiseConstantWith.RS_integ_eq_integ {f:ℝ → ℝ} {I: BoundedInterval} (P: Partition I) :RS_integ f P (fun x ↦ x) = integ f P := by
  sorry

/-- Analogue of Proposition 11.2.13 -/
theorem PiecewiseConstantWith.RS_integ_eq {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I}
  (hP: PiecewiseConstantWith f P) (hP': PiecewiseConstantWith f P') (α:ℝ → ℝ): RS_integ f P α = RS_integ f P' α := by
  sorry

open Classical in
noncomputable abbrev PiecewiseConstantOn.RS_integ (f:ℝ → ℝ) (I: BoundedInterval) (α:ℝ → ℝ):
  ℝ := if h: PiecewiseConstantOn f I then PiecewiseConstantWith.RS_integ f h.choose α else 0

theorem PiecewiseConstantOn.RS_integ_def {f:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: PiecewiseConstantWith f P) (α:ℝ → ℝ) : PiecewiseConstantOn.RS_integ f I α = PiecewiseConstantWith.RS_integ f P α := by
  have h' : PiecewiseConstantOn f I := by use P
  simp [PiecewiseConstantOn.RS_integ, h']
  exact PiecewiseConstantWith.RS_integ_eq h'.choose_spec h α

/-- α-length non-negative when α monotone -/
theorem α_length_nonneg_of_monotone {α:ℝ → ℝ}  (hα: Monotone α) (I: BoundedInterval):
  0 ≤ α[I]ₗ := by
  sorry

/-- Analogue of Theorem 11.2.16 (a) (Laws of integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) {α:ℝ → ℝ} (hα: Monotone α):
  PiecewiseConstantOn.RS_integ (f + g) I α = PiecewiseConstantOn.RS_integ f I α + PiecewiseConstantOn.RS_integ g I α := by
  sorry

/-- Analogue of Theorem 11.2.16 (b) (Laws of integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_smul {f: ℝ → ℝ} {I: BoundedInterval} (c:ℝ)
  (hf: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α) :
  PiecewiseConstantOn.RS_integ (c • f) I α = c * PiecewiseConstantOn.RS_integ f I α
   := by
  sorry

/-- Theorem 11.8.8 (c) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_sub {f g: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  PiecewiseConstantOn.RS_integ (f - g) I α = PiecewiseConstantOn.RS_integ f I α - PiecewiseConstantOn.RS_integ g I α := by
  sorry

/-- Theorem 11.8.8 (d) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_of_nonneg {f: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (h: ∀ x ∈ I, 0 ≤ f x) (hf: PiecewiseConstantOn f I) :
  0 ≤ PiecewiseConstantOn.RS_integ f I α := by
  sorry

/-- Theorem 11.8.8 (e) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_mono {f g: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (h: ∀ x ∈ I, f x ≤ g x) (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  PiecewiseConstantOn.RS_integ f I α ≤ PiecewiseConstantOn.RS_integ g I α := by
  sorry

/-- Theorem 11.8.8 (f) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_const (c: ℝ) (I: BoundedInterval) {α:ℝ → ℝ} (hα: Monotone α) :
  PiecewiseConstantOn.RS_integ (fun _ ↦ c) I α = c * α[I]ₗ := by
  sorry

/-- Theorem 11.8.8 (f) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_const' {f:ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α) (h: ConstantOn f I) :
  PiecewiseConstantOn.RS_integ f I α = (constant_value_on f I) * α[I]ₗ := by
  sorry

open Classical in
/-- Theorem 11.8.8 (g) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α):
  PiecewiseConstantOn (fun x ↦ if x ∈ I then f x else 0) J := by
  sorry

open Classical in
/-- Theorem 11.8.8 (g) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α):
  PiecewiseConstantOn.RS_integ (fun x ↦ if x ∈ I then f x else 0) J α = PiecewiseConstantOn.RS_integ f I α := by
  sorry

/-- Theorem 11.8.8 (h) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_of_join {I J K: BoundedInterval} (hIJK: K.joins' I J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f K) {α:ℝ → ℝ} (hα: Monotone α):
  PiecewiseConstantOn.RS_integ f K α = PiecewiseConstantOn.RS_integ f I α + PiecewiseConstantOn.RS_integ f J α := by
  sorry

/-- Analogue of Definition 11.3.2 (Uppper and lower Riemann integrals )-/
noncomputable abbrev upper_RS_integral (f:ℝ → ℝ) (I: BoundedInterval) (α: ℝ → ℝ): ℝ :=
  sInf ((fun g ↦ PiecewiseConstantOn.RS_integ g I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})

noncomputable abbrev lower_RS_integral (f:ℝ → ℝ) (I: BoundedInterval) (α: ℝ → ℝ): ℝ :=
  sSup ((fun g ↦ PiecewiseConstantOn.RS_integ g I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})

lemma RS_integral_bound_upper_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval}
  (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) {α:ℝ → ℝ} (hα:Monotone α)
  : M * α[I]ₗ ∈ (fun g ↦ PiecewiseConstantOn.RS_integ g I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp
  refine ⟨ fun _ ↦ M, ⟨ ⟨ ?_, ?_, ⟩, PiecewiseConstantOn.RS_integ_const M I hα ⟩ ⟩
  . intro x hx; specialize h x hx
    simp [abs_le'] at h
    simp [h.1]
  apply PiecewiseConstantOn.of_const (ConstantOn.of_const (c := M) _)
  simp


lemma RS_integral_bound_lower_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) {α:ℝ → ℝ} (hα:Monotone α)
  : -M * α[I]ₗ ∈ (fun g ↦ PiecewiseConstantOn.RS_integ g I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp
  refine ⟨ fun _ ↦ -M, ⟨ ⟨ ?_, ?_, ⟩, ?_ ⟩ ⟩
  . intro x hx; specialize h x hx
    simp [abs_le'] at h
    simp; linarith
  . apply PiecewiseConstantOn.of_const (ConstantOn.of_const (c := -M) _)
    simp
  convert PiecewiseConstantOn.RS_integ_const (-M) I hα using 1
  simp

lemma RS_integral_bound_upper_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  ((fun g ↦ PiecewiseConstantOn.RS_integ g I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty := by
  obtain ⟨ M, h ⟩ := h
  exact Set.nonempty_of_mem (RS_integral_bound_upper_of_bounded h hα)

lemma RS_integral_bound_lower_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  ((fun g ↦ PiecewiseConstantOn.RS_integ g I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty := by
  obtain ⟨ M, h ⟩ := h
  exact Set.nonempty_of_mem (RS_integral_bound_lower_of_bounded h hα)

lemma RS_integral_bound_lower_le_upper {f:ℝ → ℝ} {I: BoundedInterval} {a b:ℝ}
  {α:ℝ → ℝ} (hα: Monotone α)
  (ha: a ∈ (fun g ↦ PiecewiseConstantOn.RS_integ g I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})
  (hb: b ∈ (fun g ↦ PiecewiseConstantOn.RS_integ g I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})
  : b ≤ a:= by
    obtain ⟨ g, ⟨ ⟨ hmaj, hgp⟩, hgi ⟩ ⟩ := ha
    obtain ⟨ h, ⟨ ⟨ hmin, hhp⟩, hhi ⟩ ⟩ := hb
    rw [←hgi, ←hhi]
    apply PiecewiseConstantOn.RS_integ_mono hα _ hhp hgp
    intro x hx
    exact (ge_iff_le.mp (hmin x hx)).trans (hmaj x hx)

lemma RS_integral_bound_below {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  BddBelow ((fun g ↦ PiecewiseConstantOn.RS_integ g I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddBelow_def]
    use (RS_integral_bound_lower_nonempty h hα).some
    intro a ha; exact RS_integral_bound_lower_le_upper hα ha (RS_integral_bound_lower_nonempty h hα).some_mem

lemma RS_integral_bound_above {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α):
  BddAbove ((fun g ↦ PiecewiseConstantOn.RS_integ g I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddAbove_def]
    use (RS_integral_bound_upper_nonempty h hα).some
    intro b hb; exact RS_integral_bound_lower_le_upper hα (RS_integral_bound_upper_nonempty h hα).some_mem hb

lemma le_lower_RS_integral {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M)
  {α:ℝ → ℝ} (hα: Monotone α) :
  -M * α[I]ₗ ≤ lower_RS_integral f I α := by
  exact ConditionallyCompleteLattice.le_csSup _ _
    (RS_integral_bound_above (BddOn.of_bounded h) hα) (RS_integral_bound_lower_of_bounded h hα)

lemma lower_RS_integral_le_upper {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  lower_RS_integral f I α ≤ upper_RS_integral f I α := by
  apply ConditionallyCompleteLattice.csSup_le _ _ (RS_integral_bound_lower_nonempty h hα) _
  rw [mem_upperBounds]
  intro b hb
  apply ConditionallyCompleteLattice.le_csInf _ _ (RS_integral_bound_upper_nonempty h hα) _
  rw [mem_lowerBounds]
  intro a ha
  exact RS_integral_bound_lower_le_upper hα ha hb

lemma RS_upper_integral_le {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M)
  {α:ℝ → ℝ} (hα: Monotone α) :
  upper_RS_integral f I α ≤ M * α[I]ₗ := by
  exact ConditionallyCompleteLattice.csInf_le _ _
    (RS_integral_bound_below (BddOn.of_bounded h) hα) (RS_integral_bound_upper_of_bounded h hα)

lemma upper_RS_integral_le_integ {f g:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfg: MajorizesOn g f I) (hg: PiecewiseConstantOn g I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  upper_RS_integral f I α ≤ PiecewiseConstantOn.RS_integ g I α := by
  apply ConditionallyCompleteLattice.csInf_le _ _ (RS_integral_bound_below hf hα) _
  use g; simpa [hg]

lemma integ_le_lower_RS_integral {f h:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfh: MinorizesOn h f I) (hg: PiecewiseConstantOn h I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  PiecewiseConstantOn.RS_integ h I α ≤ lower_RS_integral f I α := by
  apply ConditionallyCompleteLattice.le_csSup _ _ (RS_integral_bound_above hf hα) _
  use h; simpa [hg]

lemma lt_of_gt_upper_RS_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {α: ℝ → ℝ} (hα: Monotone α) {X:ℝ} (hX: upper_RS_integral f I α < X ) :
  ∃ g, MajorizesOn g f I ∧ PiecewiseConstantOn g I ∧ PiecewiseConstantOn.RS_integ g I α < X := by
  obtain ⟨ Y, hY, hYX ⟩ := exists_lt_of_csInf_lt (RS_integral_bound_upper_nonempty hf hα) hX
  simp at hY
  obtain ⟨ g, ⟨ hmaj, hgp ⟩, hgi ⟩ := hY
  refine ⟨ g, hmaj, hgp, ?_ ⟩
  rwa [hgi]

lemma gt_of_lt_lower_RS_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) {X:ℝ} (hX: X < lower_RS_integral f I α) :
  ∃ h, MinorizesOn h f I ∧ PiecewiseConstantOn h I ∧ X < PiecewiseConstantOn.RS_integ h I α := by
  obtain ⟨ Y, hY, hYX ⟩ := exists_lt_of_lt_csSup (RS_integral_bound_lower_nonempty hf hα) hX
  simp at hY
  obtain ⟨ h, ⟨ hmin, hhp ⟩, hhi ⟩ := hY
  refine ⟨ h, hmin, hhp, ?_ ⟩
  rwa [hhi]

/-- Analogue of Definition 11.3.4 -/
noncomputable abbrev RS_integ (f:ℝ → ℝ) (I: BoundedInterval) (α:ℝ → ℝ) : ℝ :=
upper_RS_integral f I α

noncomputable abbrev RS_IntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) (α: ℝ → ℝ) : Prop :=
  BddOn f I ∧ lower_RS_integral f I α = upper_RS_integral f I α

/-- Analogue of various components of Lemma 11.3.3 -/
theorem upper_RS_integral_eq_upper_integral (f:ℝ → ℝ) (I: BoundedInterval) :
  upper_RS_integral f I (fun x ↦ x) = upper_integral f I := by
  sorry

theorem lower_RS_integral_eq_lower_integral (f:ℝ → ℝ) (I: BoundedInterval) :
  lower_RS_integral f I (fun x ↦ x) = lower_integral f I := by
  sorry

theorem RS_integ_eq_integ (f:ℝ → ℝ) (I: BoundedInterval) :
  RS_integ f I (fun x ↦ x) = integ f I := by
  sorry

theorem RS_IntegrableOn_iff_IntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) :
  RS_IntegrableOn f I (fun x ↦ x) ↔ IntegrableOn f I := by
  sorry

/-- Exercise 11.8.4 -/
theorem RS_integ_of_uniform_cts {I: BoundedInterval} {f:ℝ → ℝ} (hf: UniformContinuousOn f I)
 {α:ℝ → ℝ} (hα: Monotone α):
  RS_IntegrableOn f I α := by
  sorry

/-- Exercise 11.8.5 -/
theorem RS_integ_with_sign (f:ℝ → ℝ) (hf: ContinuousOn f (Set.Icc (-1) 1)) : RS_IntegrableOn f (Icc (-1) 1) Real.sign ∧ RS_integ f (Icc (-1) 1) (fun x ↦ -Real.sign x) = 2 * f 0 := by
  sorry

/-- Analogue of Lemma 11.3.7 -/
theorem RS_integ_of_piecewise_const {f:ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I)
  {α: ℝ → ℝ} (hα: Monotone α):
  RS_IntegrableOn f I α ∧ RS_integ f I α = PiecewiseConstantOn.RS_integ f I α := by
  sorry

end Chapter11
