import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_10_3
import Analysis.Section_11_9


/-!
# Analysis I, Section 11.10: Consequences of the fundamental theorems

I have attempted to make the translation as faithful a paraphrasing as possible of the
original text. When there is a choice between a more idiomatic Lean solution and a
more faithful translation, I have generally chosen the latter. In particular, there will
be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I
have consciously avoided doing so.

Main constructions and results of this section:
- Integration by parts

-/

namespace Chapter11

open BoundedInterval Chapter9 Chapter10

/-- Proposition 11.10.1 (Integration by parts formula) / Exercise 11.10.1 -/
theorem integ_of_mul_deriv {a b:ℝ} (hab: a ≤ b) {F G: ℝ → ℝ}
  (hF: DifferentiableOn ℝ F (Icc a b)) (hG : DifferentiableOn ℝ G (Icc a b))
  (hF': IntegrableOn (derivWithin F (Icc a b)) (Icc a b))
  (hG': IntegrableOn (derivWithin G (Icc a b)) (Icc a b)) :
  integ (F * derivWithin G (Icc a b)) (Icc a b) = F b * G b - F a * G a -
    integ (G * derivWithin F (Icc a b)) (Icc a b) := by
    sorry

/-- Theorem 11.10.2.  Need to add continuity of α due to our conventions on α-length -/
theorem PiecewiseConstantOn.RS_integ_eq_integ_of_mul_deriv
  {a b:ℝ} {α f:ℝ → ℝ}
  (hα_diff: DifferentiableOn ℝ α (Icc a b)) (hαcont: Continuous α)
  (hα': IntegrableOn (derivWithin α (Icc a b)) (Icc a b))
  (hf: PiecewiseConstantOn f (Icc a b)) :
  IntegrableOn (f * derivWithin α (Icc a b)) (Icc a b) ∧
  Chapter11.integ (f * derivWithin α (Icc a b)) (Icc a b) = RS_integ f (Icc a b) α := by
  -- This proof is adapted from the structure of the original text.
  set α' := derivWithin α (Icc a b)
  have hf_integ: IntegrableOn f (Icc a b) :=
    (integ_of_piecewise_const hf).1
  have hfα'_integ: IntegrableOn (f * α') (Icc a b) :=
    integ_of_mul hf_integ hα'
  refine ⟨ hfα'_integ, ?_ ⟩
  obtain ⟨ P, hP ⟩ := hf
  rw [PiecewiseConstantOn.RS_integ_def hP α, integ_split hfα'_integ P]
  unfold PiecewiseConstantWith.RS_integ
  apply Finset.sum_congr rfl; intro J hJ
  calc
    _ = Chapter11.integ ((constant_value_on f (J:Set ℝ)) • α') J := by
      apply Chapter11.integ_congr
      intro x hx
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; congr
      apply ConstantOn.eq _ hx
      exact hP J hJ
    _ = constant_value_on f (J:Set ℝ) * Chapter11.integ α' J := by
      convert (integ_of_smul _ _).2
      apply integ_mono' (P.contains _ hJ) hα'
    _ = _ := by
      congr
      have hJsub (hJab : J.a ≤ J.b) : J ⊆ Ioo (J.a - 1) (J.b + 1) := by
        apply (subset_Icc J).trans
        simp [subset_iff, Set.Icc_subset_Ioo_iff hJab]
      rcases le_iff_eq_or_lt.mp (length_nonneg J) with hJab | hJab
      . rw [(integ_on_subsingleton hJab.symm).2]
        simp [le_iff_lt_or_eq] at hJab
        rcases hJab with hJab | hJab
        . rw [α_length_of_empty _ (empty_of_lt hJab)]
        rw [α_length_of_cts (show J.a-1 < J.a by linarith) (by linarith) (show J.b < J.b+1 by linarith) (hJsub (by linarith)) (Continuous.continuousOn hαcont) ]
        simp [show J.a = J.b by linarith]
      simp [length] at hJab
      rw [α_length_of_cts (show J.a-1 < J.a by linarith) (le_of_lt hJab) (show J.b < J.b+1 by linarith) (hJsub (le_of_lt hJab)) (Continuous.continuousOn hαcont) ]
      . have : Icc J.a J.b ⊆ Icc a b := by
          have := (Ioo_subset J).trans (P.contains _ hJ)
          simp [subset_iff] at this
          replace := closure_mono this
          simp [closure_Ioo (show J.a ≠ J.b by linarith)] at this
          simp [subset_iff, this]
        calc
          _ = Chapter11.integ α' (Icc J.a J.b) :=
            integ_eq (subset_Icc J) rfl rfl (integ_mono' this hα')
          _ = _ := by
            convert integ_eq_antideriv_sub (le_of_lt hJab) (integ_mono' this hα') _
            apply AntiderivOn.mono (I := Icc a b) ⟨ hα_diff, _ ⟩ this
            intros; solve_by_elim [DifferentiableWithinAt.hasDerivWithinAt]

/-- Corollary 11.10.3 -/
theorem RS_integ_eq_integ_of_mul_deriv
  {a b:ℝ} (hab: a < b) {α f:ℝ → ℝ} (hα: Monotone α)
  (hα_diff: DifferentiableOn ℝ α (Icc a b)) (hαcont: Continuous α)
  (hα': IntegrableOn (derivWithin α (Icc a b)) (Icc a b))
  (hf: RS_IntegrableOn f (Icc a b) α) :
  IntegrableOn (f * derivWithin α (Icc a b)) (Icc a b) ∧
  integ (f * derivWithin α (Icc a b)) (Icc a b) = RS_integ f (Icc a b) α := by
  -- This proof is adapted from the structure of the original text.
  set α' := derivWithin α (Icc a b)
  have hfα'_bound: BddOn (f * α') (Icc a b) := by
    obtain ⟨ M, hM ⟩ := hf.1
    obtain ⟨ N, hN ⟩ := hα'.1
    use M * N
    intro x hx; specialize hM x hx; specialize hN x hx
    simp [abs_mul]
    gcongr
    exact (abs_nonneg _).trans hM
  have hα'_nonneg : MajorizesOn α' 0 (Icc a b) := by
    intro x hx
    convert ge_iff_le.mp (derivative_of_monotone _ _ hα (hα_diff x hx))
    rw [←mem_closure_iff_clusterPt]
    simp at hx
    rcases le_iff_lt_or_eq.mp hx.1 with h | h
    . apply (closure_mono (s := Set.Ico a x)) _
      . simp [closure_Ico (show a ≠ x by linarith), hx.1]
      intro y hy; simp at hy ⊢
      simp [hy]; exact ⟨ by linarith, by linarith ⟩
    apply (closure_mono (s := Set.Ioc x b)) _
    . simp [closure_Ioc (show x ≠ b by linarith), hx.2]
    intro y hy; simp at hy ⊢
    simp [hy]; exact ⟨ by linarith, by linarith ⟩
  have h0 := hf.2
  have h1 : RS_integ f (Icc a b) α ≤ lower_integral (f * α') (Icc a b) := by
    apply le_of_forall_sub_le
    intro ε hε
    obtain ⟨ h, hhminor, hhconst, hh ⟩ := gt_of_lt_lower_RS_integral hf.1 hα (show RS_integ f (Icc a b) α - ε < lower_RS_integral f (Icc a b) α by linarith)
    have := PiecewiseConstantOn.RS_integ_eq_integ_of_mul_deriv hα_diff hαcont hα' hhconst
    rw [←this.2] at hh
    replace : lower_integral (h * α') (Icc a b) = integ (h * α') (Icc a b) := this.1.2
    have why : lower_integral (h * α') (Icc a b) ≤ lower_integral (f * α') (Icc a b) := by
      sorry
    linarith
  have h2 : upper_integral (f * α') (Icc a b) ≤ RS_integ f (Icc a b) α := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨ h, hhmajor, hhconst, hh ⟩ := lt_of_gt_upper_RS_integral hf.1 hα (show upper_RS_integral f (Icc a b) α + ε > RS_integ f (Icc a b) α by linarith)
    have := PiecewiseConstantOn.RS_integ_eq_integ_of_mul_deriv hα_diff hαcont hα' hhconst
    rw [←this.2] at hh
    have why : upper_integral (f * α') (Icc a b) ≤ upper_integral (h * α') (Icc a b) := by
      sorry
    linarith
  have h3 : lower_integral (f * α') (Icc a b) ≤
    upper_integral (f * α') (Icc a b) := lower_integral_le_upper hfα'_bound
  exact ⟨ ⟨ hfα'_bound, by linarith ⟩, by linarith ⟩

/-- Lemma 11.10.5 / Exercise 11.10.2-/
theorem PiecewiseConstantOn.RS_integ_of_comp {a b:ℝ} (hab: a < b) {φ f:ℝ → ℝ}
  (hφ_cont: Continuous φ) (hφ_mono: Monotone φ) (hf: PiecewiseConstantOn f (Icc (φ a) (φ b))) :
  PiecewiseConstantOn (f ∘ φ) (Icc a b) ∧ RS_integ (f ∘ φ) (Icc a b) φ =
    integ f (Icc (φ a) (φ b)) := by
  -- This proof is adapted from the structure of the original text.
  obtain ⟨ P', hf ⟩ := hf
  set P := P'.remove_empty
  replace hf : PiecewiseConstantWith f P := by
    intro J hJ
    simp [P, Partition.remove_empty, Partition.instMembership] at hJ
    exact hf J hJ.1
  rw [PiecewiseConstantOn.integ_def hf]
  unfold PiecewiseConstantWith.integ
  set φ_inv : P.intervals → Set ℝ := fun J ↦ { x:ℝ | x ∈ Set.Icc a b ∧ φ x ∈ (J:Set ℝ) }
  have hφ_inv_bounded (J: P.intervals) : Bornology.IsBounded (φ_inv J) := by
    apply Bornology.IsBounded.subset (Icc_bounded a b)
    intro x; aesop
  have hφ_inv_connected (J: P.intervals) : (φ_inv J).OrdConnected := by sorry
  set φ_inv' : P.intervals → BoundedInterval := fun J ↦ ((BoundedInterval.ordConnected_iff _).mp ⟨ hφ_inv_bounded J, hφ_inv_connected J ⟩).choose
  have hφ_inv' (J:P.intervals) : φ_inv J = φ_inv' J :=
    ((BoundedInterval.ordConnected_iff _).mp ⟨ hφ_inv_bounded J, hφ_inv_connected J ⟩).choose_spec
  have hφ_inv_nonempty (J:P.intervals) : (φ_inv J).Nonempty := by sorry
  have hφ_inv_const {J:P.intervals} : ConstantOn (f ∘ φ) (φ_inv' J) ∧ constant_value_on (f ∘ φ) (φ_inv' J) = constant_value_on f J := by
    sorry
  set Q : Partition (Icc a b) := {
    intervals := Finset.image φ_inv' Finset.univ
    exists_unique x := by sorry
    contains K hK := by sorry
  }
  have hfφ_piecewise : PiecewiseConstantWith (f ∘ φ) Q := by
    sorry
  have hfφ_piecewise' : PiecewiseConstantOn (f ∘ φ) (Icc a b) := ⟨ Q, hfφ_piecewise ⟩
  refine ⟨ hfφ_piecewise' , ?_ ⟩
  rw [PiecewiseConstantOn.RS_integ_def hfφ_piecewise _]
  unfold PiecewiseConstantWith.RS_integ
  rw [Finset.sum_image _, ←Finset.sum_coe_sort (s := P.intervals)]
  . apply Finset.sum_congr rfl
    intro J _
    congr 1
    . exact hφ_inv_const.2
    sorry
  intro J _ K _ hJK
  set x := (hφ_inv_nonempty J).some
  have h1 : x ∈ φ_inv J := (hφ_inv_nonempty J).some_mem
  have h2 : x ∈ φ_inv K := by rwa [hφ_inv' J, hJK, ←hφ_inv' K] at h1
  simp [φ_inv] at h1 h2
  have h3 : φ x ∈ Icc (φ a) (φ b) := by
    have := P.contains J.val J.property
    simp only [subset_iff, mem_iff] at this ⊢
    exact this h1.2
  ext
  apply (P.exists_unique _ h3).unique _ _ <;> simp [J.property, K.property, mem_iff, h1, h2]

/-- Proposition 11.10.6 (Change of variables formula II)-/
theorem RS_integ_of_comp {a b:ℝ} (hab: a < b) {φ f: ℝ → ℝ}
  (hφ_cont: Continuous φ) (hφ_mono: Monotone φ) (hf: IntegrableOn f (Icc (φ a) (φ b))) :
  RS_IntegrableOn (f ∘ φ) (Icc a b) φ ∧
  RS_integ (f ∘ φ) (Icc a b) φ = integ f (Icc (φ a) (φ b)) := by
  -- This proof is adapted from the structure of the original text.
  have hf_bdd := hf.1
  have hfφ_bdd : BddOn (f ∘ φ) (Icc a b) := by
    sorry
  have heq : lower_integral f (Icc (φ a) (φ b)) = upper_integral f (Icc (φ a) (φ b)) := hf.2
  have hupper : upper_RS_integral (f ∘ φ) (Icc a b) φ ≤ upper_integral f (Icc (φ a) (φ b)) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨ f_up, hf_upmajor, hf_upconst, hf_up ⟩ := lt_of_gt_upper_integral hf.1 (show upper_integral f (Icc (φ a) (φ b)) + ε > integ f (Icc (φ a) (φ b)) by linarith)
    have hpc := PiecewiseConstantOn.RS_integ_of_comp hab hφ_cont hφ_mono hf_upconst
    rw [←hpc.2] at hf_up
    have : MajorizesOn (f_up ∘ φ) (f ∘ φ) (Icc a b) := by
      intro x hx; simp at hx ⊢
      apply hf_upmajor; aesop
    replace := upper_RS_integral_le_integ hfφ_bdd this hpc.1 hφ_mono
    linarith
  have hlower : lower_integral f (Icc (φ a) (φ b)) ≤ lower_RS_integral (f ∘ φ) (Icc a b) φ := by
    apply le_of_forall_sub_le
    intro ε hε
    obtain ⟨ f_low, hf_lowminor, hf_lowconst, hf_low ⟩ := gt_of_lt_lower_integral hf.1 (show lower_integral f (Icc (φ a) (φ b)) - ε < lower_integral f (Icc (φ a) (φ b)) by linarith)
    have hpc := PiecewiseConstantOn.RS_integ_of_comp hab hφ_cont hφ_mono hf_lowconst
    rw [←hpc.2] at hf_low
    have : MinorizesOn (f_low ∘ φ) (f ∘ φ) (Icc a b) := by
      intro x hx; simp at hx ⊢
      apply hf_lowminor; aesop
    replace := integ_le_lower_RS_integral hfφ_bdd this hpc.1 hφ_mono
    linarith
  have hle : lower_RS_integral (f ∘ φ) (Icc a b) φ ≤ upper_RS_integral (f ∘ φ) (Icc a b) φ :=
    lower_RS_integral_le_upper hfφ_bdd hφ_mono
  refine ⟨ ⟨ hfφ_bdd, by linarith ⟩, by linarith ⟩

/-- Proposition 11.10.7 (Change of variables formula III)-/
theorem integ_of_comp {a b:ℝ} (hab: a < b) {φ f: ℝ → ℝ}
  (hφ_diff: DifferentiableOn ℝ φ (Icc a b))
  (hφ_cont: Continuous φ) (hφ_mono: Monotone φ)
  (hφ': IntegrableOn (derivWithin φ (Icc a b)) (Icc a b))
  (hf: IntegrableOn f (Icc (φ a) (φ b))) :
  IntegrableOn (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) ∧
  integ (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) =
    integ f (Icc (φ a) (φ b)) := by
 have h1 := RS_integ_of_comp hab hφ_cont hφ_mono hf
 have h2 := RS_integ_eq_integ_of_mul_deriv hab hφ_mono hφ_diff hφ_cont hφ' h1.1
 refine ⟨ h2.1, by aesop ⟩

/-- Exercise 11.10.3-/
example {a b:ℝ} (hab: a < b) {f: ℝ → ℝ} (hf: IntegrableOn f (Icc a b)) :
  IntegrableOn (fun x ↦ f (-x)) (Icc (-b) (-a)) ∧
  integ (fun x ↦ f (-x)) (Icc (-b) (-a)) = -integ f (Icc a b) := by
  sorry

/- Exercise 11.10.4: state and prove a version of `integ_of_comp` in which `φ` is `Antitone` rather than `Monotone`. -/

end Chapter11
