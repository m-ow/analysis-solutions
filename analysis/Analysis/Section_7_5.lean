import Mathlib.Tactic
import Analysis.Section_6_4
import Analysis.Section_7_4
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Analysis I, Section 7.5: The root and ratio tests

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- The root and ratio tests/

A point that is only implicitly stated in the text is that for the root and ratio tests, the lim inf and lim sup should be interpreted within the extended reals.  The Lean formalizations below make this point more explicit.

-/

namespace Chapter7

/-- Theorem 7.5.1(a) (Root test).  A technical condition is needed to ensure the limsup is finite. -/
theorem Series.root_test_pos {s : Series}
  (h : Filter.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) Filter.atTop < 1) : s.absConverges := by
    -- This proof is written to follow the structure of the original text.
    set α':EReal := Filter.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) Filter.atTop
    have hpos : 0 ≤ α' := by
      apply Filter.le_limsup_of_frequently_le _ (by isBoundedDefault)
      apply Filter.Frequently.of_forall
      intros; positivity
    set α := α'.toReal
    have hαα' : α' = α := by
      apply (EReal.coe_toReal _ _).symm
      . contrapose! h; simp [h]
      contrapose! hpos; simp [hpos]
    rw [hαα'] at h hpos; norm_cast at h hpos
    set ε := (1-α)/2
    have hε : 0 < ε := by simp [ε]; linarith
    have hε' : α' < (α+ε:ℝ) := by rw [hαα', EReal.coe_lt_coe_iff]; linarith
    have hα : α + ε < 1 := by simp [ε]; linarith
    have hα' : 0 < α + ε := by linarith
    have := Filter.eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
    rw [Filter.eventually_atTop] at this
    obtain ⟨ N', hN ⟩ := this; set N := max N' (max s.m 1)
    have (n:ℤ) (hn: n ≥ N) : |s.seq n| ≤ (α + ε)^n := by
      have : n ≥ N' := by omega
      have npos : 0 < n := by omega
      specialize hN n this
      rw [EReal.coe_lt_coe_iff] at hN
      replace hN := le_of_lt hN
      calc
        _ = (|s.seq n|^(1/(n:ℝ)))^n := by
          rw [←Real.rpow_intCast, ←Real.rpow_mul (by positivity)]
          convert (Real.rpow_one _).symm
          field_simp
        _ ≤ _ := by
          convert pow_le_pow_left₀ (by positivity) hN n.toNat
          all_goals convert zpow_natCast _ _; omega
    set k := (N - s.m).toNat
    have hNk : N = s.m + k := by omega
    have hgeom : (fun n ↦ (α+ε) ^ n : Series).converges := by
      simp [converges_geom_iff, abs_of_pos hα', hα]
    replace hgeom := (converges_from _ N.toNat).mp hgeom
    have : (s.from N).absConverges := by
      apply (converges_of_le _ _ hgeom).1
      . simp; omega
      intro n hn
      simp [Series.from] at hn
      have hn' : n ≥ 0 := by omega
      simp [hn.1, hn.2, hn']
      convert this n hn.2
      convert (zpow_natCast _ _).symm
      omega
    unfold absConverges at this ⊢
    rw [converges_from _ k]
    convert this
    simp; constructor
    . omega
    ext n
    by_cases hnm : n ≥ s.m <;> simp [hnm]
    by_cases hn: n ≥ N <;> simp [hn] <;> intros <;> omega


/-- Theorem 7.5.1(b) (Root test) -/
theorem Series.root_test_neg {s : Series}
  (h : Filter.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) Filter.atTop > 1) : s.diverges := by
    -- This proof is written to follow the structure of the original text.
    replace h := Filter.frequently_lt_of_lt_limsup (by isBoundedDefault) h
    apply diverges_of_nodecay
    by_contra this
    rw [LinearOrderedAddCommGroup.tendsto_nhds] at this
    specialize this 1 (by positivity)
    obtain ⟨ n, hn, hs, hs' ⟩ := Filter.Frequently.forall_exists_of_atTop (Filter.Frequently.and_eventually h this) 1
    simp at hs'
    replace hs' := Real.rpow_lt_one (by positivity) hs' (show 0 < 1/(n:ℝ) by positivity)
    rw [(show (1:EReal) = (1:ℝ) by simp), EReal.coe_lt_coe_iff] at hs
    linarith

/-- Theorem 7.5.1(c) (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive: ∃ s:Series,
  Filter.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) Filter.atTop (nhds 1) ∧ s.diverges := by
    sorry

/-- Theorem 7.5.1 (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive' : ∃ s:Series,
  Filter.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) Filter.atTop (nhds 1) ∧ s.absConverges := by
    sorry

/-- Lemma 7.5.2 / Exercise 7.5.1 -/
theorem Series.ratio_ineq {c:ℤ → ℝ} (m:ℤ) (hpos: ∀ n ≥ m, c n > 0) :
  Filter.liminf (fun n ↦ ((c (n+1) / c n:ℝ): EReal)) Filter.atTop ≤
    Filter.liminf (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) Filter.atTop
  ∧ Filter.liminf (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) Filter.atTop ≤
    Filter.limsup (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) Filter.atTop
  ∧ Filter.limsup (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) Filter.atTop ≤
    Filter.limsup (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) Filter.atTop
    := by
  -- This proof is written to follow the structure of the original text.
  refine ⟨ ?_, ?_, ?_ ⟩
  . sorry
  . apply Filter.liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)
  set L' := Filter.limsup (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) Filter.atTop
  by_cases hL : L' = ⊤
  . simp [hL]
  have hL'pos : 0 ≤ L' := by
    apply Filter.le_limsup_of_frequently_le'
    rw [Filter.frequently_atTop ]
    intro N
    use max N m, by omega
    have hpos1 := hpos (max N m) (by omega)
    have hpos2 := hpos ((max N m)+1) (by omega)
    positivity
  have why : L' ≠ ⊥ := by sorry
  set L := L'.toReal
  have hL' : L' = L := (EReal.coe_toReal hL why).symm
  have hLpos : 0 ≤ L := by
    rw [hL'] at hL'pos; norm_cast at hL'pos
  apply le_of_forall_gt_imp_ge_of_dense
  intro y hy
  by_cases hy' : y = ⊤
  . simp [hy']
  have : y = y.toReal := by
    apply (EReal.coe_toReal hy' _).symm
    contrapose! hy
    simp [hy]
  rw [this, hL', EReal.coe_lt_coe_iff] at hy
  set ε := y.toReal - L
  have hε : 0 < ε := by simp [ε]; linarith
  replace this : y = (L+ε:ℝ) := by convert this; simp [ε]
  rw [this]
  have hε' : L' < (L+ε:ℝ) := by rw [hL', EReal.coe_lt_coe_iff]; linarith
  have := Filter.eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
  rw [Filter.eventually_atTop] at this
  obtain ⟨ N', hN ⟩ := this
  set N := max N' (max m 1)
  have (n:ℤ) (hn: n ≥ N) : c (n+1) / c n ≤ (L + ε) := by
    have : n ≥ N' := by omega
    have npos : 0 < n := by omega
    specialize hN n this
    norm_cast at hN
    exact le_of_lt hN
  set A := c N * (L+ε)^(-N)
  have hA : 0 < A := by
    specialize hpos N (by omega)
    positivity
  have why2 (n:ℤ) (hn: n ≥ N) : c n ≤ A * (L+ε)^n := by
    sorry
  have why2_root (n:ℤ) (hn: n ≥ N) : (((c n)^(1/(n:ℝ)):ℝ):EReal) ≤ (A^(1/(n:ℝ)) * (L+ε):ℝ) := by
    rw [EReal.coe_le_coe_iff]
    have hn' : n > 0 := by omega
    calc
      _ ≤ (A * (L+ε)^n)^(1/(n:ℝ)) := by
        apply Real.rpow_le_rpow (le_of_lt (hpos n (by omega)))
        apply why2 n hn
        have : n ≥ 0 := by omega
        positivity
      _ = A^(1/(n:ℝ)) * ((L+ε)^n)^(1/(n:ℝ)) := Real.mul_rpow (by positivity) (by positivity)
      _ = _ := by
        congr
        rw [←Real.rpow_intCast, ←Real.rpow_mul (by positivity)]
        convert (Real.rpow_one _)
        field_simp
  calc
    _ ≤ Filter.limsup (fun n:ℤ ↦ ((A^(1/(n:ℝ)) * (L+ε):ℝ):EReal)) Filter.atTop := by
      apply Filter.limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
      unfold Filter.EventuallyLE
      rw [Filter.eventually_atTop]
      use N
    _ ≤ (Filter.limsup (fun n:ℤ ↦ ((A^(1/(n:ℝ)):ℝ):EReal)) Filter.atTop) * (Filter.limsup (fun n:ℤ ↦ ((L+ε:ℝ):EReal)) Filter.atTop) := by
      convert EReal.limsup_mul_le _ _ _ _ with n
      . rfl
      . apply Filter.Frequently.of_forall
        intro n; positivity
      . unfold Filter.EventuallyLE
        apply Filter.Eventually.of_forall
        simp; positivity
      . simp [-EReal.coe_add]
      simp [-EReal.coe_add]
      right; positivity
    _ = (L+ε:ℝ) := by
      simp
      convert one_mul _
      apply Filter.Tendsto.limsup_eq
      convert Filter.Tendsto.comp (f := fun n:ℤ ↦ (A ^ (n:ℝ)⁻¹)) (g := fun x:ℝ ↦ (x:EReal)) (y := nhds 1) _ _
      . apply Continuous.tendsto' continuous_coe_real_ereal _ _ (by norm_num)
      convert Filter.Tendsto.comp (f := fun n:ℤ ↦ (n:ℝ)⁻¹) (g := fun x:ℝ ↦ A^x) (y := nhds 0) _ _
      . apply Continuous.tendsto' (Real.continuous_const_rpow (by positivity)) _ _ (by simp)
      exact tendsto_inv_atTop_zero.comp tendsto_intCast_atTop_atTop



/-- Corollary 7.5.3 (Ratio test)-/
theorem Series.ratio_test_pos {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : Filter.limsup (fun n ↦ ((|s.seq (n+1)| / |s.seq n|:ℝ):EReal)) Filter.atTop < 1) : s.absConverges := by
    apply Series.root_test_pos (lt_of_le_of_lt _ h)
    convert (ratio_ineq s.m _).2.2
    convert hnon using 1 with n
    simp

/-- Corollary 7.5.3 (Ratio test)-/
theorem Series.ratio_test_neg {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : Filter.liminf (fun n ↦ ((|s.seq (n+1)| / |s.seq n|:ℝ):EReal)) Filter.atTop > 1) : s.diverges := by
    apply Series.root_test_neg (lt_of_lt_of_le h _)
    convert (ratio_ineq s.m _).1.trans (ratio_ineq s.m _).2.1 with n; rfl
    all_goals convert hnon using 1 with n; simp

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive: ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  Filter.Tendsto (fun n ↦ |s.seq n+1| / |s.seq n|) Filter.atTop (nhds 1) ∧ s.diverges := by
    sorry

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive' : ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  Filter.Tendsto (fun n ↦ |s.seq n+1| / |s.seq n|) Filter.atTop (nhds 1) ∧ s.absConverges := by
    sorry

/-- Proposition 7.5.4 -/
theorem Series.root_self_converges : (fun (n:ℕ) ↦ (n:ℝ)^(1 / n : ℝ) : Series).convergesTo 1 := by
  -- This proof is written to follow the structure of the original text.
  sorry

/-- Exercise 7.5.2 -/
theorem Series.poly_mul_geom_converges {x:ℝ} (hx: |x|<1) (q:ℝ) : (fun n:ℕ ↦ (n:ℝ)^q * x^n : Series).converges ∧ Filter.Tendsto (fun n:ℕ ↦ (n:ℝ)^q * x^n) Filter.atTop (nhds 0) := by
  sorry


end Chapter7
