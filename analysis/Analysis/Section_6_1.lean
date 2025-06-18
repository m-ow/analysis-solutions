import Mathlib.Tactic
import Analysis.Section_5_1
import Analysis.Section_5_3
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.1

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of $ε$-closeness, $ε$-steadiness, and their eventual counterparts
- Notion of a Cauchy sequence, convergent sequence, and bounded sequence of reals

-/


/- Definition 6.1.1 (Distance).  Here we use the Mathlib distance. -/
#check Real.dist_eq

abbrev Real.close (ε x y : ℝ) : Prop := dist x y ≤ ε

/--
  Definition 6.1.2 (ε-close). This is similar to the previous notion of ε-closeness, but where
  all quantities are real instead of rational.
-/
theorem Real.close_def (ε x y : ℝ) : ε.close x y ↔ dist x y ≤ ε := by rfl

namespace Chapter6

/--
  Definition 6.1.3 (Sequence). This is similar to the Chapter 5 sequence, except that now the
  sequence is real-valued. As with Chapter 5, we start sequences from 0 by default.
-/
@[ext]
structure Sequence where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Sequences can be thought of as functions from ℤ to ℝ. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℝ) where
  coe := fun a ↦ a.seq

/-- Functions from ℕ to ℝ can be thought of as sequences. -/
instance Sequence.instCoe : Coe (ℕ → ℝ) Sequence where
  coe := fun a ↦ {
    m := 0
    seq := fun n ↦ if n ≥ 0 then a n.toNat else 0
    vanish := by
      intro n hn
      simp [hn]
  }

abbrev Sequence.mk' (m:ℤ) (a: { n // n ≥ m } → ℝ) : Sequence where
  m := m
  seq := fun n ↦ if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by
    intro n hn
    simp [hn]


lemma Sequence.eval_mk {n m:ℤ} (a: { n // n ≥ m } → ℝ) (h: n ≥ m) :
    (Sequence.mk' m a) n = a ⟨ n, h ⟩ := by simp [seq, h]

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℝ) : (a:Sequence) n = a n := by simp [seq]

/--
  a.from n₁ starts `a:Sequence` from `n₁`.  It is intended for use when `n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence `a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (m₁:ℤ) : Sequence :=
  mk' (max a.m m₁) (fun n ↦ a (n:ℤ))

lemma Sequence.from_eval (a:Sequence) {m₁ n:ℤ} (hn: n ≥ m₁) :
  (a.from m₁) n = a n := by
  simp [Sequence.from, seq, hn]
  intro h
  exact (a.vanish n h).symm

end Chapter6

/-- Definition 6.1.3 (ε-steady) -/
abbrev Real.steady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∀ n ≥ a.m, ∀ m ≥ a.m, ε.close (a n) (a m)

/-- Definition 6.1.3 (ε-steady) -/
lemma Real.steady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.steady a ↔ ∀ n ≥ a.m, ∀ m ≥ a.m, ε.close (a n) (a m) := by rfl

/-- Definition 6.1.3 (Eventually ε-steady) -/
abbrev Real.eventuallySteady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.steady (a.from N)

/-- Definition 6.1.3 (Eventually ε-steady) -/
lemma Real.eventuallySteady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.eventuallySteady a ↔ ∃ N, (N ≥ a.m) ∧ ε.steady (a.from N) := by rfl

theorem Real.steady_mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂) (hsteady: ε₁.steady a) :
    ε₂.steady a := by sorry

theorem Real.eventuallySteady_mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂)
  (hsteady: ε₁.eventuallySteady a) :
    ε₂.eventuallySteady a := by sorry

namespace Chapter6

/-- Definition 6.1.3 (Cauchy sequence) -/
abbrev Sequence.isCauchy (a:Sequence) : Prop := ∀ ε > (0:ℝ), ε.eventuallySteady a

/-- Definition 6.1.3 (Cauchy sequence) -/
lemma Sequence.isCauchy_def (a:Sequence) :
  a.isCauchy ↔ ∀ ε > (0:ℝ), ε.eventuallySteady a := by rfl

lemma Sequence.isCauchy_of_coe (a:ℕ → ℝ) :
    (a:Sequence).isCauchy ↔ ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, dist (a j) (a k) ≤ ε := by sorry

lemma Sequence.isCauchy_of_mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℝ) :
    (mk' n₀ a).isCauchy
    ↔ ∀ ε > 0, ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N, dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by sorry

instance Chapter5.Sequence.inst_coe_sequence : Coe Chapter5.Sequence Sequence  where
  coe := fun a ↦ {
    m := a.n₀
    seq := fun n ↦ ((a n):ℝ)
    vanish := by
      intro n hn
      have := a.vanish n hn
      simp [this]
  }

@[simp]
theorem Chapter5.coe_sequence_eval (a: Chapter5.Sequence) (n:ℤ) : (a:Sequence) n = (a n:ℝ) := rfl

theorem Sequence.is_steady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.steady a ↔ (ε:ℝ).steady (a:Sequence) := by sorry

theorem Sequence.is_eventuallySteady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.eventuallySteady a ↔ (ε:ℝ).eventuallySteady (a:Sequence) := by sorry

/-- Proposition 6.1.4 -/
theorem Sequence.isCauchy_of_rat (a: Chapter5.Sequence) : a.isCauchy ↔ (a:Sequence).isCauchy := by
  -- This proof is written to follow the structure of the original text.
  constructor
  swap
  . intro h
    rw [isCauchy_def] at h
    rw [Chapter5.Sequence.isCauchy_def]
    intro ε hε
    specialize h (ε:ℝ) (by positivity)
    rwa [is_eventuallySteady_of_rat]
  intro h
  rw [Chapter5.Sequence.isCauchy_def] at h
  rw [isCauchy_def]
  intro ε hε
  have : ∃ ε' > (0:ℚ), ε' < ε := exists_pos_rat_lt hε
  obtain ⟨ ε', hε', hlt ⟩ := this
  specialize h ε' hε'
  rw [is_eventuallySteady_of_rat] at h
  exact Real.eventuallySteady_mono (le_of_lt hlt) h

end Chapter6

/-- Definition 6.1.5 -/
abbrev Real.close_seq (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop := ∀ n ≥ a.m, ε.close (a n) L

/-- Definition 6.1.5 -/
theorem Real.close_seq_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.close_seq a L ↔ ∀ n ≥ a.m, dist (a n) L ≤ ε := by rfl

/-- Definition 6.1.5 -/
abbrev Real.eventually_close (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop :=
  ∃ N ≥ a.m, ε.close_seq (a.from N) L

/-- Definition 6.1.5 -/
theorem Real.eventually_close_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.eventually_close a L ↔ ∃ N, (N ≥ a.m) ∧ ε.close_seq (a.from N) L := by rfl

theorem Real.close_seq_mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.close_seq a L) :
    ε₂.close_seq a L := by sorry

theorem Real.eventually_close_mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.eventually_close a L) :
    ε₂.eventually_close a L := by sorry

namespace Chapter6

abbrev Sequence.tendsTo (a:Sequence) (L:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.eventually_close a L

theorem Sequence.tendsTo_def (a:Sequence) (L:ℝ) :
  a.tendsTo L ↔ ∀ ε > (0:ℝ), ε.eventually_close a L := by rfl

/-- Exercise 6.1.2 -/
theorem Sequence.tendsTo_iff (a:Sequence) (L:ℝ) :
  a.tendsTo L ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| ≤ ε := by sorry

noncomputable abbrev seq_6_1_6 : Sequence := (fun (n:ℕ) ↦ 1-(10:ℝ)^(-(n:ℤ)-1):Sequence)

/-- Examples 6.1.6 -/
example : (0.1:ℝ).close_seq seq_6_1_6 1 := by sorry

/-- Examples 6.1.6 -/
example : ¬ (0.01:ℝ).close_seq seq_6_1_6 1 := by sorry

/-- Examples 6.1.6 -/
example : (0.01:ℝ).eventually_close seq_6_1_6 1 := by sorry

/-- Examples 6.1.6 -/
example : seq_6_1_6.tendsTo 1 := by sorry

/-- Proposition 6.1.7 (Uniqueness of limits) -/
theorem Sequence.tendsTo_unique (a:Sequence) {L L':ℝ} (h:L ≠ L') :
    ¬ (a.tendsTo L ∧ a.tendsTo L') := by
  -- This proof is written to follow the structure of the original text.
  by_contra this
  obtain ⟨ hL, hL' ⟩ := this
  replace h : L - L' ≠ 0 := by contrapose! h; linarith
  replace h : |L-L'| > 0 := by positivity
  set ε := |L-L'| / 3
  have hε : ε > 0 := by positivity
  rw [tendsTo_iff] at hL hL'
  specialize hL ε hε
  obtain ⟨ N, hN ⟩ := hL
  specialize hL' ε hε
  obtain ⟨ M, hM ⟩ := hL'
  set n := max N M
  specialize hN n (le_max_left N M)
  specialize hM n (le_max_right N M)
  have : |L-L'| ≤ 2 * |L-L'|/3 := calc
    _ = dist L L' := by rw [Real.dist_eq]
    _ ≤ dist L (a.seq n) + dist (a.seq n) L' := dist_triangle _ _ _
    _ ≤ ε + ε := by
      rw [←Real.dist_eq] at hN hM
      rw [dist_comm] at hN
      gcongr
    _ = 2 * |L-L'|/3 := by
      simp [ε]; ring
  linarith

/-- Definition 6.1.8 -/
abbrev Sequence.convergent (a:Sequence) : Prop := ∃ L, a.tendsTo L

/-- Definition 6.1.8 -/
theorem Sequence.convergent_def (a:Sequence) : a.convergent ↔ ∃ L, a.tendsTo L := by rfl

/-- Definition 6.1.8 -/
abbrev Sequence.divergent (a:Sequence) : Prop := ¬ a.convergent

/-- Definition 6.1.8 -/
theorem Sequence.divergent_def (a:Sequence) : a.divergent ↔ ¬ a.convergent := by rfl

open Classical in
/--
  Definition 6.1.8.  We give the limit of a sequence the junk value of 0 if it is not convergent.
-/
noncomputable abbrev lim (a:Sequence) : ℝ := if h: a.convergent then h.choose else 0

/-- Definition 6.1.8 -/
theorem Sequence.lim_def {a:Sequence} (h: a.convergent) : a.tendsTo (lim a) := by
  unfold lim
  simp [h]
  convert h.choose_spec

/-- Definition 6.1.8-/
theorem Sequence.lim_eq {a:Sequence} {L:ℝ} :
a.tendsTo L ↔ a.convergent ∧ lim a = L := by
  constructor
  . intro h
    by_contra! eq
    have : a.convergent := by rw [convergent_def]; use L
    replace eq := a.tendsTo_unique (eq this)
    replace this := lim_def this
    tauto
  intro ⟨ h, h' ⟩
  convert lim_def h
  rw [h']


/-- Proposition 6.1.11 -/
theorem Sequence.lim_harmonic :
    ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence).convergent ∧ lim ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  rw [←lim_eq, tendsTo_iff]
  intro ε hε
  have : ∃ (N:ℤ), N > 1/ε := exists_int_gt (1 / ε)
  obtain ⟨ N, hN ⟩ := this
  use N
  intro n hn
  have hNpos : (N:ℝ) > 0 := by apply LT.lt.trans _ hN; positivity
  simp at hNpos
  have hnpos : n ≥ 0 := by linarith
  simp [hnpos, abs_inv]
  calc
    _ ≤ (N:ℝ)⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      calc
        _ ≤ (n:ℝ) := by simp [hn]
        _ = (n.toNat:ℤ) := by simp [hnpos]
        _ = n.toNat := rfl
        _ ≤ (n.toNat:ℝ) + 1 := by linarith
        _ ≤ _ := le_abs_self _
    _ ≤ ε := by
      rw [inv_le_comm₀ (by positivity) (by positivity)]
      apply le_of_lt
      rw [gt_iff_lt, ←inv_eq_one_div _] at hN
      assumption

/-- Proposition 6.1.12 / Exercise 6.1.5 -/
theorem Sequence.Cauchy_of_convergent {a:Sequence} (h:a.convergent) : a.isCauchy := by
  sorry

/-- Example 6.1.13 -/
example : ¬ (0.1:ℝ).eventuallySteady ((fun n ↦ (-1:ℝ)^n):Sequence) := by sorry

/-- Example 6.1.13 -/
example : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).isCauchy := by sorry

/-- Example 6.1.13 -/
example : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).convergent := by sorry

/-- Proposition 6.1.15 / Exercise 6.1.6 (Formal limits are genuine limits)-/
theorem Sequence.lim_eq_LIM {a:ℕ → ℚ} (h: (a:Chapter5.Sequence).isCauchy) :
    ((a:Chapter5.Sequence):Sequence).tendsTo (Chapter5.Real.equivR (Chapter5.LIM a)) := by sorry

/-- Definition 6.1.16 -/
abbrev Sequence.BoundedBy (a:Sequence) (M:ℝ) : Prop :=
  ∀ n, |a n| ≤ M

/-- Definition 6.1.16 -/
lemma Sequence.BoundedBy_def (a:Sequence) (M:ℝ) :
  a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

/-- Definition 6.1.16 -/
abbrev Sequence.isBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 6.1.16 -/
lemma Sequence.isBounded_def (a:Sequence) :
  a.isBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

theorem Sequence.bounded_of_cauchy {a:Sequence} (h: a.isCauchy) : a.isBounded := by
  sorry

/-- Corollary 6.1.17 -/
theorem Sequence.bounded_of_convergent {a:Sequence} (h: a.convergent) : a.isBounded := by
  sorry

/-- Example 6.1.18 -/
example : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).isBounded := by sorry

/-- Example 6.1.18 -/
example : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).convergent := by sorry

instance Sequence.inst_add : Add Sequence where
  add a b := {
    m := max a.m b.m
    seq := fun (n:ℤ) ↦ if n ≥ max a.m b.m then a n + b n else 0
    vanish := by
      intro n hn
      rw [lt_iff_not_ge] at hn
      simp [hn]
  }

/-- Theorem 6.1.19(a) (limit laws) -/
theorem Sequence.lim_add {a b:Sequence} (ha: a.convergent) (hb: b.convergent) :
    (a + b).convergent ∧ lim (a + b) = lim a + lim b := by
  sorry

instance Sequence.inst_mul : Mul Sequence where
  mul a b := {
    m := max a.m b.m
    seq := fun (n:ℤ) ↦ if n ≥ max a.m b.m then a n * b n else 0
    vanish := by
      intro n hn
      rw [lt_iff_not_ge] at hn
      simp [hn]
  }

/-- Theorem 6.1.19(b) (limit laws) -/
theorem Sequence.lim_mul {a b:Sequence} (ha: a.convergent) (hb: b.convergent) :
    (a * b).convergent ∧ lim (a * b) = lim a * lim b := by
  sorry


instance Sequence.inst_smul : SMul ℝ Sequence where
  smul c a := {
    m := a.m
    seq := fun (n:ℤ) ↦ c * a n
    vanish := by
      intro n hn
      simp [a.vanish n hn]
  }

/-- Theorem 6.1.19(c) (limit laws) -/
theorem Sequence.lim_smul (c:ℝ) {a:Sequence} (ha: a.convergent) :
    (c • a).convergent ∧ lim (c • a) = c * lim a := by
  sorry

instance Sequence.inst_sub : Sub Sequence where
  sub a b := {
    m := max a.m b.m
    seq := fun (n:ℤ) ↦ if n ≥ max a.m b.m then a n - b n else 0
    vanish := by
      intro n hn
      rw [lt_iff_not_ge] at hn
      simp [hn]
  }

/-- Theorem 6.1.19(d) (limit laws) -/
theorem Sequence.lim_sub {a b:Sequence} (ha: a.convergent) (hb: b.convergent) :
    (a - b).convergent ∧ lim (a - b) = lim a - lim b := by
  sorry

noncomputable instance Sequence.inst_inv : Inv Sequence where
  inv a := {
    m := a.m
    seq := fun (n:ℤ) ↦ (a n)⁻¹
    vanish := by
      intro n hn
      simp [a.vanish n hn]
  }

/-- Theorem 6.1.19(e) (limit laws) -/
theorem Sequence.lim_inv {a:Sequence} (ha: a.convergent) (hnon: lim a ≠ 0) :
  (a⁻¹).convergent ∧ lim (a⁻¹) = (lim a)⁻¹ := by
  sorry

noncomputable instance Sequence.inst_div : Div Sequence where
  div a b := {
    m := max a.m b.m
    seq := fun (n:ℤ) ↦ if n ≥ max a.m b.m then a n / b n else 0
    vanish := by
      intro n hn
      rw [lt_iff_not_ge] at hn
      simp [hn]
  }

/-- Theorem 6.1.19(f) (limit laws) -/
theorem Sequence.lim_div {a b:Sequence} (ha: a.convergent) (hb: b.convergent) (hnon: lim b ≠ 0) :
  (a / b).convergent ∧ lim (a / b) = lim a / lim b := by
  sorry

instance Sequence.inst_max : Max Sequence where
  max a b := {
    m := max a.m b.m
    seq := fun (n:ℤ) ↦ if n ≥ max a.m b.m then max (a n) (b n) else 0
    vanish := by
      intro n hn
      rw [lt_iff_not_ge] at hn
      simp [hn]
  }

/-- Theorem 6.1.19(g) (limit laws) -/
theorem Sequence.lim_max {a b:Sequence} (ha: a.convergent) (hb: b.convergent) (hnon: lim b ≠ 0) :
    (max a b).convergent ∧ lim (max a b) = max (lim a) (lim b) := by
  sorry

instance Sequence.inst_min : Min Sequence where
  min a b := {
    m := max a.m b.m
    seq := fun (n:ℤ) ↦ if n ≥ max a.m b.m then min (a n) (b n) else 0
    vanish := by
      intro n hn
      rw [lt_iff_not_ge] at hn
      simp [hn]
  }

/-- Theorem 6.1.19(h) (limit laws) -/
theorem Sequence.lim_min {a b:Sequence} (ha: a.convergent) (hb: b.convergent) (hnon: lim b ≠ 0) :
    (min a b).convergent ∧ lim (min a b) = min (lim a) (lim b) := by
  sorry

/-- Exercise 6.1.1 -/
theorem Sequence.mono_if {a: ℕ → ℝ} (ha: ∀ n, a (n+1) > a n) {n m:ℕ} (hnm: m > n) : a m > a n := by
  sorry

/-- Exercise 6.1.3 -/
theorem Sequence.tendsTo_of_from {a: Sequence} {c:ℝ} (m:ℤ) :
    a.tendsTo c ↔ (a.from m).tendsTo c := by
  sorry

/-- Exercise 6.1.4 -/
theorem Sequence.tendsTo_of_shift {a: Sequence} {c:ℝ} (k:ℕ) :
    a.tendsTo c ↔ (Sequence.mk' a.m (fun n : {n // n ≥ a.m} ↦ a (n+k))).tendsTo c := by
  sorry

/-- Exercise 6.1.7 -/
theorem Sequence.isBounded_of_rat (a: Chapter5.Sequence) :
    a.isBounded ↔ (a:Sequence).isBounded := by
  sorry

/-- Exercise 6.1.9 -/
theorem Sequence.lim_div_fail :
    ∃ a b, a.convergent
    ∧ b.convergent
    ∧ lim b = 0
    ∧ ¬ ((a / b).convergent ∧ lim (a / b) = lim a / lim b) := by
  sorry

/-- Exercise 6.1.10 -/
theorem Chapter5.Sequence.isCauchy_iff (a:Chapter5.Sequence) :
    a.isCauchy ↔ ∀ ε > (0:ℝ), ∃ N ≥ a.n₀, ∀ n ≥ N, ∀ m ≥ N, |a n - a m| ≤ ε := by
  sorry



end Chapter6
