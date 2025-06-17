import Mathlib.Tactic

/-!
# Analysis I, Section 7.2

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.
-/

namespace Chapter7

open BigOperators

/-- Definition 7.2.1 (Formal infinite series). This is similar to Chapter 6 sequence, but is manipulated differently.  As with Chapter 5, we will start series from 0 by default. -/
@[ext]
structure Series where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Functions from ℕ to ℝ can be thought of as series. -/
instance Series.instCoe : Coe (ℕ → ℝ) Series where
  coe := fun a ↦ {
    m := 0
    seq := fun n ↦ if n ≥ 0 then a n.toNat else 0
    vanish := by
      intro n hn
      simp [hn]
  }

@[simp]
theorem Series.eval_coe (a : ℕ → ℝ) (n : ℕ) : (a : Series).seq n = a n := by simp

abbrev Series.mk' {m:ℤ} (a: { n // n ≥ m } → ℝ) : Series where
  m := m
  seq := fun n ↦ if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by
    intro n hn
    simp [hn]

theorem Series.eval_mk' {m:ℤ} (a : { n // n ≥ m } → ℝ) {n : ℤ} (h:n ≥ m) : (Series.mk' a).seq n = a ⟨ n, h ⟩ := by simp [h] 

/-- Definition 7.2.2 (Convergence of series) -/
abbrev Series.partial (s : Series) (N:ℤ) : ℝ := ∑ n ∈ Finset.Icc s.m N, s.seq n

abbrev Series.convergesTo (s : Series) (L:ℝ) : Prop := Filter.Tendsto (s.partial) Filter.atTop (nhds L)

abbrev Series.converges (s : Series) : Prop := ∃ L, s.convergesTo L

abbrev Series.diverges (s : Series) : Prop := ¬s.converges

open Classical in
noncomputable abbrev Series.sum (s : Series) : ℝ :=
  if h : s.converges then h.choose else 0

theorem Series.converges_of_convergesTo {s : Series} {L:ℝ} (h: s.convergesTo L) : s.converges := by use L

/-- Remark 7.2.3 -/
theorem Series.sum_of_converges {s : Series} {L:ℝ} (h: s.convergesTo L) : s.sum = L := by
  simp [sum, converges_of_convergesTo h]
  exact tendsto_nhds_unique ((converges_of_convergesTo h).choose_spec) h

/-- Example 7.2.4 -/
noncomputable abbrev Series.example_7_2_4 := mk' (m := 1) (fun n ↦ (2:ℝ)^(-n:ℤ))

theorem Series.example_7_2_4a {N:ℤ} (hN: N ≥ 1) : example_7_2_4.partial N = 1 - (2:ℝ)^(-N) := by sorry

theorem Series.example_7_2_4b : example_7_2_4.convergesTo 1 := by sorry

theorem Series.example_7_2_4c : example_7_2_4.sum = 1 := by sorry

noncomputable abbrev Series.example_7_2_4' := mk' (m := 1) (fun n ↦ (2:ℝ)^(n:ℤ))

theorem Series.example_7_2_4'a {N:ℤ} (hN: N ≥ 1) : example_7_2_4'.partial N = (2:ℝ)^(N+1) - 2 := by sorry

theorem Series.example_7_2_4'b : example_7_2_4'.diverges := by sorry

/-- Proposition 7.2.5 / Exercise 7.2.2 -/
theorem Series.converges_iff_tail_decay (s:Series) : s.converges ↔ ∀ ε > 0, ∃ N ≥ s.m, ∀ p ≥ N, ∀ q ≥ N, |∑ n ∈ Finset.Icc p q, s.seq n| ≤ ε := by sorry

/-- Corollary 7.2.6 (Zero test) / Exercise 7.2.3 -/
theorem Series.decay_of_converges {s:Series} (h: s.converges) : Filter.Tendsto s.seq Filter.atTop (nhds 0) := by sorry

theorem Series.diverges_of_nodecay {s:Series} (h: ¬ Filter.Tendsto s.seq Filter.atTop (nhds 0)) : s.diverges := by sorry

/-- Example 7.2.7 -/
theorem Series.example_7_2_7 : ((fun n:ℕ ↦ (1:ℝ)):Series).diverges := by
  apply diverges_of_nodecay
  sorry

theorem Series.example_7_2_7' : ((fun n:ℕ ↦ (-1:ℝ)^n):Series).diverges := by
  apply diverges_of_nodecay
  sorry

/-- Definition 7.2.8 (Absolute convergence) -/
abbrev Series.abs (s:Series) : Series := mk' (m:=s.m) (fun n ↦ |s.seq n|)

abbrev Series.absConverges (s:Series) : Prop := s.abs.converges

abbrev Series.condConverges (s:Series) : Prop := s.converges ∧ ¬ s.absConverges

/-- Proposition 7.2.9 (Absolute convergence test) / Example 7.2.4 -/
theorem Series.converges_of_absConverges {s:Series} (h : s.absConverges) : s.converges := by sorry

theorem Series.abs_le {s:Series} (h : s.absConverges) : |s.sum| ≤ s.abs.sum := by sorry

/-- Proposition 7.2.12 (Alternating series test) -/
theorem Series.converges_of_alternating {m:ℤ} {a: { n // n ≥ m} → ℝ} (ha: ∀ n, a n ≥ 0) (ha': Antitone a) : ((mk' (m:=m) (fun n ↦ (-1)^(n:ℤ) * a n)).converges ↔ Filter.Tendsto a Filter.atTop (nhds 0)) := by
  -- This proof is written to follow the structure of the original text.
  constructor
  . intro h
    replace h := decay_of_converges h
    sorry -- TODO
  intro h
  unfold converges convergesTo
  set S := (mk' fun n ↦ (-1) ^ (n:ℤ) * a n).partial
  sorry -- TODO

/-- Example 7.2.13 -/
noncomputable abbrev Series.example_7_2_13 : Series := (mk' (m:=1) (fun n ↦ (-1:ℝ)^(n:ℤ) / (n:ℤ)))

theorem Series.example_7_2_13a : example_7_2_13.converges := by
  sorry

theorem Series.example_7_2_13b : ¬ example_7_2_13.absConverges := by
  sorry

theorem Series.example_7_2_13c :  example_7_2_13.condConverges := by
  sorry

instance Series.inst_add : Add Series where
  add a b := {
    m := max a.m b.m
    seq := fun (n:ℤ) ↦ if n ≥ max a.m b.m then a.seq n + b.seq n else 0
    vanish := by
      intro n hn
      rw [lt_iff_not_ge] at hn
      simp [hn]
  }

/-- Proposition 7.2.14 (a) (Series laws) / Exercise 7.2.5 -/
theorem Series.add {s t:Series} (hs: s.converges) (ht: t.converges) : (s + t).converges ∧ (s+t).sum = s.sum + t.sum := by sorry

instance Series.inst.smul : SMul ℝ Series where
  smul c s := {
    m := s.m
    seq := fun n ↦ if n ≥ s.m then c * s.seq n else 0
    vanish := by
      intro n hn
      rw [lt_iff_not_ge] at hn
      simp [hn]
  }
/-- Proposition 7.2.14 (b) (Series laws) / Exercise 7.2.5 -/
theorem Series.smul {c:ℝ} {s:Series} (hs: s.converges) : (c • s).converges ∧ (c • s).sum = c * s.sum := by sorry

abbrev Series.from (s:Series) (m₁:ℤ) : Series := mk' (m := max s.m m₁) (fun n ↦ s.seq (n:ℤ))

/-- Proposition 7.2.14 (c) (Series laws) / Exercise 7.2.5 -/
theorem Series.converges_from (s:Series) (k:ℕ) : s.converges ↔ (s.from (s.m+k)).converges := by sorry

theorem Series.sum_from {s:Series} (k:ℕ) (h: s.converges) : s.sum = ∑ n ∈ Finset.Ico s.m (s.m+k), s.seq n + (s.from (s.m+k)).sum := by sorry

/-- Proposition 7.2.14 (d) (Series laws) / Exercise 7.2.5 -/
theorem Series.shift {s:Series} {x:ℝ} (h: s.convergesTo x) (L:ℤ) : (mk' (m := s.m + L) (fun n ↦ s.seq (n - L))).convergesTo x := by sorry

/-- Lemma 7.2.15 (telescoping series) / Exercise 7.2.6 -/
theorem Series.telescope {a:ℕ → ℝ} (ha: Filter.Tendsto a Filter.atTop (nhds 0)) : ((fun n:ℕ ↦ a (n+1) - a n):Series).convergesTo (a 0) := by sorry

/- Exercise 7.2.1 : uncomment and prove one of the following statements, and delete the other. -/

-- theorem Series.exercise_7_2_1_convergent : (mk' (m := 1) (fun n ↦ (-1:ℝ)^(n:ℤ))).converges := by sorry

-- theorem Series.exercise_7_2_1_divergent : (mk' (m := 1) (fun n ↦ (-1:ℝ)^(n:ℤ))).diverges := by sorry

end Chapter7
