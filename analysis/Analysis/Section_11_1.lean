import Mathlib.Tactic

/-!
# Analysis I, Section 11.1: Partitions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Bounded intervals and partitions.
- Length of an interval; the lengths of a partition sum to the length of the interval.

-/

namespace Chapter11

inductive BoundedInterval where
  | Ioo (a b:ℝ) : BoundedInterval
  | Icc (a b:ℝ) : BoundedInterval
  | Ioc (a b:ℝ) : BoundedInterval
  | Ico (a b:ℝ) : BoundedInterval

open BoundedInterval

/-- There is a technical issue in that this coercion is not injective: the empty set is represented by multiple bounded intervals.  This causes some of the statements in this section to be a little uglier than necessary.-/
@[coe]
def BoundedInterval.toSet (I: BoundedInterval) : Set ℝ := match I with
  | Ioo a b => Set.Ioo a b
  | Icc a b => Set.Icc a b
  | Ioc a b => Set.Ioc a b
  | Ico a b => Set.Ico a b

instance BoundedInterval.inst_coeSet : Coe BoundedInterval (Set ℝ) where
  coe := toSet

instance BoundedInterval.instEmpty : EmptyCollection BoundedInterval where
  emptyCollection := Ioo 0 0

@[simp]
theorem BoundedInterval.coe_empty : ((∅ : BoundedInterval):Set ℝ) = ∅ := by
  simp [toSet]

open Classical in
/-- This is to make Finsets of BoundedIntervals work properly -/
noncomputable instance BoundedInterval.decidableEq : DecidableEq BoundedInterval := instDecidableEqOfLawfulBEq

@[simp]
theorem BoundedInterval.set_Ioo (a b:ℝ) : (Ioo a b : Set ℝ) = Set.Ioo a b := by rfl

@[simp]
theorem BoundedInterval.set_Icc (a b:ℝ) : (Icc a b : Set ℝ) = Set.Icc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ioc (a b:ℝ) : (Ioc a b : Set ℝ) = Set.Ioc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ico (a b:ℝ) : (Ico a b : Set ℝ) = Set.Ico a b := by rfl

-- Definition 11.1.1
#check Set.ordConnected_def

/-- Examples 11.1.3 -/
example : (Set.Icc 1 2 : Set ℝ).OrdConnected := by sorry

example : (Set.Ioo 1 2 : Set ℝ).OrdConnected := by sorry

example : ¬ (Set.Icc 1 2 ∪ Set.Icc 3 4 : Set ℝ).OrdConnected := by sorry

example : (∅:Set ℝ).OrdConnected := by sorry

example (x:ℝ) : ({x}: Set ℝ).OrdConnected := by sorry

/-- Lemma 11.1.4 / Exercise 11.1.1 -/
theorem Bornology.IsBounded.of_boundedInterval (I: BoundedInterval) : Bornology.IsBounded (I:Set ℝ) := by
  sorry

theorem BoundedInterval.ordConnected_iff (X:Set ℝ) : Bornology.IsBounded X ∧ X.OrdConnected ↔ ∃ I: BoundedInterval, X = I := by
  sorry

/-- Corollary 11.1.6 / Exercise 11.1.2 -/
theorem BoundedInterval.inter (I J: BoundedInterval) : ∃ K : BoundedInterval, (I:Set ℝ) ∩ (J:Set ℝ) = (K:Set ℝ) := by
  sorry

noncomputable instance BoundedInterval.instInter : Inter BoundedInterval where
  inter I J := (inter I J).choose

@[simp]
theorem BoundedInterval.inter_eq (I J: BoundedInterval) : (I ∩ J : BoundedInterval) = (I:Set ℝ) ∩ (J:Set ℝ)  :=
  (BoundedInterval.inter I J).choose_spec.symm

example :
  (Ioo 2 4 ∩ Icc 4 6) = (Icc 4 4 : Set ℝ) := by
  sorry

instance BoundedInterval.instMembership : Membership ℝ BoundedInterval where
  mem I x := x ∈ (I:Set ℝ)

theorem BoundedInterval.mem_iff (I: BoundedInterval) (x:ℝ) :
  x ∈ I ↔ x ∈ (I:Set ℝ) := by rfl

instance BoundedInterval.instSubset : HasSubset BoundedInterval where
  Subset I J := ∀ x, x ∈ I → x ∈ J

theorem BoundedInterval.subset_iff (I J: BoundedInterval) :
  I ⊆ J ↔ (I:Set ℝ) ⊆ (J:Set ℝ) := by rfl

abbrev BoundedInterval.a (I: BoundedInterval) : ℝ := match I with
  | Ioo a _ => a
  | Icc a _ => a
  | Ioc a _ => a
  | Ico a _ => a

abbrev BoundedInterval.b (I: BoundedInterval) : ℝ := match I with
  | Ioo _ b => b
  | Icc _ b => b
  | Ioc _ b => b
  | Ico _ b => b

theorem BoundedInterval.subset_Icc (I: BoundedInterval) : I ⊆ Icc I.a I.b := match I with
  | Ioo a b => by simp [Ioo, Icc, BoundedInterval.a, BoundedInterval.b, subset_iff, Set.Ioo_subset_Icc_self]
  | Icc a b => by simp [Icc, BoundedInterval.a, BoundedInterval.b, subset_iff]
  | Ioc a b => by simp [Ioc, Icc, BoundedInterval.a, BoundedInterval.b, subset_iff, Set.Ioc_subset_Icc_self]
  | Ico a b => by simp [Ico, Icc, BoundedInterval.a, BoundedInterval.b, subset_iff, Set.Ico_subset_Icc_self]

theorem BoundedInterval.Ioo_subset (I: BoundedInterval) : Ioo I.a I.b ⊆ I := match I with
  | Ioo a b => by simp [Ioo, BoundedInterval.a, BoundedInterval.b, subset_iff]
  | Icc a b => by simp [Icc, BoundedInterval.a, BoundedInterval.b, subset_iff, Set.Ioo_subset_Icc_self]
  | Ioc a b => by simp [Ioc, Ioo, BoundedInterval.a, BoundedInterval.b, subset_iff, Set.Ioo_subset_Ioc_self]
  | Ico a b => by simp [Ico, Ioo, BoundedInterval.a, BoundedInterval.b, subset_iff, Set.Ioo_subset_Ico_self]

instance BoundedInterval.instTrans : IsTrans BoundedInterval (· ⊆ ·) where
  trans I J K hIJ hJK := by
    simp [subset_iff] at hIJ hJK ⊢
    exact hIJ.trans hJK

@[simp]
theorem BoundedInterval.mem_inter (I J: BoundedInterval) (x:ℝ) :
  x ∈ (I ∩ J : BoundedInterval) ↔ x ∈ I ∧ x ∈ J := by
  simp [inter_eq, Set.mem_inter_iff, mem_iff, mem_iff]

abbrev BoundedInterval.length (I: BoundedInterval) : ℝ := max (I.b - I.a) 0

/-- Using ||ₗ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ₗ" : term => `(BoundedInterval.length $a)

example : |Icc 3 5|ₗ = 2 := by
  sorry

example : |Ioo 3 5|ₗ = 2 := by
  sorry

example : |Icc 5 5|ₗ = 0 := by
  sorry

theorem BoundedInterval.length_nonneg (I: BoundedInterval) : 0 ≤ |I|ₗ := by
  simp [length, max_le_iff]

theorem BoundedInterval.empty_of_lt {I: BoundedInterval} (h: I.b < I.a) : (I:Set ℝ) = ∅ := by
  cases I with
  | Ioo a b => simp [Ioo, le_of_lt h]
  | Icc a b => simp [Icc, h]
  | Ioc a b => simp [Ioc, le_of_lt h]
  | Ico a b => simp [Ico, le_of_lt h]

theorem BoundedInterval.length_of_empty {I: BoundedInterval} (hI: (I:Set ℝ) = ∅) : |I|ₗ = 0 := by
  sorry

theorem BoundedInterval.length_of_subsingleton {I: BoundedInterval} : Subsingleton (I:Set ℝ) ↔ |I|ₗ = 0 := by
  sorry

theorem BoundedInterval.dist_le_length {I:BoundedInterval} {x y:ℝ} (hx: x ∈ I) (hy: y ∈ I) : |x - y| ≤ |I|ₗ := by
  replace hx := subset_Icc I _ hx
  replace hy := subset_Icc I _ hy
  simp [mem_iff, abs_le'] at hx hy ⊢
  left; exact ⟨ by linarith, by linarith ⟩

abbrev BoundedInterval.joins (K I J: BoundedInterval) : Prop := (I:Set ℝ) ∩ (J:Set ℝ) = ∅
  ∧ (K:Set ℝ) = (I:Set ℝ) ∪ (J:Set ℝ) ∧ |K|ₗ = |I|ₗ + |J|ₗ

theorem BoundedInterval.join_Icc_Ioc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins (Icc a b) (Ioc b c) := by
  refine ⟨ ?_, ?_, ?_ ⟩
  . rw [Set.eq_empty_iff_forall_notMem]; intros; simp; intros; linarith
  . ext x; simp; constructor
    . intro ⟨ h1, h2 ⟩; simp [h1, h2]; exact le_or_lt x b
    rintro (h1 | h2)
    . exact ⟨ h1.1, by linarith ⟩
    exact ⟨ by linarith, h2.2 ⟩
  simp [length, BoundedInterval.a, BoundedInterval.b,
        show a ≤ b by linarith, show b ≤ c by linarith, show a ≤ c by linarith]

theorem BoundedInterval.join_Icc_Ioo {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ico a c).joins (Icc a b) (Ioo b c) := by
  refine ⟨ ?_, ?_, ?_ ⟩
  . rw [Set.eq_empty_iff_forall_notMem]; intros; simp; intros; linarith
  . ext x; simp; constructor
    . intro ⟨ h1, h2 ⟩; simp [h1, h2]; exact le_or_lt x b
    rintro (h1 | h2)
    . exact ⟨ h1.1, by linarith ⟩
    exact ⟨ by linarith, h2.2 ⟩
  simp [length, BoundedInterval.a, BoundedInterval.b,
        show a ≤ b by linarith, show b ≤ c by linarith, show a ≤ c by linarith]

theorem BoundedInterval.join_Ioc_Ioc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ioc a c).joins (Ioc a b) (Ioc b c) := by
  refine ⟨ ?_, ?_, ?_ ⟩
  . rw [Set.eq_empty_iff_forall_notMem]; intros; simp; intros; linarith
  . ext x; simp; constructor
    . intro ⟨ h1, h2 ⟩; simp [h1, h2]; exact le_or_lt x b
    rintro (h1 | h2)
    . exact ⟨ h1.1, by linarith ⟩
    exact ⟨ by linarith, h2.2 ⟩
  simp [length, BoundedInterval.a, BoundedInterval.b,
        show a ≤ b by linarith, show b ≤ c by linarith, show a ≤ c by linarith]

theorem BoundedInterval.join_Ioc_Ioo {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ioo a c).joins (Ioc a b) (Ioo b c) := by
  refine ⟨ ?_, ?_, ?_ ⟩
  . rw [Set.eq_empty_iff_forall_notMem]; intros; simp; intros; linarith
  . ext x; simp; constructor
    . intro ⟨ h1, h2 ⟩; simp [h1, h2]; exact le_or_lt x b
    rintro (h1 | h2)
    . exact ⟨ h1.1, by linarith ⟩
    exact ⟨ by linarith, h2.2 ⟩
  simp [length, BoundedInterval.a, BoundedInterval.b,
        show a ≤ b by linarith, show b ≤ c by linarith, show a ≤ c by linarith]

theorem BoundedInterval.join_Ico_Icc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins (Ico a b) (Icc b c) := by
  refine ⟨ ?_, ?_, ?_ ⟩
  . rw [Set.eq_empty_iff_forall_notMem]; intros; simp; intros; linarith
  . ext x; simp; constructor
    . intro ⟨ h1, h2 ⟩; simp [h1, h2]; exact lt_or_le x b
    rintro (h1 | h2)
    . exact ⟨ h1.1, by linarith ⟩
    exact ⟨ by linarith, h2.2 ⟩
  simp [length, BoundedInterval.a, BoundedInterval.b,
        show a ≤ b by linarith, show b ≤ c by linarith, show a ≤ c by linarith]

theorem BoundedInterval.join_Ico_Ico {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ico a c).joins (Ico a b) (Ico b c) := by
  refine ⟨ ?_, ?_, ?_ ⟩
  . rw [Set.eq_empty_iff_forall_notMem]; intros; simp; intros; linarith
  . ext x; simp; constructor
    . intro ⟨ h1, h2 ⟩; simp [h1, h2]; exact lt_or_le x b
    rintro (h1 | h2)
    . exact ⟨ h1.1, by linarith ⟩
    exact ⟨ by linarith, h2.2 ⟩
  simp [length, BoundedInterval.a, BoundedInterval.b,
        show a ≤ b by linarith, show b ≤ c by linarith, show a ≤ c by linarith]

theorem BoundedInterval.join_Ioo_Icc {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioc a c).joins (Ioo a b) (Icc b c) := by
  refine ⟨ ?_, ?_, ?_ ⟩
  . rw [Set.eq_empty_iff_forall_notMem]; intros; simp; intros; linarith
  . ext x; simp; constructor
    . intro ⟨ h1, h2 ⟩; simp [h1, h2]; exact lt_or_le x b
    rintro (h1 | h2)
    . exact ⟨ h1.1, by linarith ⟩
    exact ⟨ by linarith, h2.2 ⟩
  simp [length, BoundedInterval.a, BoundedInterval.b,
        show a ≤ b by linarith, show b ≤ c by linarith, show a ≤ c by linarith]

theorem BoundedInterval.join_Ioo_Ico {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioo a c).joins (Ioo a b) (Ico b c) := by
  refine ⟨ ?_, ?_, ?_ ⟩
  . rw [Set.eq_empty_iff_forall_notMem]; intros; simp; intros; linarith
  . ext x; simp; constructor
    . intro ⟨ h1, h2 ⟩; simp [h1, h2]; exact lt_or_le x b
    rintro (h1 | h2)
    . exact ⟨ h1.1, by linarith ⟩
    exact ⟨ by linarith, h2.2 ⟩
  simp [length, BoundedInterval.a, BoundedInterval.b,
        show a ≤ b by linarith, show b ≤ c by linarith, show a ≤ c by linarith]


@[ext]
structure Partition (I: BoundedInterval) where
  intervals : Finset BoundedInterval
  exists_unique (x:ℝ) (hx : x ∈ I) : ∃! J, J ∈ intervals ∧ x ∈ J
  contains (J : BoundedInterval) (hJ : J ∈ intervals) : J ⊆ I

#check Partition.mk

instance Partition.instMembership (I: BoundedInterval) : Membership BoundedInterval (Partition I) where
  mem P J := J ∈ P.intervals

instance Partition.instBot (I: BoundedInterval) : Bot (Partition I) where
  bot := {
    intervals := {I}
    exists_unique x hx := by apply ExistsUnique.intro I <;> simp [hx]
    contains J hJ := by simp at hJ; rw [hJ, subset_iff]
    }

@[simp]
theorem Partition.intervals_of_bot (I:BoundedInterval) : (⊥:Partition I).intervals = {I} := by
  rfl

noncomputable abbrev Partition.join {I J K:BoundedInterval} (P: Partition I) (Q: Partition J) (h: K.joins I J) : Partition K
:=
{
  intervals := P.intervals ∪ Q.intervals
  exists_unique x hx := by
    simp [mem_iff, h.2] at hx
    rcases hx with hx | hx
    . obtain ⟨ L, hLP, hxL ⟩ := (P.exists_unique x hx).exists
      apply ExistsUnique.intro L (by aesop)
      intro K ⟨hK, hxK⟩
      simp at hK; rcases hK with hKP | hKQ
      . exact (P.exists_unique x hx).unique ⟨ hKP, hxK ⟩ ⟨ hLP, hxL ⟩
      replace hxK := (BoundedInterval.subset_iff _ _).mp (Q.contains K hKQ) hxK
      have := congr(x ∈ $(h.1))
      simp [hx, hxK] at this
    obtain ⟨ L, hLQ, hxL ⟩ := (Q.exists_unique x hx).exists
    apply ExistsUnique.intro L (by aesop)
    intro K ⟨hK, hxK⟩
    simp at hK; rcases hK with hKP | hKQ
    . replace hxK := (BoundedInterval.subset_iff _ _).mp (P.contains K hKP) hxK
      have := congr(x ∈ $(h.1))
      simp [hx, hxK] at this
    exact (Q.exists_unique x hx).unique ⟨ hKQ, hxK ⟩ ⟨ hLQ, hxL ⟩
  contains L hL := by
    simp at hL; rcases hL with hLP | hLQ
    . apply (P.contains L hLP).trans
      simp [h, subset_iff]
    apply (Q.contains L hLQ).trans
    simp [h, subset_iff]
}

@[simp]
theorem Partition.intervals_of_join {I J K:BoundedInterval} {h:K.joins I J} (P: Partition I) (Q: Partition J) : (P.join Q h).intervals = P.intervals ∪ Q.intervals := by
  simp [Partition.join, dif_pos h]

noncomputable abbrev Partition.add_empty {I:BoundedInterval} (P: Partition I) : Partition I := {
  intervals := P.intervals ∪ {∅}
  exists_unique x hx := by
    obtain ⟨ J, hJP, hxJ ⟩ := (P.exists_unique x hx).exists
    apply ExistsUnique.intro J (by aesop)
    intro K ⟨ hK, hxK ⟩
    simp at hK; rcases hK with hK | rfl
    . exact (P.exists_unique x hx).unique ⟨ hK, hxK ⟩ ⟨ hJP, hxJ ⟩
    simp [mem_iff] at hxK
  contains L hL := by
    simp at hL; rcases hL with hL | rfl
    . exact P.contains L hL
    simp [subset_iff]
}

open Classical in
noncomputable abbrev Partition.remove_empty {I:BoundedInterval} (P: Partition I) : Partition I := {
  intervals := P.intervals.filter (fun J ↦ (J:Set ℝ).Nonempty)
  exists_unique x hx := by
    obtain ⟨ J, hJP, hxJ ⟩ := (P.exists_unique x hx).exists
    apply ExistsUnique.intro J (by
      simp [hxJ, hJP]; simp [mem_iff] at hxJ; exact Set.nonempty_of_mem hxJ )
    intro K ⟨ hK, hxK ⟩; simp at hK
    exact (P.exists_unique x hx).unique ⟨ hK.1, hxK ⟩ ⟨ hJP, hxJ ⟩
  contains L hL := by
    simp at hL; exact P.contains L hL.1
}

@[simp]
theorem Partition.intervals_of_add_empty (I: BoundedInterval) (P: Partition I) : (P.add_empty).intervals = P.intervals ∪ {∅} := by
  simp [Partition.add_empty, Finset.union_empty]

example : ∃ P:Partition (Icc 1 8),
  P.intervals = {Icc 1 1, Ioo 1 3, Ico 3 5,
                 Icc 5 5, Ioc 5 8, ∅} := by
  set P1 : Partition (Icc 1 1) := ⊥
  set P2 : Partition (Ico 1 3) := P1.join (⊥:Partition (Ioo 1 3))
                                  (BoundedInterval.join_Icc_Ioo (by norm_num) (by norm_num) )
  set P3 : Partition (Ico 1 5) := P2.join (⊥:Partition (Ico 3 5))
                                  (BoundedInterval.join_Ico_Ico (by norm_num) (by norm_num) )
  set P4 : Partition (Icc 1 5) := P3.join (⊥:Partition (Icc 5 5))
                                  (BoundedInterval.join_Ico_Icc (by norm_num) (by norm_num) )
  set P5 : Partition (Icc 1 8) := P4.join (⊥:Partition (Ioc 5 8))
                                  (BoundedInterval.join_Icc_Ioc (by norm_num) (by norm_num) )
  use P5.add_empty
  simp [P5, P4, P3, P2, P1]
  aesop

example : ∃ P:Partition (Icc 1 8),
  P.intervals = {Icc 1 1, Ioo 1 3, Ico 3 5,
                 Icc 5 5, Ioc 5 8} := by
  sorry

example : ¬ ∃ P:Partition (Icc 1 5),
  P.intervals = {Icc 1 4, Icc 3 5} := by
  sorry

example : ¬ ∃ P:Partition (Ioo 1 5),
  P.intervals = {Ioo 1 3, Ioo 3 5} := by
  sorry

example : ¬ ∃ P:Partition (Ioo 1 5),
  P.intervals = {Ioo 0 3, Ico 3 5} := by
  sorry


/-- Exercise 11.1.3.  The exercise only claims c ≤ b, but the stronger claim c < b is true and useful. -/
theorem Partition.exist_right {I: BoundedInterval} (hI: I.a < I.b) (hI': I.b ∉ I)
  {P: Partition I}
  : ∃ c ∈ Set.Ico I.a I.b, Ioo c I.b ∈ P ∨ Ico c I.b ∈ P := by
  sorry

/-- Theorem 11.1.13 (Length is finitely additive).
Due to the excessive case analysis, `simp only` is used in place of `simp` in some places
to speed up elaboration. -/
theorem Partition.sum_of_length  (I: BoundedInterval) (P: Partition I) :
  ∑ J ∈ P.intervals, |J|ₗ = |I|ₗ := by
  -- This proof is written to follow the structure of the original text.
  generalize hcard: P.intervals.card = n
  revert I; induction' n with n hn <;> intro I P hcard
  . rw [Finset.card_eq_zero] at hcard
    have : (I:Set ℝ) = ∅ := by
      sorry
    replace this := length_of_empty this
    simp only [hcard, Finset.sum_empty, this]
  -- the proof in the book treats the n=1 case separately, but this is unnecessary
  by_cases h : Subsingleton (I:Set ℝ)
  . have (J: BoundedInterval) (hJ: J ∈ P) : Subsingleton (J:Set ℝ) := by
      sorry
    simp_rw [length_of_subsingleton] at h this
    simp only [h]
    apply Finset.sum_eq_zero this
  simp only [length_of_subsingleton, length, sup_eq_right, tsub_le_iff_right, zero_add, not_le] at h
  have : ∃ K L : BoundedInterval, K ∈ P ∧ I.joins L K := by
    by_cases hI' : I.b ∈ I
    . obtain ⟨ K, hK, hbK ⟩ := (P.exists_unique I.b hI').exists
      have hKI : K ⊆ I := P.contains K hK
      by_cases hsub : Subsingleton (K:Set ℝ)
      . simp_all [mem_iff, Set.subsingleton_coe]
        replace hbK := Set.Subsingleton.eq_singleton_of_mem hsub hbK
        have : K = Icc (I.b) (I.b) := by
          sorry
        subst this
        cases I with
        | Ioo a b => simp [mem_iff, Set.mem_Ioo, lt_self_iff_false, and_false] at hI'
        | Icc a b => use (Icc b b), hK, Ico a b
                     exact join_Ico_Icc (le_of_lt h) (le_refl _)
        | Ioc a b => use (Icc b b), hK, Ioo a b
                     exact join_Ioo_Icc h (le_refl _)
        | Ico a b => simp [mem_iff, Set.mem_Ico, lt_self_iff_false, and_false] at hI'
      simp only [length_of_subsingleton, sup_eq_right, tsub_le_iff_right, zero_add, not_le] at hsub
      have hKI' := (K.Ioo_subset.trans hKI).trans I.subset_Icc
      simp only [subset_iff] at hKI'
      have hKb : K.b = I.b := by
        rw [le_antisymm_iff]
        constructor
        . replace hKI' := csSup_le_csSup bddAbove_Icc ?_ hKI'
          . simp_all [csSup_Ioo hsub, csSup_Icc (le_of_lt h)]
          simp [Set.nonempty_Ioo, hsub]
        have := K.subset_Icc _ hbK
        simp only [mem_iff, Set.mem_Icc] at this
        exact this.2
      have hKA : I.a ≤ K.a := by
        replace hKI' := csInf_le_csInf bddBelow_Icc ?_ hKI'
        . simp_all [csInf_Icc (le_of_lt h), csInf_Ioo]
        simp [Set.nonempty_Ioo, hsub]
      cases I with
      | Ioo a b => simp [mem_iff, Set.mem_Ioo, lt_self_iff_false, and_false] at hI'
      | Icc a b =>
        cases K with
        | Ioo c b' =>
          simp [mem_iff, subset_iff, BoundedInterval.a, BoundedInterval.b, Set.mem_Icc, Set.mem_Ioo] at *
          linarith
        | Icc c b' =>
          use Icc c b', Ico a c, hK
          simp [BoundedInterval.b] at hKb; subst hKb
          exact join_Ico_Icc hKA (by linarith)
        | Ioc c b' =>
          use Ioc c b', Icc a c, hK
          simp [BoundedInterval.b] at hKb; subst hKb
          exact join_Icc_Ioc hKA (by linarith)
        | Ico c b' => simp [BoundedInterval.a, BoundedInterval.b, mem_iff, Set.mem_Icc,
          le_refl, and_true, Set.mem_Ico, subset_iff] at *; linarith
      | Ioc a b =>
        cases K with
        | Ioo c b' => simp_all [mem_iff, subset_iff]
        | Icc c b' =>
          use Icc c b', Ioo a c, hK
          simp [BoundedInterval.b] at hKb; subst hKb
          simp [subset_iff] at hKI
          have : c ∈ Set.Icc c b' := by simp; linarith
          replace this := hKI this; simp at this
          exact join_Ioo_Icc (by linarith) (by linarith)
        | Ioc c b' =>
          use Ioc c b', Ioc a c, hK
          simp [BoundedInterval.b] at hKb; subst hKb
          exact join_Ioc_Ioc hKA (by linarith)
        | Ico c b' =>
          simp [mem_iff, subset_iff, BoundedInterval.a, BoundedInterval.b, Set.mem_Ioc, Set.mem_Ico] at *; linarith
      | Ico a b => simp [mem_iff, Set.mem_Ico, lt_self_iff_false, and_false] at hI'
    obtain ⟨ c, hc, hK ⟩ := P.exist_right h hI'
    cases I with
    | Ioo a b =>
      rcases hK with hK | hK
      . simp_all [mem_iff, subset_iff, BoundedInterval.a, BoundedInterval.b]
        use Ioo c b, hK, Ioc a c
        exact join_Ioc_Ioo (hc.1) (hc.2)
      simp_all [mem_iff, subset_iff, BoundedInterval.a, BoundedInterval.b]
      use Ico c b, hK, Ioo a c
      replace hK := P.contains _ hK
      simp [subset_iff] at hK
      have : c ∈ Set.Ico c b := by simp; linarith
      replace this := hK this; simp at this
      exact join_Ioo_Ico (by linarith) (by linarith)
    | Icc a b => simp [mem_iff, subset_iff, BoundedInterval.a, BoundedInterval.b] at hI' h; linarith
    | Ioc a b => simp [mem_iff, subset_iff, BoundedInterval.a, BoundedInterval.b] at hI' h; linarith
    | Ico a b =>
      rcases hK with hK | hK
      . simp_all [mem_iff, subset_iff, BoundedInterval.a, BoundedInterval.b]
        use Ioo c b, hK, Icc a c
        exact join_Icc_Ioo (hc.1) (hc.2)
      simp_all [mem_iff, subset_iff, BoundedInterval.a, BoundedInterval.b]
      use Ico c b, hK, Ico a c
      exact join_Ico_Ico (by linarith) (by linarith)
  obtain ⟨ K, L, hK, ⟨ h1, h2, h3 ⟩ ⟩ := this
  have : ∃ P' : Partition L, P'.intervals = P.intervals.erase K := by
    sorry
  obtain ⟨ P', hP' ⟩ := this
  rw [h3, ←Finset.add_sum_erase _ _ hK, ←hP', add_comm]
  congr
  apply hn _ _ _
  simp only [hP', Finset.card_erase_of_mem hK, hcard, add_tsub_cancel_right]

/-- Definition 11.1.14 (Finer and coarser partitions) -/
instance Partition.instLE (I: BoundedInterval) : LE (Partition I) where
  le P P' := ∀ J ∈ P'.intervals, ∃ K ∈ P, J ⊆ K

instance Partition.instPreOrder (I: BoundedInterval) : Preorder (Partition I) where
  le_refl P := by
    sorry
  le_trans P P' P'' hP hP' := by
    sorry

instance Partition.instOrderBot (I: BoundedInterval) : OrderBot (Partition I) where
  bot_le := by
    sorry

/-- Example 11.1.15 -/
example : ∃ P P' : Partition (Icc 1 4),
  P.intervals = {Ico 1 2, Icc 2 2, Ioo 2 3,
                 Icc 3 4} ∧
  P'.intervals = {Icc 1 2, Ioc 2 4} ∧
  P' ≤ P := by
  sorry

/-- Definition 11.1.16 (Common refinement)-/
noncomputable instance Partition.instMax (I: BoundedInterval) : Max (Partition I) where
  max P P' := {
    intervals := Finset.image₂ (fun J K ↦ J ∩ K) P.intervals P'.intervals
    exists_unique x hx := by
      obtain ⟨ J, ⟨ hJ1, hJ2⟩, hxJ ⟩ := P.exists_unique x hx
      obtain ⟨ K, ⟨ hK1, hK2⟩, hxK ⟩ := P'.exists_unique x hx
      simp [hx] at hxJ hxK
      apply ExistsUnique.intro (J ∩ K)
      . simp; exact ⟨ ⟨ J, hJ1, K, hK1, rfl ⟩, ⟨ hJ2, hK2 ⟩ ⟩
      simp; rintro L J' hJ' K' hK' rfl hx'; simp at hx'
      specialize hxJ J' hJ' hx'.1
      specialize hxK K' hK' hx'.2
      simp [hxJ, hxK]
    contains L hL := by
      simp at hL
      obtain ⟨ J, hJ, K, hK, rfl ⟩ := hL
      replace hJ := P.contains J hJ
      replace hK := P'.contains K hK
      simp [subset_iff] at hJ hK ⊢
      exact Set.inter_subset_left.trans hJ
    }


/-- Example 11.1.17 -/
example : ∃ P P' : Partition (Icc 1 4),
  P.intervals = {Ico 1 3, Icc 3 4} ∧
  P'.intervals = {Icc 1 2, Ioc 2 4} ∧
  (P' ⊔ P).intervals = {Icc 1 2, Ioo 2 3, Icc 3 4, ∅} := by
  sorry

/-- Lemma 11.1.8 / Exercise 11.1.4 -/
theorem BoundedInterval.le_max {I: BoundedInterval} (P P': Partition I) :
  P ≤ P ⊔ P' ∧ P' ≤ P ⊔ P' := by
  sorry

/-- Not from textbook: the reverse inclusion -/
theorem BoundedInterval.max_le_iff (I: BoundedInterval) {P P' P'': Partition I}
  {hP : P ≤ P''} {hP': P' ≤ P''} : P ⊔ P' ≤ P''  := by
  sorry


end Chapter11
