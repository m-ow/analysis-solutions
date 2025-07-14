import Mathlib.Tactic
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.SetTheory.ZFC.Basic
import Analysis.Section_3_1

/-!
# Analysis I, Chapter 3 epilogue

In this epilogue we show that the `ZFSet` type in Mathlib (derived as a quotient from the
`PSet` type) can be used to create models of the `SetTheory' class studied in this chapter, so long as we work in a universe of level at
least 1.  The constructions here are due to Edward van de Meent; see
https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Can.20this.20proof.20related.20to.20Set.20replacement.20be.20shorter.3F/near/527305173
-/

universe u

/-- A preliminary lemma about `PSet`: their natural numbers are ordered by membership. -/
lemma PSet.ofNat_mem_ofNat_of_lt (m n : ℕ) : n < m → ofNat n ∈ ofNat m := by
  intro h
  induction h with
  | refl =>
    rw [ofNat]
    exact mem_insert (ofNat n) (ofNat n)
  | step hm ih =>
    rw [ofNat]
    exact mem_insert_of_mem (ofNat _) ih

lemma PSet.mem_ofNat_iff (n m : ℕ) : ofNat n ∈ ofNat m ↔ n < m := by
  constructor
  · contrapose!
    rw [le_iff_lt_or_eq]
    rintro (h|rfl)
    · exact mem_asymm (ofNat_mem_ofNat_of_lt _ _ h)
    · exact mem_irrefl _
  · exact ofNat_mem_ofNat_of_lt m n

/-- Another preliminary lemma: Natural numbers in `PSet` can only be equivalent
if they are equal. -/
lemma PSet.eq_of_ofNat_equiv_ofNat (n m : ℕ): (ofNat.{u} n).Equiv (ofNat.{u} m) → n = m := by
  wlog hmn : m ≤ n generalizing n m
  · intro heq
    rw [this m n (Nat.le_of_not_ge hmn) heq.symm]
  intro h
  rw [@PSet.Equiv.eq (ofNat.{u} n) (ofNat m), Set.ext_iff] at h
  have : n ≤ m := by
    specialize h (ofNat m)
    simpa [mem_irrefl _, mem_ofNat_iff] using h
  exact Nat.le_antisymm this hmn

/-- Using the above lemmas, we can create a bijection between `ZFSet.omega` and
the natural numbers. -/
noncomputable def ZFSet.nat_equiv : ℕ ≃ omega.{u} := Equiv.ofBijective (fun n => ⟨mk (PSet.ofNat.{u} n),mk_mem_iff.mpr (PSet.Mem.mk _ (ULift.up n))⟩) (by
  constructor
  · intro n m
    simp only [Subtype.mk.injEq, eq]
    exact fun a => PSet.eq_of_ofNat_equiv_ofNat n m a
  · rintro ⟨x,hx⟩
    rw [← mk_out x, omega, mk_mem_iff, PSet.omega] at hx
    obtain ⟨n,hn⟩ := hx
    simp only [PSet.mk_type] at n
    use n.down
    simp only [Subtype.mk.injEq]
    simp only [PSet.mk_func] at hn
    rw [← mk_out x]
    exact eq.mpr (id (PSet.Equiv.symm hn))
  )

open Classical in
/-- Show that ZFSet obeys the `Chapter3.SetTheory` axioms.  Most of these axioms were
essentially already established in Mathlib and are relatively routine to transfer over;
the equivalence of `ZF.omega` and `Nat` being the trickiest one in content (and the
power set axiom also requiring some technical manipulation). -/
noncomputable instance : Chapter3.SetTheory.{u + 1,u + 1} where
  Set := ZFSet
  Object := ZFSet
  set_to_object := { toFun := fun ⦃a₁⦄ => a₁, inj' := fun _ _ h => h}
  mem o s := o ∈ s
  extensionality X Y := ZFSet.ext
  emptyset := ∅
  emptyset_mem x := ZFSet.notMem_empty x
  singleton x := {x}
  singleton_axiom _ _ := ZFSet.mem_singleton
  union_pair x y := x ∪ y
  union_pair_axiom X Y x := ZFSet.mem_union
  specify A P := ZFSet.sep (fun s => (h : s ∈ A) → P ⟨s,h⟩) A
  specification_axiom := by simp +contextual
  replace A P hp := @(A.sep (fun s => (hs : s ∈ A) → ∃ z, P ⟨s,hs⟩ z)).image (fun s =>
    if h : ∃ (hs : s ∈ A), ∃ z, P ⟨s,hs⟩ z then h.choose_spec.choose else ∅) (Classical.allZFSetDefinable _)
  replacement_axiom A P hp s := by
    simp only [Fin.isValue, ZFSet.mem_image, ZFSet.mem_sep, Subtype.exists]
    constructor
    · rintro ⟨z,⟨hzA,hz⟩, hz'⟩
      use z, hzA
      rw [dif_pos (⟨hzA, hz hzA⟩)] at hz'
      rw [← hz']
      apply Exists.choose_spec
    · intro ⟨z,hzA,hz'⟩
      use z,⟨hzA,fun _ => ⟨s,hz'⟩⟩
      apply hp ⟨z,hzA⟩
      rw [dif_pos ⟨hzA,⟨s,hz'⟩⟩]
      use Exists.choose_spec _
  nat := ZFSet.omega
  nat_equiv := ZFSet.nat_equiv
  regularity_axiom A := by
    simp only [Function.Embedding.coeFn_mk, not_exists, not_and, forall_eq', forall_exists_index]
    intro x hx
    obtain ⟨y,hy⟩ := ZFSet.regularity A (by
      rintro rfl
      exact ZFSet.notMem_empty x hx)
    use y, hy.left
    intro z hzA hzy
    have : z ∈ A ∩ y := ZFSet.mem_inter.mpr ⟨hzA,hzy⟩
    simp [hy.right] at this
  pow X Y := ZFSet.funs Y X
  function_to_object X Y := {
    toFun f := (@ZFSet.map (fun s => if h : s ∈ X then f ⟨s,h⟩ else ∅) (Classical.allZFSetDefinable _) X)
    inj' := by
      intro x y h
      ext1 ⟨s,hs⟩
      simp only at h
      simp_rw [ZFSet.ext_iff, ZFSet.mem_map] at h
      specialize h (s.pair (x ⟨s,hs⟩).val)
      simp only [ZFSet.pair_inj, existsAndEq, hs, ↓reduceDIte, and_self, SetLike.coe_eq_coe,
        true_and, true_iff] at h
      rw [← h] }
  power_set_axiom X Y F := by
    simp only [Fin.isValue, Function.Embedding.coeFn_mk]
    rw [ZFSet.mem_funs, ZFSet.IsFunc]
    constructor
    · intro ⟨hsub,huniq⟩
      use (fun x => ⟨(huniq x x.property).exists.choose,(ZFSet.pair_mem_prod.mp (hsub (huniq x x.property).exists.choose_spec)).right⟩)
      ext z
      simp only [Fin.isValue, ZFSet.mem_map]
      constructor
      · rintro ⟨y,hy,rfl⟩
        rw [dif_pos hy]
        exact (huniq y hy).exists.choose_spec
      · intro hf
        specialize hsub hf
        rw [ZFSet.mem_prod] at hsub
        obtain ⟨y,hy,x,hx,rfl⟩ := hsub
        use y,hy
        rw [dif_pos hy,(huniq y hy).unique (huniq y hy).exists.choose_spec hf]
    · rintro ⟨f,rfl⟩
      simp only [Fin.isValue, ZFSet.mem_map, ZFSet.pair_inj, existsAndEq, true_and]
      constructor
      · intro s hs
        simp only [Fin.isValue, ZFSet.mem_map] at hs
        obtain ⟨y,hy,rfl⟩ := hs
        rw [dif_pos hy, ZFSet.pair_mem_prod]
        use hy
        exact (f ⟨y,hy⟩).property
      · intro y hy
        rw [dif_pos hy]
        exact ExistsUnique.intro _ ⟨hy, rfl⟩ (by simp)
  union := ZFSet.sUnion
  union_axiom A x := by
    simp only [ZFSet.mem_sUnion, Function.Embedding.coeFn_mk, And.comm]
