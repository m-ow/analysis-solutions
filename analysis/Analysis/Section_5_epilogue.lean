import Mathlib.Tactic
import Analysis.Section_5_5

/-!
# Analysis I, Chapter 5 epilogue

In this (technical) epilogue, we show that the "Chapter 5" real numbers `Chapter5.Real` are isomorphic in various standard senses to the standard real numbers `ℝ`.  This we do by matching both structures with Dedekind cuts of the (Mathlib) rational numbers `ℚ`.

From this point onwards, `Chapter5.Real` will be deprecated, and we will use the standard real numbers `ℝ` instead.  In particular, one should use the full Mathlib API for `ℝ` for all subsequent chapters, in lieu of the `Chapter5.Real` API.

Filling the sorries here requires both the Chapter5.Real API and the Mathlib API for the standard natural numbers `ℝ`.  As such, they are excellent exercises to prepare you for the aforementioned transition.

--/

namespace Chapter5

structure DedekindCut where
  E : Set ℚ
  nonempty : E.Nonempty
  bounded : BddAbove E
  lower: IsLowerSet E

abbrev Real.toSet_Rat (x:Real) : Set ℚ := { q | (q:Real) ≤ x }

lemma Real.toSet_Rat_nonempty (x:Real) : x.toSet_Rat.Nonempty := by sorry

lemma Real.toSet_Rat_bounded (x:Real) : BddAbove x.toSet_Rat := by sorry

lemma Real.toSet_Rat_lower (x:Real) : IsLowerSet x.toSet_Rat := by sorry

abbrev Real.toCut (x:Real) : DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
 }

abbrev DedekindCut.toSet_Real (c: DedekindCut) : Set Real := (fun (q:ℚ) ↦ (q:Real)) '' c.E

lemma DedekindCut.toSet_Real_nonempty (c: DedekindCut) : c.toSet_Real.Nonempty := by sorry

lemma DedekindCut.toSet_Real_bounded (c: DedekindCut) : BddAbove c.toSet_Real := by sorry

noncomputable abbrev DedekindCut.toReal (c: DedekindCut) : Real := sSup c.toSet_Real

lemma DedekindCut.toReal_isLUB (c: DedekindCut) : IsLUB c.toSet_Real c.toReal := ExtendedReal.sSup_of_bounded c.toSet_Real_nonempty c.toSet_Real_bounded

noncomputable abbrev Real.equivCut : Real ≃ DedekindCut where
  toFun := Real.toCut
  invFun := DedekindCut.toReal
  left_inv x := by
    sorry
  right_inv c := by
    sorry

end Chapter5

/-- Now to develop analogous results for the Mathlib reals. -/

abbrev Real.toSet_Rat (x:ℝ) : Set ℚ := { q | (q:ℝ) ≤ x }

lemma Real.toSet_Rat_nonempty (x:ℝ) : x.toSet_Rat.Nonempty := by sorry

lemma Real.toSet_Rat_bounded (x:ℝ) : BddAbove x.toSet_Rat := by sorry

lemma Real.toSet_Rat_lower (x:ℝ) : IsLowerSet x.toSet_Rat := by sorry

abbrev Real.toCut (x:ℝ) : Chapter5.DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
 }

namespace Chapter5

abbrev DedekindCut.toSet_R (c: DedekindCut) : Set ℝ := (fun (q:ℚ) ↦ (q:ℝ)) '' c.E

lemma DedekindCut.toSet_R_nonempty (c: DedekindCut) : c.toSet_R.Nonempty := by sorry

lemma DedekindCut.toSet_R_bounded (c: DedekindCut) : BddAbove c.toSet_R := by sorry

noncomputable abbrev DedekindCut.toR (c: DedekindCut) : ℝ := sSup c.toSet_R

lemma DedekindCut.toR_isLUB (c: DedekindCut) : IsLUB c.toSet_R c.toR := isLUB_csSup c.toSet_R_nonempty c.toSet_R_bounded

end Chapter5

noncomputable abbrev Real.equivCut : ℝ ≃ Chapter5.DedekindCut where
  toFun := _root_.Real.toCut
  invFun := Chapter5.DedekindCut.toR
  left_inv x := by
    sorry
  right_inv c := by
    sorry

namespace Chapter5

/-- The isomorphism between the Chapter 5 reals and the Mathlib reals. -/
noncomputable abbrev Real.equivR : Real ≃ ℝ := Real.equivCut.trans _root_.Real.equivCut.symm

lemma Real.equivR_iff (x : Real) (y : ℝ) : y = Real.equivR x ↔ y.toCut = x.toCut := by
  simp only [equivR, Equiv.trans_apply, ←Equiv.apply_eq_iff_eq_symm_apply]
  rfl

/-- The isomorphism preserves order -/
noncomputable abbrev Real.equivR_order : Real ≃o ℝ where
  toEquiv := equivR
  map_rel_iff' := by sorry

/-- The isomorphism preserves ring operations -/
noncomputable abbrev Real.equivR_ring : Real ≃+* ℝ where
  toEquiv := equivR
  map_add' := by sorry
  map_mul' := by sorry

end Chapter5
