import Mathlib.Tactic
import Analysis.Appendix_B_1

/-!
# Analysis I, Appendix B.2: The decimal representation of real numbers

Am implementation of the decimal representation of Mathlib's real numbers `ℝ`.

This is separate from the way decimal numerals are already represenated in Mathlib.  We also represent the integer part of the natural numbers just by `ℕ`, avoiding using the decimal representation from the
previous section, although we still retain the `Digit` class.
-/

namespace AppendixB

structure NNRealDecimal where
  intPart : ℕ
  fracPart : ℕ → Digit

#check NNRealDecimal.mk

@[coe]
noncomputable def NNRealDecimal.toNNReal (d:NNRealDecimal) : NNReal :=
  d.intPart + ∑' i, (d.fracPart i) * (10:NNReal) ^ (-i-1:ℝ)

noncomputable instance NNRealDecimal.instCoeNNReal : Coe NNRealDecimal NNReal where
  coe := toNNReal

/-- Exercise B.2.1 -/
theorem NNRealDecimal.toNNReal_conv (d:NNRealDecimal) :
  Summable fun i ↦ (d.fracPart i) * (10:NNReal) ^ (-i-1:ℝ) := by
  sorry

theorem NNRealDecimal.surj (x:NNReal) : ∃ d:NNRealDecimal, x = d := by
  -- This proof is written to follow the structure of the original text.
  by_cases h : x = 0
  . use mk 0 fun _ ↦ 0
    simp [h, toNNReal]
  let s : ℕ → ℕ := fun n ↦ ⌊ x * 10^n ⌋₊
  have hs (n:ℕ) : s n ≤ x * 10^n := Nat.floor_le (by positivity)
  have hs' (n:ℕ) : x * 10^n < s n + 1 := Nat.lt_floor_add_one _
  have hdigit (n:ℕ) : ∃ a:Digit, s (n+1) = 10 * s n + (a:ℕ) := by
    have hl : (10:NNReal) * s n < s (n+1) + 1 := calc
      _ ≤ 10 * (x * 10^n) := by gcongr; exact hs n
      _ = x * 10^(n+1) := by ring_nf
      _ < _ := hs' _
    have hu : s (n+1) < (10:NNReal) * s n + 10 := calc
      _ ≤ x * 10^(n+1) := hs (n+1)
      _ = 10 * (x * 10^n) := by ring_nf
      _ < 10 * (s n + 1) := by gcongr; exact hs' n
      _ = _ := by ring
    norm_cast at hl hu
    set d := s (n+1) - 10 * s n
    have hd : d < 10 := by omega
    have : s (n+1) = 10 * s n + d := by omega
    use Digit.mk hd
  set a : ℕ → Digit := fun n ↦ (hdigit n).choose
  have ha (n:ℕ) : s (n+1) = 10 * s n + (a n : ℕ) := (hdigit n).choose_spec
  set d := mk (s 0) a; use d
  have hsum (n:ℕ) : s n * (10:NNReal)^(-n:ℝ) = s 0 + ∑ i ∈ Finset.range n, a i * (10:NNReal)^(-i-1:ℝ) := by
    induction' n with n hn
    . simp
    rw [ha n]; calc
      _ = s n * (10:NNReal)^(-n:ℝ) + a n * 10^(-n-1:ℝ) := by
        simp [add_mul]; congr 1 <;> ring_nf
        rw [mul_assoc, ←NNReal.rpow_add_one (by norm_num)]; congr; ring
      _ = s 0 + (∑ i ∈ Finset.range n, a i * (10:NNReal)^(-i-1:ℝ) + a n * 10^(-n-1:ℝ)) := by
        rw [hn]; abel
      _ = _ := by congr; exact (Finset.sum_range_succ _ _).symm
  have := d.toNNReal_conv.tendsto_sum_tsum_nat
  replace := this.const_add (s 0:NNReal)
  convert_to Filter.Tendsto (fun n ↦ s n * (10:NNReal)^(-n:ℝ)) Filter.atTop (nhds (d:NNReal)) at this
  . ext n; rw [hsum n]
  apply tendsto_nhds_unique _ this
  apply Filter.Tendsto.squeeze (g := fun n:ℕ ↦ x - (10:NNReal)^(-n:ℝ)) (h := fun n ↦ x)
  . convert Filter.Tendsto.const_sub (c := 0) x _
    . simp
    convert NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (1/10:NNReal) < 1 by apply NNReal.div_lt_one_of_lt; norm_num) with n
    rw [←NNReal.rpow_natCast, one_div, NNReal.inv_rpow, NNReal.rpow_neg]
  . exact tendsto_const_nhds
  . intro n; simp; calc
    _ = (x * 10^n) * (10:NNReal)^(-n:ℝ) := by
      rw [mul_assoc, ←NNReal.rpow_natCast, ←NNReal.rpow_add (by norm_num)]; simp
    _ ≤ ((s n:NNReal) + 1)*(10:NNReal)^(-n:ℝ) := by gcongr; exact le_of_lt (hs' n)
    _ = _ := by ring
  intro n; simp; calc
    _ ≤ (x * 10^n) * (10:NNReal)^(-n:ℝ) := by gcongr; exact hs n
    _ = x := by rw [mul_assoc, ←NNReal.rpow_natCast, ←NNReal.rpow_add (by norm_num)]; simp

/-- Proposition B.2.2 -/
theorem NNRealDecimal.not_inj : (1:NNReal) = (mk 1 fun _ ↦ 0) ∧ (1:NNReal) = (mk 0 fun _ ↦ 9) := by
  -- This proof is written to follow the structure of the original text.
  simp [toNNReal]
  have := (mk 0 fun _ ↦ 9).toNNReal_conv.tendsto_sum_tsum_nat
  simp at this
  apply tendsto_nhds_unique _ this
  convert_to Filter.Tendsto (fun n:ℕ ↦ 1 - (10:NNReal)^(-n:ℝ)) Filter.atTop (nhds 1) using 2 with n
  . induction' n with n hn
    . simp
    rw [Finset.sum_range_succ, hn, Nat.cast_add, Nat.cast_one, neg_add']
    have : (10:NNReal)^(-n:ℝ) = 10^(-n-1:ℝ) * 10 := by
      rw [←NNReal.rpow_add_one (by norm_num)]; simp
    have hnine : ((9:Digit):ℕ) = 9 := rfl
    simp [this, hnine, ←NNReal.coe_inj]
    rw [NNReal.coe_sub, NNReal.coe_sub]
    . simp; linarith
    . apply NNReal.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    rw [←NNReal.rpow_add_one (by norm_num)]
    apply NNReal.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  convert Filter.Tendsto.const_sub (f := fun n:ℕ ↦ (10:NNReal)^(-n:ℝ)) (c := 0) 1 _; simp
  convert NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (1/10:NNReal) < 1 by bound) with n
  rw [←NNReal.rpow_natCast, one_div, NNReal.inv_rpow, NNReal.rpow_neg]

inductive RealDecimal where
  | pos : NNRealDecimal → RealDecimal
  | neg : NNRealDecimal → RealDecimal

noncomputable instance RealDecimal.instCoeReal : Coe RealDecimal ℝ where
  coe := fun d ↦ match d with
    | RealDecimal.pos d => d.toNNReal
    | RealDecimal.neg d => -(d.toNNReal:ℝ)

theorem RealDecimal.surj (x:ℝ) : ∃ d:RealDecimal, x = d := by
  rcases le_or_gt 0 x with h | h
  . obtain ⟨ d, hd ⟩ := NNRealDecimal.surj (x.toNNReal)
    use pos d
    simp [←hd, h]
  . obtain ⟨ d, hd ⟩ := NNRealDecimal.surj ((-x).toNNReal)
    use neg d
    replace h : 0 ≤ -x := by linarith
    simp [←hd, h]

/-- Exercise B.2.2 -/
theorem RealDecimal.not_inj_one (d: RealDecimal) : (d:ℝ) = 1 ↔ (d = pos (NNRealDecimal.mk 1 fun _ ↦ 0) ∨ d = pos (NNRealDecimal.mk 0 fun _ ↦ 9)) := by
  sorry

/-- Exercise B.2.3 -/
abbrev TerminatingDecimal (x:ℝ) : Prop := ∃ (n:ℤ) (m:ℕ), x = n / (10:ℝ)^m

theorem RealDecimal.not_inj_terminating {x:ℝ} (hx: TerminatingDecimal x) : ∃ d₁ d₂:RealDecimal, d₁ ≠ d₂ ∧ ∀ d: RealDecimal, d = x ↔ d = d₁ ∨ d = d₂ := by sorry

theorem RealDecimal.inj_nonterminating {x:ℝ} (hx: ¬TerminatingDecimal x) : ∃! d:RealDecimal, d = x := by sorry

/-- Exercise B.2.4.  This is Corollary 8.3.4, but the intent is to rewrite the proof using the decimal system. -/
example : Uncountable ℝ := by sorry


end AppendixB
