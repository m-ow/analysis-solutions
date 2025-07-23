import Mathlib.Tactic

/-!
# Analysis I, Appendix B.1: The decimal representation of natural numbers

Am implementation of the decimal representation of Mathlib's natural numbers `ℕ`.

This is separate from the way decimal numerals are already represenated in Mathlib via the `OfNat` typeclass.
-/

namespace AppendixB

/- The ten digits, together with the base 10 -/
example : 0 = Nat.zero := rfl
example : 1 = (0:Nat).succ := rfl
example : 2 = (1:Nat).succ := rfl
example : 3 = (2:Nat).succ := rfl
example : 4 = (3:Nat).succ := rfl
example : 5 = (4:Nat).succ := rfl
example : 6 = (5:Nat).succ := rfl
example : 7 = (6:Nat).succ := rfl
example : 8 = (7:Nat).succ := rfl
example : 9 = (8:Nat).succ := rfl
example : 10 = (9:Nat).succ := rfl

/-- Definition B.1.1 -/
def Digit := Fin 10

instance Digit.instZero : Zero Digit := ⟨0, by decide⟩
instance Digit.instOne : One Digit := ⟨1, by decide⟩
instance Digit.instTwo : OfNat Digit 2 := ⟨2, by decide⟩
instance Digit.instThree : OfNat Digit 3 := ⟨3, by decide⟩
instance Digit.instFour : OfNat Digit 4 := ⟨4, by decide⟩
instance Digit.instFive : OfNat Digit 5 := ⟨5, by decide⟩
instance Digit.instSix : OfNat Digit 6 := ⟨6, by decide⟩
instance Digit.instSeven : OfNat Digit 7 := ⟨7, by decide⟩
instance Digit.instEight : OfNat Digit 8 := ⟨8, by decide⟩
instance Digit.instNine : OfNat Digit 9 := ⟨9, by decide⟩

instance Digit.instFintype : Fintype Digit := Fin.fintype 10
instance Digit.instDecidableEq : DecidableEq Digit := instDecidableEqFin 10

instance Digit.instInhabited : Inhabited Digit := ⟨ 0 ⟩

@[coe]
abbrev Digit.toNat (d:Digit) : ℕ := d.val

instance Digit.instCoeNat : Coe Digit Nat where
  coe := toNat

theorem Digit.lt (d:Digit) : (d:ℕ) < 10 := d.isLt

abbrev Digit.mk {n:ℕ} (h: n < 10) : Digit := ⟨n, h⟩

@[simp]
theorem Digit.toNat_mk {n:ℕ} (h: n < 10) : (Digit.mk h:ℕ) = n := rfl

@[simp]
theorem Digit.inj (d d':Digit) : d = d' ↔ (d:ℕ) = d' := by
  constructor
  . intro h; rw [h]
  obtain ⟨ d, hd ⟩ := d
  obtain ⟨ d', hd' ⟩ := d'
  aesop

theorem Digit.mk_eq_iff (d:Digit) {n:ℕ} (h: n < 10) : d = mk h ↔ (d:ℕ) = n := by
  convert Digit.inj d (mk h)
#check (0:Digit)
#check (1:Digit)
#check (2:Digit)
#check (3:Digit)
#check (4:Digit)
#check (5:Digit)
#check (6:Digit)
#check (7:Digit)
#check (8:Digit)
#check (9:Digit)

theorem Digit.eq (n: Digit) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by
  fin_cases n <;> simp

/-- Definition B.1.2 -/
structure PosintDecimal where
  digits : List Digit
  nonempty : digits ≠ []
  nonzero : digits.head nonempty ≠ 0

theorem PosintDecimal.congr' {p q:PosintDecimal} (h: p.digits = q.digits) : p = q := by
  obtain ⟨ pd, _, _ ⟩ := p
  obtain ⟨ qd, _, _ ⟩ := q
  congr

theorem PosintDecimal.congr {p q:PosintDecimal} (h: p.digits.length = q.digits.length)
  (h': ∀ (n:ℕ) (h₁ : n < p.digits.length) (h₂: n < q.digits.length), p.digits.get ⟨ n, h₁ ⟩ = q.digits.get ⟨ n, h₂ ⟩) : p = q := by
  apply congr'
  rw [List.ext_get_iff]
  simp_all

abbrev PosintDecimal.head (p:PosintDecimal): Digit := p.digits.head p.nonempty

theorem PosintDecimal.head_ne_zero (p:PosintDecimal) : p.head ≠ 0 := p.nonzero

theorem PosintDecimal.head_ne_zero' (p:PosintDecimal) : (p.head:ℕ) ≠ 0 := by
  change (p.head:ℕ) ≠ (0:Digit).toNat
  by_contra!
  simp [Digit.toNat] at this
  exact head_ne_zero p this

theorem PosintDecimal.length_pos (p:PosintDecimal) : 0 < p.digits.length := by
  simp [List.length_pos_iff, p.nonempty]

/-- A slightly clunky way of creating decimals. -/
def PosintDecimal.mk' (head:Digit) (tail:List Digit) (h: head ≠ 0) : PosintDecimal := {
  digits := head :: tail
  nonempty := by aesop
  nonzero := h
}

-- the positive integer decimal 314
#check PosintDecimal.mk' 3 [1, 4] (by decide)

-- the positive integer decimal 3
#check PosintDecimal.mk' 3 [] (by decide)

-- the positive integer decimal 10
#check PosintDecimal.mk' 1 [0] (by decide)

/-- We are indexing digits in a decimal from left to right rather than from right to left, thus necessitating a reversal here. -/
@[coe]
def PosintDecimal.toNat (p:PosintDecimal) : Nat :=
  ∑ i:Fin p.digits.length, p.digits[p.digits.length - 1 - ↑i].toNat * 10 ^ (i:ℕ)

instance PosintDecimal.instCoeNat : Coe PosintDecimal Nat where
  coe := toNat

example : (PosintDecimal.mk' 3 [1, 4] (by decide):ℕ) = 314 := by decide

/-- Remark B.1.3 -/
@[simp]
theorem PosintDecimal.ten_eq_ten : (mk' 1 [0] (by decide):ℕ) = 10 := by
  simp [toNat, mk', Digit.toNat, List.reverse]

theorem PosintDecimal.digit_eq {d:Digit} (h: d ≠ 0) : (mk' d [] h:ℕ) = d := by
  simp [toNat, mk', List.reverse]

theorem PosintDecimal.pos (p:PosintDecimal) : 0 < (p:ℕ) := by
  simp [toNat]
  calc
    _ < (p.head:ℕ) * 10 ^ (p.digits.length - 1) := by
      have := p.head_ne_zero'
      positivity
    _ ≤ _ := by
      have := p.length_pos
      set a : Fin p.digits.length := ⟨ p.digits.length - 1, by omega ⟩
      convert Finset.single_le_sum _ (Finset.mem_univ a)
      . simp [a, head, List.head_eq_getElem]
      . infer_instance
      intros; positivity

/-- An operation implicit in the proof of Theorem B.1.5: -/
abbrev PosintDecimal.append (p:PosintDecimal) (d:Digit) : PosintDecimal :=
  mk' p.head (p.digits.tail ++ [d]) p.head_ne_zero

@[simp]
theorem PosintDecimal.append_toNat (p:PosintDecimal) (d:Digit) :
  (p.append d:ℕ) = d.toNat + 10 * p.toNat  := by
  simp [append, toNat, mk', Finset.mul_sum]
  rw [Fin.sum_univ_succAbove _ 0]
  congr 1
  . simp
  have := p.length_pos
  convert Fin.sum_congr' _ _ with i; swap; simp; omega
  simp
  trans p.digits[p.digits.length - 1 - (i:ℕ)].toNat * (10^(i:ℕ) * 10); swap; ring
  congr 2
  have : p.head :: (p.digits.tail ++ [d]) = p.digits ++ [d] := by
    rw [←List.cons_append, head, List.head_cons_tail]
  have hlen : p.digits.length - 1 - ↑i < (p.digits ++ [d]).length := by simp; omega
  calc
    _ = (p.digits ++ [d])[p.digits.length - 1 - ↑i] := by congr
    _ = _ := by apply List.getElem_append_left

theorem PosintDecimal.eq_append {p:PosintDecimal} (h: 2 ≤ p.digits.length) : ∃ (q:PosintDecimal) (d:Digit), p = q.append d := by
  use mk' p.head (p.digits.tail.dropLast) p.head_ne_zero
  set a := p.digits.getLast p.nonempty; use a
  apply congr'
  simp [mk', List.cons_append]
  rw [←List.head_cons_tail p.digits p.nonempty]
  congr 1
  convert (List.dropLast_append_getLast _).symm using 2; swap
  . simp [←List.length_pos_iff]; linarith
  simp [a]

/-- Theorem B.1.5 (Uniqueness and existence of decimal representations) -/
theorem PosintDecimal.exists_unique (n:ℕ) : n > 0 → ∃! p:PosintDecimal, (p:ℕ) = n := by
  -- this proof is written to follow the structure of the original text.
  apply Nat.case_strong_induction_on n _ _
  . simp
  -- note: the variable `m` in the text is referred to as `m+1` here.
  clear n; intro m hind _
  rcases lt_or_ge m 9 with hm | hm
  . apply ExistsUnique.intro (mk' (Digit.mk (show m+1 < 10 by linarith)) [] (by simp [Digit.mk]))
    . simp [mk', Digit.mk, toNat, Digit.toNat]
    intro d hd
    rcases lt_or_ge d.digits.length 2 with hdl | hdl
    . replace hdl : d.digits.length = 1 := by linarith [d.length_pos]
      have _subsing : Subsingleton (Fin d.digits.length) := by simp [Fin.subsingleton_iff_le_one, hdl]
      let zero : Fin d.digits.length := ⟨ 0, by linarith ⟩
      simp [toNat, hdl, Fintype.sum_subsingleton _ zero, zero, Digit.toNat] at hd
      apply congr
      . simp [hdl, mk']
      intro i hi₁ hi₂
      replace hi₁ : i = 0 := by linarith
      simp [hi₁, mk', Digit.mk, hd]
    have : d.toNat ≥ 10 := calc
      _ ≥ (d.head:ℕ) * 10^(d.digits.length-1) := by
        set a : Fin d.digits.length := ⟨ d.digits.length - 1, by omega ⟩
        convert Finset.single_le_sum _ (Finset.mem_univ a)
        . simp [a, head, List.head_eq_getElem]
        . infer_instance
        intros; positivity
      _ ≥ 1 * 10^(2-1) := by
        gcongr
        . have := d.head_ne_zero'; omega
        norm_num
      _ = 10 := by norm_num
    linarith
  have := Nat.mod_add_div (m+1) 10
  set s := (m+1)/10
  set r := (m+1) % 10
  have hr : r < 10 := by simp [r]; omega
  specialize hind s (by linarith) (by linarith)
  obtain ⟨ b, hb, huniq ⟩ := hind; simp at huniq
  apply ExistsUnique.intro (b.append (Digit.mk hr))
  . simp [←this, hb]
  intro a ha
  rcases lt_or_ge a.digits.length 2 with hal | hal
  . replace hal : a.digits.length = 1 := by linarith [a.length_pos]
    have _subsing : Subsingleton (Fin a.digits.length) := by simp [Fin.subsingleton_iff_le_one, hal]
    let zero : Fin a.digits.length := ⟨ 0, by linarith ⟩
    simp [toNat, hal, Fintype.sum_subsingleton _ zero, zero, Digit.toNat] at ha
    have : a.digits[0].val < 10 := Digit.lt a.digits[0]
    linarith
  obtain ⟨ b', b'₀, rfl ⟩ := eq_append hal
  simp [←this] at ha
  have : (b'₀:ℕ) < 10 := Digit.lt b'₀
  replace : (s:ℤ) = (b':ℕ) := by omega
  have hb'₀r: (b'₀:ℕ) = (r:ℤ) := by omega
  simp at this hb'₀r
  rw [←Digit.mk_eq_iff _ hr] at hb'₀r
  specialize huniq b' this.symm
  congr

@[simp]
theorem PosintDecimal.coe_inj (p q:PosintDecimal) : (p:ℕ) = (q:ℕ) ↔ p = q := by
  constructor <;> intro h
  . exact (exists_unique _ (q.pos)).unique h rfl
  rw [h]


inductive IntDecimal where
  | zero : IntDecimal
  | pos : PosintDecimal → IntDecimal
  | neg : PosintDecimal → IntDecimal

def IntDecimal.toInt : IntDecimal → Int
  | zero => 0
  | pos p => p.toNat
  | neg p => -p.toNat

instance IntDecimal.instCoeInt : Coe IntDecimal Int where
  coe := toInt

example : (IntDecimal.neg (PosintDecimal.mk' 3 [1, 4] (by decide)):ℤ) = -314 := by decide

theorem IntDecimal.Int_bij : Function.Bijective IntDecimal.toInt := by
  constructor
  . intro p q hpq
    cases p with
    | zero => cases q with
      | zero => rfl
      | pos q => simp [toInt] at hpq; linarith [q.pos]
      | neg q => simp [toInt] at hpq; linarith [q.pos]
    | pos p => cases q with
      | zero => simp [toInt] at hpq; linarith [p.pos]
      | pos q => simpa [toInt] using hpq
      | neg q => simp [toInt] at hpq; linarith [q.pos]
    | neg p => cases q with
      | zero => simp [toInt] at hpq; linarith [p.pos]
      | pos q => simp [toInt] at hpq; linarith [q.pos]
      | neg q => simpa [toInt] using hpq
  intro n
  rcases lt_trichotomy n 0 with h | rfl | h
  . generalize e: -n = m
    lift m to Nat using (by linarith)
    obtain ⟨ p, hp, _ ⟩ := PosintDecimal.exists_unique _ (show 0 < m by linarith)
    use neg p
    simp [toInt, hp, ←e]
  . use zero; simp [toInt]
  lift n to Nat using (le_of_lt h); simp at h
  obtain ⟨ p, hp, _ ⟩ := PosintDecimal.exists_unique _ h
  use pos p
  simp [toInt, hp]

abbrev PosintDecimal.digit (p:PosintDecimal) (i:ℕ) : Digit :=
  if h: i < p.digits.length then p.digits[i] else 0

abbrev PosintDecimal.carry (p q:PosintDecimal) : ℕ → ℕ := Nat.rec 0 (fun i ε ↦ if ((p.digit i:ℕ) + (q.digit i:ℕ) + ε) < 10 then 0 else 1)

theorem PosintDecimal.carry_zero (p q:PosintDecimal) : p.carry q 0 = 0 := by
  convert Nat.rec_zero _ _

theorem PosintDecimal.carry_succ (p q:PosintDecimal) (i:ℕ) : p.carry q (i+1) = if ((p.digit i:ℕ) + (q.digit i:ℕ) + p.carry q i < 10) then 0 else 1 :=
  Nat.rec_add_one 0 (fun i ε ↦ if ((p.digit i:ℕ) + (q.digit i:ℕ) + ε) < 10 then 0 else 1) i

abbrev PosintDecimal.sum_digit (p q:PosintDecimal) (i:ℕ) : ℕ :=
  if (p.digit i + q.digit i + (p.carry q) i < 10) then
    p.digit i + q.digit i + (p.carry q) i
  else
    p.digit i + q.digit i + (p.carry q) i - 10

/-- Exercise B.1.1 -/
theorem PosintDecimal.sum_digit_lt (p q:PosintDecimal) (i:ℕ) :
  p.sum_digit q i < 10 := by sorry

theorem PosintDecimal.sum_digit_top (p q:PosintDecimal) : ∃ l, p.sum_digit q l ≠ 0 ∧ ∀ i > l, p.sum_digit q l = 0 := by sorry

theorem PosintDecimal.sum_eq (p q:PosintDecimal) : ∃ (r:PosintDecimal) (i:ℕ), (r.digit i:ℕ) = p.sum_digit q i ∧ (r:ℕ) = p + q := by
  sorry
