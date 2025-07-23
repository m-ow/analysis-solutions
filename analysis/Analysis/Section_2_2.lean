import Mathlib.Tactic
import Analysis.Section_2_1

/-!
# Analysis I, Section 2.2: Addition

This file is a translation of Section 2.2 of Analysis I to Lean 4.  All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of addition and order for the "Chapter 2" natural numbers, `Chapter2.Nat`.
- Establishment of basic properties of addition and order.

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of
`Chapter2.Nat` "by hand" for pedagogical purposes.
-/

namespace Chapter2

/-- Definition 2.2.1. (Addition of natural numbers).
    Compare with Mathlib's `Nat.add` -/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

/-- This instance allows for the `+` notation to be used for natural number addition. -/
instance Nat.instAdd : Add Nat where
  add := add

/-- Compare with Mathlib's `Nat.zero_add`. -/
@[simp]
theorem Nat.zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

/-- Compare with Mathlib's `Nat.succ_add`. -/
theorem Nat.succ_add (n m: Nat) : n++ + m = (n+m)++ := by rfl

/-- Compare with Mathlib's `Nat.one_add`. -/
theorem Nat.one_add (m:Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl, succ_add, zero_add]

theorem Nat.two_add (m:Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl, succ_add, one_add]

example : (2:Nat) + 3 = 5 := by
  rw [Nat.two_add, show 3++=4 from rfl, show 4++=5 from rfl]

-- The sum of two natural numbers is again a natural number.
#check (fun (n m:Nat) ↦ n + m)

/-- Lemma 2.2.2 (n + 0 = n). Compare with Mathlib's `Nat.add_zero`. -/
@[simp]
lemma Nat.add_zero (n:Nat) : n + 0 = n := by
  -- This proof is written to follow the structure of the original text.
  revert n; apply induction
  . exact zero_add 0
  intro n ih
  calc
    (n++) + 0 = (n + 0)++ := by rfl
    _ = n++ := by rw [ih]

/-- Lemma 2.2.3 (n+(m++) = (n+m)++). Compare with Mathlib's `Nat.add_succ`. -/
lemma Nat.add_succ (n m:Nat) : n + (m++) = (n + m)++ := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, zero_add]
  intro n ih
  rw [succ_add, ih]
  rw [succ_add]


/-- n++ = n + 1 (Why?). Compare with Mathlib's `Nat.succ_eq_add_one` -/
theorem Nat.succ_eq_add_one (n:Nat) : n++ = n + 1 := by
  revert n; apply induction
  . rfl
  intro n ih
  rw [succ_add, ih]

/-- Proposition 2.2.4 (Addition is commutative). Compare with Mathlib's `Nat.add_comm` -/
theorem Nat.add_comm (n m:Nat) : n + m = m + n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, add_zero]
  intro n ih
  rw [succ_add]
  rw [add_succ, ih]

/-- Proposition 2.2.5 (Addition is associative) / Exercise 2.2.1
    Compare with Mathlib's `Nat.add_assoc`. -/
theorem Nat.add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
  revert a; apply induction
  . rfl
  intro n ih
  rw [succ_add, succ_add, succ_add, ih]

/-- Proposition 2.2.6 (Cancellation law).
    Compare with Mathlib's `Nat.add_left_cancel`. -/
theorem Nat.add_left_cancel (a b c:Nat) (habc: a + b = a + c) : b = c := by
  -- This proof is written to follow the structure of the original text.
  revert a; apply induction
  . intro hbc
    rwa [zero_add, zero_add] at hbc
  intro a ih
  intro hbc
  rw [succ_add, succ_add] at hbc
  replace hbc := succ_cancel hbc
  exact ih hbc


/-- (Not from textbook) Nat can be given the structure of a commutative additive monoid.
This permits tactics such as `abel` to apply to the Chapter 2 natural numbers. -/
instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- This illustration of the `abel` tactic is not from the
    textbook. -/
example (a b c d:Nat) : (a+b)+(c+0+d) = (b+c)+(d+a) := by abel

/-- Definition 2.2.7 (Positive natural numbers).-/
def Nat.IsPos (n:Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n:Nat) : n.IsPos ↔ n ≠ 0 := by rfl

/-- Proposition 2.2.8 (positive plus natural number is positive).
    Compare with Mathlib's `Nat.add_pos_left`. -/
theorem Nat.add_pos_left {a:Nat} (b:Nat) (ha: a.IsPos) : (a + b).IsPos := by
  -- This proof is written to follow the structure of the original text.
  revert b; apply induction
  . rwa [add_zero]
  intro b hab
  rw [add_succ]
  have : (a+b)++ ≠ 0 := succ_ne _
  exact this

/-- Compare with Mathlib's `Nat.add_pos_right`. -/
theorem Nat.add_pos_right {a:Nat} (b:Nat) (ha: a.IsPos) : (b + a).IsPos := by
  rw [add_comm]
  exact add_pos_left _ ha

/-- Corollary 2.2.9 (if sum vanishes, then summands vanish).
    Compare with Mathlib's `Nat.add_eq_zero`. -/
theorem Nat.add_eq_zero (a b:Nat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h
  simp only [not_and_or, ←ne_eq] at h
  rcases h with ha | hb
  . rw [← isPos_iff] at ha
    have : (a + b).IsPos := add_pos_left _ ha
    contradiction
  rw [← isPos_iff] at hb
  have : (a + b).IsPos := add_pos_right _ hb
  contradiction

/-
The API in `Tools/ExistsUnique.Lean`, and the method `existsUnique_of_exists_of_unique` in
particular, may be useful for the next problem.  Also, the `obtain` tactic is
useful for extracting witnesses from existential statements; for instance, `obtain ⟨ x, hx ⟩ := h`
extracts a witness `x` and a proof `hx : P x` of the property from a hypothesis `h : ∃ x, P x`.
-/

#check existsUnique_of_exists_of_unique

/-- Lemma 2.2.10 (unique predecessor) / Exercise 2.2.2 -/
lemma Nat.uniq_succ_eq (a:Nat) (ha: a.isPos) : ∃! b, b++ = a := by
  revert a; apply induction
  . intro ha; contradiction
  intro n ih ha
  by_contra h
  simp at h

/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the `≤` operation on the natural numbers. -/
instance Nat.instLE : LE Nat where
  le n m := ∃ a:Nat, m = n + a

/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the `<` notation on the natural numbers. -/
instance Nat.instLT : LT Nat where
  lt n m := n ≤ m ∧ n ≠ m

lemma Nat.le_iff (n m:Nat) : n ≤ m ↔ ∃ a:Nat, m = n + a := by rfl

lemma Nat.lt_iff (n m:Nat) : n < m ↔ (∃ a:Nat, m = n + a) ∧ n ≠ m := by rfl

/-- Compare with Mathlib's `ge_iff_le`. -/
lemma Nat.ge_iff_le (n m:Nat) : n ≥ m ↔ m ≤ n := by rfl

/-- Compare with Mathlib's `gt_iff_lt`. -/
lemma Nat.gt_iff_lt (n m:Nat) : n > m ↔ m < n := by rfl

/-- Compare with Mathlib's `Nat.le_of_lt`. -/
lemma Nat.le_of_lt {n m:Nat} (hnm: n < m) : n ≤ m := hnm.1

/-- Compare with Mathlib's `Nat.le_iff_lt_or_eq`. -/
lemma Nat.le_iff_lt_or_eq (n m:Nat) : n ≤ m ↔ n < m ∨ n = m := by
  rw [Nat.le_iff, Nat.lt_iff]
  by_cases h : n = m
  . simp [h]
    use 0
    rw [add_zero]
  simp [h]

example : (8:Nat) > 5 := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  . have : (8:Nat) = 5 + 3 := by rfl
    rw [this]
    use 3
  decide

/-- Compare with Mathlib's `Nat.lt_succ_self`. -/
theorem Nat.succ_gt_self (n:Nat) : n++ > n := by
  revert n; apply induction
  . rw [Nat.gt_iff_lt, Nat.lt_iff]; constructor
    use 1; rfl
    decide
  intro n ih
  rw [Nat.gt_iff_lt, Nat.lt_iff]; constructor
  . use 1; rw [succ_eq_add_one]
  . rw [Nat.gt_iff_lt, Nat.lt_iff] at ih
    have h : (n ≠ n++) := ih.right
    apply succ_ne_succ; assumption


/-- Proposition 2.2.12 (Basic properties of order for natural numbers) / Exercise 2.2.3

(a) (Order is reflexive). Compare with Mathlib's `Nat.le_refl`.-/
theorem Nat.ge_refl (a:Nat) : a ≥ a := by
  use 0; simp

/-- (b) (Order is transitive).  The `obtain` tactic will be useful here.
    Compare with Mathlib's `Nat.le_trans`. -/
theorem Nat.ge_trans {a b c:Nat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  revert a; apply induction
  . intro h0b; cases' hbc with x hx; cases' h0b with z hz;
    rw [hx] at hz; use (x + z);
    rw [<- Nat.add_assoc]; assumption
  intro n ih hnb
  cases' hnb with z hz;
  cases' hbc with x hx; rw [hx] at hz
  use (x + z); rw [<- Nat.add_assoc]; assumption

/-- (c) (Order is anti-symmetric). Compare with Mathlib's `Nat.le_antisymm`. -/
theorem Nat.ge_antisymm {a b:Nat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  cases' hab with k hk; cases' hba with n hn;
  have h : (a + 0 = a) := Nat.add_zero a
  rw [<- h] at hk
  rw [hn] at hk
  rw [Nat.add_assoc] at hk
  apply Nat.add_cancel_left at hk
  have hk' : n + k = 0 := Eq.symm hk
  apply Nat.add_eq_zero at hk'
  cases' hk' with hK hN
  rw [hK] at hn; simp at hn;
  have hn' : a = b := Eq.symm hn
  assumption

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_right`. -/
theorem Nat.add_ge_add_right (a b c:Nat) : a ≥ b ↔ a + c ≥ b + c := by
  apply Iff.intro
  . intro hab
    cases' hab with x hx;
    use x; rw [hx, Nat.add_assoc]
    nth_rw 2 [Nat.add_comm]
    rw [Nat.add_assoc]
  . intro h
    cases' h with x hx; use x
    rw [Nat.add_assoc] at hx
    nth_rw 3 [Nat.add_comm] at hx
    rw [<- Nat.add_assoc] at hx
    rw [Nat.add_comm] at hx
    nth_rw 2 [Nat.add_comm] at hx
    apply Nat.add_cancel_left at hx; assumption

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_left`.  -/
theorem Nat.add_ge_add_left (a b c:Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_right`.  -/
theorem Nat.add_le_add_right (a b c:Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_left`.  -/
theorem Nat.add_le_add_left (a b c:Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

/-- (e) a < b iff a++ ≤ b.  Compare with Mathlib's `Nat.succ_le_iff`. -/
theorem Nat.lt_iff_succ_le (a b:Nat) : a < b ↔ a++ ≤ b := by
  apply Iff.intro
  . intro hab; rw [lt_iff] at hab
    cases' hab with hE hN; cases' hE with d hd
    have hD : d.isPos := by
      { rw [isPos_iff]; by_contra h
        rw [h] at hd; simp at hd
        have hd' : a = b := Eq.symm hd; contradiction }
    apply uniq_succ_eq at hD; cases' hD with e he
    simp at he; cases' he with he h'
    rw [<- he] at hd
    use e; rw [succ_add, add_comm]; rwa [<- add_comm, succ_add] at hd
  . intro hab; constructor
    . cases' hab with x hx
      use (1 + x); rwa [<- add_assoc, <- succ_eq_add_one]
    . by_contra h; cases' hab with x hx; rw [h] at hx
      have hb0 : (b = b + 0) := by rw [add_zero]
      nth_rw 1 [hb0] at hx; rw [succ_eq_add_one, add_assoc] at hx
      apply add_cancel_left at hx
      have hx' : (1 + x = 0) := Eq.symm hx
      apply add_eq_zero at hx'; simp at hx'

/-- (f) a < b if and only if b = a + d for positive d. -/
theorem Nat.lt_iff_add_pos (a b:Nat) : a < b ↔ ∃ d:Nat, d.isPos ∧ b = a + d := by
  apply Iff.intro
  . intro hab; cases' hab with hE hN; cases' hE with k hk;
    use k; constructor;
    . rw [isPos_iff]; by_contra h
      rw [h] at hk; simp at hk
      have hba : (a = b) := Eq.symm hk; contradiction
    . assumption
  . intro h; rw [lt_iff]
    cases' h with k hk; cases' hk with hP hK
    constructor
    . use k
    . by_contra h; rw [h] at hK
      have hb0 : (b = b + 0) := by rw [add_zero]
      nth_rw 1 [hb0] at hK; apply add_cancel_left at hK
      rw [isPos_iff] at hP
      have hK' : (k = 0) := Eq.symm hK; contradiction

/-- If a < b then a ̸= b,-/
theorem Nat.ne_of_lt (a b:Nat) : a < b → a ≠ b := by
  intro h; exact h.2

/-- if a > b then a ̸= b. -/
theorem Nat.ne_of_gt (a b:Nat) : a > b → a ≠ b := by
  intro h; exact h.2.symm

/-- If a > b and a < b then contradiction -/
theorem Nat.not_lt_of_gt (a b:Nat) : a < b ∧ a > b → False := by
  intro h
  have := (ge_antisymm (Nat.le_of_lt h.1) (Nat.le_of_lt h.2)).symm
  have := ne_of_lt _ _ h.1
  contradiction

/-- This lemma was a `why?` statement from Proposition 2.2.13,
but is more broadly useful, so is extracted here. -/
theorem Nat.zero_le (a:Nat) : 0 ≤ a := by
  sorry

/-- Proposition 2.2.13 (Trichotomy of order for natural numbers) / Exercise 2.2.4
    Compare with Mathlib's `trichotomous`. -/
theorem Nat.trichotomous (a b:Nat) : a < b ∨ a = b ∨ a > b := by
  -- This proof is written to follow the structure of the original text.
  revert a; apply induction
  . have why : 0 ≤ b := b.zero_le
    replace why := (Nat.le_iff_lt_or_eq _ _).mp why
    tauto
  intro a ih
  rcases ih with case1 | case2 | case3
  . rw [lt_iff_succ_le] at case1
    rw [Nat.le_iff_lt_or_eq] at case1
    tauto
  . have why : a++ > b := by
      { rw [gt_iff_lt, lt_iff_add_pos]; use 1; constructor
        . rw [isPos_iff]; simp
        . rw [<- succ_eq_add_one]; rwa [succ.injEq] }
    tauto
  have why : a++ > b := by
    { constructor
      . cases' case3 with h1 h2; cases' h1 with x hx;
        use (x + 1); rwa [<- add_assoc, <- succ_eq_add_one, succ.injEq];
      . by_contra h
        cases' case3 with hE hN; cases' hE with x hx
        rw [h] at hx; rw [succ_eq_add_one, add_assoc] at hx
        have h0 : (a + 0 = a) := by rw [add_zero]
        nth_rw 1 [<- h0] at hx; apply add_cancel_left at hx
        have hx' : (1 + x = 0) := Eq.symm hx
        apply add_eq_zero at hx'; contradiction }
  tauto

/--
  (Not from textbook) Establish the decidability of this order computably.  The portion of the
  proof involving decidability has been provided; the remaining sorries involve claims about the
  natural numbers.  One could also have established this result by the `classical` tactic
  followed by `exact Classical.decRel _`, but this would make this definition (as well as some
  instances below) noncomputable.

  Compare with Mathlib's `Nat.decLe`.
-/
def Nat.decLe : (a b : Nat) → Decidable (a ≤ b)
  | 0, b => by
    apply isTrue
    use b; rfl
  | a++, b => by
    cases decLe a b with
    | isTrue h =>
      cases decEq a b with
      | isTrue h =>
        apply isFalse
        intro contra
        rw [<- lt_iff_succ_le] at contra
        apply ne_of_lt at contra
        contradiction
      | isFalse h' =>
        apply isTrue
        rw [<- lt_iff_succ_le]
        rw [le_iff_lt_or_eq] at h
        rcases h with h1 | h2
        · assumption
        · contradiction
    | isFalse h =>
      apply isFalse
      intro h'
      rw [le_iff_lt_or_eq] at h
      simp at h
      rcases h with ⟨h1, h2⟩
      rw [<- lt_iff_succ_le] at h'
      contradiction

instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := Nat.decLe


/-- (Not from textbook) Nat has the structure of a linear ordering. This allows for tactics
such as `order` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.linearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_le := by
    intro a b
    constructor
    · intro h
      constructor
      · exact le_of_lt h
      · intro contra
        rw [le_iff_lt_or_eq] at contra
        rcases contra with h1 | h2
        · rw [<- gt_iff_lt] at h1
          exact not_lt_of_gt a b ⟨h, h1⟩
        · rw [h2] at h
          apply ne_of_lt at h
          contradiction
    · intro h
      rcases h with ⟨h1, h2⟩
      rw [le_iff_lt_or_eq] at h1
      rcases h1 with h1' | h2'
      · assumption
      · rw [le_iff_lt_or_eq] at h2
        simp at h2
        rcases h2 with ⟨ha, hb⟩
        rw [h2'] at hb
        contradiction
  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total := by
    intro a b
    revert a
    apply induction
    · left; use b; rfl
    · intro n h
      rcases h with hnb | hbn
      · rw [le_iff_lt_or_eq] at hnb
        rcases hnb with h1 | h2
        · left; rwa [<- lt_iff_succ_le]
        · right; rw [h2]; use 1; rw [succ_eq_add_one]
      · rw [le_iff_lt_or_eq] at hbn
        rcases hbn with h1 | h2
        · apply le_of_lt at h1
          cases' h1 with w hw
          right; use w + 1
          rw [<- add_assoc, hw, succ_eq_add_one]
        · right; rw [h2]
          use 1; rw [succ_eq_add_one]
  toDecidableLE := decidableRel

/-- This illustration of the `order` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) (hbc: b ≤ c) (hcd: c ≤ d)
        (hda: d ≤ a) : a = c := by order

/-- (Not from textbook) Nat has the structure of an ordered monoid. This allows for tactics
such as `gcongr` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left := by
    intro a b hab c
    exact (add_le_add_left a b c).mp hab

/-- This illustration of the `gcongr` tactic is not from the
    textbook. -/
example (a b c d e:Nat) (hab: a ≤ b) (hbc: b < c) (hde: d < e) :
  a+d ≤ c + e := by
  gcongr
  order

/-- Proposition 2.2.14 (Strong principle of induction) / Exercise 2.2.5
    Compare with Mathlib's `Nat.strong_induction_on`.
-/
theorem Nat.strong_induction {m₀:Nat} {P: Nat → Prop}
  (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) :
    ∀ m, m ≥ m₀ → P m := by
  sorry

/-- Exercise 2.2.6 (backwards induction)
    Compare with Mathlib's `Nat.decreasingInduction`. -/
theorem Nat.backwards_induction {n:Nat} {P: Nat → Prop}
  (hind: ∀ m, P (m++) → P m) (hn: P n) :
    ∀ m, m ≤ n → P m := by
  sorry

/-- Exercise 2.2.7 (induction from a starting point)
    Compare with Mathlib's `Nat.le_induction`. -/
theorem Nat.induction_from {n:Nat} {P: Nat → Prop} (hind: ∀ m, P m → P (m++)) :
    P n → ∀ m, m ≥ n → P m := by
  sorry



end Chapter2
