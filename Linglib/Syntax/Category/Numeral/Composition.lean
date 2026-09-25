/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Nat.Hyperoperation
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Hurford's universal numeral grammar

This file defines Hurford's phrase-structure grammar of numerals and the Packing Strategy, the
constraint that selects one well-formed numeral for each number. A NUMBER is *one* or a PHRASE,
optionally followed by another NUMBER, and denotes the sum of its parts. A PHRASE is a NUMBER
followed by an M and denotes their product. An M is a lexical base such as *ten*, or a NUMBER
followed by an M, and denotes the second raised to the power of the first. The three rules are
one hyperoperation at the levels 1, 2 and 3. The Packing Strategy requires the sister of every
NUMBER to have the highest value the lexicon allows under the value of the node above it, and
leaves exactly one numeral for each positive number.

## Main definitions

* `Number`, `Phrase`, `M`: the three categories, with their `value`s
* `M.IsHighestUnder`: the highest-valued lexical M under a ceiling
* `Number.Packed`: the Packing Strategy relative to a lexicon of Ms
* `decimal`: the lexicon with an M for every power of ten

## Main results

* `Number.value_phraseAnd_eq_hyperoperation`, `Phrase.value_mk_eq_hyperoperation`,
  `M.value_mk_eq_hyperoperation`: the values are hyperoperations
* `Number.existsUnique_packed`: every positive number has exactly one packed NUMBER
* `Number.eq_oneHundredThirteen`: under `decimal` the packed NUMBER for 113 is Griffiths's tree

## Implementation notes

The grammar is Hurford's 1975 one as Griffiths reports it, with digits as tallies of *one* and
bases of any size so that other languages' Ms fit. Hurford's interpretive function reads the
operation off a node's depth, where here the level is the category's. The Packing Strategy is
Hurford's 2007 statement, the ceiling of a sister being the value of the node above it.

## References

* [hurford-1975]
* [hurford-2007]
* [griffiths-1977]
-/

@[expose] public section

namespace Numeral

/-! ### The phrase-structure categories -/

mutual
/-- A NUMBER is *one* or a PHRASE, optionally followed by another NUMBER. -/
inductive Number where
  /-- *one*, a single mark, is a NUMBER. -/
  | one : Number
  /-- *one* followed by a NUMBER is a NUMBER. -/
  | oneAnd (rest : Number) : Number
  /-- A PHRASE is a NUMBER. -/
  | phrase (p : Phrase) : Number
  /-- A PHRASE followed by a NUMBER is a NUMBER, as in *twenty-three*. -/
  | phraseAnd (p : Phrase) (rest : Number) : Number
  deriving DecidableEq, Repr

/-- A PHRASE is a NUMBER followed by an M, as in *two hundred*. -/
inductive Phrase where
  | mk (n : Number) (m : M) : Phrase
  deriving DecidableEq, Repr

/-- An M is a lexical base or a NUMBER followed by an M, as *hundred* is `[two ten]`. -/
inductive M where
  /-- A lexical base is a row of `b` marks. -/
  | base (b : ℕ) (hb : 1 < b := by decide) : M
  /-- A NUMBER followed by an M is an M. -/
  | mk (n : Number) (m : M) : M
  deriving DecidableEq, Repr
end

/-! ### The projection rules -/

mutual
/-- The value of a NUMBER is the sum of its immediate constituents. -/
def Number.value : Number → ℕ
  | .one => 1
  | .oneAnd rest => 1 + rest.value
  | .phrase p => p.value
  | .phraseAnd p rest => p.value + rest.value

/-- The value of a PHRASE is the product of its immediate constituents. -/
def Phrase.value : Phrase → ℕ
  | .mk n m => n.value * m.value

/-- The value of an M is its second constituent raised to the power of its first. -/
def M.value : M → ℕ
  | .base b _ => b
  | .mk n m => m.value ^ n.value
end

/-- *ten* is the base of ten marks. -/
def M.ten : M := .base 10

@[simp] theorem M.value_ten : M.ten.value = 10 := rfl

/-! ### One operation at three levels

Each projection rule is a hyperoperation whose level is the category's, whose base is the second
constituent, and whose iteration count is the first: a NUMBER adds the value of its PHRASE to the
rest one mark at a time, a PHRASE adds its M to itself as often as its NUMBER says, and an M
multiplies the inner M by itself as often. The recursion defining the sequence,
`hyperoperation_recursion`, is the reduction of each operation to iterations of the one below. -/

theorem Number.value_phraseAnd_eq_hyperoperation (p : Phrase) (rest : Number) :
    (phraseAnd p rest).value = hyperoperation 1 rest.value p.value := by
  rw [hyperoperation_one, value, add_comm]

theorem Phrase.value_mk_eq_hyperoperation (n : Number) (m : M) :
    (mk n m).value = hyperoperation 2 m.value n.value := by
  rw [hyperoperation_two, value, mul_comm]

theorem M.value_mk_eq_hyperoperation (n : Number) (m : M) :
    (mk n m).value = hyperoperation 3 m.value n.value := by
  rw [hyperoperation_three, value]

/-! ### Values -/

theorem M.value_pos : ∀ m : M, 0 < m.value
  | .base _ hb => Nat.zero_lt_of_lt hb
  | .mk _ m => Nat.pow_pos m.value_pos

mutual
theorem Number.value_pos : ∀ n : Number, 0 < n.value
  | .one => Nat.one_pos
  | .oneAnd _ => Nat.add_pos_left Nat.one_pos _
  | .phrase p => p.value_pos
  | .phraseAnd p _ => Nat.add_pos_left p.value_pos _

theorem Phrase.value_pos : ∀ p : Phrase, 0 < p.value
  | .mk n m => Nat.mul_pos n.value_pos m.value_pos
end

theorem M.one_lt_value : ∀ m : M, 1 < m.value
  | .base _ hb => hb
  | .mk n m => m.one_lt_value.trans_le (Nat.le_self_pow n.value_pos.ne' _)

/-- `tally n` is the NUMBER `[one [one ... one]]` of `n + 1` marks, the structure of a digit. -/
def Number.tally : ℕ → Number
  | 0 => .one
  | n + 1 => .oneAnd (tally n)

@[simp] theorem Number.value_tally (n : ℕ) : (tally n).value = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tally, value, ih, add_comm]

/-- The grammar names exactly the positive numbers. -/
theorem Number.range_value : Set.range value = {n | 0 < n} := by
  ext n
  refine ⟨fun ⟨e, he⟩ ↦ he ▸ e.value_pos, fun hn ↦ ⟨tally (n - 1), ?_⟩⟩
  simp only [value_tally]
  exact Nat.sub_add_cancel hn

/-- `tenPow k` is the M of value `10 ^ (k + 1)`, *ten* or `[k + 1 ten]`. -/
def M.tenPow : ℕ → M
  | 0 => .ten
  | k + 1 => .mk (.tally (k + 1)) .ten

@[simp] theorem M.value_tenPow (k : ℕ) : (tenPow k).value = 10 ^ (k + 1) := by
  cases k with
  | zero => rfl
  | succ k => simp [tenPow, value]

/-- A digit times a base-power M, as in *four hundred*, has value `(m + 1) × 10 ^ (k + 1)`. -/
theorem Phrase.value_tally_tenPow (m k : ℕ) :
    (Phrase.mk (.tally m) (.tenPow k)).value = (m + 1) * 10 ^ (k + 1) := by
  simp [value]

/-! ### The Packing Strategy -/

variable {L : Set M}

/-- `m` is the highest-valued M of the lexicon `L` whose value does not exceed the ceiling `v`. -/
def M.IsHighestUnder (L : Set M) (v : ℕ) (m : M) : Prop :=
  m ∈ L ∧ IsGreatest (value '' {m' ∈ L | m'.value ≤ v}) m.value

theorem M.isHighestUnder_iff {v : ℕ} {m : M} :
    m.IsHighestUnder L v ↔ m ∈ L ∧ m.value ≤ v ∧ ∀ m' ∈ L, m'.value ≤ v → m'.value ≤ m.value := by
  simp only [IsHighestUnder, IsGreatest, upperBounds, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hm, ⟨m', ⟨-, hm'⟩, he⟩, hub⟩
    exact ⟨hm, he ▸ hm', fun m'' h h' ↦ hub ⟨m'', ⟨h, h'⟩, rfl⟩⟩
  · rintro ⟨hm, hmv, hub⟩
    exact ⟨hm, ⟨m, ⟨hm, hmv⟩, rfl⟩, by rintro _ ⟨m'', ⟨h, h'⟩, rfl⟩; exact hub m'' h h'⟩

theorem M.IsHighestUnder.value_le {v : ℕ} {m : M} (h : m.IsHighestUnder L v) : m.value ≤ v :=
  (isHighestUnder_iff.1 h).2.1

/-- A lexical M above the highest one under a ceiling is above the ceiling. -/
theorem M.IsHighestUnder.lt_value {v : ℕ} {m m' : M} (h : m.IsHighestUnder L v) (hm' : m' ∈ L)
    (hlt : m.value < m'.value) : v < m'.value :=
  lt_of_not_ge fun hv ↦ (h.2.2 ⟨m', ⟨hm', hv⟩, rfl⟩).not_gt hlt

theorem M.IsHighestUnder.eq (hL : Set.InjOn value L) {v : ℕ} {m m' : M}
    (h : m.IsHighestUnder L v) (h' : m'.IsHighestUnder L v) : m = m' :=
  hL h.1 h'.1 (h.2.unique h'.2)

/-- Wherever some lexical M fits under the ceiling, a highest one does. -/
theorem M.exists_isHighestUnder {v : ℕ} {m₀ : M} (hm₀ : m₀ ∈ L) (hv : m₀.value ≤ v) :
    ∃ m : M, m.IsHighestUnder L v := by
  have hS := Set.Nonempty.isGreatest_csSup (s := value '' {m ∈ L | m.value ≤ v})
    ⟨_, m₀, ⟨hm₀, hv⟩, rfl⟩
    ((Set.finite_Iic v).subset (by rintro _ ⟨m, ⟨-, hm⟩, rfl⟩; exact hm))
  obtain ⟨m, ⟨hmL, -⟩, hm⟩ := hS.1
  exact ⟨m, hmL, hm ▸ hS⟩

/-- A NUMBER is packed relative to the lexicon `L` when the sister of every NUMBER in it has the
highest possible value. After *one* that holds only where no lexical M fits under the whole; a
PHRASE sister has the highest lexical M under the NUMBER's value, and leaves a remainder below
that M. -/
def Number.Packed (L : Set M) : Number → Prop
  | .one => True
  | .oneAnd rest => (∀ m ∈ L, 1 + rest.value < m.value) ∧ rest.Packed L
  | .phrase (.mk n m) => m.IsHighestUnder L (n.value * m.value) ∧ n.Packed L
  | .phraseAnd (.mk n m) rest =>
      m.IsHighestUnder L (n.value * m.value + rest.value) ∧ rest.value < m.value ∧
        n.Packed L ∧ rest.Packed L

instance M.decidableIsHighestUnder (L : List M) (v : ℕ) (m : M) :
    Decidable (m.IsHighestUnder {m | m ∈ L} v) :=
  decidable_of_iff (m ∈ L ∧ m.value ≤ v ∧ ∀ m' ∈ L, m'.value ≤ v → m'.value ≤ m.value)
    (isHighestUnder_iff (L := {m | m ∈ L})).symm

/-- The Packing Strategy is decidable over a finite lexicon. -/
instance Number.decidablePacked (L : List M) : DecidablePred (Packed {m | m ∈ L})
  | .one => inferInstanceAs (Decidable True)
  | .oneAnd r =>
    haveI := decidablePacked L r
    inferInstanceAs (Decidable ((∀ m ∈ L, 1 + r.value < m.value) ∧ r.Packed {m | m ∈ L}))
  | .phrase (.mk n m) =>
    haveI := decidablePacked L n
    inferInstanceAs
      (Decidable (m.IsHighestUnder {m | m ∈ L} (n.value * m.value) ∧ n.Packed {m | m ∈ L}))
  | .phraseAnd (.mk n m) r =>
    haveI := decidablePacked L n
    haveI := decidablePacked L r
    inferInstanceAs (Decidable (m.IsHighestUnder {m | m ∈ L} (n.value * m.value + r.value) ∧
      r.value < m.value ∧ n.Packed {m | m ∈ L} ∧ r.Packed {m | m ∈ L}))

/-- The Packing Strategy admits the tally of `n + 1` marks exactly when every lexical M is
higher. -/
theorem Number.packed_tally_iff {n : ℕ} : (tally n).Packed L ↔ ∀ m ∈ L, n + 1 < m.value := by
  induction n with
  | zero =>
    simp only [tally, Packed, true_iff]
    exact fun m _ ↦ by have := m.one_lt_value; omega
  | succ n ih =>
    simp only [tally, Packed, value_tally, ih]
    exact ⟨fun h m hm ↦ by have := h.1 m hm; omega,
      fun h ↦ ⟨fun m hm ↦ by have := h m hm; omega, fun m hm ↦ by have := h m hm; omega⟩⟩

/-- Below the lowest lexical M the only packed NUMBER is the tally. -/
theorem Number.Packed.eq_tally : ∀ {e : Number}, e.Packed L → (∀ m ∈ L, e.value < m.value) →
    e = tally (e.value - 1)
  | .one, _, _ => rfl
  | .oneAnd r, ⟨_, hr⟩, hlow => by
    have hr' := hr.eq_tally fun m hm ↦ by have := hlow m hm; simp only [value] at this; omega
    obtain ⟨k, hk⟩ : ∃ k, r.value = k + 1 := ⟨r.value - 1, by have := r.value_pos; omega⟩
    simp only [value, hk, Nat.add_sub_cancel] at hr' ⊢
    rw [show 1 + (k + 1) - 1 = k + 1 by omega, hr']
    rfl
  | .phrase (.mk _ m), ⟨hm, _⟩, hlow => absurd (hlow m hm.1) hm.value_le.not_gt
  | .phraseAnd (.mk _ m) _, ⟨hm, _⟩, hlow => absurd (hlow m hm.1) hm.value_le.not_gt

/-- When the groups of the highest lexical M under `v` exhaust `v`, a packed NUMBER for their
number makes one for `v`. -/
theorem Number.packed_phrase {v : ℕ} {m : M} (hm : m.IsHighestUnder L v) (hmv : m.value ∣ v)
    {n : Number} (hn : n.Packed L) (hnv : n.value = v / m.value) :
    (phrase (.mk n m)).Packed L ∧ (phrase (.mk n m)).value = v := by
  simp only [Packed, Number.value, Phrase.value, hnv, Nat.div_mul_cancel hmv, and_true]
  exact ⟨hm, hn⟩

/-- Packed NUMBERs for the number of groups of the highest lexical M under `v` and for the
remainder make one for `v`. -/
theorem Number.packed_phraseAnd {v : ℕ} {m : M} (hm : m.IsHighestUnder L v) {n r : Number}
    (hn : n.Packed L) (hnv : n.value = v / m.value) (hr : r.Packed L)
    (hrv : r.value = v % m.value) :
    (phraseAnd (.mk n m) r).Packed L ∧ (phraseAnd (.mk n m) r).value = v := by
  simp only [Packed, Number.value, Phrase.value, hnv, hrv, Nat.div_add_mod', and_true]
  exact ⟨hm, Nat.mod_lt _ m.value_pos, hn, hr⟩

/-- Every positive number has a packed NUMBER, built from the highest lexical M under it, the
number of copies of that M that fit, and the remainder. -/
theorem Number.exists_packed (L : Set M) {v : ℕ} (hv : 0 < v) :
    ∃ e : Number, e.Packed L ∧ e.value = v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  by_cases hlow : ∀ m ∈ L, v < m.value
  · exact ⟨tally (v - 1), packed_tally_iff.2 fun m hm ↦ by have := hlow m hm; omega,
      by simp only [value_tally]; omega⟩
  push Not at hlow
  obtain ⟨m₀, hm₀, hm₀v⟩ := hlow
  obtain ⟨m, hm⟩ := M.exists_isHighestUnder hm₀ hm₀v
  have h1 := m.one_lt_value
  have hmv := hm.value_le
  obtain ⟨n, hn, hnv⟩ :=
    ih (v / m.value) (Nat.div_lt_self hv h1) (Nat.div_pos hmv (by omega))
  rcases Nat.eq_zero_or_pos (v % m.value) with hr | hr
  · exact ⟨_, packed_phrase hm (Nat.dvd_of_mod_eq_zero hr) hn hnv⟩
  · obtain ⟨r, hr', hrv⟩ := ih (v % m.value) ((Nat.mod_lt _ (by omega)).trans_le hmv) hr
    exact ⟨_, packed_phraseAnd hm hn hnv hr' hrv⟩

/-- A packed NUMBER is determined by its value, given a lexicon whose Ms have distinct values. -/
theorem Number.Packed.eq_of_value_eq (hL : Set.InjOn M.value L) {e e' : Number}
    (he : e.Packed L) (he' : e'.Packed L) (h : e.value = e'.value) : e = e' := by
  induction hv : e.value using Nat.strong_induction_on generalizing e e' with
  | _ v ih =>
  by_cases hlow : ∀ m ∈ L, v < m.value
  · rw [he.eq_tally (hv ▸ hlow), he'.eq_tally (h ▸ hv ▸ hlow), h]
  push Not at hlow
  obtain ⟨m₀, hm₀, hm₀v⟩ := hlow
  have hm₀e : m₀.value ≤ e.value := hv ▸ hm₀v
  have hm₀e' : m₀.value ≤ e'.value := h ▸ hv ▸ hm₀v
  have := m₀.one_lt_value
  have key : ∀ {m : M} {a b : ℕ}, b < m.value → (a * m.value + b) / m.value = a :=
    fun hb ↦ by rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hb, Nat.add_zero]
  rcases e with _ | r | ⟨n, m⟩ | ⟨⟨n, m⟩, r⟩
  · simp only [Number.value] at hm₀e; omega
  · have := he.1 m₀ hm₀; simp only [Number.value] at hm₀e; omega
  all_goals
    rcases e' with _ | r' | ⟨n', m'⟩ | ⟨⟨n', m'⟩, r'⟩
    · simp only [Number.value] at hm₀e'; omega
    · have := he'.1 m₀ hm₀; simp only [Number.value] at hm₀e'; omega
  all_goals
    simp only [Packed, Number.value, Phrase.value] at he he' h hv
  · rw [← h] at he'
    obtain rfl := he.1.eq hL he'.1
    have := Nat.mul_le_mul_left n.value (show 2 ≤ m.value by have := m.one_lt_value; omega)
    rw [ih _ (by have := n.value_pos; omega) he.2 he'.2
      (Nat.eq_of_mul_eq_mul_right m.value_pos h) rfl]
  · rw [← h] at he'
    obtain rfl := he.1.eq hL he'.1
    have := congrArg (· % m.value) h
    simp only [Nat.mul_mod_left, Nat.mul_add_mod', Nat.mod_eq_of_lt he'.2.1] at this
    have := r'.value_pos; omega
  · rw [h] at he
    obtain rfl := he.1.eq hL he'.1
    have := congrArg (· % m.value) h
    simp only [Nat.mul_mod_left, Nat.mul_add_mod', Nat.mod_eq_of_lt he.2.1] at this
    have := r.value_pos; omega
  · rw [← h] at he'
    obtain rfl := he.1.eq hL he'.1
    have hn : n.value = n'.value := by
      simpa only [key he.2.1, key he'.2.1] using congrArg (· / m.value) h
    have hr : r.value = r'.value := by rw [hn] at h; omega
    have := Nat.mul_le_mul_left n.value (show 2 ≤ m.value by have := m.one_lt_value; omega)
    have := Nat.le_mul_of_pos_left m.value n.value_pos
    rw [ih _ (by have := n.value_pos; omega) he.2.2.1 he'.2.2.1 hn rfl,
      ih _ (by omega) he.2.2.2 he'.2.2.2 hr rfl]

/-- Every positive number has exactly one packed NUMBER, given a lexicon whose Ms have distinct
values. -/
theorem Number.existsUnique_packed (hL : Set.InjOn M.value L) {v : ℕ} (hv : 0 < v) :
    ∃! e : Number, e.Packed L ∧ e.value = v := by
  obtain ⟨e, he, rfl⟩ := exists_packed L hv
  exact ⟨e, ⟨he, rfl⟩, fun e' ⟨he', h⟩ ↦ he'.eq_of_value_eq hL he h⟩

/-! ### The decimal lexicon -/

/-- `decimal` is the lexicon with an M for every power of ten. -/
def decimal : Set M := Set.range M.tenPow

theorem injOn_value_decimal : Set.InjOn M.value decimal := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
  simp only [M.value_tenPow, Nat.pow_right_inj (by decide : 1 < 10), Nat.add_right_cancel_iff] at h
  rw [h]

/-- Under the decimal lexicon the highest M under `v` is the power of ten with `v` below the
next. -/
theorem M.tenPow_isHighestUnder_decimal_iff {k v : ℕ} :
    (tenPow k).IsHighestUnder decimal v ↔ 10 ^ (k + 1) ≤ v ∧ v < 10 ^ (k + 2) := by
  simp only [isHighestUnder_iff, decimal, Set.mem_range_self, true_and, Set.forall_mem_range,
    value_tenPow]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ lt_of_not_ge fun hv ↦ ?_, fun hv j hj ↦ ?_⟩
  · have := h (k + 1) hv
    rw [Nat.pow_le_pow_iff_right (by decide)] at this
    omega
  · have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 10)).1 (hj.trans_lt hv)
    exact Nat.pow_le_pow_right (by decide) (by omega)

/-- `[[one hundred] [[one ten] three]]` is *one hundred and thirteen* in the structure
[griffiths-1977] gives it. -/
def Number.oneHundredThirteen : Number :=
  .phraseAnd (.mk .one (.tenPow 1)) (.phraseAnd (.mk .one .ten) (.tally 2))

/-- `[[eleven ten] three]` also has the value 113. -/
def Number.eleventyThree : Number :=
  .phraseAnd (.mk (.phraseAnd (.mk .one .ten) .one) .ten) (.tally 2)

theorem Number.value_oneHundredThirteen : oneHundredThirteen.value = 113 := rfl

theorem Number.value_eleventyThree : eleventyThree.value = 113 := rfl

theorem Number.packed_oneHundredThirteen : oneHundredThirteen.Packed decimal :=
  ⟨M.tenPow_isHighestUnder_decimal_iff.2 (by decide), by decide, trivial,
    (M.tenPow_isHighestUnder_decimal_iff (k := 0)).2 (by decide), by decide, trivial,
    packed_tally_iff.2 <| Set.forall_mem_range.2 fun k ↦ by
      simpa using (by decide : 3 < 10).trans_le (Nat.le_self_pow k.succ_ne_zero 10)⟩

/-- `[[eleven ten] three]` is not packed, since *hundred* fits under 113. -/
theorem Number.not_packed_eleventyThree : ¬ eleventyThree.Packed decimal := fun h ↦
  absurd ((M.tenPow_isHighestUnder_decimal_iff (k := 0)).1 h.1) (by decide)

/-- Under the decimal lexicon the packed NUMBER for 113 is *one hundred and thirteen*. -/
theorem Number.eq_oneHundredThirteen {e : Number} (he : e.Packed decimal) (h : e.value = 113) :
    e = oneHundredThirteen :=
  he.eq_of_value_eq injOn_value_decimal packed_oneHundredThirteen h

end Numeral
