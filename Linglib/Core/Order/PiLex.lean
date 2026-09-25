module

public import Mathlib.Order.PiLex
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max

/-!
# The lexicographic order on finite tuples

This file relates `Pi.Lex` on `Fin n → α` to the lexicographic order on lists and characterizes
it by the first differing coordinate. The order on `Fin (n + 1)`-tuples compares heads and then
tails (`Pi.toLex_lt_toLex_iff_succ`), so it is the order of the tuples' lists
(`List.ofFn_lex_lt_iff`, `List.ofFn_le_ofFn_iff`); since the list order is decidable, so is the
tuple order (`Pi.Lex.decidableLT`, `Pi.Lex.decidableLE`), where mathlib's `LinearOrder` on
`Pi.Lex` carries only a classical instance. A tuple is lexicographically at most another when
every coordinate where it exceeds the other is preceded by one where it falls short
(`Pi.lex_le_iff_forall`), which is to say that it falls short at the first coordinate where
they differ (`Pi.lex_le_iff_find`).

[UPSTREAM] candidates for `Mathlib/Order/PiLex.lean` and `Mathlib/Data/List/OfFn.lean`.
-/

@[expose] public section

namespace Pi

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- The lexicographic order on `Fin (n + 1)`-tuples compares heads, then tails. -/
theorem toLex_lt_toLex_iff_succ (f g : Fin (n + 1) → α) :
    toLex f < toLex g ↔ f 0 < g 0 ∨ f 0 = g 0 ∧ toLex (Fin.tail f) < toLex (Fin.tail g) := by
  constructor
  · rintro ⟨i, hb, hi⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · exact Or.inl hi
    · exact Or.inr ⟨hb 0 (Fin.succ_pos i'),
        ⟨i', fun j hj ↦ hb j.succ (Fin.succ_lt_succ_iff.mpr hj), hi⟩⟩
  · rintro (hlt | ⟨h0, i', hb, hi⟩)
    · exact ⟨0, fun j hj ↦ absurd hj (Fin.not_lt_zero j), hlt⟩
    · refine ⟨i'.succ, fun j hj ↦ ?_, hi⟩
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact h0
      · exact hb j' (Fin.succ_lt_succ_iff.mp hj)

end Pi

namespace List

variable {α : Type*} [LinearOrder α]

/-- The lexicographic order on `Fin n`-tuples is the lexicographic order on their lists. -/
theorem ofFn_lex_lt_iff : ∀ {n : ℕ} (f g : Fin n → α),
    Lex (· < ·) (ofFn f) (ofFn g) ↔ toLex f < toLex g
  | 0, f, g => by
    rw [ofFn_zero, ofFn_zero]
    exact ⟨nofun, fun h ↦ by obtain ⟨i, -⟩ := h; exact i.elim0⟩
  | n + 1, f, g => by
    rw [ofFn_succ, ofFn_succ, cons_lex_cons_iff, ofFn_lex_lt_iff, Pi.toLex_lt_toLex_iff_succ]
    rfl

theorem ofFn_lt_ofFn_iff {n : ℕ} (f g : Fin n → α) : ofFn f < ofFn g ↔ toLex f < toLex g :=
  ofFn_lex_lt_iff f g

theorem ofFn_le_ofFn_iff {n : ℕ} (f g : Fin n → α) : ofFn f ≤ ofFn g ↔ toLex f ≤ toLex g := by
  rw [← not_lt, ← not_lt, ofFn_lt_ofFn_iff]

/-- The lexicographic order on lists compares heads, then tails. -/
theorem cons_le_cons_iff' {a b : α} {l₁ l₂ : List α} :
    a :: l₁ ≤ b :: l₂ ↔ a < b ∨ a = b ∧ l₁ ≤ l₂ := by
  rw [← not_lt, ← not_lt (a := l₂) (b := l₁),
    show b :: l₂ < a :: l₁ ↔ b < a ∨ b = a ∧ l₂ < l₁ from cons_lex_cons_iff]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h, h.ne', h.not_gt]
  · simp
  · simp [h, h.ne', h.not_gt]

end List

namespace Pi.Lex

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- `<` on `Lex (Fin n → α)` is decided by comparing the tuples' lists. -/
instance decidableLT : DecidableLT (Lex (Fin n → α)) := fun a b ↦
  decidable_of_iff _ (List.ofFn_lex_lt_iff (ofLex a) (ofLex b))

instance decidableLE : DecidableLE (Lex (Fin n → α)) := fun a b ↦
  decidable_of_iff (¬ b < a) not_lt

end Pi.Lex

namespace Pi

variable {α : Type*} [LinearOrder α] {m : ℕ}

/-- A tuple is lexicographically at most another iff every coordinate where it strictly exceeds
the other is preceded by one where it is strictly below. -/
theorem lex_le_iff_forall (A B : Fin m → α) :
    toLex A ≤ toLex B ↔ ∀ p, B p < A p → ∃ p' < p, A p' < B p' := by
  rw [← not_lt]
  constructor
  · intro hnlt p hp
    by_contra hcon
    by_cases hS : (Finset.univ.filter (fun j : Fin m ↦ j < p ∧ B j ≠ A j)).Nonempty
    · set q := (Finset.univ.filter (fun j : Fin m ↦ j < p ∧ B j ≠ A j)).min' hS with hq
      have hmem := Finset.min'_mem _ hS
      rw [← hq] at hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      obtain ⟨hqp, hne⟩ := hmem
      have hbefore : ∀ j, j < q → B j = A j := by
        intro j hj
        by_contra hjne
        have hjmem : j ∈ Finset.univ.filter (fun j : Fin m ↦ j < p ∧ B j ≠ A j) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨lt_trans hj hqp, hjne⟩
        have := Finset.min'_le _ _ hjmem
        rw [← hq] at this
        exact absurd hj (not_lt.mpr this)
      rcases lt_or_ge (B q) (A q) with hlt | hge
      · exact hnlt ⟨q, fun j hj ↦ hbefore j hj, hlt⟩
      · exact hcon ⟨q, hqp, lt_of_le_of_ne hge (fun h ↦ hne h.symm)⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hS
      have hbefore : ∀ j, j < p → B j = A j := by
        intro j hj
        by_contra hjne
        have hjmem : j ∈ Finset.univ.filter (fun j : Fin m ↦ j < p ∧ B j ≠ A j) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hj, hjne⟩
        rw [hS] at hjmem; simp at hjmem
      exact hnlt ⟨p, fun j hj ↦ hbefore j hj, hp⟩
  · intro hY hlt
    obtain ⟨i, hpre, hi⟩ := hlt
    obtain ⟨p', hp'lt, hp'⟩ := hY i hi
    exact absurd (hpre p' hp'lt).symm (ne_of_lt hp')

/-- A tuple is lexicographically at most another iff it is strictly below at the first
coordinate where they differ, when one exists. -/
theorem lex_le_iff_find (A B : Fin m → α) [DecidablePred fun i ↦ B i ≠ A i] :
    toLex A ≤ toLex B ↔ ∀ he : ∃ i, B i ≠ A i, A (Fin.find _ he) < B (Fin.find _ he) := by
  rw [lex_le_iff_forall]
  constructor
  · intro h he
    by_contra hle
    obtain ⟨p', hlt, hp'⟩ := h _ ((not_lt.mp hle).lt_of_ne (Fin.find_spec he))
    exact Fin.find_min he hlt hp'.ne'
  · intro hlead p hp
    have he : ∃ i, B i ≠ A i := ⟨p, hp.ne⟩
    refine ⟨Fin.find _ he, ?_, hlead he⟩
    exact (Fin.find_le_of_pos he hp.ne).lt_of_ne fun h ↦
      absurd (h ▸ hlead he) hp.asymm

end Pi
