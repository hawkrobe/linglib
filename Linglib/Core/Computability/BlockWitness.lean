import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Lemmas

/-!
# Block-Structured Witnesses for Pumping-Lemma Arguments

A `BlockWitness symbols p` is the string `s₀ᵖ s₁ᵖ ⋯ sₙ₋₁ᵖ` formed by
concatenating one block of length `p` per symbol in `symbols`. Such witnesses
are the standard test strings for non-context-freeness arguments via the
CFL pumping lemma.

Three downstream consumers in `Linglib.Core.Computability.NonContextFree`
share this substrate: `anbncndn`, `anbnc`, and `ambncmdn`.

## Substrate scope (current)

This file provides the **structural and counting** layer:

* `BlockWitness symbols p` — the witness construction.
* `length_eq`, `length_take` — size arithmetic.
* `split_at` — clean decomposition at any block boundary.
* `filter_count` — counts of in-alphabet symbols (each = `p`, by `Nodup`).
* `mem_iff` — membership characterization.

## Future: full adjacency-lemma unification (TODO)

The pumping arguments in `NonContextFree.lean` currently still carry their
own per-alphabet adjacency helpers (`not_a_and_d_in_vxy` for FourSymbol,
`not_a_and_c_in_vxy3` for ThreeSymbol, etc.). Factoring these into a single
`not_both_in_vxy` over arbitrary `BlockWitness` requires position arithmetic
that the current substrate doesn't yet expose. The unification is mechanical
but intricate; it would replace ~150 LOC of per-alphabet locality lemmas
with a single proof. Tracked as an integration TODO.
-/

universe u

variable {α : Type u}

/-- A block-structured witness: concatenates one block of length `p` per
    symbol in `symbols`. -/
def BlockWitness (symbols : List α) (p : Nat) : List α :=
  symbols.flatMap (fun s => List.replicate p s)

namespace BlockWitness

@[simp] theorem nil (p : Nat) : BlockWitness ([] : List α) p = [] := rfl

@[simp] theorem cons (s : α) (ss : List α) (p : Nat) :
    BlockWitness (s :: ss) p = List.replicate p s ++ BlockWitness ss p := by
  simp [BlockWitness, List.flatMap_cons]

@[simp] theorem zero (symbols : List α) :
    BlockWitness symbols 0 = [] := by
  induction symbols with
  | nil => rfl
  | cons _ _ ih => simp [cons, ih]

theorem length_eq (symbols : List α) (p : Nat) :
    (BlockWitness symbols p).length = symbols.length * p := by
  induction symbols with
  | nil => simp
  | cons s ss ih =>
    rw [cons, List.length_append, List.length_replicate, ih, List.length_cons,
        Nat.succ_mul, Nat.add_comm]

/-- The witness splits cleanly at any block boundary. -/
theorem split_at (symbols : List α) (p i : Nat) :
    BlockWitness symbols p =
      BlockWitness (symbols.take i) p ++ BlockWitness (symbols.drop i) p := by
  induction symbols generalizing i with
  | nil => simp
  | cons s ss ih =>
    cases i with
    | zero => simp
    | succ k =>
      rw [List.take_succ_cons, List.drop_succ_cons, cons, cons, ih, List.append_assoc]

theorem length_take (symbols : List α) (p : Nat) {i : Nat}
    (hi : i ≤ symbols.length) :
    (BlockWitness (symbols.take i) p).length = i * p := by
  rw [length_eq, List.length_take, min_eq_left hi]

/-- Filter count: each in-alphabet symbol contributes exactly `p`; absent
    symbols contribute 0. Requires `symbols.Nodup` so blocks don't merge. -/
theorem filter_count [DecidableEq α]
    {symbols : List α} (hnd : symbols.Nodup) (p : Nat) (s : α) :
    ((BlockWitness symbols p).filter (· == s)).length =
      if s ∈ symbols then p else 0 := by
  induction symbols with
  | nil => simp
  | cons t ts ih =>
    rw [cons, List.filter_append, List.length_append,
        List.filter_replicate]
    have hnd' : ts.Nodup := hnd.of_cons
    have ht_notin : t ∉ ts := List.Nodup.notMem hnd
    rw [ih hnd']
    by_cases hst : s = t
    · subst hst
      simp [ht_notin]
    · have hbeq : (t == s) = false := by
        rw [beq_eq_false_iff_ne]; exact fun h => hst h.symm
      simp only [hbeq, List.length_nil, List.mem_cons]
      have : ¬ (s = t) := hst
      simp [this]

/-- A symbol appears in `BlockWitness symbols p` iff it's in `symbols`
    (and `p ≥ 1`). -/
theorem mem_iff [DecidableEq α] {symbols : List α} {p : Nat}
    (hp : p ≥ 1) (s : α) :
    s ∈ BlockWitness symbols p ↔ s ∈ symbols := by
  induction symbols with
  | nil => simp
  | cons t ts ih =>
    rw [cons, List.mem_append, List.mem_cons, ih]
    constructor
    · rintro (h | h)
      · left; exact List.eq_of_mem_replicate h
      · right; exact h
    · rintro (rfl | h)
      · left; exact List.mem_replicate.mpr ⟨Nat.one_le_iff_ne_zero.mp hp, rfl⟩
      · right; exact h

end BlockWitness
