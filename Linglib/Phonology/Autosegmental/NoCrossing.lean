import Linglib.Phonology.Autosegmental.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Order.Monotone.Monovary

/-!
# Index-level no-crossing constraint for autosegmental association lines

A set of links between two ordered tiers — modelled as `Finset (ℕ × ℕ)`,
where the first component indexes the upper tier (e.g., tones) and the
second the lower (e.g., segments) — is **no-crossing** iff for any two
links `(k₁, i₁)`, `(k₂, i₂)`, `k₁ < k₂` implies `i₁ ≤ i₂`. This is the
discrete-index version of the [goldsmith-1976] / [sagey-1986]
No-Crossing Constraint and is the canonical filter on autosegmental GEN.

## Main definitions

* `IndexCrosses links k i` — candidate link `(k, i)` would cross some
  existing link in `links`. The decidable filter predicate used by GEN.
* `IsNoCrossing links` — the link set satisfies the NCC, expressed as
  mathlib's `MonovaryOn Prod.snd Prod.fst`.

## Main results

* `IsNoCrossing.subset` — passes through `MonovaryOn.subset`.
* `IsNoCrossing.insert_of_not_indexCrosses` — the load-bearing bridge:
  extending a no-crossing set with a candidate that doesn't cross any
  existing link preserves the property.

## Implementation notes

`IsNoCrossing` is defined via mathlib's `MonovaryOn` (`Mathlib.Order.Monotone.Monovary`):
the "two functions vary together over a set" abstraction. A link set is
no-crossing iff the seg-index function monovaries with the tone-index
function over the link set. This buys mathlib's API (subset closure,
universe restriction, etc.) for free.

`IndexCrosses` is the operational candidate predicate used inside GEN.
Its body is the existential index-ordering formulation
(`[goldsmith-1976]`-style); decidability falls out by
`Finset.decidableBEx`.

The **substrate hom** `linkToPointAssociation : ℕ × ℕ → Association ℕ`
bridges this discrete-index substrate to the interval substrate in
`Defs.lean`: each index pair becomes an `Association` with point
intervals, and `indexCrosses_iff_crosses_pointAssociation` shows
the two crossing predicates agree under this map. This connects
Goldsmith-style index-NCC to Sagey-style interval-NCC by construction.

## References

* [goldsmith-1976] — autosegmental phonology, NCC as well-formedness
* [sagey-1986] — temporal derivation of NCC from interval overlap
-/

namespace Phonology.Autosegmental

open Core.Time (Interval)

/-! ### Candidate-level crossing predicate -/

/-- The candidate link `(k, i)` would **cross** some existing link in
    `links`. Two links cross iff their tier-order disagrees with their
    backbone-order: `(k < k' ∧ i' < i) ∨ (k' < k ∧ i < i')`. -/
def IndexCrosses (links : Finset (ℕ × ℕ)) (k i : ℕ) : Prop :=
  ∃ l ∈ links, (k < l.fst ∧ l.snd < i) ∨ (l.fst < k ∧ i < l.snd)

instance (links : Finset (ℕ × ℕ)) (k i : ℕ) : Decidable (IndexCrosses links k i) :=
  decidable_of_iff
    (∃ l ∈ links, (k < l.fst ∧ l.snd < i) ∨ (l.fst < k ∧ i < l.snd)) Iff.rfl

/-! ### Set-level no-crossing property (via mathlib `MonovaryOn`) -/

/-- The link set has no crossings: the seg-index function monovaries
    with the tone-index function. Defined through mathlib's `MonovaryOn`
    to inherit its lemma library. -/
def IsNoCrossing (links : Finset (ℕ × ℕ)) : Prop :=
  MonovaryOn Prod.snd Prod.fst (↑links : Set (ℕ × ℕ))

/-- `IsNoCrossing` in elementary form: for any two links in the set,
    tone-order implies seg-order. -/
theorem isNoCrossing_iff (links : Finset (ℕ × ℕ)) :
    IsNoCrossing links ↔
      ∀ l₁ ∈ links, ∀ l₂ ∈ links, l₁.fst < l₂.fst → l₁.snd ≤ l₂.snd := by
  unfold IsNoCrossing MonovaryOn
  constructor
  · intro h l₁ hl₁ l₂ hl₂ hlt
    exact h (Finset.mem_coe.mpr hl₁) (Finset.mem_coe.mpr hl₂) hlt
  · intro h l₁ hl₁ l₂ hl₂ hlt
    exact h l₁ (Finset.mem_coe.mp hl₁) l₂ (Finset.mem_coe.mp hl₂) hlt

/-- A subset of a no-crossing link set is no-crossing. Inherited from
    `MonovaryOn.subset`. -/
theorem IsNoCrossing.subset {s t : Finset (ℕ × ℕ)} (hst : s ⊆ t)
    (h : IsNoCrossing t) : IsNoCrossing s :=
  MonovaryOn.subset (Finset.coe_subset.mpr hst) h

/-- **Insertion bridge.** Extending a no-crossing link set with a
    candidate `(k, i)` that doesn't cross any existing link preserves
    the no-crossing property. -/
theorem IsNoCrossing.insert_of_not_indexCrosses
    {links : Finset (ℕ × ℕ)} {k i : ℕ}
    (hNC : IsNoCrossing links) (hNX : ¬ IndexCrosses links k i) :
    IsNoCrossing (insert (k, i) links) := by
  rw [isNoCrossing_iff] at hNC ⊢
  intro l₁ hl₁ l₂ hl₂ hlt
  simp only [Finset.mem_insert] at hl₁ hl₂
  rcases hl₁ with rfl | hl₁ <;> rcases hl₂ with rfl | hl₂
  · exact absurd hlt (lt_irrefl _)
  · -- l₁ = (k, i), l₂ ∈ links; hlt : k < l₂.fst; goal : i ≤ l₂.snd
    rcases Nat.lt_or_ge l₂.snd i with h | h
    · exact absurd ⟨l₂, hl₂, Or.inl ⟨hlt, h⟩⟩ hNX
    · exact h
  · -- l₁ ∈ links, l₂ = (k, i); hlt : l₁.fst < k; goal : l₁.snd ≤ i
    rcases Nat.lt_or_ge i l₁.snd with h | h
    · exact absurd ⟨l₁, hl₁, Or.inr ⟨hlt, h⟩⟩ hNX
    · exact h
  · exact hNC l₁ hl₁ l₂ hl₂ hlt

/-! ### Substrate hom: index pair → point-interval `Association` -/

/-- View an index link `(k, i) : ℕ × ℕ` as an `Association ℕ` with point
    intervals at `k` (timing tier) and `i` (melody tier). The canonical
    hom from the index-NCC substrate (`IndexCrosses`) to the interval-NCC
    substrate (`crosses`). -/
def linkToPointAssociation (l : ℕ × ℕ) : Association ℕ where
  timing := ⟨Interval.point l.fst⟩
  melody := ⟨Interval.point l.snd⟩

/-- **Substrate bridge.** Crossing between the point-interval associations
    of two index links agrees with the index-ordering condition. -/
theorem indexCrosses_iff_crosses_pointAssociation (l₁ l₂ : ℕ × ℕ) :
    (l₁.fst < l₂.fst ∧ l₂.snd < l₁.snd) ↔
    crosses (linkToPointAssociation l₁) (linkToPointAssociation l₂) := by
  unfold crosses linkToPointAssociation Interval.precedes Interval.point
  simp

end Phonology.Autosegmental
