import Linglib.Core.Order.UpperLower.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.DeriveFintype

/-!
# Containment feature pairs

This file defines valuations of two dependent bivalent features. A containment pair is the set
of positive features among an outer feature and an inner feature depending on it, and it is
well-formed when the inner feature entails the outer, so that the positive features form a
lower set of the two-element dependency chain. Lower sets of a chain are nested and number one
more than the chain, which is why two dependent features yield three cells, linearly ordered by
specification, and never a fourth. Person, number, gender and animacy features present their
carriers as containment pairs through `ContainmentPairLike`.

## Main definitions

* `Agreement.ContainmentPair`: the positive features of a valuation, a finset of
  `ContainmentPair.Feature`.
* `ContainmentPair.WellFormed`: the containment filter, a lower set of the dependency chain.
* `ContainmentPair.maximal`, `ContainmentPair.intermediate`, `ContainmentPair.minimal`: the
  three well-formed cells.
* `ContainmentPair.specLevel`: the number of positive features.
* `Agreement.ContainmentPairLike`: an injective presentation of a carrier as containment pairs.

## Main results

* `ContainmentPair.classification`: every well-formed pair is one of the three cells.
* `ContainmentPair.card_wellFormed`: there are three well-formed cells.
* `ContainmentPair.no_four_way`, `ContainmentPairLike.no_four_way`: no four distinct
  well-formed cells.

## Implementation notes

The skeleton is the descriptive containment filter of the feature-geometric tradition, not
Harbour's calculus, which rejects the filter and uses the filtered cell as the quadripartition
exclusive. That calculus lives at `Syntax/Minimalist/Phi/` and `Studies/Harbour2016.lean`.

## References

* [H. Harley and E. Ritter, *Person and number in pronouns* (2002)][harley-ritter-2002]
* [D. Adger and D. Harbour, *Why phi?* (2008)][adger-harbour-2008]
* [D. Harbour, *Impossible Persons* (2016)][harbour-2016]
-/

namespace Agreement

namespace ContainmentPair

/-- The two features, the inner depending on the outer. -/
inductive Feature where
  | outer
  | inner
  deriving DecidableEq, Repr, Fintype

/-- Position on the dependency chain, the outer feature below the inner. -/
def Feature.rank : Feature → Fin 2
  | .outer => 0
  | .inner => 1

instance : LinearOrder Feature := LinearOrder.lift' Feature.rank (by decide)

end ContainmentPair

/-- A valuation of two dependent bivalent features: the set of positive ones. -/
abbrev ContainmentPair := Finset ContainmentPair.Feature

namespace ContainmentPair

/-! ### The containment filter -/

/-- Containment: the inner feature entails the outer, so the positive features form a lower
set of the dependency chain. -/
def WellFormed (p : ContainmentPair) : Prop := IsLowerSet (↑p : Set Feature)

instance : DecidablePred WellFormed := fun _ ↦ inferInstanceAs (Decidable (IsLowerSet _))

/-- The most specified cell, both features positive: first person, singular. -/
def maximal : ContainmentPair := Finset.univ

/-- The intermediate cell, the outer feature alone: second person, dual. -/
def intermediate : ContainmentPair := {.outer}

/-- The least specified cell, no positive feature: third person, plural. -/
def minimal : ContainmentPair := ∅

@[simp] theorem maximal_wellFormed : maximal.WellFormed := by decide
@[simp] theorem intermediate_wellFormed : intermediate.WellFormed := by decide
@[simp] theorem minimal_wellFormed : minimal.WellFormed := by decide

/-- The filtered combination, the inner feature without the outer. -/
theorem not_wellFormed_singleton_inner : ¬ ({.inner} : ContainmentPair).WellFormed := by
  decide

/-- Every well-formed pair is one of the three cells. -/
theorem classification :
    ∀ p : ContainmentPair, p.WellFormed → p = maximal ∨ p = intermediate ∨ p = minimal := by
  decide

/-- On well-formed pairs the inner feature entails the outer. -/
theorem outer_mem_of_inner_mem :
    ∀ p : ContainmentPair, p.WellFormed → .inner ∈ p → .outer ∈ p := by
  decide

/-! ### The specification chain -/

/-- Specification level, the number of positive features. -/
def specLevel (p : ContainmentPair) : ℕ := p.card

@[simp] theorem spec_maximal : maximal.specLevel = 2 := by decide
@[simp] theorem spec_intermediate : intermediate.specLevel = 1 := by decide
@[simp] theorem spec_minimal : minimal.specLevel = 0 := by decide

/-- A pair has at most its two features. -/
theorem specLevel_le_two (p : ContainmentPair) : p.specLevel ≤ 2 :=
  (Finset.card_le_univ p).trans (by decide)

/-- Specification separates well-formed pairs. -/
theorem specLevel_injOn_wellFormed :
    ∀ p q : ContainmentPair, p.WellFormed → q.WellFormed → p.specLevel = q.specLevel → p = q :=
  fun _ _ hp hq h ↦ (hp.eq_iff_card_eq hq).2 h

/-- The markedness chain: the well-formed cells are the lower sets of the dependency chain,
linearly ordered by specification. -/
instance : LinearOrder {p : ContainmentPair // p.WellFormed} :=
  inferInstanceAs (LinearOrder {s : Finset Feature // IsLowerSet (↑s : Set Feature)})

/-- Two dependent features yield exactly three cells. -/
theorem card_wellFormed : Fintype.card {p : ContainmentPair // p.WellFormed} = 3 := by decide

private theorem no_four_way' :
    ∀ a b c d : {p : ContainmentPair // p.WellFormed},
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False := by
  decide +kernel

/-- No four distinct well-formed cells. -/
theorem no_four_way :
    ∀ a b c d : ContainmentPair,
      a.WellFormed → b.WellFormed → c.WellFormed → d.WellFormed →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False :=
  fun a b c d ha hb hc hd hab hac had hbc hbd hcd ↦
    no_four_way' ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩
      (fun h ↦ hab (congrArg Subtype.val h)) (fun h ↦ hac (congrArg Subtype.val h))
      (fun h ↦ had (congrArg Subtype.val h)) (fun h ↦ hbc (congrArg Subtype.val h))
      (fun h ↦ hbd (congrArg Subtype.val h)) (fun h ↦ hcd (congrArg Subtype.val h))

end ContainmentPair

/-! ### Carrier presentation -/

/-- An injective presentation of `α` as containment pairs, the `SetLike` pattern: a map plus
its injectivity, not a bijection, since a three-valued carrier such as an honorific scale
embeds onto the well-formed cells only. Well-formedness, specification and the three-cell
bound are inherited through it. -/
class ContainmentPairLike (α : Type*) where
  /-- Present an element as a containment pair. -/
  toPair : α → ContainmentPair
  /-- The presentation is faithful. -/
  toPair_injective : Function.Injective toPair

namespace ContainmentPairLike

variable {α : Type*} [ContainmentPairLike α]

/-- An instance from an outright equivalence, as for person, number and gender features. -/
@[reducible]
def ofEquiv {β : Type*} (e : β ≃ ContainmentPair) : ContainmentPairLike β :=
  ⟨e, e.injective⟩

theorem injective : Function.Injective (toPair (α := α)) :=
  toPair_injective

/-- Well-formedness through the presentation. -/
def WellFormed (a : α) : Prop := (toPair a).WellFormed

instance : DecidablePred (WellFormed (α := α)) :=
  fun a ↦ inferInstanceAs (Decidable (toPair a).WellFormed)

/-- Specification level through the presentation. -/
def specLevel (a : α) : ℕ := (toPair a).specLevel

/-- No four distinct well-formed elements of a presented carrier. -/
theorem no_four_way (a b c d : α)
    (ha : WellFormed a) (hb : WellFormed b) (hc : WellFormed c) (hd : WellFormed d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    False :=
  ContainmentPair.no_four_way (toPair a) (toPair b) (toPair c) (toPair d) ha hb hc hd
    (fun h ↦ hab (injective h)) (fun h ↦ hac (injective h)) (fun h ↦ had (injective h))
    (fun h ↦ hbc (injective h)) (fun h ↦ hbd (injective h)) (fun h ↦ hcd (injective h))

/-- The specification ordering transports to any presented triple landing on the three cells,
so person, number and gender inherit their hierarchy from one chain. -/
theorem specLevel_strict_order {a b c : α}
    (ha : toPair a = ContainmentPair.maximal) (hb : toPair b = ContainmentPair.intermediate)
    (hc : toPair c = ContainmentPair.minimal) :
    specLevel a > specLevel b ∧ specLevel b > specLevel c := by
  simp only [specLevel, ha, hb, hc]
  exact ⟨by decide, by decide⟩

end ContainmentPairLike

end Agreement
