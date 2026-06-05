import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Order.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Containment Feature Pairs

A pair of bivalent features whose inner member entails the outer
([+inner] → [+outer]): the two-feature *dependency* skeleton of the
feature-geometric tradition ([harley-ritter-2002]), stated over bivalent
values with the dependency carried as a cooccurrence filter — what
[adger-harbour-2008] call a "filter system … designating some semantically
possible [combinations] as geometrically illicit" (their Structure theme).

The pattern recurs across φ-feature domains:

- **Person**: [±author] (inner) ⊂ [±participant] (outer)
- **Number**: [±atomic] (inner) ⊂ [±minimal] (outer)
- **Gender**: [±neuter] (inner) ⊂ [±feminine] (outer)

with honorific-level and animacy instances joining the same skeleton.
The filter cuts the four bivalent cells to **three**, linearly ordered by
specification (the "size of structure" markedness metric of
[adger-harbour-2008]):

| outer | inner | Status         | Person      | Number   |
|-------|-------|----------------|-------------|----------|
|   +   |   +   | most specified | 1st person  | singular |
|   +   |   −   | intermediate   | 2nd person  | dual     |
|   −   |   −   | least specified| 3rd person  | plural   |
|   −   |   +   | **filtered**   | —           | —        |

## Main declarations

* `ContainmentPair` — the bivalent pair carrier (all four cells)
* `ContainmentPair.WellFormed` — the containment filter, as the Bool order
  fact `inner ≤ outer`; the well-formed cells carry a `LinearOrder`
  (specification chain) and have `Fintype.card` three
* `ContainmentPairLike` — injective presentation of a carrier type as
  containment pairs (the `SetLike` pattern); `no_four_way`, `specLevel`,
  and `WellFormed` are inherited through it
* `ContainmentPairLike.ofEquiv` — instance constructor for carriers that
  are outright equivalent to the pair (person, number, gender features)

## Implementation notes

Well-formedness is order theory, not stipulation: writing the valuation as
a map from the two-element dependency chain {outer < inner} to `Bool`,
`WellFormed` says the valuation is antitone in dependency — equivalently,
the positively-valued features form a lower set of the chain. Lower sets
of an n-chain form an (n+1)-chain, whence three cells from two features,
the `LinearOrder`, and the impossibility of a fourth cell; longer
dependency chains (e.g. [±proximate] above person, `Phi/Geometry.lean`)
yield n+1 cells the same way.

**This skeleton is not [harbour-2016]'s system** (which this file's
docstring previously claimed). *Impossible Persons* argues against both
ingredients: against cooccurrence filters (ch. 9.4 — "missing feature
combinations are not to be reified as universal principles"; feature
cooccurrence is free, constrained only by the logic of the semantics) and
for semantically active bivalence with order-of-composition effects
(ch. 9.2, 9.5). In Harbour's calculus the filtered cell is *used*:
`+author(−participant(π))` is the exclusive in the quadripartition and an
available representation of Germanic third person in the tripartition
(ch. 8.3.1, 9.2). The Harbour calculus proper lives at
`Syntax/Minimalist/Phi/` (lattice operations `⊕`/`⊖`) and
`Studies/Harbour2016.lean` (`signOf`); this file is the *descriptive*
containment skeleton that calculus refines and in part rejects.
-/

namespace Features

/-- A pair of bivalent features with a containment (dependency) relation:
    bearing the inner feature entails bearing the outer one. The carrier
    holds all four bivalent cells; the filter is `WellFormed`.

    Instances present their carriers via `ContainmentPairLike`:
    person (`outer` = participant, `inner` = author), number
    (`outer` = minimal, `inner` = atomic), gender, animacy, honorific level. -/
structure ContainmentPair where
  /-- The entailed (outer, dominating) feature. -/
  outer : Bool
  /-- The entailing (inner, dependent) feature — implies `outer`. -/
  inner : Bool
  deriving DecidableEq, Repr, Inhabited, BEq, Fintype

namespace ContainmentPair

/-! ### The containment filter -/

/-- Containment: the inner feature entails the outer — equivalently
    `inner ≤ outer` in `Bool`'s order, so the valuation is antitone in
    dependency and the positive features form a lower set of the
    dependency chain. -/
def WellFormed (p : ContainmentPair) : Prop :=
  p.inner → p.outer

instance : DecidablePred WellFormed :=
  fun p => inferInstanceAs (Decidable (p.inner = true → p.outer = true))

/-! ### Canonical cells -/

/-- Most specified cell: [+outer, +inner].
    Person: 1st (speaker). Number: singular (atom). -/
def maximal : ContainmentPair := ⟨true, true⟩

/-- Intermediate cell: [+outer, −inner].
    Person: 2nd (non-speaker participant). Number: dual (minimal non-atom). -/
def intermediate : ContainmentPair := ⟨true, false⟩

/-- Least specified cell: [−outer, −inner].
    Person: 3rd (non-participant). Number: plural (non-minimal non-atom). -/
def minimal : ContainmentPair := ⟨false, false⟩

@[simp] theorem maximal_wellFormed : maximal.WellFormed := by decide
@[simp] theorem intermediate_wellFormed : intermediate.WellFormed := by decide
@[simp] theorem minimal_wellFormed : minimal.WellFormed := by decide

/-- The unique filtered combination: [−outer, +inner]. -/
theorem illFormed_only : ¬ (⟨false, true⟩ : ContainmentPair).WellFormed := by
  decide

/-- Every well-formed pair is one of the three canonical cells. -/
theorem classification :
    ∀ p : ContainmentPair, p.WellFormed →
      p = maximal ∨ p = intermediate ∨ p = minimal := by
  decide

/-- Inner entails outer on well-formed pairs. -/
theorem inner_implies_outer :
    ∀ p : ContainmentPair, p.WellFormed → p.inner = true → p.outer = true := by
  decide

/-! ### The specification chain

The well-formed cells form a three-element linear order — the
"size of structure" markedness chain ([adger-harbour-2008]):
`minimal < intermediate < maximal`. -/

/-- Specification level: the number of positive features.
    `maximal ↦ 2`, `intermediate ↦ 1`, `minimal ↦ 0`. On well-formed
    pairs this is injective and realizes the markedness chain. -/
def specLevel (p : ContainmentPair) : Nat :=
  p.outer.toNat + p.inner.toNat

@[simp] theorem spec_maximal : maximal.specLevel = 2 := rfl
@[simp] theorem spec_intermediate : intermediate.specLevel = 1 := rfl
@[simp] theorem spec_minimal : minimal.specLevel = 0 := rfl

/-- The chain in concrete form: specification strictly descends
    `maximal > intermediate > minimal`. -/
theorem spec_strict_order :
    maximal.specLevel > intermediate.specLevel ∧
    intermediate.specLevel > minimal.specLevel :=
  ⟨by decide, by decide⟩

/-- `specLevel` separates well-formed pairs. -/
theorem specLevel_injOn_wellFormed :
    ∀ p q : ContainmentPair, p.WellFormed → q.WellFormed →
      p.specLevel = q.specLevel → p = q := by decide

/-- The markedness chain: well-formed pairs are linearly ordered by
    specification level. -/
instance : LinearOrder {p : ContainmentPair // p.WellFormed} :=
  LinearOrder.lift' (fun p => p.val.specLevel)
    (fun p q h =>
      Subtype.ext (specLevel_injOn_wellFormed _ _ p.property q.property h))

/-- Two dependent bivalent features yield exactly three cells — lower sets
    of a 2-chain form a 3-chain. -/
theorem card_wellFormed : Fintype.card {p : ContainmentPair // p.WellFormed} = 3 := by
  show (Finset.univ : Finset {p : ContainmentPair // p.WellFormed}).card = 3
  refine Finset.card_eq_three.mpr
    ⟨⟨maximal, maximal_wellFormed⟩, ⟨intermediate, intermediate_wellFormed⟩,
     ⟨minimal, minimal_wellFormed⟩,
     fun h => absurd (congrArg (fun p => p.val.specLevel) h) (by decide),
     fun h => absurd (congrArg (fun p => p.val.specLevel) h) (by decide),
     fun h => absurd (congrArg (fun p => p.val.specLevel) h) (by decide), ?_⟩
  ext d
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  rcases classification d.val d.property with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))

/-- **No four-way distinction.** Four distinct well-formed pairs are
    impossible — a corollary of `card_wellFormed`, checked directly.

    For person: no language draws a 4-way distinction from one containment
    pair; for number: likewise for base number. (The *filter*, not the
    arithmetic, is the theoretical commitment — [harbour-2016] ch. 9.4
    rejects it and generates a 4th person as the quadripartition exclusive;
    see the module docstring.) -/
theorem no_four_way :
    ∀ a b c d : ContainmentPair,
      a.WellFormed → b.WellFormed → c.WellFormed → d.WellFormed →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False := by
  intro a b c d ha hb hc hd hab hac had hbc hbd hcd
  rcases classification a ha with rfl | rfl | rfl <;>
    rcases classification b hb with rfl | rfl | rfl <;>
      rcases classification c hc with rfl | rfl | rfl <;>
        rcases classification d hd with rfl | rfl | rfl <;>
          simp_all

end ContainmentPair

/-! ### Carrier presentation -/

/-- An injective presentation of `α` as containment pairs (the `SetLike`
    pattern: a coercion-like map plus injectivity, not a bijection — a
    three-valued carrier such as an honorific scale embeds onto the
    well-formed cells only). `WellFormed`, `specLevel`, and `no_four_way`
    are inherited through the embedding. -/
class ContainmentPairLike (α : Type*) where
  /-- Present an element as a containment pair. -/
  toPair : α → ContainmentPair
  /-- The presentation is faithful. -/
  toPair_injective : Function.Injective toPair

namespace ContainmentPairLike

variable {α : Type*} [ContainmentPairLike α]

/-- Build an instance from an outright equivalence (person, number, and
    gender features are bivalent pair records, hence equivalent carriers). -/
@[reducible]
def ofEquiv {β : Type*} (e : β ≃ ContainmentPair) : ContainmentPairLike β :=
  ⟨e, e.injective⟩

theorem injective : Function.Injective (toPair (α := α)) :=
  toPair_injective

/-- Well-formedness through the presentation. -/
def WellFormed (a : α) : Prop := (toPair a).WellFormed

instance : DecidablePred (WellFormed (α := α)) :=
  fun a => inferInstanceAs (Decidable (toPair a).WellFormed)

/-- Specification level through the presentation. -/
def specLevel (a : α) : Nat := (toPair a).specLevel

/-- No four-way distinction for any presented carrier. -/
theorem no_four_way [DecidableEq α] (a b c d : α)
    (ha : WellFormed a) (hb : WellFormed b)
    (hc : WellFormed c) (hd : WellFormed d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : False :=
  ContainmentPair.no_four_way
    (toPair a) (toPair b) (toPair c) (toPair d)
    ha hb hc hd
    (fun h => hab (injective h)) (fun h => hac (injective h))
    (fun h => had (injective h)) (fun h => hbc (injective h))
    (fun h => hbd (injective h)) (fun h => hcd (injective h))

/-- The specification ordering transports to any presented triple landing
on the three cells. Person (`1 > 2 > 3`), number (`sg > du > pl`), and
gender inherit their hierarchy from this single chain fact rather than
re-checking it per domain. -/
theorem specLevel_strict_order {a b c : α}
    (ha : toPair a = ContainmentPair.maximal)
    (hb : toPair b = ContainmentPair.intermediate)
    (hc : toPair c = ContainmentPair.minimal) :
    specLevel a > specLevel b ∧ specLevel b > specLevel c := by
  simp only [specLevel, ha, hb, hc]
  exact ⟨by decide, by decide⟩

end ContainmentPairLike

end Features
