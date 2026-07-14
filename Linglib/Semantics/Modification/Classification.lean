import Linglib.Semantics.Modification.Basic
import Linglib.Semantics.Intensional.Rigidity
import Mathlib.Order.PropInstances
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Common

/-!
# Modifier-meaning classification at the intensional carrier

We instantiate the order-theoretic modifier classes of
`Modification/Basic.lean` at intensional properties. The classification
goes back to [parsons-1970] and [kamp-1975] (definitions (4)–(7)) and
was consolidated in [kamp-partee-1995]; the modern labels are Partee's.

## Main definitions

* `Property W E`: intensional properties, `Intensional.Intension W (E → Prop)`.
* `isIntersective_iff`, `isPrivative_iff`: pointwise forms of the
  order-theoretic classes at this carrier.
* `isExtensional_of_isIntersective`: intersective modifier meanings are
  `Intensional.IsExtensional`.
* `not_isSubsective_of_isPrivative`: privative meanings with non-empty
  extension are not subsective.
* `RevisedClass`: [partee-2010]'s three-class hierarchy after the
  privative collapse.

## Implementation notes

Extensionality is orthogonal to the entailment hierarchy; the
independence witnesses are in `Studies/Kamp1975.lean`. Whether
*adjectives* uniformly denote `Modifier (Property W E)` is a
theoretical claim (`Studies/Elbourne2026.lean`); the carrier is named
for the denotation type, not the word class.
-/

namespace Modification

/-- An intensional property: an `Intensional.Intension` valued in
    characteristic predicates over entities (a function from worlds to
    predicates). -/
abbrev Property (W E : Type*) := Intensional.Intension W (E → Prop)

/-! ### Pointwise forms of the order-theoretic classes -/

section Hierarchy

open Modifier

variable {W E : Type*} {adj : Modifier (Property W E)}

/-- Pointwise form of `Modifier.isIntersective` at the intensional
    carrier: the extension at each world is the intersection of the
    noun's extension with some fixed property Q ([kamp-1975]
    definition (4), "predicative").

    Examples: "gray", "French", "carnivorous", "four-legged". -/
theorem isIntersective_iff :
    isIntersective adj ↔
      ∃ (Q : Property W E), ∀ (N : Property W E) (w : W) (x : E),
        adj N w x ↔ (Q w x ∧ N w x) := by
  simp only [isIntersective, funext_iff, Pi.inf_apply, inf_Prop_eq, eq_iff_iff]

/-- Pointwise form of `Modifier.isPrivative` at the intensional carrier:
    the extension is always disjoint from the noun's extension
    ([kamp-1975] definition (5)).

    Examples: "fake", "counterfeit".
    [partee-2010] argues this class should be eliminated. -/
theorem isPrivative_iff :
    isPrivative adj ↔
      ∀ (N : Property W E) (w : W) (x : E), adj N w x → ¬ N w x := by
  simp only [isPrivative, Pi.disjoint_iff, Prop.disjoint_iff, not_and]

/-! ### Implication structure

    Intersective → subsective holds at any carrier
    (`Modifier.isIntersective.isSubsective`); intersective → extensional
    and the privative/subsective incompatibility are stated here. The
    order-theoretic core of the latter is `Modifier.isPrivative.eq_bot`. -/

/-- Intersective modifier meanings are extensional: meet with a fixed
    property reads the noun only through its extension at each world. -/
theorem isExtensional_of_isIntersective (h : isIntersective adj) :
    Intensional.IsExtensional adj := by
  obtain ⟨Q, hQ⟩ := h
  intro w N₁ N₂ hN
  simp only [hQ, Pi.inf_apply, hN]

/-- Privative modifier meanings are not subsective (when the modifier has
    non-empty extension for some noun). -/
theorem not_isSubsective_of_isPrivative (hp : isPrivative adj)
    (hne : ∃ N w x, adj N w x) : ¬ isSubsective adj := by
  intro hs
  obtain ⟨N, w, x, hadj⟩ := hne
  exact isPrivative_iff.mp hp N w x hadj (hs N w x hadj)

end Hierarchy

/-! ### Revised hierarchy ([partee-2010])

The post-collapse 3-class hierarchy after eliminating "privative" via
noun coercion. Per [partee-2010] footnote 1, the hierarchy is
subset-ordered (intersective ⊂ subsective ⊂ unrestricted), not linear;
the enum picks the *narrowest fit* per adjective. The licensing
mechanism (NVP + HPP) is in
`Semantics/Modification/Coercion.lean`. -/

section Revised

variable {W E : Type*}

/-- Adjective hierarchy after [partee-2010]'s collapse: the
    privative class is eliminated in favor of subsective + noun coercion. -/
inductive RevisedClass where
  /-- `⟦A N⟧ = ⟦Q⟧ ∩ ⟦N⟧` (Kamp's intersective). -/
  | intersective
  /-- `⟦A N⟧ ⊆ ⟦N*⟧` — includes former "privatives" via coercion. -/
  | subsective
  /-- No entailment: alleged, potential, putative (the plain/modal
      non-subsective class). -/
  | nonSubsective
  deriving DecidableEq

/-- Predicate-level interpretation of `RevisedClass`. Per the subset
    ordering, `intersective` and `subsective` are not disjoint: every
    intersective modifier meaning satisfies `Modifier.isSubsective`
    (`Modifier.isIntersective.isSubsective`).

    Caveat on `.nonSubsective`: the membership condition `¬ isSubsective
    adj` is necessary but coarse — it also holds of Kamp-privatives,
    which under Partee's reanalysis are not supposed to exist as a
    natural class. Read `.nonSubsective` as Partee's *intended* "modal"
    class (alleged, potential, putative); the bare predicate
    `¬ isSubsective` over-generates. -/
def RevisedClass.satisfies : RevisedClass → Modifier (Property W E) → Prop
  | .intersective  => Modifier.isIntersective
  | .subsective    => Modifier.isSubsective
  | .nonSubsective => fun adj => ¬ Modifier.isSubsective adj

end Revised

end Modification
