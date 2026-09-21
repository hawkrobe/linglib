import Linglib.Studies.DeganoAloni2025
import Linglib.Studies.Dekier2021
import Linglib.Studies.Haspelmath1997

/-!
# Bubnov (2026): Not all coexpressions are syncretisms

Indefinite pronouns coexpress the specific known, specific unknown and non-specific functions in
the four patterns AAA, ABB, AAB and ABC, never in the pattern ABA. The nanosyntactic account of
[dekier-2021] derives that gap from a containment hierarchy whose most complex layer is the
specific known one. [bubnov-2026] argues that the hierarchy is the wrong explanation and the
semantic account of [degano-aloni-2025] the right one.

Two objections are formalized. The first is that a hierarchy spelled out by distinct exponents
predicts morphological containment — under the spellout the three Russian markers realize properly
nested structures — while no such containment is attested in any indefinite paradigm. The second
concerns diachrony: the attested changes extend a form's coverage in both directions along the
map, whereas the loss of a lexical entry never lets a surviving entry spell out a layer above the
one it stores, so the hierarchy predicts change in one direction only.

The semantic alternative replaces containment with restrictions on the variation and constancy of
the indefinite's value: a form is used wherever its restriction is met, so coexpression is
underspecification rather than syncretism. On that account the unattested pattern is the one whose
two restrictions exclude each other, constancy across all epistemic alternatives and variation
inside one of them, so that it can be stated only as a disjunction, and every attested diachronic
change is a weakening of a restriction, whichever direction it takes along the map.

## Main results

* `russian_spans_properly_nested`: the containment the nanosyntactic analysis predicts.
* `attested_changes_are_weakenings`, `attested_changes_gain_opposite_functions`: the attested
  changes weaken a restriction while moving in opposite directions along the hierarchy.
* `entry_loss_extends_downward_only`: losing entries extends coverage only downwards.
* `coexpression_is_underspecification`: each form of the four coexpression patterns is a single
  type.

## References

* [bubnov-2026]
* [dekier-2021]
* [degano-aloni-2025]
* [haspelmath-1997]
* [aloni-port-2015]
-/

namespace Bubnov2026

open DeganoAloni2025 Dekier2021 Indefinite Morphology.Containment
open Haspelmath1997 (Series english german latin yakut kannada)

/-! ### The containment the hierarchy predicts -/

/-- Under the nanosyntactic analysis the three Russian markers spell out properly nested
structures: *-nibud'* the bare non-specific layer, *-to* that layer with the specific-unknown one
above it, *koe-* all three. Distinct exponents for nested structures are what morphological
containment consists in, and none is attested in any indefinite paradigm. -/
theorem russian_spans_properly_nested :
    (spelloutWinner (lexicon russian) 0).map SpanRule.spans = some 0 ∧
      (spelloutWinner (lexicon russian) 1).map SpanRule.spans = some 1 ∧
      (spelloutWinner (lexicon russian) 2).map SpanRule.spans = some 2 := by
  decide

/-! ### The unattested type

The unattested type would have to require constancy of the value across all epistemic
alternatives and variation of it within one of them at once, which cannot be met
(`DeganoAloni2025.not_var_of_dep_empty`), so the type can be stated only as a disjunction, and
the disjunction is the one requirement that is not convex
(`DeganoAloni2025.IndefiniteType.not_ordConnected_skPlusNS`). It is also the pattern ABA: its
profile is the one no connected region of the map covers
(`DeganoAloni2025.uses_ne_skPlusNS_profile`), and the convex requirements are exactly the
connected profiles (`DeganoAloni2025.contiguous_profile_iff`). -/

/-! ### Diachrony -/

/-- The attested changes weaken the restriction, so the form comes to cover more of the map: a
specific unknown form becomes epistemic, a non-specific form becomes epistemic, as German
*irgend-* did ([aloni-port-2015]), and an epistemic form becomes unmarked. -/
theorem attested_changes_are_weakenings {V E : Type*} (T : Finset (V → E)) (v x : V) :
    (IndefiniteType.specificUnknown.Requires T v x → IndefiniteType.epistemic.Requires T v x) ∧
      (IndefiniteType.nonSpecific.Requires T v x → IndefiniteType.epistemic.Requires T v x) ∧
      (IndefiniteType.epistemic.Requires T v x → IndefiniteType.unmarked.Requires T v x) :=
  ⟨And.right, Team.Var.anti (Finset.empty_subset _), fun _ ↦ trivial⟩

/-- The two changes move in opposite directions along the hierarchy: one form gains the
non-specific function, at the bottom, and the other gains the specific-unknown function above it.
No rule that extends coverage in a single direction produces both. -/
theorem attested_changes_gain_opposite_functions :
    Use.nonSpecific ∈
        IndefiniteType.epistemic.profile \ IndefiniteType.specificUnknown.profile ∧
      Use.specificUnknown ∈
        IndefiniteType.epistemic.profile \ IndefiniteType.nonSpecific.profile := by
  decide

/-- The narrow entry of a language with a non-specific and a specific-unknown marker. -/
def nonSpecificRule : SpanRule 3 String := ⟨"A", 0, none⟩

/-- Its wider entry, spelling out the specific-unknown structure. -/
def specificUnknownRule : SpanRule 3 String := ⟨"B", 1, none⟩

/-- Losing the narrow entry lets the wider one spell out both structures, the change from a
specific unknown form to an epistemic one, while losing the wider entry leaves the narrow one
unable to spell out the higher structure. -/
theorem entry_loss_example :
    spellout [nonSpecificRule, specificUnknownRule] = ![some "A", some "B", none] ∧
      spellout [specificUnknownRule] = ![some "B", some "B", none] ∧
      spellout [nonSpecificRule] = ![some "A", none, none] := by decide

/-- Whatever entries a lexicon loses, a surviving entry spells out only layers of the structure
it stores: the loss of an entry extends coverage downwards and never upwards, so it derives the
change from a specific unknown form to an epistemic one and never the change from a non-specific
form to an epistemic one, although both are attested. -/
theorem entry_loss_extends_downward_only {n : ℕ} {v v' : List (SpanRule n String)}
    (hv : v'.Sublist v) {g : Fin n} {it : SpanRule n String}
    (h : spelloutWinner v' g = some it) : it ∈ v ∧ g ≤ it.spans :=
  ⟨hv.subset (spelloutWinner_spec h).1, le_spans_of_spelloutWinner_eq_some h⟩

/-! ### Coexpression as underspecification -/

/-- Each form of the four coexpression patterns is a single type: English *some-* imposes no
restriction (AAA), Yakut *-eme* requires variation within an epistemic alternative and *-ere*
constancy within one (ABB), Latin *ali-* requires variation across the alternatives and *-dam*
constancy across them (AAB), and Russian *-nibud'*, *-to* and *koe-* require variation within an
alternative, variation across them and constancy across them (ABC). -/
theorem coexpression_is_underspecification :
    (∃ s ∈ english, s.pronoun = English.Indefinites.someEntry ∧ Instantiates s .unmarked) ∧
      (∃ s ∈ yakut, s.pronoun = Yakut.Indefinites.emeEntry ∧ Instantiates s .nonSpecific) ∧
      (∃ s ∈ yakut, s.pronoun = Yakut.Indefinites.ereEntry ∧ Instantiates s .specific) ∧
      (∃ s ∈ latin, s.pronoun = Latin.Indefinites.aliEntry ∧ Instantiates s .epistemic) ∧
      (∃ s ∈ latin, s.pronoun = Latin.Indefinites.damEntry ∧ Instantiates s .specificKnown) ∧
      (∃ s ∈ russian, s.pronoun = Russian.Indefinites.nibudEntry ∧ Instantiates s .nonSpecific) ∧
      (∃ s ∈ russian, s.pronoun = Russian.Indefinites.toEntry ∧ Instantiates s .epistemic) ∧
      ∃ s ∈ russian, s.pronoun = Russian.Indefinites.koeEntry ∧ Instantiates s .specificKnown := by
  decide

/-- Russian *-to* is the epistemic type on the region [haspelmath-1997] draws for it, which
covers the specific-unknown and the non-specific function, while the nanosyntactic lexicon
leaves it the specific-unknown layer alone: *-nibud'* is the non-specific form of the same
paradigm and takes that layer by the Elsewhere Principle. What a form may express and what it
spells out under paradigmatic competition come apart. -/
theorem to_is_epistemic_under_competition :
    (∃ s ∈ russian, s.pronoun = Russian.Indefinites.toEntry ∧ Instantiates s .epistemic) ∧
      spellout (lexicon russian) 0 = some "kto-nibud'" := by decide

end Bubnov2026
