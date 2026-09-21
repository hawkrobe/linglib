import Linglib.Studies.DeganoAloni2025
import Linglib.Studies.Dekier2021
import Linglib.Studies.Haspelmath1997

/-!
# Bubnov 2026: not all coexpressions are syncretisms

Indefinite pronouns coexpress the specific-known, specific-unknown and non-specific functions in
the four patterns AAA, ABB, AAB and ABC, never in the pattern ABA. A nanosyntactic account derives
that gap from a containment hierarchy whose most complex layer is the specific-known one. This file
formalizes the argument that the hierarchy is the wrong explanation and a semantic account is the
right one.

Two objections are formalized. The first is that a hierarchy spelled out by distinct exponents
predicts morphological containment — under the spellout the three Russian markers realize properly
nested structures — while no such containment is attested in any indefinite paradigm. The second
concerns diachrony: the attested changes extend a form's coverage in both directions along the
map, whereas losing a lexical entry can only extend the surviving entry's coverage downwards, so
the hierarchy predicts change in one direction only.

The semantic alternative replaces containment with restrictions on the variation and constancy of
the indefinite's value: a form is used wherever its restriction is met, so coexpression is
underspecification rather than syncretism. On that account the unattested pattern is the one whose
restriction is contradictory — constancy across all epistemic alternatives together with variation
inside one of them — and every attested diachronic change is a weakening of a restriction,
whichever direction it takes along the map.

## Main results

* `russian_spans_properly_nested` — the containment the nanosyntactic analysis predicts
* `type_vi_contradictory` — the unattested type's restriction cannot be met
* `uses_ne_skPlusNS_profile` — it is also the profile no connected region of the map covers
* `attested_changes_are_weakenings`, `attested_changes_gain_opposite_functions` — the two attested
  changes weaken a restriction while moving in opposite directions along the hierarchy
* `entry_loss_extends_downward_only` — losing an entry derives only one of them
* `paradigms_realize_types` — the attested paradigms across six languages instantiate the typology

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
(`DeganoAloni2025.not_requires_skPlusNS`), so the type can be stated only as a disjunction. -/

/-- The same type is the one the implicational map excludes: its profile skips the
specific-unknown function lying between the two it covers, so no connected region of the map
covers exactly its uses. The semantic account and the adjacency requirement rule out the same
cell for unrelated reasons. -/
theorem uses_ne_skPlusNS_profile {s : Finset HaspelmathFunction} (h : Contiguous s) :
    uses s ≠ DAType.skPlusNS.profile := fun he ↦ by
  have hk : Use.specificKnown ∈ uses s := he ▸ by decide
  have hn : Use.nonSpecific ∈ uses s := he ▸ by decide
  have hu : Use.specificUnknown ∈ uses s :=
    mem_uses.2 (Haspelmath1997.specificUnknown_mem_of_irrealis_mem h (mem_uses.1 hk)
      (mem_uses.1 hn))
  exact absurd (he ▸ hu) (by decide)

/-- No other type's profile skips it. -/
theorem other_profiles_contiguous (t : DAType) (h : t ≠ .skPlusNS)
    (hsk : Use.specificKnown ∈ t.profile) (hns : Use.nonSpecific ∈ t.profile) :
    Use.specificUnknown ∈ t.profile := by
  cases t <;> first | exact absurd rfl h | (revert hsk hns; decide)

/-! ### Diachrony -/

/-- Both attested changes weaken the restriction, so the form comes to cover more of the map: a
specific-unknown form becomes epistemic, and a non-specific form becomes epistemic. -/
theorem attested_changes_are_weakenings :
    DAType.specificUnknown.profile ⊆ DAType.epistemic.profile ∧
      DAType.nonSpecific.profile ⊆ DAType.epistemic.profile := by decide

/-- The two changes move in opposite directions along the hierarchy: one form gains the
non-specific function, at the bottom, and the other gains the specific-unknown function above it.
No rule that extends coverage in a single direction produces both. -/
theorem attested_changes_gain_opposite_functions :
    Use.nonSpecific ∈ DAType.epistemic.profile \ DAType.specificUnknown.profile ∧
      Use.specificUnknown ∈ DAType.epistemic.profile \ DAType.nonSpecific.profile := by
  decide

/-- The narrow entry of a language with a non-specific and a specific-unknown marker. -/
def nonSpecificRule : SpanRule 3 String := ⟨"A", 0, none⟩

/-- Its wider entry, spelling out the specific-unknown structure. -/
def specificUnknownRule : SpanRule 3 String := ⟨"B", 1, none⟩

/-- Losing the narrow entry lets the wider one spell out both structures, but losing the wider
entry leaves the narrow one unable to spell out the higher structure. So the loss of a lexical
entry derives the change from a specific-unknown form to an epistemic one, and never the change
from a non-specific form to an epistemic one — although both are attested. -/
theorem entry_loss_extends_downward_only :
    spellout [nonSpecificRule, specificUnknownRule] 0 = some "A" ∧
      spellout [nonSpecificRule, specificUnknownRule] 1 = some "B" ∧
      spellout [specificUnknownRule] 0 = some "B" ∧
      spellout [specificUnknownRule] 1 = some "B" ∧
      spellout [nonSpecificRule] 1 = none := by decide

/-! ### The typology on attested paradigms -/

/-- The types instantiated by the paradigms of six languages: English *some-* imposes no
restriction, Yakut *-ere* constancy within an epistemic alternative, Latin *ali-* variation across
them, Latin *-dam* and Russian *koe-* constancy across them, Kannada *-oo* the conjunction of
constancy within and variation across, and Russian *-nibud'*, Yakut *-eme* and Kannada *-aadaruu*
variation within one. -/
def witnesses : List (List Series × IndefinitePronoun × DAType) :=
  [(english, English.Indefinites.someEntry, .unmarked),
   (yakut, Yakut.Indefinites.ereEntry, .specific),
   (latin, Latin.Indefinites.aliEntry, .epistemic),
   (german, German.Indefinites.irgendEntry, .epistemic),
   (latin, Latin.Indefinites.damEntry, .specificKnown),
   (russian, Russian.Indefinites.koeEntry, .specificKnown),
   (kannada, Kannada.Indefinites.ooEntry, .specificUnknown),
   (russian, Russian.Indefinites.nibudEntry, .nonSpecific),
   (yakut, Yakut.Indefinites.emeEntry, .nonSpecific),
   (kannada, Kannada.Indefinites.aadaruuEntry, .nonSpecific)]

/-- Every witness is a series of its paradigm covering exactly the uses its type permits, on
the regions [haspelmath-1997] draws. -/
theorem paradigms_realize_types :
    ∀ w ∈ witnesses, ∃ s ∈ w.1, s.pronoun = w.2.1 ∧ Instantiates s w.2.2 := by decide

/-- Russian *-to* is the epistemic type, but the region drawn for it covers only the
specific-unknown function: *-nibud'* is the non-specific form of the same paradigm and takes
that function from it. Coverage is the restriction net of paradigmatic competition, which is why
the surface classification of *-to* is narrower than its type; the book's own example of
*kogo-to* under *xočet* 'wants' finds the non-specific reading possible beside the preferred
*-nibud'*. -/
theorem to_is_epistemic_under_competition :
    ∃ s ∈ russian, s.pronoun = Russian.Indefinites.toEntry ∧
      ConsistentWith s .epistemic ∧ ¬ Instantiates s .epistemic := by decide

/-- German *irgend-* instantiates the change from a non-specific form to an epistemic one, and its
epistemic restriction is the one the modal-indefinite literature attributes to it. -/
theorem irgend_is_epistemic :
    (∃ s ∈ german, s.pronoun = German.Indefinites.irgendEntry ∧ Instantiates s .epistemic) ∧
      DAType.nonSpecific.profile ⊆ DAType.epistemic.profile := by decide

end Bubnov2026
