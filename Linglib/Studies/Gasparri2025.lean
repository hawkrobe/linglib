import Linglib.Data.Examples.Gasparri2025

/-!
# Gasparri (2025): Bare Singular Names and Genericity
[gasparri-2025]

Journal of Semantics 42(1–2): 127–135.

Predicativists treat bare singular names (BSNs) like *Ruth* as predicative
DPs: ⟦∅ Ruth⟧ = ⟦the⟧ [λx. x is called Ruth]. If names are count nouns,
BSNs should pattern with definite singulars like *the tiger* for
genericity. The rows in `Data/Examples/Gasparri2025.json` show BSNs CAN
get generic readings, but exhibit **generic recalcitrance** — they are
harder to read generically than ordinary definite singulars, and need a
licensor (naming-convention context, Q-adverb, locative) to recover.

## Main declarations

- `genericOf` — judgment of a row's generic reading
- `generic_recalcitrance` — unlicensed BSNs resist generics; unlicensed
  definite singulars do not
- `licensing_enables_generic` — naming-convention contexts license BSN generics
- `quotation_rescues_kind_level` — kind-level predicates reject BSNs but
  accept quoted names and definite commons
-/

namespace Gasparri2025

open Data.Examples

/-- Judgment of the row's generic reading, if recorded. -/
def genericOf (row : LinguisticExample) : Option Features.Judgment :=
  (row.readings.find? (·.1 == "generic")).map (·.2)

/-- **Generic recalcitrance**: without a licensor, no bare singular name
    has an acceptable generic reading, while every definite common NP does.
    This is the asymmetry predicativism leaves unexplained: if *Ruth* is
    just ⟦the⟧ + a predicate, it should pattern with *the tiger*. -/
theorem generic_recalcitrance :
    ∀ row ∈ Examples.all, row.feature? "licensor" = some "none" →
      (genericOf row = some .acceptable ↔
        row.feature? "subject_type" = some "definite_common") := by
  decide

/-- Naming-convention contexts license generic readings of BSNs:
    recalcitrance is not a categorical ban. -/
theorem licensing_enables_generic :
    ∀ row ∈ Examples.all,
      row.feature? "subject_type" = some "bare_name" →
      row.feature? "licensor" = some "generic_context" →
        genericOf row = some .acceptable := by
  decide

/-- Kind-level predicates (*extinct*) accept definite commons and quoted
    names but not bare names: quotation rescues the kind-level parallel. -/
theorem quotation_rescues_kind_level :
    genericOf Examples.tristan_extinct = some .questionable ∧
    genericOf Examples.quoted_tristan_extinct = some .acceptable ∧
    genericOf Examples.dodo_extinct = some .acceptable := ⟨rfl, rfl, rfl⟩

end Gasparri2025
