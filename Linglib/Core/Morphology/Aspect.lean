import Linglib.Core.Morphology.MorphRule

/-!
# Aspect Morphology

Morphological rules for aspect marking on verbs.

All rules are `isVacuous := true` because the semantic work (event structure,
progressive, perfective) lives in the Theory layer
(`Theories/Semantics.Compositional/Verb/Aspect/`), not in the morphological rule itself.

## References

- Comrie, B. (1976). Aspect. Cambridge University Press.
- Bybee, J. L. (1985). Morphology. Benjamins.
-/

namespace Core.Morphology.Aspect

/-- Present participle rule: appends "-ing" to the lemma.

    Irregular forms (e.g., "running", "lying") are supplied via `irregularForm`.
    Semantically vacuous — progressive/gerundive semantics is handled in Theory. -/
def presPartRule (σ : Type) (irregularForm : Option String := none) : MorphRule σ :=
  { category := .aspect
  , value := "prespart"
  , formRule := λ lemma_ => irregularForm.getD (lemma_ ++ "ing")
  , featureRule := id
  , semEffect := id
  , isVacuous := true }

-- ════════════════════════════════════════════════════
-- § Verification Theorems
-- ════════════════════════════════════════════════════

theorem presPart_vacuous (σ : Type) (irr : Option String) :
    (presPartRule σ irr).isVacuous = true := rfl

theorem presPart_category (σ : Type) (irr : Option String) :
    (presPartRule σ irr).category = .aspect := rfl

end Core.Morphology.Aspect
