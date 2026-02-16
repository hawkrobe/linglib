import Linglib.Core.Morphology.MorphRule

/-!
# Degree Morphology

Morphological rules for comparative and superlative degree marking
on adjectives.

Both rules are `isVacuous := true` because the semantic work
(degree quantification, MAX operator) lives in the Theory layer
(`Theories/Semantics.Montague/Adjective/Comparative.lean`), not in
the morphological rule itself. The morphological rules handle only
the formal side: surface form generation and feature marking.

## Examples

- Regular: tall → taller, tallest
- Irregular: good → better, best
- Periphrastic: expensive → "more expensive", "most expensive"

## References

- Kennedy, C. (2007). Vagueness and grammar.
- Kennedy, C. & McNally, L. (2005). Scale structure, degree modification.
-/

namespace Core.Morphology.Degree

/-- Comparative degree rule: generates the comparative form of an adjective.

    Regular formation appends "-er" to the lemma; irregular forms
    (e.g., "better", "more expensive") are supplied via `irregularForm`.

    Semantically vacuous at the morphological level — comparative
    semantics (degree quantification) is handled compositionally
    by `Semantics.Lexical.Adjective.Comparative`. -/
def comparativeRule (σ : Type) (irregularForm : Option String := none) : MorphRule σ :=
  { category := .degree
  , value := "comp"
  , formRule := λ lemma_ => irregularForm.getD (lemma_ ++ "er")
  , featureRule := id
  , semEffect := id
  , isVacuous := true }

/-- Superlative degree rule: generates the superlative form of an adjective.

    Regular formation appends "-est" to the lemma; irregular forms
    (e.g., "best", "most expensive") are supplied via `irregularForm`.

    Semantically vacuous at the morphological level — superlative
    semantics (MAX operator) is handled compositionally. -/
def superlativeRule (σ : Type) (irregularForm : Option String := none) : MorphRule σ :=
  { category := .degree
  , value := "super"
  , formRule := λ lemma_ => irregularForm.getD (lemma_ ++ "est")
  , featureRule := id
  , semEffect := id
  , isVacuous := true }

/-- Both degree rules are semantically vacuous. -/
theorem comparative_vacuous (σ : Type) (irr : Option String) :
    (comparativeRule σ irr).isVacuous = true := rfl

theorem superlative_vacuous (σ : Type) (irr : Option String) :
    (superlativeRule σ irr).isVacuous = true := rfl

/-- Both degree rules have category `.degree`. -/
theorem comparative_category (σ : Type) (irr : Option String) :
    (comparativeRule σ irr).category = .degree := rfl

theorem superlative_category (σ : Type) (irr : Option String) :
    (superlativeRule σ irr).category = .degree := rfl

end Core.Morphology.Degree
