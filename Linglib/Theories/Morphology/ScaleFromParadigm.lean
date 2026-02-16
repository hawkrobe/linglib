import Linglib.Core.MorphRule
import Linglib.Core.HornScale

/-!
# Scale Generation from Morphological Paradigms

Derives Horn scales automatically from adjective paradigms. Given a stem
with comparative and superlative rules, we can construct the scale
`⟨positive, comparative, superlative⟩` — ordered from weakest to strongest.

This connects morphological infrastructure (`Core/Morphology/`) to
scalar-alternative infrastructure (`Core/HornScale.lean`), enabling
automatic generation of the alternatives needed for scalar implicature
computation.

## Main definitions

- `MorphScale`: a Horn scale with its originating forms tracked
- `adjectiveScale`: extracts a degree scale from a stem's paradigm
- `morphologicalAlternatives`: returns paradigm-mates as scalar alternatives

## References

- Horn, L. R. (1972). On the Semantic Properties of Logical Operators in English.
- Kennedy, C. (2007). Vagueness and grammar.
-/

namespace Core.Morphology.ScaleFromParadigm

open Core.Scale (HornScale strongerAlternatives weakerAlternatives)

/-- A morphologically-derived Horn scale, tracking the positive,
    comparative, and superlative forms. -/
structure MorphScale where
  /-- The positive (base) form -/
  positive : String
  /-- The comparative form -/
  comparative : String
  /-- The superlative form -/
  superlative : String
  deriving Repr, BEq

/-- Convert a `MorphScale` to a `HornScale String`, ordered from
    weakest (positive) to strongest (superlative). -/
def MorphScale.toHornScale (ms : MorphScale) : HornScale String :=
  ⟨[ms.positive, ms.comparative, ms.superlative]⟩

/-- Extract a degree scale from a stem's paradigm.

    Looks for rules with `category = .degree` and `value = "comp"` / `"super"`,
    and builds a 3-point scale `[positive, comparative, superlative]`.
    Returns `none` if either the comparative or superlative rule is missing. -/
def adjectiveScale {σ : Type} (stem : Stem σ) : Option MorphScale :=
  let compRule := stem.paradigm.find? (λ r => r.category == .degree && r.value == "comp")
  let superRule := stem.paradigm.find? (λ r => r.category == .degree && r.value == "super")
  match compRule, superRule with
  | some comp, some super_ =>
    some { positive := stem.lemma_
         , comparative := comp.formRule stem.lemma_
         , superlative := super_.formRule stem.lemma_ }
  | _, _ => none

/-- Given a stem and a form (positive, comparative, or superlative),
    return the paradigm-mates as scalar alternatives.

    Returns all scale members except the given form, preserving
    scale order (weakest to strongest). -/
def morphologicalAlternatives {σ : Type} (stem : Stem σ) (form : String) :
    List String :=
  match adjectiveScale stem with
  | none => []
  | some ms =>
    let scale := ms.toHornScale
    scale.members.filter (· != form)

end Core.Morphology.ScaleFromParadigm
