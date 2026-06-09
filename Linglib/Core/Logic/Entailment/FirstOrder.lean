import Mathlib.ModelTheory.Satisfiability
import Linglib.Core.Logic.Entailment.Basic

/-!
# First-order logical consequence as an `Entails` instance

mathlib's first-order semantic consequence `T ⊨ᵇ φ`
(`FirstOrder.Language.Theory.ModelsBoundedFormula`) is the instance of
`Core.Logic.Entailment.Valid` whose evaluation points are the *models of `T`* and whose
satisfaction relation is `sat M φ := M ⊨ φ` (`Sentence.Realize`). First-order premises are
folded into the theory `T`, so the premise-free `Valid` already captures FO consequence.

This is the **base case** of the shared entailment schema: any linglib fragment whose truth
conditions are genuinely first-order — e.g. DRT static truth, which already interprets DRSs
into `FirstOrder.Language.Structure`s via `DRS.Realize` — can route its entailment through
this bridge and inherit mathlib's first-order metatheory (compactness, completeness, Łoś,
elementary maps) rather than re-deriving it.

## Main results

* `valid_iff_models` — linglib `Valid` over `T`'s models, with `sat = Realize`, *is*
  mathlib's `T ⊨ᵇ φ`.
-/

open FirstOrder Language Core.Logic.Entailment

namespace Core.Logic.Entailment.FirstOrder

universe u v

variable {L : Language.{u, v}}

/-- **The base case**: `Core.Logic.Entailment.Valid` over the models of a first-order theory
`T`, with satisfaction `M ⊨ ψ` (`Sentence.Realize`), is exactly mathlib's first-order
semantic consequence `T ⊨ᵇ φ`. The two are definitionally the same `∀ M ⊨ T, M ⊨ φ`; the
bridge is `models_sentence_iff`. -/
theorem valid_iff_models (T : L.Theory) (φ : L.Sentence) :
    Valid (Pt := FirstOrder.Language.Theory.ModelType.{u, v, max u v} T)
      (fun M ψ => Sentence.Realize M ψ) φ ↔ T ⊨ᵇ φ :=
  FirstOrder.Language.Theory.models_sentence_iff.symm

end Core.Logic.Entailment.FirstOrder
