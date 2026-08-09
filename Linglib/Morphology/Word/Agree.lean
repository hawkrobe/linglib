/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Word.Basic

/-!
# φ-agreement between word tokens

The φ-projection (`Word.phi`: person, number, gender) and the agreement
relation it induces: two tokens agree when their φ-features unify
(`UD.MorphFeatures.compatible`), an unspecified feature acting as a wildcard.
A reflexive, symmetric tolerance relation — not transitive
(`Word.Agree.not_transitive`). The feature-based agreement check binding and
concord consumers share; `Proform.Agree` is its carrier-generic form.
-/

namespace Morphology

/-- The φ-feature subset (person, number, gender) of a word. -/
def Word.phi (w : Word) : UD.MorphFeatures :=
  { person := w.features.person, number := w.features.number,
    gender := w.features.gender }

/-- φ-agreement between two words: their person/number/gender features are
    compatible (an unspecified feature is a wildcard). A reflexive, symmetric
    *tolerance* relation on `Word` (not transitive), decided by the shared
    `UD.MorphFeatures.compatible`. The feature-based agreement check binding
    and concord consumers share — no surface-form gender lookup. -/
def Word.Agree (w1 w2 : Word) : Prop := w1.phi.compatible w2.phi

instance (w1 w2 : Word) : Decidable (Word.Agree w1 w2) := by
  unfold Word.Agree; infer_instance

@[refl] theorem Word.Agree.refl (w : Word) : Word.Agree w w :=
  UD.MorphFeatures.compatible_self w.phi

/-- φ-agreement is symmetric — the docstring's "symmetric tolerance relation",
    as a theorem. -/
@[symm] theorem Word.Agree.symm {w1 w2 : Word} (h : Word.Agree w1 w2) :
    Word.Agree w2 w1 := by
  unfold Word.Agree at h ⊢
  rwa [UD.MorphFeatures.compatible_comm]

/-- φ-agreement is *not* transitive: an unspecified feature is a wildcard, so
    underspecified *they* agrees with both *she* and *he* while *she ≁ he*. -/
theorem Word.Agree.not_transitive :
    ¬ ∀ w1 w2 w3 : Word, Word.Agree w1 w2 → Word.Agree w2 w3 → Word.Agree w1 w3 := by
  intro h
  exact absurd
    (h ⟨"she", .PRON, { person := some .third, number := some .Sing, gender := some .Fem }⟩
       ⟨"they", .PRON, { person := some .third }⟩
       ⟨"he", .PRON, { person := some .third, number := some .Sing, gender := some .Masc }⟩
       (by decide) (by decide))
    (by decide)

/-- φ-agreement entails number compatibility: the `HasNumber` mixin never
    diverges from the agreement check on `Word`. -/
theorem Word.Agree.hasNumber_compatible {w1 w2 : Word} (h : w1.Agree w2) :
    HasNumber.Compatible w1 w2 :=
  UD.MorphFeatures.compatible_hasNumber (f1 := w1.phi) (f2 := w2.phi) h

-- `reflex` is deliberately not an agreement feature: a reflexive-marked token still
-- agrees with an unmarked one (the φ-projection drops it).
example : Word.Agree ⟨"sich", .PRON, { reflex := true }⟩ ⟨"Kind", .NOUN, {}⟩ := by decide

end Morphology
