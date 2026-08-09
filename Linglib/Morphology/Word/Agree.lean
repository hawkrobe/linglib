/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Features.Phi
import Linglib.Morphology.Word.Basic

/-!
# φ-agreement between word tokens

`Word.phi` projects a word's person, number, and gender. Two words `Agree` when
these features unify (`UD.MorphFeatures.compatible`), an unspecified feature
acting as a wildcard; the relation is reflexive and symmetric but not
transitive. `HasPhi.Agree` is its generic form.
-/

namespace Morphology

/-- The φ-feature subset (person, number, gender) of a word. -/
def Word.phi (w : Word) : UD.MorphFeatures :=
  { person := w.features.person, number := w.features.number,
    gender := w.features.gender }

instance : HasPhi Word := ⟨Word.phi⟩

/-- Two words agree when their φ-features (person, number, gender) are
    compatible, an unspecified feature acting as a wildcard. This is the
    feature-based agreement check binding and concord consumers share. -/
def Word.Agree (w1 w2 : Word) : Prop := w1.phi.compatible w2.phi

/-- On word tokens, generic agreement is `Word.Agree`. -/
theorem Word.hasPhi_agree (w1 w2 : Word) : HasPhi.Agree w1 w2 ↔ w1.Agree w2 := Iff.rfl

instance (w1 w2 : Word) : Decidable (Word.Agree w1 w2) := by
  unfold Word.Agree; infer_instance

@[refl] theorem Word.Agree.refl (w : Word) : Word.Agree w w :=
  UD.MorphFeatures.compatible_self w.phi

/-- φ-agreement is symmetric. -/
@[symm] theorem Word.Agree.symm {w1 w2 : Word} (h : Word.Agree w1 w2) :
    Word.Agree w2 w1 := by
  unfold Word.Agree at h ⊢
  rwa [UD.MorphFeatures.compatible_comm]

/-- φ-agreement is not transitive; underspecified *they* agrees with both
    *she* and *he* while *she* and *he* disagree. -/
theorem Word.Agree.not_transitive :
    ¬ ∀ w1 w2 w3 : Word, Word.Agree w1 w2 → Word.Agree w2 w3 → Word.Agree w1 w3 := by
  intro h
  exact absurd
    (h ⟨"she", .PRON, { person := some .third, number := some .Sing, gender := some .Fem }⟩
       ⟨"they", .PRON, { person := some .third }⟩
       ⟨"he", .PRON, { person := some .third, number := some .Sing, gender := some .Masc }⟩
       (by decide) (by decide))
    (by decide)

/-- φ-agreement entails number compatibility (`HasNumber.Compatible`). -/
theorem Word.Agree.hasNumber_compatible {w1 w2 : Word} (h : w1.Agree w2) :
    HasNumber.Compatible w1 w2 :=
  UD.MorphFeatures.compatible_hasNumber (f1 := w1.phi) (f2 := w2.phi) h

-- `reflex` is deliberately not an agreement feature: a reflexive-marked token still
-- agrees with an unmarked one (the φ-projection drops it).
example : Word.Agree ⟨"sich", .PRON, { reflex := true }⟩ ⟨"Kind", .NOUN, {}⟩ := by decide

end Morphology
