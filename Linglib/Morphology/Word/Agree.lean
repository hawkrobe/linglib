/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Agreement.Phi
import Linglib.Morphology.Word.Basic

/-!
# φ-agreement between word tokens

`Word.phi` is the bundle a word's features ingest as, and two words `Agree` when their
bundles are compatible, an unspecified dimension acting as a wildcard. The relation is
reflexive and symmetric but not transitive; `HasPhi.Agree` is its generic form.

## Implementation notes

* A word's number tag with no analytical value, the inverse, collective and count forms,
  ingests as `⊥`, so such a word agrees in number with anything.
-/

namespace Morphology

/-- The bundle a word's features ingest as. -/
def Word.phi (w : Word) : Agreement.Bundle := Agreement.Bundle.ofUD w.features

instance : HasPhi Word := ⟨Word.phi⟩

/-- Two words agree when their bundles are compatible, an unspecified dimension acting as a
wildcard; the agreement check binding and concord consumers share. -/
def Word.Agree (w1 w2 : Word) : Prop := Compat w1.phi w2.phi

/-- On word tokens, generic agreement is `Word.Agree`. -/
theorem Word.hasPhi_agree (w1 w2 : Word) : HasPhi.Agree w1 w2 ↔ w1.Agree w2 := Iff.rfl

instance (w1 w2 : Word) : Decidable (Word.Agree w1 w2) := by
  unfold Word.Agree; infer_instance

@[refl] theorem Word.Agree.refl (w : Word) : Word.Agree w w := Compat.of_le le_rfl le_rfl

@[symm] theorem Word.Agree.symm {w1 w2 : Word} (h : Word.Agree w1 w2) : Word.Agree w2 w1 :=
  Compat.symm h

/-- φ-agreement is not transitive: underspecified *they* agrees with both *she* and *he*
while *she* and *he* disagree. -/
theorem Word.Agree.not_transitive :
    ¬ ∀ w1 w2 w3 : Word, Word.Agree w1 w2 → Word.Agree w2 w3 → Word.Agree w1 w3 := by
  intro h
  exact absurd
    (h ⟨"she", .PRON, { person := some .third, number := some .Sing, gender := some .Fem }⟩
       ⟨"they", .PRON, { person := some .third }⟩
       ⟨"he", .PRON, { person := some .third, number := some .Sing, gender := some .Masc }⟩
       (by decide) (by decide))
    (by decide)

/-- A reflexive-marked token still agrees with an unmarked one: `reflex` is not an
agreement feature. -/
example : Word.Agree ⟨"sich", .PRON, { reflex := true }⟩ ⟨"Kind", .NOUN, {}⟩ := by decide

end Morphology
