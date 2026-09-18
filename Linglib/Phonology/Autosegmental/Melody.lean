/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Floating

/-!
# Lexical melodies

This file defines the melody of a morpheme, its underlying autosegmental contribution as an
input form, and shows that GEN keeps the sponsor of every element.

A melody consists of the autosegments and slots that one morpheme sponsors, with its lexical
pre-linking in melody-local coordinates. Pre-linking is a matter of analysis. A melody with
no lines is the universally unlinked underlying form of harmonic serialism, and a partially
linked one is a stratal form such as `/M^H/`. The valued, unvalued, and floating
autosegments of Rolle's typology of grammatical tone are the linked slots, the unlinked
slots, and the floating autosegments of the form. A word is the concatenation of the
melodies of its morphemes, as in the Generalized Nonlinear Affixation program.

## Main definitions

* `FloatingForm.melody`: the input form of one morpheme's autosegments, slots, and pre-links.

## Main results

* `FloatingForm.gen_preserves_morphemes`: GEN keeps every sponsor, which is Consistency of
  Exponence.

## References

* [rolle-2018]
* [wolf-2007]
* [pulleyblank-1986]
* [mccarthy-mullin-smith-2012]
* [mcpherson-lamont-2026]
* [jardine-heinz-2015]
* [bermudez-otero-2012]
* [bye-svenonius-2012]
* [zimmermann-2024]
-/

namespace Autosegmental

namespace FloatingForm

variable {S T M : Type*} (m : M) (tones : List T) (tbus : List S) (links : Finset (ℕ × ℕ))

/-- `melody m tones tbus links` is the input form of the morpheme `m`, with the autosegments
    `tones` over the slots `tbus` and the pre-links `links` in melody-local coordinates. -/
def melody : FloatingForm S T M :=
  input (.ofList (tones.map (⟨·, m⟩))) (.ofList (tbus.map (⟨·, m⟩))) links

@[simp] theorem melody_upper :
    (melody m tones tbus links).upper = .ofList (tones.map (⟨·, m⟩)) := rfl

@[simp] theorem melody_lower :
    (melody m tones tbus links).lower = .ofList (tbus.map (⟨·, m⟩)) := rfl

@[simp] theorem melody_links : (melody m tones tbus links).links = links := rfl

@[simp] theorem melody_deleted : (melody m tones tbus links).deleted = ∅ := rfl

@[simp] theorem melody_surfaceLinks : (melody m tones tbus links).surfaceLinks = links := rfl

@[simp] theorem isInput_melody : (melody m tones tbus links).IsInput := ⟨rfl, rfl⟩

/-- Every autosegment of a melody is sponsored by its morpheme. -/
theorem melody_upperMorpheme? {k : ℕ} (hk : k < tones.length) :
    (melody m tones tbus links).upperMorpheme? k = some m := by
  rw [upperMorpheme?, melody_upper, LabeledTuple.ofList_get?]
  simp [hk]

/-- Every slot of a melody is sponsored by its morpheme. -/
theorem melody_lowerMorpheme? {j : ℕ} (hj : j < tbus.length) :
    (melody m tones tbus links).lowerMorpheme? j = some m := by
  rw [lowerMorpheme?, melody_lower, LabeledTuple.ofList_get?]
  simp [hj]

/-- GEN never alters morphemic affiliation, so every one-step candidate carries its input's
    sponsors on both tiers. This is Consistency of Exponence. -/
theorem gen_preserves_morphemes [DecidableEq S] [DecidableEq T] [DecidableEq M]
    {f g : FloatingForm S T M} (hg : g ∈ f.gen) :
    g.upperMorpheme? = f.upperMorpheme? ∧ g.lowerMorpheme? = f.lowerMorpheme? := by
  refine ⟨funext fun k ↦ ?_, funext fun i ↦ ?_⟩
  · rw [upperMorpheme?, upperMorpheme?, upper_of_mem_gen hg]
  · rw [lowerMorpheme?, lowerMorpheme?, lower_of_mem_gen hg]

end FloatingForm

end Autosegmental
